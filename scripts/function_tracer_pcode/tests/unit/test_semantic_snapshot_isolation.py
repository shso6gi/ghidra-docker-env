# -*- coding: utf-8 -*-
"""凍結後の意味が生 object から切り離されていること（計画 B8 / B11 / B12）。

`runtime_ref` / `storage_info` / `data_type_obj` は **意味そのものではなく**、
意味を一度だけ読み取る元になる生 object。凍結後にそれらが変わっても、
structural key・solver query identity・SMT 出力・unknown 宣言・幅は動かない。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.core.semantic_projection import canonical_atom
from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.render_smt import expression_smt_bit_width
from scripts.function_tracer_pcode.core.render_smt.unknowns import (
    collect_unknown_smt_declarations,
)
from scripts.function_tracer_pcode.core.render_smt.widths import (
    _expr_prefers_signed_extension,
)
from scripts.function_tracer_pcode.core import structural
from scripts.function_tracer_pcode.core.semantic_snapshot import semantic_projection
from scripts.function_tracer_pcode.tests.unit._publication import published


class MutableRuntimeRef:
    """あとから中身が変わる runtime ref（意味に混ぜてはいけない生 object）。"""

    def __init__(self, key):
        self.key = key

    def stable_key(self):
        return self.key

    def semantic_key(self):
        return self.key


class MutableStorage:
    def __init__(self, key):
        self.key = key
        self.size = 4
        self.is_register = True
        self.register_name = "r0"

    def storage_identity_key(self):
        return self.key


class MutableDataType:
    def __init__(self, signed):
        self.signed = signed

    def isSigned(self):  # noqa: N802 - Ghidra の API 名に合わせる
        return self.signed

    def getName(self):  # noqa: N802
        return "int" if self.signed else "uint"


def _unknown_expression():
    ref = MutableRuntimeRef(("unknown_source", 1))
    return Expression.unknown("u", runtime_ref=ref), ref


def _memory_expression():
    ref = MutableRuntimeRef(("mem", 1))
    return (
        Expression.memory(
            Expression.parameter("a", 0, size=8), size=4, read_order_key=0, runtime_ref=ref
        ),
        ref,
    )


def _parameter_expression():
    ref = MutableRuntimeRef(("parameter", 0, "a"))
    storage = MutableStorage(("stack", -16))
    data_type = MutableDataType(True)
    expr = Expression.parameter(
        "a", 0, size=4, storage_info=storage, data_type_obj=data_type, runtime_ref=ref
    )
    return expr, ref, storage, data_type


# ---------------------------------------------------------------------------
# B11: 凍結後に生 object を書き換えても意味は動かない
# ---------------------------------------------------------------------------


def test_structural_key_ignores_runtime_ref_mutation_after_freeze():
    expr, ref = _memory_expression()
    expr.freeze()
    before = structural.expression_key(expr)
    ref.key = ("mem", 999)
    assert structural.expression_key(expr) == before
    assert structural.candidate_hash(expr) == expr.structural_hash()


def test_unknown_declaration_ignores_runtime_ref_mutation_after_freeze():
    expr, ref = _unknown_expression()
    published(expr)
    before = collect_unknown_smt_declarations(expr)
    before_smt = expr.to_smt()
    ref.key = ("unknown_source", 999)
    assert collect_unknown_smt_declarations(expr) == before
    assert expr.to_smt() == before_smt


def test_declared_signedness_ignores_data_type_mutation_after_freeze():
    expr, _ref, _storage, data_type = _parameter_expression()
    expr.freeze()
    assert _expr_prefers_signed_extension(expr) is True
    data_type.signed = False
    assert _expr_prefers_signed_extension(expr) is True, (
        "width coercion must read the frozen projection, not the raw data type object"
    )


def test_solver_query_identity_ignores_runtime_and_storage_mutation_after_freeze():
    expr, ref, storage, _data_type = _parameter_expression()
    expr.freeze()
    before = ConditionSMTOracle._expression_identity_key(expr)
    ref.key = ("parameter", 7, "zzz")
    storage.key = ("stack", 4096)
    assert ConditionSMTOracle._expression_identity_key(expr) == before


def test_unfrozen_expressions_still_read_the_raw_objects():
    """未凍結の式は従来どおり生 object を読む（値も費用も従来どおり）。"""

    expr, ref = _memory_expression()
    before = structural.expression_key(expr)
    ref.key = ("mem", 2)
    assert structural.expression_key(expr) != before


def test_projection_is_pinned_at_freeze_time():
    expr, ref, storage, data_type = _parameter_expression()
    expr.freeze()
    projection = semantic_projection(expr)
    pinned_runtime = projection.runtime_stable_key
    pinned_storage = projection.storage_identity
    pinned_signedness = projection.declared_signedness

    ref.key = ("parameter", 3, "b")
    storage.key = ("stack", 4)
    data_type.signed = False

    again = semantic_projection(expr)
    assert again is projection
    # Issue #215: projection の identity は `canonical_atom` の atom（値の区別を落とさない）
    assert again.runtime_stable_key == pinned_runtime == canonical_atom(("parameter", 0, "a"))
    assert again.storage_identity == pinned_storage
    assert again.declared_signedness == pinned_signedness is True


def test_declared_type_is_read_exactly_once_at_freeze():
    """宣言型は **凍結時に 1 回だけ** 読み、以後は値として固定される。

    遅延セルを snapshot の中に残すと「凍結 → 生 object 書き換え → 初回参照」で
    意味が動いてしまう。読むのは凍結の瞬間だけ。
    """

    expr, _ref, _storage, data_type = _parameter_expression()
    queried = []
    data_type.isSigned = lambda: (queried.append(1), True)[1]

    expr.freeze()
    assert len(queried) == 1, "the declared type must be resolved while freezing"

    data_type.isSigned = lambda: (queried.append(1), False)[1]
    projection = semantic_projection(expr)
    assert projection.declared_signedness is True
    assert projection.declared_signedness is True
    assert len(queried) == 1, "the raw data type object must never be read again"


def test_pointer_parameters_do_not_ask_the_type_object_at_all():
    """宣言名で pointer と分かる型は、型 object へ問い合わせない。

    `get_declared_type_signedness` は pointer には常に `False` を返すので意味は
    同じで、**解析が読まなかった型 object を凍結が新しく叩かない**という性質
    だけが増える（記録済みの観測列に無い問い合わせを作らない）。
    """

    data_type = MutableDataType(True)
    queried = []
    data_type.isSigned = lambda: (queried.append(1), True)[1]
    expr = Expression.parameter(
        "p", 0, size=8, data_type="int *", data_type_obj=data_type
    )
    expr.freeze()

    assert queried == []
    assert semantic_projection(expr).declared_signedness is False
    assert _expr_prefers_signed_extension(expr) is False


def test_freeze_then_mutate_then_first_read_keeps_the_meaning():
    """`freeze → raw mutation → first semantic read` でも意味が動かない。

    凍結してから **一度も意味を読まないうちに** 生 object を書き換えても、
    最初に読んだ意味は凍結時のもの。遅延セルが残っているとここで負ける。
    """

    expr, ref, storage, data_type = _parameter_expression()
    expr.freeze()

    ref.key = ("parameter", 99, "mutated")
    storage.key = ("stack", 9999)
    data_type.signed = False

    projection = semantic_projection(expr)
    assert projection.runtime_stable_key == canonical_atom(("parameter", 0, "a"))
    assert projection.runtime_semantic_key == canonical_atom(("parameter", 0, "a"))
    assert projection.storage_identity is not None
    assert projection.declared_signedness is True
    assert _expr_prefers_signed_extension(expr) is True
    assert ConditionSMTOracle._expression_identity_key(expr) == (
        "runtime_ref",
        "parameter",
        ("semantic", canonical_atom(("parameter", 0, "a"))),
    )


# ---------------------------------------------------------------------------
# B8: 凍結は observable な描画出力を変えない
# ---------------------------------------------------------------------------


@pytest.fixture
def rendering_corpus():
    left = Expression.parameter("a", 0, size=4)
    right = Expression.constant(7, size=4)
    guard = Condition(Expression.binary_op("INT_LESS", left, right))
    memory, _ref = _memory_expression()
    unknown, _unknown_ref = _unknown_expression()
    return [
        Expression.binary_op("INT_ADD", left, right),
        Expression.unary_op("INT_SEXT", left),
        Expression.phi([(guard, left), (None, right)]),
        Expression.call("f", [left, right]),
        memory,
        unknown,
    ]


def test_freeze_does_not_change_to_string_or_to_smt(rendering_corpus):
    for expr in rendering_corpus:
        before_string = expr.to_string()
        before_smt = published(expr).to_smt()
        expr.freeze()
        assert expr.to_string() == before_string
        assert expr.to_smt() == before_smt


def test_freeze_does_not_change_to_string_for_intrinsics():
    """SMT へ落とせない種別でも人向けの表示は変わらない。"""

    expr = Expression.intrinsic(
        "i", [Expression.parameter("a", 0, size=4)], size=4, opcode=3
    )
    before = expr.to_string()
    expr.freeze()
    assert expr.to_string() == before


def test_condition_rendering_is_unchanged_by_freeze():
    condition = Condition(
        Expression.binary_op(
            "INT_LESS", Expression.parameter("a", 0, size=4), Expression.constant(1, size=4)
        ),
        negated=True,
    )
    assert condition.to_string() == "(not (a < 1))"
    assert published(condition).to_smt().startswith("(not ")


# ---------------------------------------------------------------------------
# B12: solver へ渡す SMT は、公開済みの意味からしか作らない
# ---------------------------------------------------------------------------


def _unpublished_sum() -> Expression:
    return Expression.binary_op(
        "INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(1, size=4)
    )


def test_smt_generation_refuses_an_unpublished_expression():
    """未公開の式は solver 用の論理式にならない。

    ここで代わりに公開してしまうと、「確定した」と誰も言っていない中間値から
    判定用の論理式が作れてしまう。公開点を持たない producer は落ちて見つかる
    のが正しい。
    """

    from scripts.function_tracer_pcode.core.errors import (
        AnalysisFailureError,
        UnpublishedSemanticInputError,
    )

    expr = _unpublished_sum()

    with pytest.raises(UnpublishedSemanticInputError) as raised:
        expr.to_smt()

    # PR-106-0 の失敗族に属する = 既存の 1 本の経路で ERROR internal_exception。
    assert isinstance(raised.value, AnalysisFailureError)


def test_the_renderer_does_not_advance_the_lifecycle():
    """描画は状態を読むだけで、値を確定させない。"""

    expr = _unpublished_sum()

    with pytest.raises(Exception):
        expr.to_smt()

    assert expr.is_frozen is False
    # 拒否されたあとでも、まだ組み立て中の値として書き換えられる。
    expr.size = 8
    assert expr.size == 8


def test_the_refusal_is_recorded_before_it_is_raised():
    """握り潰されても pair 境界が拾えるよう、記録してから raise する。"""

    from scripts.function_tracer_pcode.core.errors import pair_failure_scope

    with pair_failure_scope(("bin1", "bin2"), None) as ledger:
        try:
            _unpublished_sum().to_smt()
        except Exception:  # 深部の包括捕捉を再現する（test 側の模擬）
            pass
        pending = ledger.pending_failure()
        assert pending is not None
        assert pending.is_internal_bug is True
        assert pending.site == "core.render_smt.expression_to_smt"


def test_a_published_expression_renders_and_stays_fixed():
    expr = published(_unpublished_sum())

    rendered = expr.to_smt()

    from scripts.function_tracer_pcode.core.errors import FrozenExpressionError

    with pytest.raises(FrozenExpressionError):
        expr.size = 8
    assert expr.to_smt() == rendered


def test_the_evidence_renderer_is_a_separate_entry_point():
    """証拠テキストは組み立て中の値にも出せるが、solver 入口とは別。

    同じ関数が「公開を要求する/しない」を引数で切り替える形にすると、call site
    を見ても solver へ行く値かどうか分からない。入口を分けてあること自体が
    contract なので、ここで固定する。
    """

    from scripts.function_tracer_pcode.core.render_smt import (
        expression_to_smt,
        render_expression_smt_evidence,
    )

    expr = _unpublished_sum()

    evidence = render_expression_smt_evidence(expr)
    assert evidence

    # 証拠は文字列で返る = そのまま solver 入口へ渡せる型ではない。
    assert isinstance(evidence, str)
    with pytest.raises(Exception):
        expression_to_smt(expr)


def test_smt_generation_refuses_a_graph_that_cannot_be_frozen():
    from scripts.function_tracer_pcode.core.errors import ExpressionCycleError

    cyclic = Expression.unary_op("BOOL_NEGATE", Expression.constant(1, 1))
    cyclic.__dict__["operands"] = [cyclic]
    with pytest.raises(ExpressionCycleError):
        published(cyclic).to_smt()


def test_global_address_identity_is_pinned_at_freeze():
    """global object のアドレス identity も凍結時の値で固定される。"""

    from scripts.function_tracer_pcode.core.render_smt.unknowns import (
        global_address_identity,
        global_address_smt,
    )

    from scripts.function_tracer_pcode.core.runtime_refs import AddressValueRef

    class MutableAddressRef(AddressValueRef):
        """`AddressValueRef` の値のうち identity だけを可変にした代役。"""

        def __init__(self):
            super().__init__(address_offset=0x1000)
            object.__setattr__(self, "identity", ("g_counter", 4, 0))

        def global_object_identity(self):
            return self.identity

    ref = MutableAddressRef()
    expr = Expression.variable("g", size=4, runtime_ref=ref)
    expr.freeze()

    before_identity = global_address_identity(expr)
    before_smt = global_address_smt(expr, 64)
    assert before_identity == ("g_counter", 4, 0)

    object.__setattr__(ref, "identity", ("other_object", 8, 16))

    assert global_address_identity(expr) == before_identity
    assert global_address_smt(expr, 64) == before_smt


def test_loop_lowering_identity_is_pinned_at_freeze():
    """loop lowering の SMT function identity も凍結時の値で固定される。"""

    class MutableLoopRef:
        reduction_kind = "sum"

        def __init__(self):
            self.key = ("readonly", 1)

        def semantic_key(self):
            return self.key

        def stable_key(self):
            return self.key

    ref = MutableLoopRef()
    expr = Expression.variable("acc", size=4, runtime_ref=ref)
    expr.freeze()

    before = semantic_projection(expr).loop_lowering.identity
    ref.key = ("readonly", 999)
    assert semantic_projection(expr).loop_lowering.identity == before


def test_variable_symbol_declaration_is_decided_by_the_projection():
    """VARIABLE をそのまま宣言する種別かどうかも投影が持つ。"""

    from scripts.function_tracer_pcode.core.runtime_refs import CanonicalLocation

    plain = Expression.variable("v", size=4)
    assert semantic_projection(plain).declares_variable_symbol is False

    located = Expression.variable(
        "v", size=4, runtime_ref=CanonicalLocation("param_1", offset=16, size=4)
    )
    located.freeze()
    assert semantic_projection(located).declares_variable_symbol is True


def test_expressions_inside_a_runtime_ref_are_published_with_the_node():
    """runtime ref が抱える式も、node の公開と同時に凍る。

    ref が frozen dataclass でも、中の `Expression` は別 object なので、凍らせ
    ない限り「凍結後も意味が動く」経路が残る（loop summary の `transition_expr`
    など）。
    """

    from dataclasses import dataclass
    from typing import Optional

    from scripts.function_tracer_pcode.core.errors import FrozenExpressionError

    @dataclass(frozen=True)
    class NestedRef:
        transition_expr: Optional[Expression]
        cases: tuple

        def stable_key(self):
            return ("nested", 1)

    inner = Expression.binary_op(
        "INT_ADD", Expression.parameter("s", 0, size=4), Expression.constant(1, size=4)
    )
    nested = Expression.unary_op("INT_ZEXT", Expression.parameter("t", 1, size=4))
    expr = Expression.variable("acc", size=4, runtime_ref=NestedRef(inner, (nested,)))

    assert inner.is_frozen is False
    expr.freeze()

    assert inner.is_frozen is True, "a runtime ref's expressions are part of the meaning"
    assert nested.is_frozen is True, "nested containers are published too"
    with pytest.raises(FrozenExpressionError):
        inner.size = 8


def test_unsupported_values_are_not_kept_as_raw_objects():
    """値として固定できないものを snapshot がそのまま抱えないこと。"""

    class Wobbly:
        pass

    payload = Wobbly()

    class RefWithRawValue:
        def stable_key(self):
            return ("ref", payload)

    expr = Expression.unknown("u", runtime_ref=RefWithRawValue())
    expr.freeze()

    projection = semantic_projection(expr)
    # Issue #215: 値として固定できない部分を含む key は identity の field に持たない（型名だけの印で
    # 別の ref と同じ identity になるため）。外したことは `runtime_identity_unfixable` に残る
    assert projection.runtime_stable_key is None
    assert projection.runtime_semantic_key is None
    assert projection.runtime_identity_unfixable is True
    # 区別できない値を digest に載せない。
    from scripts.function_tracer_pcode.core.structural import structural_identity_digest

    assert structural_identity_digest(expr) is None


def test_bit_width_of_a_frozen_expression_is_stable():
    expr, _ref, _storage, data_type = _parameter_expression()
    expr.freeze()
    before = expression_smt_bit_width(expr)
    data_type.signed = False
    assert expression_smt_bit_width(expr) == before


# ---------------------------------------------------------------------------
# Issue #219 T-A2: LEGACY 表現（`to_dict()` / snapshot の木）も生 `StorageInfo` から切り離す
# ---------------------------------------------------------------------------


def _register_storage():
    from scripts.function_tracer_pcode.core.storage import StorageInfo

    return StorageInfo(
        is_register=True,
        space_name="register",
        offset=8,
        size=4,
        register_name="x0",
        base_register_name="x0",
    )


def _storage_rooted_expression(storage):
    parameter = Expression.parameter("a", 0, size=4, storage_info=storage)
    return Expression.binary_op("INT_ADD", parameter, Expression.constant(1, size=4))


def _mutate_every_storage_field(storage):
    """`StorageInfo` の LEGACY 表現が読む field をすべて別の値へ書き換える。"""

    storage.is_register = False
    storage.space_name = "stack"
    storage.space_id = 77
    storage.offset = 4096
    storage.size = 8
    storage.size_bits = 64
    storage.register_offset = 12
    storage.register_size = 8
    storage.register_size_bits = 64
    storage.register_name = "x9"
    storage.base_register_name = "x9"
    storage.base_register_offset = 99
    storage.base_register_size = 8
    storage.base_register_size_bits = 64
    storage.bit_offset_in_base = 32
    storage.is_stack_pointer = True
    storage.is_frame_pointer = True


def test_legacy_representation_ignores_storage_mutation_after_freeze():
    """凍結後に生の `StorageInfo` を書き換えても、検証済みの式の `to_dict()` は動かない。

    main（`d398073`）では `_to_dict_active` が live な `storage_info.to_dict()` を読むので、
    structural key・SMT は動かないのに LEGACY 表現だけが動いた（isolation 契約の穴）。
    """

    storage = _register_storage()
    expr = _storage_rooted_expression(storage)
    expr.freeze()
    before = expr.to_dict()

    _mutate_every_storage_field(storage)

    assert expr.to_dict() == before


def test_legacy_size_estimate_matches_the_output_after_storage_mutation():
    """凍結済み node の大きさの cache（`_FROZEN_TREE_BYTES`）と実出力が食い違わない。"""

    from scripts.function_tracer_pcode.core.expression import estimate_legacy_dict_bytes
    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY, JsonEncodingPolicy
    from scripts.function_tracer_pcode.core.render_output import utf8_length

    storage = _register_storage()
    expr = _storage_rooted_expression(storage)
    expr.freeze()
    estimate_legacy_dict_bytes(expr, work=None)  # 凍結済み node の大きさを cache させる

    _mutate_every_storage_field(storage)

    written = utf8_length(JsonEncodingPolicy.dumps(RESULT_JSON_POLICY, expr.to_dict()))
    assert estimate_legacy_dict_bytes(expr, work=None) == written


def test_analysis_snapshot_fingerprint_ignores_storage_mutation_after_publication():
    """解析の snapshot fingerprint（authority の束縛 identity）も凍結時の storage で固定される。"""

    from scripts.function_tracer_pcode.core.analysis import ReturnInfo
    from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot
    from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis
    from scripts.function_tracer_pcode.tests.unit._publication import published_raw_analysis

    storage = _register_storage()
    analysis = published_raw_analysis(
        create_mock_analysis(
            "f",
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=_storage_rooted_expression(storage),
                )
            ],
        )
    )
    before = AnalysisSnapshot.from_function_analysis(analysis)

    _mutate_every_storage_field(storage)

    after = AnalysisSnapshot.from_function_analysis(analysis)
    assert after.semantic_fingerprint == before.semantic_fingerprint
    assert after.semantic_fields == before.semantic_fields


def test_unfrozen_expressions_still_serialize_the_live_storage():
    """CONSTRUCTION の式は従来どおり、その時点の `StorageInfo` を描く。"""

    storage = _register_storage()
    expr = _storage_rooted_expression(storage)
    before = expr.to_dict()

    storage.register_name = "x9"

    after = expr.to_dict()
    assert after != before
    assert after["operands"][0]["storage_info"]["register_name"] == "x9"

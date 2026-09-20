# -*- coding: utf-8 -*-
"""凍結後の意味が生 object から切り離されていること（計画 B8 / B11 / B12）。

`runtime_ref` / `storage_info` / `data_type_obj` は **意味そのものではなく**、
意味を一度だけ読み取る元になる生 object。凍結後にそれらが変わっても、
structural key・solver query identity・SMT 出力・unknown 宣言・幅は動かない。
"""

from __future__ import annotations

import pytest

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
    expr.freeze()
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
    assert again.runtime_stable_key == pinned_runtime == ("parameter", 0, "a")
    assert again.storage_identity == pinned_storage
    assert again.declared_signedness == pinned_signedness is True


def test_freezing_does_not_query_the_declared_type():
    """凍結は JVM 呼び出しを増やさない。

    宣言型の signedness は「最初に必要になったとき 1 回だけ」解決して固定する。
    凍結時に前倒しで全部読むと、解析が触らなかった型 object にまで問い合わせる
    ことになり、記録済みの観測列（`tests/fixtures/pcode/`）とも実行コストとも
    食い違う。
    """

    expr, _ref, _storage, data_type = _parameter_expression()
    queried = []
    data_type.isSigned = lambda: (queried.append(1), True)[1]

    expr.freeze()
    assert queried == []

    projection = semantic_projection(expr)
    assert projection.declared_signedness is True
    assert len(queried) == 1
    assert projection.declared_signedness is True
    assert len(queried) == 1, "the raw data type object must be read only once"


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
        before_smt = expr.to_smt()
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
    assert condition.to_smt().startswith("(not ")


# ---------------------------------------------------------------------------
# B12: SMT 生成は凍結済みの意味に対してだけ行う
# ---------------------------------------------------------------------------


def test_smt_generation_freezes_its_input():
    expr = Expression.binary_op(
        "INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(1, size=4)
    )
    assert expr.is_frozen is False
    rendered = expr.to_smt()
    assert expr.is_frozen is True
    # 生成したあとで意味を書き換えられない = 論理式ともとの意味がずれない。
    from scripts.function_tracer_pcode.core.errors import FrozenExpressionError

    with pytest.raises(FrozenExpressionError):
        expr.size = 8
    assert expr.to_smt() == rendered


def test_smt_generation_refuses_a_graph_that_cannot_be_frozen():
    from scripts.function_tracer_pcode.core.errors import ExpressionCycleError

    cyclic = Expression.unary_op("BOOL_NEGATE", Expression.constant(1, 1))
    cyclic.__dict__["operands"] = [cyclic]
    with pytest.raises(ExpressionCycleError):
        cyclic.to_smt()


def test_bit_width_of_a_frozen_expression_is_stable():
    expr, _ref, _storage, data_type = _parameter_expression()
    expr.freeze()
    before = expression_smt_bit_width(expr)
    data_type.signed = False
    assert expression_smt_bit_width(expr) == before

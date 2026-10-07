# -*- coding: utf-8 -*-
"""Issue #215 (SN3) round 7: 値の identity の契約を、生成した SMT と実際の条件 oracle まで通して確かめる。

契約（期待値はここから決める。実装の出力を写さない）:

* **区別の保存**: 値の区別（容器の型・dict と組の列・bool と int・int と float・float の bit 列・
  enum の member）は、どの置き場所（runtime ref そのもの / `stable_key()` / `semantic_key()` /
  それらの入れ子 / origin / storage / leaf の値）でも、凍結の前後でも落ちない。別の値は同じ
  identity・同じ solver symbol にならない
* **識別不能は identity にならない**: 識別不能 token・状態を読めない object・閉路・要素の衝突・
  深すぎる入れ子・構造 key の placeholder を含む値は identity を持たない（None）。その ref は
  `identity_unfixable` を立て、symbol を共有しない（oracle は UNSAT と言わない）
* **正当な共有は残る**: 同じ構造の値を持つ別の ref は同じ identity・同じ symbol で、
  `x != x'` は UNSAT
* **閉路は例外にならない**: key・凍結・digest・provenance・SMT の組み立てが閉路と深い入れ子で
  止まり、識別不能として扱う

検査の深さ: helper の戻り値だけでなく、`ConditionSMTOracle` が組んだ script（`distinct` の両辺）と
solver の判定（`conjunction_is_unsat`）まで見る。
"""

from __future__ import annotations

import enum
import struct

import pytest

from scripts.function_tracer_pcode.analysis.condition.condition_cache import condition_cache_scope
from scripts.function_tracer_pcode.analysis.condition.query_identity import solver_symbol_identity
from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
from scripts.function_tracer_pcode.core import structural
from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.semantic_freeze import freeze_expression
from scripts.function_tracer_pcode.core.semantic_projection import MAX_VALUE_DEPTH, identity_value
from scripts.function_tracer_pcode.core.semantic_snapshot import semantic_projection
from scripts.function_tracer_pcode.core.structural import (
    exact_structural_identity,
    expression_key,
    expression_key_status,
    unidentified_identity,
)


# ---------------------------------------------------------------------------
# 置き場所
# ---------------------------------------------------------------------------


class _StableRef:
    __slots__ = ("value",)

    def __init__(self, value):
        self.value = value

    def stable_key(self):
        return self.value


class _SemanticRef:
    __slots__ = ("value",)

    def __init__(self, value):
        self.value = value

    def semantic_key(self):
        return self.value


class _NestedRef:
    """値を `stable_key()` の入れ子の奥に持つ ref。"""

    __slots__ = ("value",)

    def __init__(self, value):
        self.value = value

    def stable_key(self):
        return ("nested", ("level", (self.value, 1)))


class _Origin:
    __slots__ = ("value",)

    def __init__(self, value):
        self.value = value

    def stable_key(self):
        return self.value


class _OriginRef:
    """自分の `stable_key()` は全 instance で等しく、origin の key だけが値を持つ ref。"""

    __slots__ = ("origin_kind", "origin_ref")

    def __init__(self, value):
        self.origin_kind = "loop"
        self.origin_ref = _Origin(value)

    def stable_key(self):
        return ("same_for_all",)


class _Storage:
    __slots__ = ("value",)

    def __init__(self, value):
        self.value = value

    def storage_identity_key(self):
        return self.value


def _variable(ref, name="x"):
    return Expression(ExpressionType.VARIABLE, name=name, runtime_ref=ref, size=4)


def _storage_parameter(value, name="p"):
    # index が無い（-1）parameter は storage の identity で symbol になる
    return Expression(ExpressionType.PARAMETER, name=None, value=-1, size=4, storage_info=_Storage(value))


#: solver symbol の identity を持つ置き場所（oracle まで通す）
SYMBOL_PLACEMENTS = {
    "stable": lambda value: _variable(_StableRef(value)),
    "semantic": lambda value: _variable(_SemanticRef(value)),
    "nested": lambda value: _variable(_NestedRef(value)),
    "origin": lambda value: Expression(ExpressionType.UNKNOWN, name="u", runtime_ref=_OriginRef(value), size=4),
    "storage": _storage_parameter,
}
#: 構造 key の置き場所（leaf の値・runtime ref そのもの）
KEY_PLACEMENTS = {
    "leaf": lambda value: Expression(ExpressionType.VARIABLE, name="v", value=value, size=4),
    "direct_ref": lambda value: Expression(ExpressionType.UNKNOWN, name="u", runtime_ref=value, size=4),
    "stable": lambda value: Expression(ExpressionType.UNKNOWN, name="u", runtime_ref=_StableRef(value), size=4),
}


def _maybe_frozen(expr, frozen):
    return freeze_expression(expr) if frozen else expr


# ---------------------------------------------------------------------------
# 値
# ---------------------------------------------------------------------------


class _Color(enum.Enum):
    RED = 1


class _Shade(enum.Enum):
    DARK = 1


def _nan(payload):
    return struct.unpack(">d", struct.pack(">Q", 0x7FF8000000000000 | payload))[0]


#: 別の値の組（左と右は値として区別できる。Python の `==` で等しくなる組を含む）
DIFFERENT = {
    "list_vs_tuple": (lambda: ("ref", [1]), lambda: ("ref", (1,))),
    "dict_vs_pairs": (lambda: ("ref", {"a": 1}), lambda: ("ref", (("a", 1),))),
    "set_vs_frozenset": (lambda: ("ref", {1}), lambda: ("ref", frozenset({1}))),
    "bool_vs_int": (lambda: ("ref", True), lambda: ("ref", 1)),
    "int_vs_float": (lambda: ("ref", 1), lambda: ("ref", 1.0)),
    "zero_signs": (lambda: ("ref", 0.0), lambda: ("ref", -0.0)),
    "nan_payloads": (lambda: ("ref", _nan(1)), lambda: ("ref", _nan(2))),
    "enum_vs_value": (lambda: ("ref", _Color.RED), lambda: ("ref", 1)),
    "enums_same_value": (lambda: ("ref", _Color.RED), lambda: ("ref", _Shade.DARK)),
    "bytes_vs_str": (lambda: ("ref", b"a"), lambda: ("ref", "a")),
    "control_1_vs_2": (lambda: ("ref", 1), lambda: ("ref", 2)),
}


def _cyclic_list():
    value = [1]
    value.append(value)
    return value


def _cyclic_dict():
    value = {}
    value["k"] = value
    return value


def _deep(depth):
    value = 0
    for _ in range(depth):
        value = [value]
    return value


class _Opaque:
    __slots__ = ()


class _Twin(str):
    """基底型の "a" と同じ値に読まれるが、dict の中では別の key になる str。"""

    def __hash__(self):
        return 1

    def __eq__(self, other):
        return self is other


class _Serialized:
    """型が `to_dict()` だけを宣言する object（直列化の宣言で identity の宣言ではない: 状態の一部を落とす）。"""

    __slots__ = ("hidden",)

    def __init__(self):
        self.hidden = object()

    def to_dict(self):
        return {"kind": "summary"}


class _OddModule:
    __slots__ = ()


_OddModule.__module__ = 7  # 型名が str でない型の object（`object_id` の印の形を崩す）

_SHARED_TOKEN = unidentified_identity("unresolved")

#: 値として固定できない値（2 回作ると別の値。同じ token は同じ object を返す）
UNFIXABLE = {
    "shared_unidentified_token": lambda: _SHARED_TOKEN,
    "wrapped_unidentified_token": lambda: ("ref", (_SHARED_TOKEN, 1)),
    "stateless_object": lambda: ("ref", _Opaque()),
    "cyclic_list": _cyclic_list,
    "cyclic_dict": _cyclic_dict,
    "too_deep": lambda: _deep(MAX_VALUE_DEPTH + 5),
    "colliding_dict": lambda: {_Twin("a"): 1, "a": 2},
    "placeholder_key": lambda: ("truncated", "INT_ADD", None, 4),
    "to_dict_object": lambda: ("ref", _Serialized()),
    "odd_module_object": lambda: ("ref", _OddModule()),
}


# ---------------------------------------------------------------------------
# oracle
# ---------------------------------------------------------------------------


def _notequal_verdict(left, right):
    """(`conjunction_is_unsat([x != y])`, script の `distinct` 行)。"""

    condition = Condition(Expression.binary_op("INT_NOTEQUAL", left, right), False)
    ConditionSMTOracle.reset_caches()
    with condition_cache_scope():
        _usable, script = ConditionSMTOracle._build_script([condition])
        verdict = ConditionSMTOracle.conjunction_is_unsat([condition], use_cache=False)
    distinct = [line for line in (script or "").splitlines() if "distinct" in line]
    return verdict, distinct


def _same_symbol(distinct_lines):
    for line in distinct_lines:
        body = line.replace("(assert (distinct ", "").rstrip(")").split()
        if len(body) == 2 and body[0] == body[1]:
            return True
    return False


# ---------------------------------------------------------------------------
# 区別の保存（solver の identity と oracle）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("placement", sorted(SYMBOL_PLACEMENTS))
@pytest.mark.parametrize("name", sorted(DIFFERENT))
def test_different_values_never_share_a_solver_symbol(name, placement, frozen):
    make_left, make_right = DIFFERENT[name]
    left = _maybe_frozen(SYMBOL_PLACEMENTS[placement](make_left()), frozen)
    right = _maybe_frozen(SYMBOL_PLACEMENTS[placement](make_right()), frozen)
    left_identity, right_identity = solver_symbol_identity(left), solver_symbol_identity(right)
    assert left_identity is None or left_identity != right_identity
    verdict, distinct = _notequal_verdict(left, right)
    # 別の値の symbol は別: x != y は UNSAT ではない（SAT か、使えないなら None）
    assert verdict is not True, distinct
    assert not _same_symbol(distinct), distinct


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("placement", sorted(SYMBOL_PLACEMENTS))
@pytest.mark.parametrize(
    "make",
    [
        lambda: ("ref", (1, "a", None, True)),
        lambda: ("ref", [1, {"k": (2.5, b"x")}]),
        lambda: ("ref", _Color.RED),
        lambda: ("ref", frozenset({1, 2})),
    ],
    ids=["tuple_scalars", "list_dict_float_bytes", "enum", "frozenset"],
)
def test_equal_values_share_one_solver_symbol(make, placement, frozen):
    # 対照: 同じ構造の値を持つ別の ref（別の object）は同じ symbol。x != x' は UNSAT
    left = _maybe_frozen(SYMBOL_PLACEMENTS[placement](make()), frozen)
    right = _maybe_frozen(SYMBOL_PLACEMENTS[placement](make()), frozen)
    if placement != "origin":  # origin は UNKNOWN の宣言 symbol（solver symbol identity を持たない種別）
        assert solver_symbol_identity(left) is not None
        assert solver_symbol_identity(left) == solver_symbol_identity(right)
    verdict, distinct = _notequal_verdict(left, right)
    assert verdict is True, distinct
    assert _same_symbol(distinct), distinct


# ---------------------------------------------------------------------------
# 識別不能は identity にならない
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("placement", sorted(SYMBOL_PLACEMENTS))
@pytest.mark.parametrize("name", sorted(UNFIXABLE))
def test_an_unfixable_value_gives_no_identity_and_no_shared_symbol(name, placement, frozen):
    make = UNFIXABLE[name]
    left = _maybe_frozen(SYMBOL_PLACEMENTS[placement](make()), frozen)
    right = _maybe_frozen(SYMBOL_PLACEMENTS[placement](make()), frozen)
    projection = semantic_projection(left)
    if placement == "storage":
        assert projection.storage_identity is None
    else:
        assert projection.runtime_identity_unfixable is True
        assert projection.runtime_stable_key is None
        assert projection.runtime_semantic_key is None
        assert projection.runtime_stable_origin is None
    assert structural.structural_identity_digest(left) is None
    assert structural.expression_provenance_key(left) != structural.expression_provenance_key(right)
    verdict, distinct = _notequal_verdict(left, right)
    assert verdict is not True, distinct
    assert not _same_symbol(distinct), distinct


@pytest.mark.parametrize("name", sorted(UNFIXABLE))
def test_identity_value_rejects_every_unfixable_value(name):
    assert identity_value(UNFIXABLE[name]()) is None


def test_identity_value_keeps_process_scoped_identified_tokens():
    # 同じ process の中の識別済み token（tail token）は同じ構造を指す: 共有してよい
    token = exact_structural_identity(Expression.parameter("p", 0, size=4))[1]
    assert token[0] == structural.EXACT_TAIL_TAG
    assert identity_value(("ref", token)) is not None
    assert identity_value(("ref", token)) == identity_value(("ref", token))


# ---------------------------------------------------------------------------
# 構造 key（leaf / runtime ref）でも同じ区別と識別不能
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("placement", sorted(KEY_PLACEMENTS))
@pytest.mark.parametrize("name", sorted(DIFFERENT))
def test_different_values_never_share_a_structural_key(name, placement, frozen):
    make_left, make_right = DIFFERENT[name]
    left = _maybe_frozen(KEY_PLACEMENTS[placement](make_left()), frozen)
    right = _maybe_frozen(KEY_PLACEMENTS[placement](make_right()), frozen)
    left_key, left_ok = expression_key_status(left)
    right_key, right_ok = expression_key_status(right)
    assert not (left_ok and right_ok and left_key == right_key)
    assert exact_structural_identity(left) != exact_structural_identity(right)
    left_digest, right_digest = structural.structural_identity_digest(left), structural.structural_identity_digest(right)
    assert left_digest is None or left_digest != right_digest


#: 構造 key の置き場所で値として固定できない値。構造 key の placeholder の形をした値（``("truncated", …)``）
#: は、leaf の値・ref そのものとしては同じ値どうしが等しい（比較不能にはなるが、別の値と一致しない）ので
#: ここには入れない（solver の identity は保守的に拒む: 上の `UNFIXABLE`）
KEY_UNFIXABLE = {name: make for name, make in UNFIXABLE.items() if name != "placeholder_key"}


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("placement", sorted(KEY_PLACEMENTS))
@pytest.mark.parametrize("name", sorted(KEY_UNFIXABLE))
def test_an_unfixable_value_is_never_comparable_and_never_raises(name, placement, frozen):
    make = KEY_UNFIXABLE[name]
    expr = _maybe_frozen(KEY_PLACEMENTS[placement](make()), frozen)
    other = _maybe_frozen(KEY_PLACEMENTS[placement](make()), frozen)
    _key, comparable = expression_key_status(expr)
    assert comparable is False
    assert exact_structural_identity(expr) != exact_structural_identity(other)
    assert structural.structural_identity_digest(expr) is None
    assert structural.expression_provenance_key(expr) != structural.expression_provenance_key(other)


# ---------------------------------------------------------------------------
# 閉路: 全経路が止まる
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("make", [_cyclic_list, _cyclic_dict, lambda: _deep(MAX_VALUE_DEPTH * 4)], ids=["list", "dict", "deep"])
@pytest.mark.parametrize(
    "placement",
    ["leaf", "direct_ref", "stable", "semantic", "nested", "origin", "storage"],
)
def test_a_cyclic_or_deep_value_stops_every_reader(make, placement, frozen):
    builders = dict(KEY_PLACEMENTS, **SYMBOL_PLACEMENTS)
    expr = _maybe_frozen(builders[placement](make()), frozen)
    expression_key(expr)
    expression_key_status(expr)
    exact_structural_identity(expr)
    structural.structural_identity_digest(expr)
    structural.expression_provenance_key(expr)
    solver_symbol_identity(expr)
    verdict, _distinct = _notequal_verdict(expr, _maybe_frozen(builders[placement](make()), frozen))
    assert verdict is not True


# ---------------------------------------------------------------------------
# 形を調べる consumer は owner の読み口を通す（identity の atom を自分で照合しない）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "key",
    [
        ("loop", ("parameter",)),
        ("loop", ("parameter", None)),
        ("loop", ("parameter", 1, None)),
        ("loop", ("x", ("parameter", 1, 2, None))),
        ("loop", {"k": ("parameter", 1, 2, None)}),
        ("loop", frozenset({("parameter", 1, 2, None)})),
        ("loop", [("parameter", 1, None)]),
    ],
    ids=["no_index", "none_index", "none_width", "deeper", "in_dict", "in_frozenset", "in_list"],
)
def test_an_incomplete_parameter_key_is_still_rejected_as_a_solver_symbol(key):
    # solver symbol の安全性の判定（欠けた parameter key の拒否）は identity の atom を `identity_view` で
    # 読む: atom の形のまま照合すると、欠けた key を見落として symbol を共有させる
    from scripts.function_tracer_pcode.analysis.condition.query_identity import solver_symbol_identity_is_safe

    # round 8: 成分の欠けた schema は projection の入口で identity にならない（None）。どちらでも記号は共有しない
    identity = solver_symbol_identity(freeze_expression(_variable(_StableRef(key))))
    assert identity is None or solver_symbol_identity_is_safe(identity) is False
    # 対照: 欠けていない parameter key を入れ子に持つ ref は symbol にしてよい
    complete = solver_symbol_identity(freeze_expression(_variable(_StableRef(("loop", ("parameter", 1, 2))))))
    assert solver_symbol_identity_is_safe(complete) is True


def test_the_cross_binary_shape_reads_the_parameter_identity_through_the_view():
    # 対応候補の形（artifact に固有の program id を外す）は provenance key を `provenance_key_view` で読む
    from scripts.function_tracer_pcode.core.runtime_refs import LocationBaseRef
    from scripts.function_tracer_pcode.proof.call_effect.obligations import _cross_binary_expression_shape

    def parameter(program_id):
        ref = LocationBaseRef.parameter("p", index=2, owner_program_id=program_id, owner_entry_offset=0x1000)
        return freeze_expression(Expression.parameter("p", 2, "int", size=4, runtime_ref=ref))

    left, right = (structural.expression_provenance_key(parameter(program)) for program in (11, 22))
    assert left != right
    assert _cross_binary_expression_shape(left) == _cross_binary_expression_shape(right) == ("runtime_ref", ("parameter", 2))


def test_an_address_identity_outside_its_schema_is_not_an_identity():
    # global object のアドレス identity は (str, int, int) の schema を確かめてから exact な値で持つ
    from scripts.function_tracer_pcode.core.runtime_refs import AddressValueRef

    class _ListIdentity(AddressValueRef):
        def global_object_identity(self):
            return ["g", 4, 0]

    class _TupleIdentity(AddressValueRef):
        def global_object_identity(self):
            return ("g", 4, 0)

    odd = freeze_expression(Expression(ExpressionType.CONSTANT, value=0x1000, size=8, runtime_ref=_ListIdentity(address_offset=0x1000)))
    assert semantic_projection(odd).address_object_identity is None
    assert semantic_projection(odd).runtime_identity_unfixable is True
    good = freeze_expression(Expression(ExpressionType.CONSTANT, value=0x1000, size=8, runtime_ref=_TupleIdentity(address_offset=0x1000)))
    assert semantic_projection(good).address_object_identity == ("g", 4, 0)
    assert semantic_projection(good).runtime_identity_unfixable is False


@pytest.mark.parametrize("make", [_cyclic_list, _cyclic_dict, lambda: _deep(MAX_VALUE_DEPTH * 4)], ids=["list", "dict", "deep"])
def test_the_provenance_value_reader_stops_on_cycles_by_itself(make):
    # provenance の digest は識別できない値の前に止まるが（`_provenance_inputs_identified`）、値の表現の
    # reader 自身も閉路と深い入れ子で止まる（読み手ごとの guard に頼らない: 入口を足しても再帰しない）
    key = structural._stable_value_key(make())
    assert structural._value_key_has_opaque(key)


def test_shape_matchers_and_forbidden_tag_checks_see_inside_identity_atoms():
    # provenance key の ref の identity（atom）の中の schema と印は、owner の読み口（`provenance_key_view` /
    # `tags_of`）で読む consumer から見える
    from scripts.function_tracer_pcode.analysis.returns.summary_returns import _key_contains_forbidden_identity
    from scripts.function_tracer_pcode.core.runtime_refs import UnknownValueRef
    from scripts.function_tracer_pcode.core.semantic_projection import canonical_atom
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy

    class _Op:
        __slots__ = ()

        def stable_key(self):
            return ("pcode_op", 1, 2)

    unknown = freeze_expression(
        Expression.unknown("phi", runtime_ref=UnknownValueRef.phi_circular(pcode_op_ref=_Op()))
    )
    target = ("object_target", structural.expression_provenance_key(unknown))
    assert PairwiseStrategy._object_target_contains_originated_phi_circular(target) is True
    assert PairwiseStrategy._value_contains_originated_phi_circular(target) is True
    for tag in ("process_object", structural.UNIDENTIFIED_TAG, "object_id"):
        wrapped = ("runtime_ref", canonical_atom((tag, 1, "n")))
        assert _key_contains_forbidden_identity(wrapped) is True
        assert PairwiseStrategy._return_coverage_identity_contains_forbidden_atoms(wrapped) is True


def test_an_unfixable_parameter_ref_does_not_fall_back_to_its_index_or_name():
    # projection が外した identity を、index・名前の粗い identity で補わない
    def parameter():
        return freeze_expression(Expression(ExpressionType.PARAMETER, name="p", value=0, size=4, runtime_ref=_StableRef(("ref", _Opaque()))))

    assert solver_symbol_identity(parameter()) is None
    verdict, _distinct = _notequal_verdict(parameter(), parameter())
    assert verdict is not True


def test_a_semantic_only_ref_keeps_its_identity_in_the_provenance_key():
    left = freeze_expression(_variable(_SemanticRef(("ref", 1))))
    right = freeze_expression(_variable(_SemanticRef(("ref", 2))))
    same = freeze_expression(_variable(_SemanticRef(("ref", 1))))
    assert structural.expression_provenance_key(left) != structural.expression_provenance_key(right)
    assert structural.expression_provenance_key(left) == structural.expression_provenance_key(same)


def test_semantic_and_stable_lowering_identities_never_share_a_name():
    semantic = freeze_expression(_variable(_SemanticRef(("ref", 1))))
    stable = freeze_expression(_variable(_StableRef(("ref", 1))))
    assert semantic_projection(semantic).runtime_lowering_identity != semantic_projection(stable).runtime_lowering_identity


def test_a_semantic_only_ref_is_read_through_the_provenance_view_too():
    # `runtime_semantic_ref` の identity も owner の読み口で形を読む（形の照合が atom を見落とさない）
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy

    expr = freeze_expression(_variable(_SemanticRef(("opaque_unknown", "void", 7))))
    key = structural.expression_provenance_key(expr)
    assert key[0] == "runtime_semantic_ref"
    assert structural.provenance_key_view(key) == ("runtime_semantic_ref", ("opaque_unknown", "void", 7))
    assert PairwiseStrategy._object_target_contains_void_opaque_unknown(("target", key)) is True


def test_deferred_call_refs_are_found_inside_identity_atoms():
    from scripts.function_tracer_pcode.core.semantic_projection import canonical_atom
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy

    raw = ("deferred_call", "call_out_of_scope", ("function", 22, 0x4000), None)
    target = ("target", ("runtime_ref", canonical_atom(raw)))
    assert PairwiseStrategy._deferred_call_runtime_refs_from_value(target) == (("runtime_ref", raw),)


def test_a_fully_readable_frozen_dataclass_with_to_dict_stays_an_identity():
    # 状態の全部を読める凍結 dataclass は `to_dict()` を宣言していても値（identity）になる。`to_dict()`
    # だけで表した object は識別しない
    import dataclasses

    @dataclasses.dataclass(frozen=True)
    class Point:
        x: int

        def to_dict(self):
            return {"x": self.x}

    Point.__qualname__ = "Point"  # 関数の外で定義した型と同じ扱い（`<locals>` は識別しない）
    assert identity_value(("ref", Point(1))) is not None
    assert identity_value(("ref", Point(1))) == identity_value(("ref", Point(1)))
    assert identity_value(("ref", Point(1))) != identity_value(("ref", Point(2)))
    assert identity_value(("ref", _Serialized())) is None


def test_constants_with_different_opaque_values_never_share_a_provenance_key():
    # #218 の再現（AC1）: 型名だけに落ちる値を持つ別々の式は、digest 経路でも同じ provenance key にならない
    class _Object:
        pass

    left, right = Expression.constant(0, size=4), Expression.constant(0, size=4)
    left.value, right.value = _Object(), _Object()
    assert structural.expression_provenance_key(left) != structural.expression_provenance_key(right)
    assert structural.expression_provenance_key(left) != structural.expression_provenance_key(left)

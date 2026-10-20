# -*- coding: utf-8 -*-
"""Issue #215 (SN3): 値の読み方の契約（`semantic_projection.read_container` / `canonical_atom`）。

runtime ref の意味 key は、`stable_key()` の戻り値を不可逆に畳む前処理（旧 `immutable_value` の
tuple 化・`__iter__` の呼び出し・`repr` 順の並べ替え・key の衝突の無視）を通ると、後段の分類では
取り戻せない区別を失う。契約（期待値はここから決める）:

* 値は基底型の実装で読む。subclass の `__iter__` / `__getitem__` / `__len__` / `items` /
  `__eq__` / `__hash__` / `__repr__` を呼ばない
* 容器の型（list / tuple / set / dict）と、要素・key と値の対応を保つ
* 別の要素・key が同じ atom になる容器は識別できない（比較不能・tail 識別不能・memo 不可）
* 同じ構造の値は同じ key・同じ tail（再利用できる）

置き場所: leaf の値 / runtime ref そのもの / `stable_key()` の戻り値 / `stable_key()` の戻り値に包む。
凍結の前後で確かめ、consumer（normalizer の fallback、validated identity の `structural_equals`）まで通す。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.analysis.condition.condition_cache import condition_cache_scope
from scripts.function_tracer_pcode.analysis.condition.normalizer import ConditionNormalizer
from scripts.function_tracer_pcode.core import structural
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.semantic_freeze import freeze_expression
from scripts.function_tracer_pcode.core.structural import (
    UNIDENTIFIED_TAG,
    exact_structural_identity,
    expression_key,
    expression_key_status,
    identity_is_memoizable,
)

CALLS: list = []


class LyingList(list):
    """基底 storage と違う中身を返す list（呼ばれたら記録する）。"""

    def __iter__(self):
        CALLS.append("list.__iter__")
        return iter([0])

    def __getitem__(self, index):
        CALLS.append("list.__getitem__")
        return 0

    def __len__(self):
        CALLS.append("list.__len__")
        return 1


class LyingTuple(tuple):
    def __iter__(self):
        CALLS.append("tuple.__iter__")
        return iter((0,))

    def __len__(self):
        CALLS.append("tuple.__len__")
        return 1


class LyingSet(frozenset):
    def __iter__(self):
        CALLS.append("frozenset.__iter__")
        return iter((0,))


class LyingDict(dict):
    def items(self):
        CALLS.append("dict.items")
        return iter([("k", 0)])

    def __iter__(self):
        CALLS.append("dict.__iter__")
        return iter(["k"])

    def keys(self):
        CALLS.append("dict.keys")
        return iter(["k"])

    def values(self):
        CALLS.append("dict.values")
        return iter([0])


class Twin(str):
    """基底型の "a" と同じ値に読まれるが、dict の中では別の key になる str。"""

    def __hash__(self):
        return 1

    def __eq__(self, other):
        return self is other

    def __repr__(self):
        CALLS.append("Twin.__repr__")
        return "'a'"


class _Ref:
    def __init__(self, value):
        self.value = value

    def stable_key(self):
        return self.value


class _WrappingRef:
    def __init__(self, value):
        self.value = value

    def stable_key(self):
        return ("wrapped", (self.value, 1))


def _leaf(value):
    return Expression(ExpressionType.VARIABLE, name="v", value=value, size=4)


def _direct_ref(value):
    return Expression(ExpressionType.UNKNOWN, name="u", runtime_ref=value, size=4)


def _stable_ref(value):
    return Expression(ExpressionType.UNKNOWN, name="u", runtime_ref=_Ref(value), size=4)


def _wrapped_ref(value):
    return Expression(ExpressionType.UNKNOWN, name="u", runtime_ref=_WrappingRef(value), size=4)


PLACEMENTS = {"leaf": _leaf, "direct_ref": _direct_ref, "stable_ref": _stable_ref, "wrapped_ref": _wrapped_ref}


def _build(placement, value, frozen):
    expr = PLACEMENTS[placement](value)
    return freeze_expression(expr) if frozen else expr


#: 基底 storage が違う 2 つの値（上書きした method は同じ中身を返す）
DIFFERENT = {
    "lying_list": (lambda: LyingList([1]), lambda: LyingList([2])),
    "lying_tuple": (lambda: LyingTuple((1,)), lambda: LyingTuple((2,))),
    "lying_set": (lambda: LyingSet({1}), lambda: LyingSet({2})),
    "lying_dict": (lambda: LyingDict({"k": 1}), lambda: LyingDict({"k": 2})),
    "list_vs_tuple": (lambda: [1, 2], lambda: (1, 2)),
    "dict_vs_pairs": (lambda: {"a": 1}, lambda: (("a", 1),)),
}


def _applicable(placement, name):
    # runtime ref そのものとしての容器は、従来どおり要素の安定 key で読む（set は意味 key を持たない）
    return not (placement == "direct_ref" and name == "lying_set")


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("placement", sorted(PLACEMENTS))
@pytest.mark.parametrize("name", sorted(DIFFERENT))
def test_values_that_differ_in_base_storage_or_type_never_share_a_key(name, placement, frozen):
    if not _applicable(placement, name):
        pytest.skip("a set as the runtime ref itself carries no semantic key (main semantics)")
    make_one, make_two = DIFFERENT[name]
    del CALLS[:]
    one, two = _build(placement, make_one(), frozen), _build(placement, make_two(), frozen)
    key_one, comparable_one = expression_key_status(one)
    key_two, _ = expression_key_status(two)
    assert key_one != key_two
    assert exact_structural_identity(one) != exact_structural_identity(two)
    # subclass の上書きした method は呼ばれない（基底 storage を読む）
    assert [call for call in CALLS if not call.startswith("Twin")] == []
    # 完全性の対照: 同じ値を作り直せば同じ key・同じ tail（識別済みなら memo してよい）
    again = _build(placement, make_one(), frozen)
    if comparable_one:
        assert expression_key(again) == key_one
        assert exact_structural_identity(again) == exact_structural_identity(one)
        assert identity_is_memoizable(exact_structural_identity(one))


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("placement", sorted(PLACEMENTS))
def test_a_dict_whose_keys_collapse_to_one_atom_is_never_identified(placement, frozen):
    del CALLS[:]
    one = _build(placement, {Twin("a"): 1, "a": 2}, frozen)
    two = _build(placement, {Twin("a"): 2, "a": 1}, frozen)
    key_one, comparable = expression_key_status(one)
    assert comparable is False
    assert key_one != expression_key_status(two)[0]
    first = exact_structural_identity(one)
    assert first[1][0] == UNIDENTIFIED_TAG
    assert first != exact_structural_identity(one)
    assert not identity_is_memoizable(first)
    assert "Twin.__repr__" not in CALLS
    # 対照: 区別できる key の dict は順序に依らず同じ key
    left = _build(placement, {"a": 1, "b": 2}, frozen)
    right = _build(placement, {"b": 2, "a": 1}, frozen)
    assert expression_key_status(left)[1] is True
    assert expression_key(left) == expression_key(right)


def _large(leaf):
    node = leaf
    for index in range(60):
        node = Expression.binary_op("INT_ADD", node, Expression.constant(index, size=4))
        node.size = 4
    return node


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
def test_the_normalizer_signature_keeps_values_apart_and_reuses_equal_ones(frozen):
    with condition_cache_scope():
        one = ConditionNormalizer._condition_expr_key(_large(_build("stable_ref", LyingList([1]), frozen)))
        two = ConditionNormalizer._condition_expr_key(_large(_build("stable_ref", LyingList([2]), frozen)))
        same = ConditionNormalizer._condition_expr_key(_large(_build("stable_ref", LyingList([1]), frozen)))
        collided = _large(_build("stable_ref", {Twin("a"): 1, "a": 2}, frozen))
        assert one != two
        assert one == same
        assert ConditionNormalizer._condition_expr_key(collided) != ConditionNormalizer._condition_expr_key(collided)


def test_the_validated_identity_api_reads_values_the_same_way():
    one = freeze_expression(_leaf(LyingList([1])))
    two = freeze_expression(_leaf(LyingList([2])))
    assert not structural.structural_equals(one, two)
    assert structural.structural_equals(one, freeze_expression(_leaf(LyingList([1]))))


class _DynamicKey:
    """`stable_key` を型が宣言せず、instance の `__getattr__` が作る object。"""

    def __getattr__(self, name):
        if name == "stable_key":
            CALLS.append("dynamic.stable_key")
            return lambda: ("dynamic",)
        raise AttributeError(name)


class _DeclaredKey:
    def stable_key(self):
        return ("declared",)


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
def test_only_a_stable_key_declared_by_the_type_is_read(frozen):
    # instance の hook が作る method は、型の宣言ではない（値の user code を identity にしない）
    del CALLS[:]
    dynamic = _build("direct_ref", _DynamicKey(), frozen)
    expression_key_status(dynamic)
    exact_structural_identity(dynamic)
    assert "dynamic.stable_key" not in CALLS
    # 対照: 型が宣言した stable_key は読まれ、同じ key は再利用できる
    declared = _build("direct_ref", _DeclaredKey(), frozen)
    assert expression_key(declared) == expression_key(_build("direct_ref", _DeclaredKey(), frozen))
    assert expression_key(declared) != expression_key(_build("direct_ref", None, frozen))


class _Opaque:
    __slots__ = ()


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize(
    "make",
    [
        lambda tag: frozenset({Twin(tag), tag}),
        lambda tag: {Twin(tag): 1, tag: 2},
        lambda tag: ("x", _Opaque()),
    ],
    ids=["colliding_set", "colliding_dict", "opaque_inside"],
)
def test_an_identity_that_cannot_be_fixed_never_merges_two_refs(make, frozen):
    # 値として固定できない部分を持つ安定 key は identity に使わない: 型名だけの印で、別の ref が
    # 同じ SMT の unknown 記号・同じ provenance key にならない（修正前: 両方とも一致した）
    from scripts.function_tracer_pcode.core.render_smt.unknowns import _unknown_runtime_identity_key

    one, two = _build("stable_ref", make("a"), frozen), _build("stable_ref", make("b"), frozen)
    assert _unknown_runtime_identity_key(one) != _unknown_runtime_identity_key(two)
    assert structural.object_target_key(one) != structural.object_target_key(two)
    assert expression_key_status(one)[1] is False


def test_a_mapping_proxy_reads_only_the_dict_it_wraps():
    from types import MappingProxyType

    del CALLS[:]
    one = _build("stable_ref", MappingProxyType(LyingDict({"k": 1})), False)
    two = _build("stable_ref", MappingProxyType(LyingDict({"k": 2})), False)
    assert expression_key(one) != expression_key(two)
    assert "dict.items" not in CALLS
    assert expression_key(_build("stable_ref", MappingProxyType({"k": 1}), False)) == expression_key(
        _build("stable_ref", MappingProxyType({"k": 1}), False)
    )


class _SelfKey:
    def stable_key(self):
        return self


def test_a_cyclic_value_is_unidentified_instead_of_raising():
    cyclic = [1]
    cyclic.append(cyclic)
    for value in (cyclic, _SelfKey()):
        for frozen in (False, True):
            expr = _build("stable_ref", value, frozen) if value is cyclic else _build("direct_ref", value, frozen)
            key, comparable = expression_key_status(expr)
            assert comparable is False
            assert exact_structural_identity(expr) != exact_structural_identity(expr)


@pytest.mark.parametrize("make", [
    lambda inner: LyingList([inner]),
    lambda inner: LyingDict({"k": inner}),
    lambda inner: LyingDict({inner: 1}),
], ids=["list_value", "dict_value", "dict_key"])
def test_the_freeze_walk_reaches_expressions_hidden_from_a_subclass_iterator(make):
    # 凍結の到達走査も基底 storage を読む: 上書きした iterator が隠した式も凍結の対象になる
    from scripts.function_tracer_pcode.core.semantic_lifecycle import is_validated

    inner = Expression.parameter("p", 0, size=4)
    expr = Expression(ExpressionType.UNKNOWN, name="u", runtime_ref=make(inner), size=4)
    del CALLS[:]
    freeze_expression(expr)
    assert is_validated(inner)
    assert [call for call in CALLS if call.startswith(("list.", "dict."))] == []


class _UnfixableRef:
    """`stable_key()` が値として固定できない object を含む ref（型名だけの印になる）。"""

    __slots__ = ("payload",)

    def __init__(self):
        self.payload = _Opaque()

    def stable_key(self):
        return ("glob", self.payload)


class _UnfixableSemanticRef:
    """`semantic_key()` だけが固定できない ref。`stable_key()` は全 instance で等しい（粗い key）。"""

    __slots__ = ("payload",)

    def __init__(self):
        self.payload = _Opaque()

    def semantic_key(self):
        return ("sem", self.payload)

    def stable_key(self):
        return ("glob",)


class _UnfixableSemanticOnlyRef:
    __slots__ = ("payload",)

    def __init__(self):
        self.payload = _Opaque()

    def semantic_key(self):
        return ("sem", self.payload)


class _UnfixableOriginRef:
    """origin の stable key だけが固定できない ref。自分の `stable_key()` は全 instance で等しい。"""

    __slots__ = ("origin_kind", "origin_ref")

    def __init__(self):
        self.origin_kind = "loop"
        self.origin_ref = _UnfixableRef()

    def stable_key(self):
        return ("glob",)


_UNFIXABLE_REFS = [_UnfixableRef, _UnfixableSemanticRef, _UnfixableSemanticOnlyRef, _UnfixableOriginRef]


@pytest.mark.parametrize("ref_type", _UNFIXABLE_REFS, ids=lambda t: t.__name__.strip("_"))
@pytest.mark.parametrize("kind", [ExpressionType.UNKNOWN, ExpressionType.VARIABLE])
def test_an_unfixable_ref_identity_reaches_no_consumer_as_an_identity(kind, ref_type):
    # projection が identity の field から外すので、全 consumer（SMT の unknown 記号・条件 oracle の
    # 記号・provenance key）で別の ref と併合されず、ref を持たない式とも区別される。一部の成分だけが
    # 固定できない ref も、残りの粗い key（全 instance で等しい stable key）に退避して併合しない
    from scripts.function_tracer_pcode.analysis.condition.query_identity import solver_symbol_identity
    from scripts.function_tracer_pcode.core.render_smt.unknowns import _unknown_runtime_identity_key
    from scripts.function_tracer_pcode.core.semantic_snapshot import semantic_projection
    from scripts.function_tracer_pcode.core.structural import structural_identity_digest

    def make(ref):
        return freeze_expression(Expression(kind, name="g", runtime_ref=ref, size=4))

    one, two, bare = make(ref_type()), make(ref_type()), make(None)
    projection = semantic_projection(one)
    assert projection.runtime_identity_unfixable is True
    assert projection.runtime_stable_key is None
    assert projection.runtime_semantic_key is None
    assert projection.runtime_stable_origin is None
    assert structural_identity_digest(one) is None
    assert structural.object_target_key(one) != structural.object_target_key(two)
    assert structural.object_target_key(one) != structural.object_target_key(bare)
    if kind is ExpressionType.UNKNOWN:
        assert _unknown_runtime_identity_key(one) != _unknown_runtime_identity_key(two)
    try:
        first, second = solver_symbol_identity(one), solver_symbol_identity(two)
    except (TypeError, ValueError):
        first = second = None
    assert first is None or first != second


def test_a_fixable_ref_identity_is_kept_and_shared():
    # 対照: 固定できる key の ref は identity を持ち、同じ key の ref は同じ記号になる
    from scripts.function_tracer_pcode.core.render_smt.unknowns import _unknown_runtime_identity_key
    from scripts.function_tracer_pcode.core.semantic_snapshot import semantic_projection

    class _Fixed:
        __slots__ = ()

        def stable_key(self):
            return ("glob", 1)

    one = freeze_expression(Expression(ExpressionType.UNKNOWN, name="g", runtime_ref=_Fixed(), size=4))
    two = freeze_expression(Expression(ExpressionType.UNKNOWN, name="g", runtime_ref=_Fixed(), size=4))
    assert semantic_projection(one).runtime_identity_unfixable is False
    from scripts.function_tracer_pcode.core.semantic_projection import canonical_atom

    assert semantic_projection(one).runtime_stable_key == canonical_atom(("glob", 1))
    assert _unknown_runtime_identity_key(one) == _unknown_runtime_identity_key(two)
    assert structural.object_target_key(one) == structural.object_target_key(two)

# -*- coding: utf-8 -*-
"""Issue #215 (SN3): atom と label の分類の契約を、Expression / ref の生成から consumer まで確かめる。

期待値は契約から決める（`core/structural.py` の「atom と label の分類」節）:

* scalar の値は `live_values` の規則（基底型の slot）で読む。subclass の `__eq__` / `__hash__` /
  `__int__` は値の identity に入らない。基底値が違えば key は違い、同じなら同じ（C-K1 / C-K2）。
* 識別できない値（既にある識別不能 token を何重に包んでも、`object_id`、型名だけの印）を持つ
  node の key は比較できず、tail は識別不能 token で、再計算とも等しくない。memo もされない（C-K5）。
* process の中でだけ意味を持つ token（打ち切った key の tail token、live object の identity）を
  持つ node は、比較はできないが識別済み（tail は再計算で等しく、memo してよい）。
* 通常 key・tail・memo・consumer は同じ分類を読む: 比較可能 ⇒ tail は識別済み・process に依らない。
  tail が識別不能 ⇒ 比較不能・再計算と不一致。

各値を leaf の値 / UNKNOWN の runtime ref / MEMORY の runtime ref に置き、凍結の前後で確かめる。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.analysis.condition.condition_cache import condition_cache_scope
from scripts.function_tracer_pcode.analysis.condition.normalizer import ConditionNormalizer
from scripts.function_tracer_pcode.core import structural
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.semantic_freeze import freeze_expression
from scripts.function_tracer_pcode.core.semantic_projection import canonical_atom
from scripts.function_tracer_pcode.core.structural import (
    EXACT_TAIL_TAG,
    UNIDENTIFIED_TAG,
    exact_structural_identity,
    expression_key,
    expression_key_safe,
    expression_key_status,
    key_is_comparable,
    key_is_process_independent,
)


# --------------------------------------------------------------------------
# 値: 敵対的な scalar の subclass（比較 method を呼ぶと値が無意味に一致する）
# --------------------------------------------------------------------------

class HostileInt(int):
    """どの値とも等しいと答え、hash も変換も値を隠す int。"""

    def __eq__(self, other):
        return True

    def __ne__(self, other):
        return False

    def __hash__(self):
        return 0

    def __lt__(self, other):
        return False

    def __int__(self):
        return 0

    def __index__(self):
        return 0


class HostileStr(str):
    def __eq__(self, other):
        return True

    def __ne__(self, other):
        return False

    def __hash__(self):
        return 0


class _Ref:
    def __init__(self, value):
        self.value = value

    def stable_key(self):
        return ("ref", self.value)


def _wrapped(token, depth):
    value = ("payload", token)
    for _ in range(depth):
        value = canonical_atom(value)
    return value


def _truncated_key():
    node = Expression.parameter("a", 0, size=4)
    for index in range(20):
        node = Expression.binary_op("INT_ADD", node, Expression.constant(index, size=4))
        node.size = 4
    return expression_key(node, budget=4)


# 置き場所: leaf の値 / UNKNOWN の runtime ref / MEMORY の runtime ref
def _leaf(value):
    return Expression(ExpressionType.VARIABLE, name="v", value=value, size=4)


def _unknown_ref(value):
    return Expression(ExpressionType.UNKNOWN, name="u", runtime_ref=_Ref(value), size=4)


def _memory_ref(value):
    memory = Expression(ExpressionType.MEMORY, operands=[Expression.parameter("p", 0, size=8)], size=4)
    memory.read_order_key = 1
    memory.runtime_ref = _Ref(value)
    return memory


PLACEMENTS = {"leaf": _leaf, "unknown_ref": _unknown_ref, "memory_ref": _memory_ref}


def _build(placement, value, frozen):
    expr = PLACEMENTS[placement](value)
    return freeze_expression(expr) if frozen else expr


def _tag(identity):
    return identity[1][0]


# --------------------------------------------------------------------------
# ① exact でない scalar は基底値で識別される（比較 method を呼ばない）
# --------------------------------------------------------------------------

@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("placement", sorted(PLACEMENTS))
@pytest.mark.parametrize(
    "make", [HostileInt, lambda v: HostileStr(str(v))], ids=["int_subclass", "str_subclass"],
)
def test_a_scalar_subclass_is_identified_by_its_base_value(make, placement, frozen):
    one, two = _build(placement, make(1), frozen), _build(placement, make(2), frozen)
    key_one, comparable_one = expression_key_status(one)
    key_two, comparable_two = expression_key_status(two)
    # 契約: 基底値が違えば key は違う（修正前は __eq__ で一致し、比較可能と答えた）
    assert key_one != key_two
    assert comparable_one and comparable_two
    assert exact_structural_identity(one) != exact_structural_identity(two)
    assert _tag(exact_structural_identity(one)) == EXACT_TAIL_TAG
    # 完全性の対照: 基底値が同じなら、subclass でも組み込みの値でも同じ key・同じ tail
    same = _build(placement, make(1), frozen)
    plain = _build(placement, 1 if make is HostileInt else "1", frozen)
    assert expression_key(same) == key_one == expression_key(plain)
    assert exact_structural_identity(same) == exact_structural_identity(one) == exact_structural_identity(plain)


@pytest.mark.parametrize("budget", [2, 4, 256])
def test_a_scalar_subclass_deep_in_a_truncated_tail_is_identified_by_its_base_value(budget):
    def chain(value):
        node = _leaf(value)
        for index in range(30):
            node = Expression.binary_op("INT_ADD", node, Expression.constant(index, size=4))
            node.size = 4
        return node

    assert expression_key(chain(HostileInt(1)), budget=budget) != expression_key(chain(HostileInt(2)), budget=budget)
    assert expression_key(chain(HostileInt(1)), budget=budget) == expression_key(chain(1), budget=budget)


def test_a_label_subclass_is_read_by_its_base_value():
    def variable(name):
        return Expression(ExpressionType.VARIABLE, name=name, value=None, size=HostileInt(4))

    assert expression_key(variable(HostileStr("x"))) != expression_key(variable(HostileStr("y")))
    assert expression_key(variable(HostileStr("x"))) == expression_key(Expression(
        ExpressionType.VARIABLE, name="x", value=None, size=4,
    ))
    # 読めない label（名前が任意の object）は識別不能
    odd = Expression(ExpressionType.VARIABLE, name=object(), value=None, size=4)
    key, comparable = expression_key_status(odd)
    assert comparable is False and key != expression_key(odd)
    assert _tag(exact_structural_identity(odd)) == UNIDENTIFIED_TAG


# --------------------------------------------------------------------------
# ② 既にある識別不能 token は識別済みへ昇格しない（memo・consumer を含む）
# --------------------------------------------------------------------------

@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("placement", sorted(PLACEMENTS))
@pytest.mark.parametrize("depth", [0, 1, 2, 3])
def test_an_existing_unidentified_token_is_never_promoted_to_an_identified_tail(depth, placement, frozen):
    token = structural.unidentified_identity("probe")
    expr = _build(placement, _wrapped(token, depth), frozen)
    key, comparable = expression_key_status(expr)
    assert comparable is False
    assert expression_key_safe(expr) is None
    # 修正前: tail が識別済み exact_tail になり、再計算で一致した
    first, second = exact_structural_identity(expr), exact_structural_identity(expr)
    assert _tag(first) == UNIDENTIFIED_TAG
    assert first != second
    # 通常 key も、同じ token を持つ別の node・自分自身の再計算と等しくならない
    other = _build(placement, _wrapped(token, depth), frozen)
    assert key != expression_key(expr)
    assert key != expression_key(other)


def _large(leaf):
    """normalizer の小さい予算（48 node）で比較できない式（署名は厳密な identity の fallback）。"""

    node = leaf
    for index in range(60):
        node = Expression.binary_op("INT_ADD", node, Expression.constant(index, size=4))
        node.size = 4
    return node


@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
def test_the_normalizer_fallback_never_memoizes_an_unidentified_identity(frozen):
    token = structural.unidentified_identity("probe")
    unidentified = _large(_build("leaf", _wrapped(token, 1), frozen))
    identified = _large(_build("leaf", HostileInt(7), frozen))
    with condition_cache_scope():
        first = ConditionNormalizer._condition_expr_key(unidentified)
        second = ConditionNormalizer._condition_expr_key(unidentified)
        assert first != second  # 修正前: memo が同じ identity を返し、署名が一致した
        # 再利用の対照: 識別済みの式は同じ署名（memo が効く）で、同じ構造の別 object とも一致する
        stable = ConditionNormalizer._condition_expr_key(identified)
        assert stable == ConditionNormalizer._condition_expr_key(identified)
        assert stable == ConditionNormalizer._condition_expr_key(_large(_build("leaf", 7, frozen)))
        assert _tag(stable) == EXACT_TAIL_TAG


def test_the_owner_memo_predicate_rejects_every_wrapping_of_an_unidentified_token():
    token = structural.unidentified_identity("probe")
    for depth in range(4):
        assert not structural.identity_is_memoizable(("x", _wrapped(token, depth)))
    assert structural.identity_is_memoizable(("x", _wrapped(("exact_tail", "0" * 64, 0), 2)))


# --------------------------------------------------------------------------
# process の中でだけ意味を持つ token: 比較はできないが識別済み（memo してよい）
# --------------------------------------------------------------------------

@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
@pytest.mark.parametrize("placement", sorted(PLACEMENTS))
def test_a_process_scoped_token_is_identified_but_not_comparable(placement, frozen):
    truncated = _truncated_key()
    expr = _build(placement, _wrapped(truncated, 1), frozen)
    key, comparable = expression_key_status(expr)
    assert comparable is False
    first = exact_structural_identity(expr)
    assert _tag(first) == EXACT_TAIL_TAG
    assert first == exact_structural_identity(expr)
    assert first == exact_structural_identity(_build(placement, _wrapped(truncated, 1), frozen))


# --------------------------------------------------------------------------
# 通常 key・tail・status が同じ分類を読む（値の種類 × 置き場所 × 凍結 × option）
# --------------------------------------------------------------------------

def _value_corpus():
    token = structural.unidentified_identity("probe")
    return {
        "exact_int": 5,
        "exact_str": "s",
        "float": 1.5,
        "int_subclass": HostileInt(5),
        "str_subclass": HostileStr("s"),
        "tuple": ("a", 1, HostileInt(2)),
        "nested_tuple": (("a", (1, ("b", HostileStr("c")))),),
        "unidentified_1": _wrapped(token, 1),
        "unidentified_3": _wrapped(token, 3),
        "object": object(),
        "truncated_key": _wrapped(_truncated_key(), 1),
    }


@pytest.mark.parametrize("options", [
    {}, {"normalize_commutative": False}, {"include_semantic_runtime_refs": False},
    {"include_memory_read_order": False}, {"strip_width_adapters": True, "collapse_full_masks": True},
], ids=["default", "no_commutative", "no_runtime_refs", "no_read_order", "lossy_shapes"])
@pytest.mark.parametrize("frozen", [False, True], ids=["unfrozen", "frozen"])
def test_the_key_the_tail_and_the_status_follow_one_classification(frozen, options):
    for name, value in _value_corpus().items():
        for placement in PLACEMENTS:
            if frozen and name == "object" and placement == "leaf":
                continue  # 凍結は任意の object を値に持つ式を拒む（凍結の契約）
            expr = _build(placement, value, frozen)
            key, comparable = expression_key_status(expr, **options)
            assert comparable is key_is_comparable(key), (name, placement)
            first = exact_structural_identity(expr, **options)
            second = exact_structural_identity(expr, **options)
            if comparable:
                assert _tag(first) == EXACT_TAIL_TAG, (name, placement)
                assert key_is_process_independent(key), (name, placement)
                assert key == expression_key(expr, **options), (name, placement)
            if _tag(first) == UNIDENTIFIED_TAG:
                assert not comparable, (name, placement)
                assert first != second, (name, placement)
                assert key != expression_key(expr, **options), (name, placement)
            else:
                assert first == second, (name, placement)
                # 通常 key と tail の受理規則は 1 つ: tail が識別済みなら、その label は canonical
                # encoding が受け付ける exact な値だけから成る
                view = structural._key_view(expr, structural.ExactTailOptions.of(**options))
                if isinstance(view, structural._KeyView):
                    structural._canonical_bytes(view.label)


# --------------------------------------------------------------------------
# 同じ分類の穴の横展開（包み直した印・enum・private な状態・容器・種別・cache）
# --------------------------------------------------------------------------

class _Opaque:
    __slots__ = ()


@pytest.mark.parametrize("placement", sorted(PLACEMENTS))
def test_an_object_or_unsupported_atom_wrapped_again_is_still_unidentified(placement):
    # `stable_key()` が `canonical_atom` の値を返すと、`object_id` / 型名だけの印が包み直される
    for marker in (canonical_atom(_Opaque()), ("unsupported_value", "m", "q")):
        for depth in (1, 2):
            value = marker
            for _ in range(depth):
                value = canonical_atom(value)
            expr = _build(placement, value, False)
            key, comparable = expression_key_status(expr)
            assert comparable is False, (marker[0], depth)
            assert key != expression_key(_build(placement, value, False))
            assert _tag(exact_structural_identity(expr)) == UNIDENTIFIED_TAG


def test_enum_members_are_identified_by_their_name():
    import enum

    class Color(enum.Enum):
        RED = 1
        BLUE = 2

    red, blue = _leaf(Color.RED), _leaf(Color.BLUE)
    assert expression_key(red) != expression_key(blue)
    assert expression_key(red) == expression_key(_leaf(Color.RED))
    assert expression_key_status(red)[1] is True


def test_an_object_whose_state_is_partly_private_is_not_identified_by_its_public_attributes():
    class Holder:
        def __init__(self, public, private):
            self.public = public
            self._private = private

    class Public:
        def __init__(self, public):
            self.public = public

    left, right = _leaf(Holder(1, "a")), _leaf(Holder(1, "b"))
    assert expression_key_status(left)[1] is False
    assert expression_key(left) != expression_key(right)
    # 対照: 公開された属性で状態が尽きる object は値で識別される
    assert expression_key(_leaf(Public(1))) == expression_key(_leaf(Public(1)))
    assert expression_key(_leaf(Public(1))) != expression_key(_leaf(Public(2)))


def test_a_node_kind_or_container_that_is_not_exact_is_not_read():
    class HostileKind:
        name = "CONSTANT"

        def __eq__(self, other):
            return True

        def __hash__(self):
            return hash(ExpressionType.CONSTANT)

    fake = Expression.constant(1, size=4)
    fake.expr_type = HostileKind()
    key, comparable = expression_key_status(fake)
    assert comparable is False
    assert key != expression_key(Expression.constant(1, size=4))

    class HostileList(list):
        def __getitem__(self, index):
            return Expression.constant(0, size=4)

        def __len__(self):
            return 2

    real = Expression.binary_op("INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(1, size=4))
    real.size = 4
    odd = Expression.binary_op("INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(1, size=4))
    odd.size = 4
    odd.operands = HostileList(odd.operands)
    assert expression_key_status(odd)[1] is False
    assert expression_key(odd) != expression_key(real)


def test_the_contradiction_cache_never_returns_an_unidentified_identity_twice():
    from scripts.function_tracer_pcode.core.condition import Condition

    token = structural.unidentified_identity("probe")
    expr = _large(_build("leaf", _wrapped(token, 1), True))
    expr = Expression.binary_op("INT_EQUAL", expr, Expression.constant(0, size=4))
    expr.size = 1
    expr = freeze_expression(expr)
    with condition_cache_scope():
        first = ConditionNormalizer.normalize_for_contradiction(Condition(expr))
        second = ConditionNormalizer.normalize_for_contradiction(Condition(expr))
    assert first != second

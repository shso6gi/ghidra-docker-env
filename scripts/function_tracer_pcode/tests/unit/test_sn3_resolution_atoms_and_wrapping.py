# -*- coding: utf-8 -*-
"""Issue #215 (SN3): key の段・atom・包みの規則の反例と対照（PR #216 の再監査で見つけたもの）。

どれも `core/structural.py`（構造 identity の owner）の契約の穴で、consumer 側では閉じられない:

* redirect（全 bit の mask を剥がす V_o）を path に積むと、back_ref の距離が key の段と
  ずれる。別の閉路が同じ key になった（C-K1 / C-K8）。
* runtime ref の意味 key の `object_id`（`id()`）と、型名だけの「支えられない値」が、
  比較可能な key と識別済みの tail token に入っていた（C-K5 / C-K6）。
* `canonical_atom` に二重に包まれた placeholder / token が検出と昇格規則から漏れた（C-K3 / Gate A）。
* 幅 adapter だけの閉路で key の計算が止まらない、可換演算の 2 子の順序が `TypeError` になる、
  予算 512 で `RecursionError` になる（失敗の経路。C-K5: 識別できないものは token にする）。
"""

from __future__ import annotations

import json
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.core import structural
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType
from scripts.function_tracer_pcode.core.semantic_projection import canonical_atom
from scripts.function_tracer_pcode.core.structural import (
    exact_structural_identity,
    exact_tail_token,
    ExactTailOptions,
    expression_key,
    expression_key_safe,
    expression_key_status,
    key_contains_placeholder,
    key_is_comparable,
)
from scripts.function_tracer_pcode.tests.unit._sn3_legacy_structural_key import legacy_expression_key


REPO_ROOT = Path(__file__).resolve().parents[4]
FULL = 0xFFFFFFFF


def _param(name="a", index=0, size=4):
    return Expression.parameter(name, index, size=size)


def _const(value, size=4):
    return Expression.constant(value, size=size)


def _binary(operator, left, right, size=4):
    expr = Expression.binary_op(operator, left, right)
    expr.size = size
    return expr


def _memory(address, read_order):
    expr = Expression(ExpressionType.MEMORY, operands=[address], size=4)
    expr.read_order_key = read_order
    return expr


class _Ref:
    """`stable_key()` を持つ runtime ref（`stable_key()` の値は任意）。"""

    def __init__(self, value):
        self.value = value

    def stable_key(self):
        return ("ref", self.value)


def _unknown_with_ref(value):
    return Expression(ExpressionType.UNKNOWN, name="u", runtime_ref=_Ref(value))


# --------------------------------------------------------------------------
# redirect は key の段を作らない: back_ref の距離は key の段数
# --------------------------------------------------------------------------

def _redirect_cycle():
    """R = b - N、N = a - M、M = N & 0xFFFFFFFF（M は N へ解ける）。展開は b - (a - (a - …))。"""

    a, b = _param("a", 0), _param("b", 1)
    n = _binary("INT_SUB", a, _const(0))
    m = _binary("INT_AND", n, _const(FULL))
    n.operands[1] = m
    return _binary("INT_SUB", b, n)


def _plain_cycle():
    """R = b - N、N = a - R。展開は b - (a - (b - (a - …)))（上と違う）。"""

    a, b = _param("a", 0), _param("b", 1)
    n = _binary("INT_SUB", a, _const(0))
    root = _binary("INT_SUB", b, n)
    n.operands[1] = root
    return root


def test_a_redirect_inside_a_cycle_does_not_shift_the_back_reference():
    redirect, plain = _redirect_cycle(), _plain_cycle()
    # 展開が違うことの対照（予算の無い identity は path に redirect を積まない）
    assert exact_structural_identity(redirect, collapse_full_masks=True) != exact_structural_identity(
        plain, collapse_full_masks=True
    )
    assert expression_key(redirect, collapse_full_masks=True) != expression_key(plain, collapse_full_masks=True)
    # 同じ形は同じ key（完全性の対照）
    assert expression_key(_redirect_cycle(), collapse_full_masks=True) == expression_key(
        _redirect_cycle(), collapse_full_masks=True
    )


def _redirect_in_tail():
    a, b, c = _param("a", 0), _param("b", 1), _param("c", 2)
    n = _binary("INT_SUB", a, _const(0))
    k = _binary("INT_SUB", c, n)
    n.operands[1] = _binary("INT_AND", k, _const(FULL))
    return _binary("INT_SUB", b, n)


def _shifted_in_tail():
    a, b, c = _param("a", 0), _param("b", 1), _param("c", 2)
    k = _binary("INT_SUB", c, _const(0))
    n = _binary("INT_SUB", a, k)
    root = _binary("INT_SUB", _binary("INT_AND", b, _const(FULL)), n)
    k.operands[1] = root
    return root


@pytest.mark.parametrize("budget", range(1, 9))
def test_a_redirect_inside_a_truncated_tail_does_not_shift_its_back_references(budget):
    left, right = _redirect_in_tail(), _shifted_in_tail()
    assert exact_structural_identity(left, collapse_full_masks=True) != exact_structural_identity(
        right, collapse_full_masks=True
    )
    assert expression_key(left, budget=budget, collapse_full_masks=True) != expression_key(
        right, budget=budget, collapse_full_masks=True
    )
    assert expression_key(left, budget=budget, collapse_full_masks=True) == expression_key(
        _redirect_in_tail(), budget=budget, collapse_full_masks=True
    )


def test_an_acyclic_redirect_keeps_the_main_key_value():
    # C-K2(a) の対照: 閉路の無い redirect の key は main と同じ値（budget の数え方も同じ）
    inner = _binary("INT_ADD", _param(), _const(1))
    expr = _binary("INT_MUL", _binary("INT_AND", inner, _const(FULL)), _param("b", 1))
    for budget in (2, 3, 4, 5, 256):
        key, comparable = expression_key_status(expr, budget=budget, collapse_full_masks=True)
        legacy = legacy_expression_key(expr, budget=budget, collapse_full_masks=True)
        assert comparable is key_is_comparable(legacy)
        if comparable:
            assert key == legacy


def test_a_cycle_of_redirects_terminates_and_is_never_equal():
    first = _binary("INT_AND", _param(), _const(FULL))
    second = _binary("INT_AND", first, _const(FULL))
    first.operands[0] = second
    for budget in (1, 3, 256):
        key = expression_key(first, budget=budget, collapse_full_masks=True)
        assert key_contains_placeholder(key)
        assert key != expression_key(first, budget=budget, collapse_full_masks=True)
    assert exact_structural_identity(first, collapse_full_masks=True) != exact_structural_identity(
        first, collapse_full_masks=True
    )


def test_a_cycle_back_through_a_redirect_points_at_its_resolved_node():
    # R = NEG(R) & 0xFFFFFFFF: R は NEG へ解ける。閉路は NEG への back_ref（redirect だけの閉路ではない）
    negate = Expression.unary_op("INT_NEGATE", _param())
    negate.size = 4
    redirect = _binary("INT_AND", negate, _const(FULL))
    negate.operands[0] = redirect
    for budget in (1, 2, 256):
        key = expression_key(redirect, budget=budget, collapse_full_masks=True)
        assert key == expression_key(redirect, budget=budget, collapse_full_masks=True)
        assert structural.UNIDENTIFIED_TAG not in json.dumps(key)
    # redirect も予算を 1 使うので、等しくなるのは打ち切りの無い予算のとき
    assert expression_key(redirect, collapse_full_masks=True) == expression_key(negate, collapse_full_masks=True)
    assert expression_key(redirect, collapse_full_masks=True) == (
        "unary", "INT_NEGATE", 4, ("cycle", "UNARY_OP", "", 4, ("back_ref", 1)),
    )


def test_a_width_adapter_cycle_terminates_and_is_never_equal():
    # 修正前は `_key_view` の adapter を剥がす loop が止まらなかった: 別 process で期限を付ける
    script = textwrap.dedent(
        """
        from scripts.function_tracer_pcode.core.expression import Expression
        from scripts.function_tracer_pcode.core.structural import (
            ExactTailOptions, exact_tail_token, expression_key, key_contains_placeholder,
        )
        a = Expression.parameter("a", 0, size=4)
        z = Expression.unary_op("INT_ZEXT", a)
        z.size = 8
        z.operands[0] = z
        key = expression_key(z, strip_width_adapters=True)
        assert key_contains_placeholder(key), key
        assert key != expression_key(z, strip_width_adapters=True)
        token = exact_tail_token(z, ExactTailOptions(strip_width_adapters=True))
        assert token[0] == "exact_tail_unidentified", token
        print("ok")
        """
    )
    completed = subprocess.run(
        [sys.executable, "-B", "-c", script], cwd=REPO_ROOT, capture_output=True, text=True, timeout=120,
    )
    assert completed.returncode == 0, completed.stderr
    assert completed.stdout.strip() == "ok"


# --------------------------------------------------------------------------
# runtime ref の意味 key も leaf の値と同じ atom の規則
# --------------------------------------------------------------------------

def test_a_float_in_a_runtime_ref_is_identified_by_its_value_not_by_a_reused_id():
    # 修正前は float が `("object_id", …, id(value))` になり、死後に id が再利用された別の値と
    # 同じ比較可能な key・同じ識別済み token になった
    # （id の再利用は GC の時機に依存するので数えない。下の「値が同じ別 object は同じ key」と
    # 「key に object_id が無い」が、id ではなく値で識別していることを直接固定する）
    keys: dict = {}
    identities: dict = {}
    for index in range(200):
        value = index * 1.5 + 0.1
        keys.setdefault(expression_key_safe(_unknown_with_ref(value)), set()).add(value)
        identities.setdefault(exact_structural_identity(_unknown_with_ref(value)), set()).add(value)
    assert all(len(values) == 1 for values in keys.values())
    assert all(len(values) == 1 for values in identities.values())
    assert None not in keys  # 識別できる値なので比較可能
    # 値が同じ別の float object は同じ key（id ではなく値で識別する）
    first, second = float("3.25"), float("3.25")
    assert first is not second
    key = expression_key(_unknown_with_ref(first))
    assert key == expression_key(_unknown_with_ref(second))
    assert '"object_id"' not in json.dumps(key)
    # 同じ値は同じ key（完全性の対照）。-0.0 と 0.0 は区別する
    assert expression_key(_unknown_with_ref(2.5)) == expression_key(_unknown_with_ref(2.5))
    assert expression_key(_unknown_with_ref(0.0)) != expression_key(_unknown_with_ref(-0.0))


class _Mutable:
    """`immutable_value` が値として固定できない object（型名だけの印になる）。"""

    def __init__(self, x):
        self.x = x


def test_an_unsupported_runtime_ref_value_is_never_equal():
    # 修正前は型名だけの印が tuple として畳まれ、別の値どうしが同じ比較可能な key になった
    first = _unknown_with_ref(_Mutable(1))
    second = _unknown_with_ref(_Mutable(2))
    assert expression_key_safe(first) is None
    assert expression_key(first) != expression_key(second)
    assert expression_key(first) != expression_key(first)
    assert exact_structural_identity(first) != exact_structural_identity(second)
    key, comparable = expression_key_status(first)
    assert comparable is False and key_contains_placeholder(key)
    # 対照: 値として固定できる ref は比較可能で、同じ値は同じ key
    assert expression_key_safe(_unknown_with_ref(("x", 1))) == expression_key_safe(_unknown_with_ref(("x", 1)))


def test_an_unidentified_atom_inside_memory_runtime_metadata_is_not_comparable():
    memory = _memory(_param(), 1)
    memory.runtime_ref = _Ref(_Mutable(1))
    assert expression_key_safe(memory) is None
    assert expression_key(memory) != expression_key(memory)


# --------------------------------------------------------------------------
# 何重に包まれても placeholder と token は見える
# --------------------------------------------------------------------------

def _chain(depth, tail):
    node = _param()
    for index in range(depth):
        node = _binary("INT_SUB", node, _const(index))
    return _binary("INT_SUB", node, _const(tail))


@pytest.mark.parametrize("wraps", [1, 2, 3])
def test_a_placeholder_or_token_wrapped_several_times_is_seen(wraps):
    truncated = expression_key(_chain(20, 1), budget=4)
    unidentified = structural.unidentified_identity("probe")
    for inner in (truncated, unidentified):
        wrapped = inner
        for _ in range(wraps):
            wrapped = canonical_atom(wrapped)
        for value in (("x", wrapped), json.loads(json.dumps(("x", wrapped)))):
            assert key_contains_placeholder(value)
            assert not structural.key_is_process_independent(value)
    token = unidentified
    for _ in range(wraps):
        token = canonical_atom(token)
    replaced = structural.cross_process_node(token)
    assert replaced != token and replaced[0] == structural.UNIDENTIFIED_TAG


@pytest.mark.parametrize("plain", [("tuple", ("list", "str"), ("a", 1)), ("tuple", ("cycle_count", 1)), ("list", ["str"])])
@pytest.mark.parametrize("wraps", [1, 2, 3])
def test_a_wrapped_plain_value_is_still_comparable(wraps, plain):
    # 対照: tag を持たない値は何重に包んでも placeholder ではない（包みの形に似た 2 要素の値も）
    for _ in range(wraps):
        plain = canonical_atom(plain)
    assert not key_contains_placeholder(("x", plain))
    assert structural.key_is_process_independent(("x", plain))
    assert structural.cross_process_node(plain) == plain


class _KeyRef:
    def __init__(self, key):
        self.key = key

    def stable_key(self):
        return ("structural", self.key)


def test_a_key_whose_runtime_ref_holds_a_truncated_key_is_not_comparable_at_any_nesting():
    inner = expression_key(_chain(20, 1), budget=4)
    middle = Expression(ExpressionType.UNKNOWN, name="u", runtime_ref=_KeyRef(inner))
    outer = Expression(ExpressionType.UNKNOWN, name="u", runtime_ref=_KeyRef(expression_key(middle)))
    for expr in (middle, outer):
        key, comparable = expression_key_status(expr)
        assert comparable is False
        assert comparable is key_is_comparable(key)
        assert expression_key_safe(expr) is None
        assert not structural.key_is_process_independent(key)
    # 対照: 比較可能な key を持つ ref は比較可能
    plain = Expression(ExpressionType.UNKNOWN, name="u", runtime_ref=_KeyRef(expression_key(_param())))
    assert expression_key_safe(plain) is not None


@pytest.mark.parametrize(
    "value",
    [("opaque", 1), ("cycle",), ("truncated", "x")],
    ids=["opaque", "cycle", "truncated"],
)
def test_a_leaf_value_that_holds_a_placeholder_is_not_comparable(value):
    # status / safe key / key_is_comparable が同じ答えを返す（C-K3）
    variable = Expression(ExpressionType.VARIABLE, name="v", value=value, size=4)
    key, comparable = expression_key_status(variable)
    assert comparable is False
    assert key_is_comparable(key) is False
    assert expression_key_safe(variable) is None
    # 識別不能 token を値に持つ leaf も同じ
    token_leaf = Expression(ExpressionType.VARIABLE, name="v", value=structural.unidentified_identity("x"), size=4)
    assert expression_key_status(token_leaf)[1] is False


def test_a_dataclass_field_named_like_an_unidentified_tag_is_still_identified():
    from dataclasses import dataclass

    @dataclass(frozen=True)
    class Fields:
        object_id: int
        unsupported_value: str

    variable = Expression(ExpressionType.VARIABLE, name="v", value=Fields(1, "x"), size=4)
    key = expression_key_safe(variable)
    assert key is not None
    assert key == expression_key_safe(Expression(ExpressionType.VARIABLE, name="v", value=Fields(1, "x"), size=4))
    assert key != expression_key_safe(Expression(ExpressionType.VARIABLE, name="v", value=Fields(2, "x"), size=4))


# --------------------------------------------------------------------------
# 失敗の経路: 可換の順序と、深さ
# --------------------------------------------------------------------------

def test_commutative_operands_without_a_tuple_order_still_get_one_key():
    # 修正前: `("read_order", None)` と `("read_order", 3)` の `<` が TypeError
    a = _param()
    left = expression_key(_binary("INT_ADD", _memory(a, None), _memory(a, 3)))
    right = expression_key(_binary("INT_ADD", _memory(a, 3), _memory(a, None)))
    assert left == right
    assert left != expression_key(_binary("INT_ADD", _memory(a, None), _memory(a, 4)))
    assert expression_key_safe(_binary("INT_ADD", _memory(a, 3), _memory(a, None))) == left
    # 対照: 比べられる組は main と同じ値
    ordered = _binary("INT_ADD", _memory(a, 2), _memory(a, 3))
    assert expression_key(ordered) == legacy_expression_key(ordered)


def test_a_large_budget_does_not_hit_the_recursion_limit():
    # 修正前は 1 段 2 frame の再帰で、予算 512 の key が RecursionError になった
    deep = _chain(1500, 1)
    key, comparable = expression_key_status(deep, budget=4000)
    assert comparable
    limit = sys.getrecursionlimit()
    sys.setrecursionlimit(20000)
    try:
        legacy = legacy_expression_key(deep, budget=4000)
        same = key == legacy  # 深い tuple の比較も再帰する
    finally:
        sys.setrecursionlimit(limit)
    assert same
    assert expression_key_safe(_chain(400, 1), budget=1024) is not None

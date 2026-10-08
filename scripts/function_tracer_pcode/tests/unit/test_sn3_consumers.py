# -*- coding: utf-8 -*-
"""Issue #215 / #181: 構造 key を identity に使う consumer が、深い条件を取り違えない。

consumer 側に個別の検査は足していない。`core/structural` の key が「等しい ⇒ 構造が
等しい」（C-K1）になったことで、`==` / `hash` だけで判定する consumer がそのまま健全に
なることを、代表的な consumer ごとに確かめる。consumer が独自に持っていた identity
（比較不能を `None` / 型名に潰す `condition_identity_key` や summary key）は owner の key
を使う形に寄せた。

条件 oracle / simplifier の cache identity は #105（PR #214 の `SolverQueryIdentity` /
`ImplicationIdentity`、完全比較）が所有するので、ここでは扱わない。

修正前の main では、下の test（`test_simplify_…` を除く）は FAIL する（PR 本文に記録）。
"""

from __future__ import annotations

from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.core import Condition, Expression
from scripts.function_tracer_pcode.core.structural import condition_key


def _param():
    return Expression.parameter("param_1", 0, data_type="int", size=4)


def _const(value):
    return Expression.constant(value, size=4)


def _chain(depth):
    node = _param()
    for index in range(depth):
        node = Expression.binary_op("INT_ADD", node, Expression.constant(index, size=4))
    return node


def _deep_less(tail, depth=400):
    """``param_1 + 0 + … + (depth-1) <s tail``。末尾の定数だけが違う深い条件。"""

    return Condition(Expression.binary_op("INT_SLESS", _chain(depth), _const(tail)))


def _nested_call_less(tail, depth=200):
    """深い部分が CALL の引数の中にあり、末尾が打ち切られる条件（入れ子の placeholder）。"""

    from scripts.function_tracer_pcode.core.expression import ExpressionType

    call = Expression(
        ExpressionType.CALL, name="f", size=4,
        operands=[Expression.binary_op("INT_ADD", _chain(depth), _const(tail))],
    )
    return Condition(Expression.binary_op("INT_SLESS", _const(0), call))


# --------------------------------------------------------------------------
# condition simplifier / SMT oracle
# --------------------------------------------------------------------------

def test_simplify_conditions_keeps_two_deep_conditions_that_differ_at_the_tail():
    from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier

    first = _deep_less(10).negate()
    second = _deep_less(20).negate()
    simplified = ConditionSimplifier.simplify_conditions([first, second])
    keys = {repr(condition_key(item)) for item in simplified}
    assert repr(condition_key(first)) in keys or repr(condition_key(second)) in keys
    # ¬(x<10) ∧ ¬(x<20) は ¬(x<20) と同値。2 つの条件を 1 つに取り違えて
    # ¬(x<10) だけを残してはいけない（それは x∈[10,20) を誤って含む）
    assert repr(condition_key(second)) in keys


# --------------------------------------------------------------------------
# return case merge（pairwise）
# --------------------------------------------------------------------------

def test_extract_return_cases_keeps_cases_whose_conditions_differ_only_at_the_tail():
    from scripts.function_tracer_pcode.core import ReturnInfo
    from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis
    from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import extract_return_cases

    analysis = FunctionReturnAnalysis(
        function_name="f", entry_point="0x1000",
        parameters=[{"name": "param_1", "index": 0, "size": 4, "data_type": "int", "is_signed": True}],
        returns=[ReturnInfo("0x10", _const(1), [_deep_less(10, 140)]),
                 ReturnInfo("0x20", _const(1), [_deep_less(20, 140)])],
        return_type="int",
    )
    cases = extract_return_cases(analysis, apply_effective_partition=False)
    assert len(cases) == 2
    assert [case.source_indices for case in cases] == [[0], [1]]


# --------------------------------------------------------------------------
# divergence proof の条件 identity（None-collapse）
# --------------------------------------------------------------------------

def test_condition_identity_key_separates_uncomparable_conditions():
    from scripts.function_tracer_pcode.analysis.returns.divergence_proofs import condition_identity_key

    left = condition_identity_key(_deep_less(10))
    right = condition_identity_key(_deep_less(20))
    assert left != right
    assert None not in left
    assert left == condition_identity_key(_deep_less(10))


# --------------------------------------------------------------------------
# #181: monolithic case identity
# --------------------------------------------------------------------------

_IDENTITIES = pytest.mark.parametrize(
    "identity",
    [
        "scripts.function_tracer_pcode.proof.strategies.monolithic_support:_monolithic_case_identity",
        "scripts.function_tracer_pcode.proof.monolithic_authority:_case_identity",
    ],
)


def _identity(path):
    import importlib

    module, name = path.split(":")
    return getattr(importlib.import_module(module), name)


def _case(conditions, *, value=None, index=0):
    return SimpleNamespace(
        index=index, source_indices=(index,), value_expr=value if value is not None else _const(1),
        conditions=list(conditions),
    )


@_IDENTITIES
def test_181_ac1_case_sets_with_deep_conditions_that_differ_at_the_tail_get_different_identities(identity):
    fn = _identity(identity)
    assert fn(_case([_deep_less(10)])) != fn(_case([_deep_less(20)]))
    assert fn(_case([_param_less(1), _deep_less(10)])) != fn(_case([_param_less(1), _deep_less(20)]))


def _param_less(value):
    return Condition(Expression.binary_op("INT_SLESS", _param(), _const(value)))


@_IDENTITIES
def test_181_ac2_ordinary_case_sets_still_reuse_the_same_identity(identity):
    fn = _identity(identity)
    # 完全に識別できる通常の case は、別 object で組み直しても同じ identity（再利用が成立）
    assert fn(_case([_param_less(1), _param_less(2)])) == fn(_case([_param_less(1), _param_less(2)]))
    # 深い条件でも同じ構造なら同じ identity（「常に再利用しない」へ退化していない）
    assert fn(_case([_deep_less(10)])) == fn(_case([_deep_less(10)]))


# --------------------------------------------------------------------------
# 構造 key を作れなかったときの identity（型名に潰さない）
# --------------------------------------------------------------------------

class _Unkeyable:
    """`structural_key` が失敗する条件 / 値（consumer の例外 fallback を通す）。"""

    negated = False
    expression = None

    def structural_key(self, **_kwargs):
        raise RuntimeError("no key")


def test_summary_keys_do_not_collapse_conditions_whose_key_cannot_be_built():
    from scripts.function_tracer_pcode.analysis.returns import summary_returns

    left = summary_returns._conditions_key([_Unkeyable()])
    right = summary_returns._conditions_key([_Unkeyable()])
    assert left != right
    # 「安定しない identity」として拒まれる（`object_id` と同じ扱い）
    assert summary_returns._key_contains_forbidden_identity(left)
    assert summary_returns._expression_key(_Unkeyable()) != summary_returns._expression_key(_Unkeyable())


def test_recurrence_summary_keys_do_not_collapse_on_failure():
    from scripts.function_tracer_pcode.analysis.recurrence import guard_proof, object_identity

    assert guard_proof._impl__summary_return_conditions_key(None, [_Unkeyable()]) != \
        guard_proof._impl__summary_return_conditions_key(None, [_Unkeyable()])
    assert object_identity._impl__summary_return_expression_key(None, _Unkeyable()) != \
        object_identity._impl__summary_return_expression_key(None, _Unkeyable())


# --------------------------------------------------------------------------
# expander の dedup 署名（normalizer）: 大きい式は厳密な identity で、key と同じ option
# --------------------------------------------------------------------------

def _load(read_order, tail=7):
    from scripts.function_tracer_pcode.core.expression import ExpressionType

    memory = Expression(ExpressionType.MEMORY, operands=[_param()], size=4)
    memory.read_order_key = read_order
    return Expression.binary_op("INT_ADD", Expression.binary_op("INT_ADD", _chain(80), memory), _const(tail))


@pytest.mark.parametrize("scoped", [False, True])
def test_the_signature_of_a_large_expression_follows_the_same_options_as_its_key(scoped):
    from scripts.function_tracer_pcode.analysis.condition.condition_cache import condition_cache_scope
    from scripts.function_tracer_pcode.analysis.condition.normalizer import ConditionNormalizer

    def signature(expr, read_order):
        return ConditionNormalizer._condition_expr_key(expr, include_memory_read_order=read_order)

    def run():
        first, second, other_tail = _load(1), _load(2), _load(1, tail=8)
        assert not ConditionNormalizer._expr_key(first)[1]  # 小さい予算では比べられない
        # read order を見ない署名では read order だけが違う式は同じ、見る署名では違う
        assert signature(first, False) == signature(second, False)
        assert signature(first, True) != signature(second, True)
        # どちらの署名でも、末尾が違う式は違う（C-K1）
        assert signature(first, False) != signature(other_tail, False)
        assert signature(first, True) != signature(other_tail, True)
        # 同じ式・同じ option は同じ（memo が option で混線しない: 順に両方を問う）
        assert signature(first, True) == signature(_load(1), True)
        assert signature(first, False) == signature(_load(1), False)

    if scoped:
        with condition_cache_scope():
            run()
    else:
        run()

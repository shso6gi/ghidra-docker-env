# -*- coding: utf-8 -*-
"""Issue #281: 条件 signature と構造 key の向きが、形の違う key の組で落ちない・順序に依存しない。

#281 の機序: bounded refinement が caller の node を operand だけ差し替えて作り直すとき `opcode` を
落としていた。`("intrinsic", "PTRADD", None, …)` と `("intrinsic", "PTRADD", 65, …)` が同じ条件集合に
並び、`conditions_signature` の `sort()` が `None` と `int` を比べて `TypeError` になった。

この file は **既存の API だけ** で書いてある（修正前の commit でも import でき、例外で落ちることを
記録するため）。operand の派生の方針と順序の契約は `test_issue281_operand_derivation.py`。
"""

import itertools
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.analysis.bounded_refinement import BoundedCallRefiner
from scripts.function_tracer_pcode.analysis.condition import ConditionNormalizer
from scripts.function_tracer_pcode.analysis.effects.condition_algebra import _impl__additive_signature
from scripts.function_tracer_pcode.analysis.effects.summary import EffectSummary
from scripts.function_tracer_pcode.analysis.recurrence.object_identity import _impl__canonicalize_expression
from scripts.function_tracer_pcode.analysis.returns.condition_logic import ConditionLogicService
from scripts.function_tracer_pcode.core import (
    CallTargetRef,
    Condition,
    DeferredCallInfo,
    Expression,
    ExpressionType,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.intrinsics import PTRADD_OPCODE
from scripts.function_tracer_pcode.semantics.transform.expander import ExpressionExpander
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


def _param(name: str = "n", index: int = 0, size: int = 8) -> Expression:
    return Expression.parameter(name, index=index, data_type="long", size=size)


def _const(value: int, size: int = 8) -> Expression:
    return Expression.constant(value, size=size)


def _ptradd(base: Expression, *, opcode=PTRADD_OPCODE) -> Expression:
    return Expression.intrinsic("PTRADD", [base, _const(4), _const(8)], size=8, opcode=opcode)


def _eq_zero(expr: Expression, negated: bool = False) -> Condition:
    return Condition(Expression.binary_op("INT_EQUAL", expr, _const(0, size=expr.size or 8)), negated=negated)


# ---------------------------------------------------------------------------
# AC1: 修正前に落ちる組（#281 の 7 件の実測と同じ形の key）
# ---------------------------------------------------------------------------


def _mixed_opcode_conditions():
    # 7 件で観測した組: 同じ PTRADD の key の opcode の位置が None と 65
    return [_eq_zero(_ptradd(_param(), opcode=None)), _eq_zero(_ptradd(_param(), opcode=PTRADD_OPCODE))]


def _mixed_read_order_conditions():
    # 同じ番地の読み出しの key の read_order が None と int
    return [
        _eq_zero(Expression.memory(_param(), size=8, read_order_key=None)),
        _eq_zero(Expression.memory(_param(), size=8, read_order_key=3)),
    ]


@pytest.mark.parametrize("make_conditions", [_mixed_opcode_conditions, _mixed_read_order_conditions])
def test_conditions_signature_accepts_none_and_int_at_the_same_key_position(make_conditions):
    conditions = make_conditions()
    keys = [ConditionNormalizer.normalize_for_contradiction(c) for c in conditions]
    # 前提: tuple の `<` ではこの 2 つを比べられない（修正前の `sort()` が落ちた理由）
    with pytest.raises(TypeError):
        keys[0] < keys[1]

    signature = ConditionNormalizer.conditions_signature(conditions)

    assert len(signature) == 2


@pytest.mark.parametrize("make_conditions", [_mixed_opcode_conditions, _mixed_read_order_conditions])
def test_pruning_conditions_signature_accepts_mixed_key_shapes(make_conditions):
    conditions = make_conditions()
    signature = ConditionLogicService.pruning_conditions_signature(None, conditions)
    assert signature == ConditionNormalizer.conditions_signature(conditions)


def test_swap_decision_accepts_mixed_key_shapes_and_is_symmetric():
    left = _ptradd(_param(), opcode=None)
    right = _ptradd(_param(), opcode=PTRADD_OPCODE)
    forward = ConditionNormalizer.normalize_for_contradiction(
        Condition(Expression.binary_op("INT_EQUAL", left, right), negated=False)
    )
    backward = ConditionNormalizer.normalize_for_contradiction(
        Condition(Expression.binary_op("INT_EQUAL", right, left), negated=False)
    )
    assert forward == backward
    # 不等号は向きを入れ替えると演算子と極性も入れ替わる: left < right と right > left は同じ正規形
    less = ConditionNormalizer.normalize_for_contradiction(
        Condition(Expression.binary_op("INT_SLESS", left, right), negated=False)
    )
    greater = ConditionNormalizer.normalize_for_contradiction(
        Condition(Expression.binary_op("INT_SLESS", right, left), negated=False)
    )
    assert less != greater


def test_additive_signature_orders_terms_with_mixed_key_shapes():
    expr = Expression.binary_op("INT_ADD", _ptradd(_param(), opcode=None), _ptradd(_param(), opcode=PTRADD_OPCODE))
    swapped = Expression.binary_op("INT_ADD", _ptradd(_param(), opcode=PTRADD_OPCODE), _ptradd(_param(), opcode=None))
    assert _impl__additive_signature(expr) == _impl__additive_signature(swapped)


def test_commutative_expansion_signature_orders_mixed_key_shapes():
    expander = object.__new__(ExpressionExpander)
    a = _ptradd(_param(), opcode=None)
    b = _ptradd(_param(), opcode=PTRADD_OPCODE)
    forward = expander._expansion_expression_signature(Expression.binary_op("INT_ADD", a, b))
    backward = expander._expansion_expression_signature(Expression.binary_op("INT_ADD", b, a))
    assert forward == backward


def test_object_identity_canonicalization_orders_mixed_key_shapes():
    holder = SimpleNamespace()
    holder._canonicalize_expression = lambda e: _impl__canonicalize_expression(holder, e)
    a = _ptradd(_param(), opcode=None)
    b = _ptradd(_param(), opcode=PTRADD_OPCODE)
    forward = holder._canonicalize_expression(Expression.binary_op("INT_ADD", a, b))
    backward = holder._canonicalize_expression(Expression.binary_op("INT_ADD", b, a))
    assert forward.operands[0].opcode == backward.operands[0].opcode


# ---------------------------------------------------------------------------
# AC2 / AC3: 順序に依存せず、異なる集合は異なる signature
# ---------------------------------------------------------------------------


def _condition_pool():
    x = _param("x", 0)
    y = _param("y", 1)
    return [
        _eq_zero(_ptradd(x, opcode=None)),
        _eq_zero(_ptradd(x, opcode=PTRADD_OPCODE)),
        _eq_zero(Expression.memory(x, size=8, read_order_key=None)),
        _eq_zero(Expression.memory(x, size=8, read_order_key=3)),
        Condition(Expression.binary_op("INT_SLESS", x, _const(1)), negated=False),
        Condition(Expression.binary_op("INT_SLESS", x, _const(1)), negated=True),
        Condition(Expression.binary_op("INT_SLESS", x, y), negated=False),
        Condition(Expression.binary_op("INT_SLESS", y, x), negated=False),
    ]


def test_conditions_signature_is_independent_of_condition_order():
    pool = _condition_pool()
    reference = ConditionNormalizer.conditions_signature(pool)
    for permutation in itertools.islice(itertools.permutations(pool), 0, 5040, 37):
        assert ConditionNormalizer.conditions_signature(list(permutation)) == reference


def test_different_condition_sets_have_different_signatures():
    pool = _condition_pool()
    signatures = {}
    for size in range(0, 4):
        for subset in itertools.combinations(range(len(pool)), size):
            signature = ConditionNormalizer.conditions_signature([pool[i] for i in subset])
            assert signature not in signatures, (subset, signatures.get(signature))
            signatures[signature] = subset
    # 多重集合: 同じ条件の重複は数が違えば別
    once = ConditionNormalizer.conditions_signature([pool[0]])
    twice = ConditionNormalizer.conditions_signature([pool[0], pool[0]])
    assert once != twice



def test_bounded_refinement_keeps_the_opcode_of_a_rebuilt_node():
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[_param()],
        sequence=0,
    )
    call_value = Expression.unknown(deferred.placeholder_name, runtime_ref=deferred.unknown_ref)
    caller = create_mock_analysis(
        "caller",
        parameters=[
            {"name": "n", "index": 0, "data_type": "long", "size": 8},
            {"name": "m", "index": 1, "data_type": "long", "size": 8},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=_const(1),
                # 展開で作り直される PTRADD と、展開に関わらない PTRADD
                conditions=[
                    # deferred call を operand に持つ caller の PTRADD は、展開で作り直される
                    _eq_zero(_ptradd(call_value)),
                    Condition(
                        Expression.binary_op("INT_SLESS", _ptradd(_param("m", index=1)), _const(0)), negated=False
                    ),
                ],
            )
        ],
    )
    caller.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    callee = create_mock_analysis(
        "callee",
        parameters=[{"name": "x", "index": 0, "data_type": "long", "size": 8}],
        returns=[
            ReturnInfo(
                address="0x2000", value=Expression.binary_op("INT_ADD", _param("x", 0), _const(1)), conditions=[]
            )
        ],
    )
    callee.effect_summary = EffectSummary(parameter_names=["x"], effects=[])
    refiner = BoundedCallRefiner(
        lambda target_ref, args=None: callee if target_ref == CallTargetRef.from_name("callee") else None,
        max_unroll=1,
        max_cases=8,
        debug=False,
    )

    assert refiner.refine_analysis(caller) is True

    ptradds = [
        node
        for ret in caller.returns
        for condition in ret.conditions
        for node in [condition.expression.operands[0]]
        if node.expr_type is ExpressionType.INTRINSIC
    ]
    rebuilt = [node for node in ptradds if node.operands[0].expr_type is ExpressionType.BINARY_OP]
    assert rebuilt, "the deferred call inside the PTRADD was expanded"
    # 修正前は作り直した PTRADD の opcode が None になり、作り直されない PTRADD（opcode 65）と同じ
    # 条件列に並ぶと conditions_signature が TypeError になった（その組は上の test が固定する）
    assert all(node.opcode == PTRADD_OPCODE for node in ptradds)

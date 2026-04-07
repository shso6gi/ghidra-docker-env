# -*- coding: utf-8 -*-
"""分岐条件の call-aware 復元に関する回帰テスト"""

from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.condition import ConditionTracker
from scripts.function_tracer_pcode.model import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.transform.expander import ExpandedValue


def _param(name: str, index: int, size: int = 4) -> Expression:
    return Expression.parameter(name, index=index, size=size)


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size=size)


def _slt(left: Expression, right: Expression) -> Expression:
    return Expression.binary_op("INT_SLESS", left, right)


def test_condition_tracker_refines_unknown_branch_condition_via_call_summary():
    tracer = Mock()
    tracer.high_function = Mock()
    tracer.debug = False

    tracker = ConditionTracker(tracer)

    class _FakeCondVarnode:
        def getSize(self):
            return 1

    cond_varnode = _FakeCondVarnode()
    raw_condition = _slt(
        _param("param_3", 2),
        Expression.unknown("call_out_of_scope:ptr_select_path"),
    )
    block_info = Mock()
    block_info.index = 7
    block_info.branch_condition = raw_condition
    block_info.branch_condition_varnode = cond_varnode
    tracker.block_by_index = {7: block_info}

    choose_left = Condition(_slt(_param("param_2", 1), _param("param_1", 0)))
    choose_right = choose_left.negate()
    expanded_values = [
        ExpandedValue(
            _slt(
                _param("param_3", 2),
                Expression.binary_op("INT_ADD", _param("param_1", 0), _const(10)),
            ),
            [choose_left],
        ),
        ExpandedValue(
            _slt(
                _param("param_3", 2),
                Expression.binary_op(
                    "INT_ADD",
                    Expression.binary_op("INT_MULT", _param("param_2", 1), _const(3)),
                    _const(1),
                ),
            ),
            [choose_right],
        ),
    ]

    class _FakeExpander:
        def __init__(self, *args, **kwargs):
            pass

        def expand_from_varnode(self, varnode, base_conditions, depth=0):
            assert varnode is cond_varnode
            assert base_conditions == []
            return expanded_values

    with patch("scripts.function_tracer_pcode.transform.ExpressionExpander", _FakeExpander):
        changed = tracker.refine_branch_conditions(call_resolver=Mock(), parameters=[])

    assert changed == 1
    refined = block_info.branch_condition
    assert refined.expr_type == ExpressionType.PHI
    assert "call_out_of_scope" not in refined.to_string()
    assert "unknown" not in refined.to_smt()
    assert "ite" in refined.to_smt()

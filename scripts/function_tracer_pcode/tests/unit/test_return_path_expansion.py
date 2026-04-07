# -*- coding: utf-8 -*-
"""non-PHI return の複数経路展開に関する回帰テスト"""

from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.condition import ConditionTracker
from scripts.function_tracer_pcode.model import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.transform.expander import ExpandedValue


def _param(name: str, size: int = 4) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, size=size)


def _cond(operator: str, left: Expression, right: Expression, negated: bool = False) -> Condition:
    return Condition(
        Expression(
            ExpressionType.BINARY_OP,
            operator=operator,
            operands=[left, right],
            size=1,
        ),
        negated=negated,
    )


def test_condition_tracker_collects_all_valid_paths_to_return():
    tracer = Mock()
    tracer.high_function = Mock()
    tracer.debug = False

    tracker = ConditionTracker(tracer)

    return_parent = object()
    return_op = Mock()
    return_op.getParent.return_value = return_parent

    block_info = Mock()
    block_info.index = 3
    all_paths = [[Mock()], [Mock(), Mock()]]

    tracker.get_block_by_hash = Mock(return_value=block_info)
    tracker.get_all_valid_paths_to_block = Mock(return_value=all_paths)

    result = tracker.get_all_valid_paths_to_return(return_op)

    assert result == all_paths
    tracker.get_block_by_hash.assert_called_once_with(return_parent)
    tracker.get_all_valid_paths_to_block.assert_called_once_with(
        block_info,
        limit_paths=None,
    )


def test_condition_tracker_collects_all_valid_block_paths_to_return():
    class _FakeBlock:
        def __init__(self, index):
            self._index = index

        def getIndex(self):
            return self._index

    tracer = Mock()
    tracer.high_function = Mock()
    tracer.debug = False

    tracker = ConditionTracker(tracer)

    entry_block = _FakeBlock(0)
    true_block = _FakeBlock(1)
    false_block = _FakeBlock(2)
    return_block = _FakeBlock(3)

    selector = _param("param_1")
    zero = Expression.constant(0, 4)
    branch_condition = Expression.binary_op("INT_NOTEQUAL", selector, zero)

    entry_info = Mock(
        index=0,
        out_edges=[true_block, false_block],
        branch_condition=branch_condition,
        true_out_index=1,
        false_out_index=2,
    )
    entry_info.has_conditional_branch.return_value = True
    true_info = Mock(index=1, out_edges=[return_block])
    true_info.has_conditional_branch.return_value = False
    false_info = Mock(index=2, out_edges=[return_block])
    false_info.has_conditional_branch.return_value = False
    return_info = Mock(index=3, out_edges=[])
    return_info.has_conditional_branch.return_value = False

    mapping = {
        true_block: true_info,
        false_block: false_info,
        return_block: return_info,
    }

    tracker.entry_block = entry_info
    tracker.get_block_by_hash = Mock(side_effect=lambda block: mapping.get(block))

    return_op = Mock()
    return_op.getParent.return_value = return_block

    path_entries = tracker.get_all_valid_block_paths_to_return(return_op)

    assert len(path_entries) == 2
    assert [[block.index for block in blocks] for blocks, _conds in path_entries] == [
        [0, 1, 3],
        [0, 2, 3],
    ]
    condition_strings = [[cond.to_string() for cond in conds] for _blocks, conds in path_entries]
    assert condition_strings[0] == ["(param_1 != 0)"]
    assert condition_strings[1] in (["(param_1 == 0)"], ["(not (param_1 != 0))"])


def test_return_analyzer_expands_non_multiequal_return_for_each_valid_path():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)

    tracer = Mock()
    tracer.clear_cache = Mock()

    path_a = [
        _cond("INT_SLESS", _param("param_1"), _param("param_2")),
    ]
    path_b = [
        _cond("INT_SLESSEQUAL", _param("param_2"), _param("param_1")),
        _cond("INT_SLESS", _param("param_1"), _param("param_3"), negated=True),
    ]
    all_paths = [path_a, path_b]

    class FakeExpander:
        calls = []

        def __init__(self, tracer_obj, tracker_obj, debug=False, call_resolver=None, **kwargs):
            self.tracer = tracer_obj
            self.tracker = tracker_obj
            self.debug = debug
            self.call_resolver = call_resolver

        def expand_from_varnode(self, return_varnode, base_conditions, depth=0):
            FakeExpander.calls.append([cond.to_string() for cond in base_conditions])
            return [
                ExpandedValue(
                    Expression(ExpressionType.CONSTANT, value=0xFFFFFFF6, size=4),
                    list(base_conditions),
                )
            ]

    with patch.object(ReturnAnalyzer, "_contains_multiequal", return_value=False):
        with patch("scripts.function_tracer_pcode.transform.ExpressionExpander", FakeExpander):
            results = analyzer._analyze_return_value(
                return_varnode=Mock(),
                address="0x1000",
                tracer=tracer,
                condition_tracker=Mock(),
                path_conditions=path_a,
                return_index=7,
                all_path_conditions=all_paths,
            )

    assert len(results) == 2
    assert [ret.branch_index for ret in results] == [700, 701]
    assert [cond.to_string() for cond in results[0].conditions] == [
        cond.to_string() for cond in path_a
    ]
    assert [cond.to_string() for cond in results[1].conditions] == [
        cond.to_string() for cond in path_b
    ]
    assert FakeExpander.calls == [
        [cond.to_string() for cond in path_a],
        [cond.to_string() for cond in path_b],
    ]
    tracer.clear_cache.assert_called_once()

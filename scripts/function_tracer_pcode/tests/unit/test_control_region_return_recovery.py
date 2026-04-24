# -*- coding: utf-8 -*-

from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.model import Condition, Expression
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


class _FakeSeq:
    def __init__(self, target="0x1000", time=1, order=0):
        self._target = target
        self._time = time
        self._order = order

    def getTarget(self):
        return self._target

    def getTime(self):
        return self._time

    def getOrder(self):
        return self._order


class _FakeReturnOp:
    def __init__(self, value_varnode=None):
        self._value_varnode = value_varnode
        self._seq = _FakeSeq("0x401000", 9, 2)

    def getNumInputs(self):
        return 2 if self._value_varnode is not None else 1

    def getInput(self, index):
        if index == 1 and self._value_varnode is not None:
            return self._value_varnode
        raise AssertionError(index)

    def getSeqnum(self):
        return self._seq


class _FakeTracer:
    def __init__(self, *_args, **_kwargs):
        self.high_function = Mock()
        self.debug = False
        self.unknown_tracker = Mock(events=[])
        self.record_deferred_call = None

    def find_return_ops(self):
        return [Mock()]

    def clear_cache(self):
        return None


class _FakeConditionTracker:
    def __init__(self, _tracer):
        self.block_by_index = {}

    def build(self):
        return None

    def refine_branch_conditions(self, **_kwargs):
        return None


def test_materialize_direct_path_specific_return_source_recovers_constant():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analyzer._current_parameters = []

    tracer = Mock()
    tracer.trace_varnode.return_value = Expression.constant(1000, 4)
    tracer.clear_cache = Mock()

    condition = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.parameter("param_1", 0, size=4),
            Expression.constant(0, 4),
        ),
        False,
    )

    results = analyzer._materialize_direct_path_specific_return_source(
        Mock(getDef=Mock(return_value=None)),
        "0x401000",
        tracer,
        [condition],
        0,
        site_metadata={"pcode_identity": "0x401000:t1", "pcode_time": 1, "pcode_order": 0},
    )

    assert results is not None
    assert len(results) == 1
    assert results[0].value.expr_type.name == "CONSTANT"
    assert int(results[0].value.value) == 1000


def test_materialize_direct_path_specific_return_source_keeps_non_phi_expression():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analyzer._current_parameters = []

    tracer = Mock()
    tracer.trace_varnode.return_value = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("param_1", 0, size=4),
        Expression.constant(4, 4),
    )
    tracer.clear_cache = Mock()

    with patch.object(
        analyzer,
        "_split_object_centric_return_case",
        side_effect=AssertionError("non-PHI expressions should not be split"),
    ):
        results = analyzer._materialize_direct_path_specific_return_source(
            Mock(getDef=Mock(return_value=None)),
            "0x401000",
            tracer,
            [],
            0,
            site_metadata={"pcode_identity": "0x401000:t1", "pcode_time": 1, "pcode_order": 0},
        )

    assert results is not None
    assert len(results) == 1
    assert results[0].value.expr_type.name == "BINARY_OP"
    assert results[0].value.operator == "INT_ADD"


def test_return_infos_have_conflicting_overlap_detects_incompatible_cases():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    shared_condition = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.parameter("param_1", 0, size=4),
            Expression.constant(0, 4),
        ),
        False,
    )
    left = analyzer._make_return_info(
        address="0x1",
        value=Expression.constant(1000, 4),
        conditions=[shared_condition],
        branch_index=0,
    )
    right = analyzer._make_return_info(
        address="0x2",
        value=Expression.constant(1001, 4),
        conditions=[shared_condition],
        branch_index=1,
    )

    assert analyzer._return_infos_have_conflicting_overlap([left, right]) is True


def test_recover_control_region_returns_early_prefers_switch_recovery():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    recovered = [
        analyzer._make_return_info(
            address="0x1",
            value=Expression.constant(1000, 4),
            conditions=[],
            branch_index=0,
        )
    ]

    with patch.object(
        analyzer,
        "_recover_switch_like_returns_from_placeholder_analysis",
        return_value=recovered,
    ) as switch_mock, patch.object(
        analyzer,
        "_recover_control_flow_returns_from_block_paths",
    ) as path_mock:
        result, notes = analyzer._recover_control_region_returns_early(
            Mock(),
            Mock(),
            Mock(),
            [Mock()],
            active_functions=set(),
        )

    switch_mock.assert_called_once()
    path_mock.assert_not_called()
    assert result == recovered
    assert notes == ["switch_return_recovery", "control_region_return_recovery"]


def test_analyze_function_skips_effect_summary_when_control_region_recovery_succeeds():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analyzer.program.getImageBase.return_value.getOffset.return_value = 0

    function = Mock()
    function.getName.return_value = "branch_switch_dense"
    function.getEntryPoint.return_value = "0x401000"

    decompile_results = Mock()
    decompile_results.decompileCompleted.return_value = True
    decompile_results.getHighFunction.return_value = Mock(getFunctionPrototype=Mock(return_value=None))
    analyzer._get_decompiler = Mock(return_value=Mock(decompileFunction=Mock(return_value=decompile_results)))

    recovered = [
        analyzer._make_return_info(
            address="0x401000",
            value=Expression.constant(1000, 4),
            conditions=[],
            branch_index=0,
        )
    ]

    with patch("scripts.function_tracer_pcode.analysis.analyzer.PcodeTracer", _FakeTracer), patch(
        "scripts.function_tracer_pcode.analysis.analyzer.ConditionTracker",
        _FakeConditionTracker,
    ), patch(
        "scripts.function_tracer_pcode.analysis.phi_resolver.PhiHandler",
        Mock,
    ), patch.object(
        analyzer,
        "_collect_parameters",
        return_value=[{"name": "param_1", "index": 0, "size": 4}],
    ), patch.object(
        analyzer,
        "_augment_parameters_with_implicit_passthrough",
        side_effect=lambda params, *_args, **_kwargs: params,
    ), patch.object(
        analyzer,
        "_get_return_type_info",
        return_value=(None, "int"),
    ), patch.object(
        analyzer,
        "_detect_signedness",
        return_value=None,
    ), patch.object(
        analyzer,
        "_recover_control_region_returns_early",
        return_value=(recovered, ["control_region_return_recovery"]),
    ), patch.object(
        analyzer,
        "_build_effect_summary",
        side_effect=AssertionError("effect_summary should not be built"),
    ), patch.object(
        analyzer,
        "_analyze_return_op",
        side_effect=AssertionError("generic return analysis should not run"),
    ), patch.object(
        analyzer,
        "_apply_structural_recurrence_summary",
        return_value=None,
    ), patch.object(
        analyzer,
        "_apply_bounded_call_refinement",
        return_value=None,
    ):
        result = analyzer.analyze_function(function, timeout=1)

    assert result is not None
    assert len(result.returns) == 1
    assert int(result.returns[0].value.value) == 1000
    assert "control_region_return_recovery" in result.analysis_notes


def test_apply_structural_recurrence_summary_skips_resolved_plain_memory_return_without_candidate():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    function = Mock()
    function.getName.return_value = "plain_load"
    high_function = Mock()
    high_function.getBasicBlocks.return_value = []
    tracer = Mock()
    analysis = create_mock_analysis(
        "plain_load",
        return_type="int",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int *", "size": 8},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4},
        ],
        returns=[
            analyzer._make_return_info(
                address="0x1000",
                value=Expression.memory(Expression.parameter("param_1", index=0, size=8), size=4),
                conditions=[],
                branch_index=0,
            )
        ],
    )

    with patch(
        "scripts.function_tracer_pcode.analysis.analyzer.StructuralRecurrenceSummarizer.try_summarize_function",
        side_effect=AssertionError("resolved plain memory returns should not trigger structural summary"),
    ):
        result = analyzer._apply_structural_recurrence_summary(
            function,
            high_function,
            analysis,
            tracer,
        )

    assert result is None


def test_apply_structural_recurrence_summary_uses_structural_summarizer():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    function = Mock()
    function.getName.return_value = "branch_for_accumulate"
    high_function = Mock()
    tracer = Mock()
    analysis = create_mock_analysis(
        "branch_for_accumulate",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            analyzer._make_return_info(
                address="0x1000",
                value=Expression.constant(0, 4),
                conditions=[],
                branch_index=0,
            ),
            analyzer._make_return_info(
                address="0x1004",
                value=Expression.unknown("phi_circular"),
                conditions=[],
                branch_index=1,
            ),
        ],
    )

    summary_returns = [
        analyzer._make_return_info(
            address="0x2000",
            value=Expression.constant(0, 4),
            conditions=[],
            branch_index=10,
        ),
        analyzer._make_return_info(
            address="0x2004",
            value=Expression.intrinsic(
                "COUNTED_LOOP_SUM",
                [
                    Expression.constant(0, 4),
                    Expression.constant(0, 4),
                    Expression.parameter("param_1", 0, size=4),
                ],
                size=4,
            ),
            conditions=[],
            branch_index=11,
        ),
    ]

    with patch(
        "scripts.function_tracer_pcode.analysis.analyzer.StructuralRecurrenceSummarizer.try_summarize_function",
        return_value=(summary_returns, "counted_scalar_loop_summary"),
    ) as summary_mock:
        result = analyzer._apply_structural_recurrence_summary(
            function,
            high_function,
            analysis,
            tracer,
        )

    assert result == (summary_returns, "counted_scalar_loop_summary")
    summary_mock.assert_called_once()


def test_analyze_function_applies_counted_loop_summary_after_return_analysis():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    function = Mock()
    function.getName.return_value = "branch_for_accumulate"
    function.getEntryPoint.return_value = "0x401000"
    high_function = Mock()
    fake_results = Mock()
    fake_results.decompileCompleted.return_value = True
    fake_results.getHighFunction.return_value = high_function

    summary_returns = [
        analyzer._make_return_info(
            address="0x401000",
            value=Expression.constant(0, 4),
            conditions=[
                Condition(
                    Expression.binary_op(
                        "INT_SLESSEQUAL",
                        Expression.parameter("param_1", 0, size=4),
                        Expression.constant(0, 4),
                    ),
                    False,
                )
            ],
            branch_index=201000,
        ),
        analyzer._make_return_info(
            address="0x401000",
            value=Expression.intrinsic(
                "COUNTED_LOOP_SUM",
                [
                    Expression.constant(0, 4),
                    Expression.constant(0, 4),
                    Expression.parameter("param_1", 0, size=4),
                ],
                size=4,
            ),
            conditions=[
                Condition(
                    Expression.binary_op(
                        "INT_SLESS",
                        Expression.constant(0, 4),
                        Expression.parameter("param_1", 0, size=4),
                    ),
                    False,
                )
            ],
            branch_index=201010,
        ),
    ]

    generic_return = analyzer._make_return_info(
        address="0x401000",
        value=Expression.unknown("phi_circular"),
        conditions=[],
        branch_index=0,
    )

    with patch.object(
        analyzer,
        "_get_decompiler",
        return_value=Mock(decompileFunction=Mock(return_value=fake_results)),
    ), patch.object(
        analyzer,
        "_make_tracer",
        return_value=_FakeTracer(),
    ), patch(
        "scripts.function_tracer_pcode.analysis.analyzer.ConditionTracker",
        _FakeConditionTracker,
    ), patch.object(
        analyzer,
        "_collect_parameters",
        return_value=[{"name": "param_1", "index": 0, "size": 4}],
    ), patch.object(
        analyzer,
        "_augment_parameters_with_implicit_passthrough",
        side_effect=lambda params, *_args, **_kwargs: params,
    ), patch.object(
        analyzer,
        "_get_return_type_info",
        return_value=(None, "int"),
    ), patch.object(
        analyzer,
        "_detect_signedness",
        return_value=None,
    ), patch(
        "scripts.function_tracer_pcode.analysis.analyzer.StructuralRecurrenceSummarizer.try_summarize_function",
        return_value=(summary_returns, "counted_scalar_loop_summary"),
    ) as summary_mock, patch.object(
        analyzer,
        "_recover_control_region_returns_early",
        return_value=(None, []),
    ), patch.object(
        analyzer,
        "_invoke_build_effect_summary",
        return_value=analyzer._make_empty_effect_summary([{"name": "param_1", "index": 0, "size": 4}]),
    ), patch.object(
        analyzer,
        "_recover_call_wrapper_returns",
        return_value=None,
    ), patch.object(
        analyzer,
        "_recover_switch_like_returns_from_pcode",
        return_value=None,
    ), patch.object(
        analyzer,
        "_analyze_return_op",
        return_value=[generic_return],
    ) as analyze_return_mock:
        result = analyzer.analyze_function(function, timeout=1)

    assert result is not None
    assert len(result.returns) == 2
    assert "counted_scalar_loop_summary" in result.analysis_notes
    analyze_return_mock.assert_called_once()
    summary_mock.assert_called_once()


def test_mark_incomplete_control_flow_recomputes_reasons_after_summary_rewrite():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analysis = create_mock_analysis(
        "branch_for_accumulate",
        return_type="int",
        parameters=[{"name": "param_1", "index": 0, "data_type": "int", "size": 4}],
        returns=[
            analyzer._make_return_info(
                address="0x1000",
                value=Expression.unknown("phi_circular"),
                conditions=[],
                branch_index=0,
            )
        ],
    )

    analyzer._mark_incomplete_control_flow(analysis)
    assert analysis.incomplete_control_flow is True
    assert "unknown_return" in analysis.analysis_notes

    analysis.returns = [
        analyzer._make_return_info(
            address="0x1004",
            value=Expression.constant(0, 4),
            conditions=[],
            branch_index=1,
        )
    ]
    analyzer._mark_incomplete_control_flow(analysis)

    assert analysis.incomplete_control_flow is False
    assert "unknown_return" not in analysis.analysis_notes

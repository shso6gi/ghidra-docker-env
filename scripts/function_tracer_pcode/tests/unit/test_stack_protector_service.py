"""StackProtectorService collaborator（Phase 5 #6）の回帰テスト。"""

import inspect
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.stack_protector import StackProtectorService
from scripts.function_tracer_pcode.core.expression import Expression


def _analyzer(debug=False):
    return ReturnAnalyzer(program=Mock(), debug=debug)


def test_collaborator_holds_only_injected_callables():
    service = _analyzer()._stack_protector
    assert set(vars(service)) == {
        "extract_stack_protector_memory_probe",
        "return_site_metadata_from_info",
        "make_return_info",
        "debug_reporter",
        "debug_flag",
    }


def test_every_delegator_forwards_to_the_collaborator():
    analyzer = _analyzer()
    names = [n for n, _ in inspect.getmembers(StackProtectorService, predicate=inspect.isfunction) if n != "__init__"]
    assert len(names) == 8
    for name in names:
        sentinel = object()
        assert not isinstance(inspect.getattr_static(ReturnAnalyzer, "_" + name), staticmethod), name
        with patch.object(analyzer._stack_protector, name, return_value=sentinel) as mocked:
            params = list(inspect.signature(getattr(ReturnAnalyzer, "_" + name)).parameters.values())[1:]
            args, kwargs = [], {}
            for param in params:
                if param.kind is inspect.Parameter.KEYWORD_ONLY:
                    kwargs[param.name] = Mock()
                else:
                    args.append(Mock())
            assert getattr(analyzer, "_" + name)(*args, **kwargs) is sentinel
            mocked.assert_called_once_with(*args, **kwargs)


def test_constant_int_value_matches_facade_result():
    analyzer = _analyzer()
    assert analyzer._constant_int_value(Expression.constant(9, 4)) == 9
    assert analyzer._stack_protector.constant_int_value(Expression.constant(9, 4)) == 9
    assert analyzer._stack_protector.constant_int_value(Expression.variable("param_1", 4)) is None
    assert analyzer._stack_protector.constant_int_value(None) is None


def test_dependency_graph_uses_the_collaborator_directly():
    """#67 / #68 の facade callback を直接依存に置き換えたこと。"""
    analyzer = _analyzer()
    assert analyzer._condition_logic.stack_protector is analyzer._stack_protector
    assert analyzer._placeholder_algebra.stack_protector is analyzer._stack_protector
    assert not hasattr(analyzer._condition_logic, "constant_int_value")
    assert not hasattr(analyzer._placeholder_algebra, "constant_int_value")


def test_unextracted_helpers_dispatch_through_the_facade_at_call_time():
    analyzer = _analyzer()
    for facade_name, attr in (
        ("_extract_stack_protector_memory_probe", "extract_stack_protector_memory_probe"),
        ("_return_site_metadata_from_info", "return_site_metadata_from_info"),
        ("_make_return_info", "make_return_info"),
    ):
        sentinel = object()
        with patch.object(ReturnAnalyzer, facade_name, return_value=sentinel) as mocked:
            assert getattr(analyzer._stack_protector, attr)(Mock(), key=1) is sentinel
            mocked.assert_called_once()


def test_debug_reporter_and_decompose_are_direct_dependencies():
    from scripts.function_tracer_pcode.analysis.returns import lifecycle, stack_protector
    analyzer = _analyzer()
    assert analyzer._stack_protector.debug_reporter is analyzer._debug_reporter
    assert stack_protector.decompose_comparison_condition is lifecycle.decompose_comparison_condition


def test_debug_flag_supplier_reads_analyzer_state_at_call_time():
    analyzer = _analyzer(debug=False)
    assert analyzer._stack_protector.debug_flag() is False
    analyzer.debug = True
    assert analyzer._stack_protector.debug_flag() is True

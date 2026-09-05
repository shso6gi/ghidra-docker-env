"""ReturnPathSelectionService collaborator（control_recovery 分割 3/n）の回帰テスト。"""

import ast
import inspect
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns import control_recovery as cr_module
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.control_recovery import ReturnPathSelectionService

NAMES = {
    "propagate_multiequal_input_for_return_path", "select_multiequal_input_for_return_path",
    "score_multiequal_incoming_for_return_path", "path_condition_sets_union_condition",
    "matches_blocked_return_path_conditions", "split_branch_index", "min_branch_index",
    "select_path_specific_return_source", "return_path_is_covered_by_existing_return",
    "control_region_returns_are_safe", "check_condition_coverage", "is_control_outcome_forbidden_fp_mnemonic",
    "high_function_has_forbidden_control_outcome_ops", "mark_incomplete_control_flow",
}
DIRECT = ("condition_logic", "block_graph", "expression_cases", "debug_reporter")
FACADE_CALLBACKS = ("make_tracked_return_value", "return_info_effective_region_conditions")
SUPPLIERS = ("debug_flag", "current_blocked_return_path_conditions_value")


def _analyzer():
    return ReturnAnalyzer(program=Mock(), debug=False)


def test_collaborator_holds_only_its_dependencies():
    analyzer = _analyzer()
    service = analyzer._return_paths
    assert set(vars(service)) == set(DIRECT) | set(FACADE_CALLBACKS) | set(SUPPLIERS)
    for attr in DIRECT:
        assert getattr(service, attr) is getattr(analyzer, "_" + attr), attr


def test_every_delegator_forwards_to_the_collaborator():
    analyzer = _analyzer()
    names = {n for n, _ in inspect.getmembers(ReturnPathSelectionService, predicate=inspect.isfunction)} - {"__init__"}
    assert names == NAMES
    for name in sorted(names):
        sentinel = object()
        assert not isinstance(inspect.getattr_static(ReturnAnalyzer, "_" + name), (staticmethod, classmethod)), name
        with patch.object(analyzer._return_paths, name, return_value=sentinel) as mocked:
            params = list(inspect.signature(getattr(ReturnAnalyzer, "_" + name)).parameters.values())[1:]
            args, kwargs = [], {}
            for param in params:
                if param.kind is inspect.Parameter.KEYWORD_ONLY:
                    kwargs[param.name] = Mock()
                else:
                    args.append(Mock())
            assert getattr(analyzer, "_" + name)(*args, **kwargs) is sentinel
            mocked.assert_called_once_with(*args, **kwargs)


def test_self_references_are_closed_and_self_is_never_passed():
    tree = ast.parse(inspect.getsource(cr_module))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "ReturnPathSelectionService")
    for node in ast.walk(cls):
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id == "self":
            assert node.attr in NAMES | set(DIRECT) | set(FACADE_CALLBACKS) | set(SUPPLIERS), node.attr
    assert not [n for n in ast.walk(cls) if isinstance(n, ast.Call)
                and any(isinstance(a, ast.Name) and a.id == "self" for a in list(n.args) + [k.value for k in n.keywords])]


def test_suppliers_read_analyzer_state_at_call_time():
    analyzer = _analyzer()
    service = analyzer._return_paths
    analyzer._current_blocked_return_path_conditions = [("k",)]
    assert service.current_blocked_return_path_conditions_value() is analyzer._current_blocked_return_path_conditions
    analyzer.debug = True
    assert service.debug_flag() is True


def test_unextracted_helpers_dispatch_through_the_facade_at_call_time():
    analyzer = _analyzer()
    for attr in FACADE_CALLBACKS:
        sentinel = object()
        with patch.object(ReturnAnalyzer, "_" + attr, return_value=sentinel) as mocked:
            assert getattr(analyzer._return_paths, attr)(Mock(), key=1) is sentinel
            mocked.assert_called_once()


def test_dependants_use_the_service_directly():
    analyzer = _analyzer()
    assert analyzer._return_normalization.return_paths is analyzer._return_paths
    assert analyzer._branch_guarded_while.return_paths is analyzer._return_paths
    assert "propagate_multiequal_input_for_return_path" not in vars(analyzer._return_normalization)
    assert "high_function_has_forbidden_control_outcome_ops" not in vars(analyzer._branch_guarded_while)


def test_min_branch_index_and_signatures_match_facade():
    analyzer = _analyzer()
    assert analyzer._min_branch_index([]) == analyzer._return_paths.min_branch_index([])
    for name in sorted(NAMES):
        facade = inspect.signature(getattr(ReturnAnalyzer, "_" + name)).parameters
        collab = inspect.signature(getattr(ReturnPathSelectionService, name)).parameters
        assert list(facade)[1:] == list(collab)[1:], name

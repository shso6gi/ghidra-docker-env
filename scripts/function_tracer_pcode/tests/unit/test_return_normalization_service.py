"""ReturnNormalizationService collaborator（Phase 5 #9）の回帰テスト。"""

import ast
import inspect
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns import return_normalization as rn_module
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.return_normalization import ReturnNormalizationService
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType

DIRECT = {
    "expression_cases": {"clone_expression", "is_direct_location_carrier", "expression_has_nontrivial_location_wrapper"},
    "condition_logic": {
        "substitute_parameter_constants_under_conditions",
        "reduce_phi_expression_under_conditions_with_smt",
        "parameter_constant_assignments_from_conditions",
        "evaluate_expression_under_parameter_assignments",
    },
    "stack_protector": {"strip_stack_protector_only_conditions"},
    "pcode_sites": {"get_pcode_opcode"},
}
FACADE_CALLBACKS = (
    "debug_expr_summary",
    "debug_print",
    "count_memory_reads",
    "propagate_indirect_return_effect",
    "normalize_return_value_with_effect_summary",
    "tracked_return_value_is_affected_by_op",
    "merge_equivalent_return_infos",
    "exclusivize_return_regions",
    "deduplicate_tracked_return_values",
    "propagate_passthrough_input_from_op",
    "propagate_multiequal_input_for_return_path",
    "normalize_return_callother_userops",
)
SUPPLIERS = ("current_parameters_value", "current_effect_summary_value", "debug_flag")


def _analyzer(debug=False):
    return ReturnAnalyzer(program=Mock(), debug=debug)


def test_collaborator_holds_only_its_dependencies():
    analyzer = _analyzer()
    service = analyzer._return_normalization
    assert set(vars(service)) == set(DIRECT) | set(FACADE_CALLBACKS) | set(SUPPLIERS)
    for attr in DIRECT:
        assert getattr(service, attr) is getattr(analyzer, "_" + attr)


def test_every_delegator_forwards_to_the_collaborator():
    analyzer = _analyzer()
    names = [n for n, _ in inspect.getmembers(ReturnNormalizationService, predicate=inspect.isfunction) if n != "__init__"]
    assert len(names) == 9
    for name in names:
        sentinel = object()
        assert not isinstance(inspect.getattr_static(ReturnAnalyzer, "_" + name), (staticmethod, classmethod)), name
        with patch.object(analyzer._return_normalization, name, return_value=sentinel) as mocked:
            params = list(inspect.signature(getattr(ReturnAnalyzer, "_" + name)).parameters.values())[1:]
            args, kwargs = [], {}
            for param in params:
                if param.kind is inspect.Parameter.KEYWORD_ONLY:
                    kwargs[param.name] = Mock()
                else:
                    args.append(Mock())
            assert getattr(analyzer, "_" + name)(*args, **kwargs) is sentinel
            mocked.assert_called_once_with(*args, **kwargs)


def test_collaborator_owned_names_are_called_only_through_direct_dependencies():
    """直接依存 9 名称と expression_contains_phi は facade / 自身の属性経由で呼ばれない（AST 検査）。"""
    tree = ast.parse(inspect.getsource(rn_module))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "ReturnNormalizationService")
    owned = {name: dep for dep, names in DIRECT.items() for name in names}
    seen = {}
    for node in ast.walk(cls):
        if isinstance(node, ast.Attribute) and node.attr in owned:
            base = node.value
            assert isinstance(base, ast.Attribute) and isinstance(base.value, ast.Name) and base.value.id == "self", node.attr
            seen.setdefault(node.attr, set()).add(base.attr)
    assert {k: v for k, v in seen.items()} == {name: {dep} for name, dep in owned.items() if name in seen}
    assert set(seen) == set(owned)
    # expression_contains_phi は module 関数として直接呼ぶ（属性経由ではない）
    calls = [n for n in ast.walk(cls) if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "expression_contains_phi"]
    attrs = [n for n in ast.walk(cls) if isinstance(n, ast.Attribute) and n.attr == "expression_contains_phi"]
    assert calls and not attrs


def test_suppliers_read_analyzer_state_at_call_time():
    analyzer = _analyzer(debug=False)
    service = analyzer._return_normalization
    analyzer._current_parameters = [{"name": "param_1"}]
    analyzer._current_effect_summary = object()
    assert service.current_parameters_value() is analyzer._current_parameters
    assert service.current_effect_summary_value() is analyzer._current_effect_summary
    assert service.debug_flag() is False
    analyzer.debug = True
    assert service.debug_flag() is True


def test_unextracted_helpers_dispatch_through_the_facade_at_call_time():
    analyzer = _analyzer()
    for attr in FACADE_CALLBACKS:
        sentinel = object()
        with patch.object(ReturnAnalyzer, "_" + attr, return_value=sentinel) as mocked:
            assert getattr(analyzer._return_normalization, attr)(Mock(), key=1) is sentinel
            mocked.assert_called_once()


def test_normalize_bound_parameter_values_matches_facade_result():
    analyzer = _analyzer()
    values = {0: Expression.constant(5, 4)}
    assert analyzer._normalize_bound_parameter_values(None) == analyzer._return_normalization.normalize_bound_parameter_values(None)
    a = analyzer._normalize_bound_parameter_values(values)
    b = analyzer._return_normalization.normalize_bound_parameter_values(values)
    assert type(a) is type(b) and (a == b or {k: v.to_string() for k, v in a.items()} == {k: v.to_string() for k, v in b.items()})

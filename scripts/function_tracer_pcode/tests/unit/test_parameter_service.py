"""ParameterService collaborator（Phase 5 #11）の回帰テスト。"""

import ast
import inspect
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns import parameters as pm_module
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.parameters import ParameterService

DIRECT = {
    "pcode_sites": {"coerce_optional_int"},
    "return_normalization": {"rewrite_expression_signedness"},
}
FACADE_CALLBACKS = (
    "debug_print", "target_active_key", "should_synthesize_implicit_passthrough_for_call",
    "return_site_metadata_from_info", "make_tracked_return_value", "make_return_info",
    "get_freshest_callee_parameters",
)
SUPPLIERS = ("program_value", "debug_flag")


def _analyzer(debug=False):
    return ReturnAnalyzer(program=Mock(), debug=debug)


def test_collaborator_holds_only_its_dependencies():
    analyzer = _analyzer()
    service = analyzer._parameters
    assert set(vars(service)) == set(DIRECT) | set(FACADE_CALLBACKS) | set(SUPPLIERS) | {"set_current_parameters"}
    for attr in DIRECT:
        assert getattr(service, attr) is getattr(analyzer, "_" + attr)


def test_every_delegator_forwards_to_the_collaborator():
    analyzer = _analyzer()
    names = [n for n, _ in inspect.getmembers(ParameterService, predicate=inspect.isfunction) if n != "__init__"]
    assert len(names) == 26
    for name in names:
        sentinel = object()
        assert not isinstance(inspect.getattr_static(ReturnAnalyzer, "_" + name), (staticmethod, classmethod)), name
        with patch.object(analyzer._parameters, name, return_value=sentinel) as mocked:
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
    tree = ast.parse(inspect.getsource(pm_module))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "ParameterService")
    owned = {name: dep for dep, names in DIRECT.items() for name in names}
    seen = {}
    for node in ast.walk(cls):
        if isinstance(node, ast.Attribute) and node.attr in owned:
            base = node.value
            assert isinstance(base, ast.Attribute) and isinstance(base.value, ast.Name) and base.value.id == "self", node.attr
            seen.setdefault(node.attr, set()).add(base.attr)
    assert set(seen) == set(owned)
    assert all(v == {owned[k]} for k, v in seen.items())


def test_current_parameters_is_written_only_through_the_injected_setter():
    """facade 状態への唯一の書き込みが setter 経由であり、facade 属性を直接触らないこと。"""
    tree = ast.parse(inspect.getsource(pm_module))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "ParameterService")
    for node in ast.walk(cls):
        if isinstance(node, ast.Attribute) and node.attr in {"_current_parameters", "program", "debug"}:
            raise AssertionError(f"facade attribute accessed directly: {node.attr}")
    analyzer = _analyzer()
    new_params = [{"name": "param_1", "index": 0, "size": 4}]
    analyzer._parameters.set_current_parameters(new_params)
    assert analyzer._current_parameters is new_params


def test_suppliers_read_analyzer_state_at_call_time():
    analyzer = _analyzer(debug=False)
    service = analyzer._parameters
    assert service.program_value() is analyzer.program
    assert service.debug_flag() is False
    analyzer.debug = True
    assert service.debug_flag() is True
    analyzer.program = None
    assert service.program_value() is None


def test_unextracted_helpers_dispatch_through_the_facade_at_call_time():
    analyzer = _analyzer()
    for attr in FACADE_CALLBACKS:
        sentinel = object()
        with patch.object(ReturnAnalyzer, "_" + attr, return_value=sentinel) as mocked:
            assert getattr(analyzer._parameters, attr)(Mock(), key=1) is sentinel
            mocked.assert_called_once()


def test_sealed_return_abi_facts_remains_a_module_function():
    assert callable(pm_module._sealed_return_abi_facts)
    assert not hasattr(ParameterService, "_sealed_return_abi_facts")


def test_is_void_type_matches_facade_result():
    analyzer = _analyzer()
    assert analyzer._is_void_type(None) == analyzer._parameters.is_void_type(None)
    assert analyzer._is_signed_type(None) == analyzer._parameters.is_signed_type(None)

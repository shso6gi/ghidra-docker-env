"""EffectIntegrationService collaborator（Phase 5 #12）の回帰テスト。"""

import ast
import inspect
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns import effect_integration as ei_module
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.effect_integration import (
    OBSERVABLE_EFFECT_SURFACE_SOURCE,
    EffectIntegrationService,
    local_memory_key,
    observable_store_effects,
)

DIRECT = {
    "expression_cases": {
        "expression_has_nontrivial_location_wrapper", "wrapper_preserves_collapsed_operand",
        "resolve_precise_object_state_value", "fold_constant_expression", "expression_runtime_guard_conditions",
        "expand_object_centric_expression_cases", "deduplicate_expression_cases", "count_unresolved_value_nodes",
        "count_phi_nodes", "count_opaque_unknowns", "count_object_centric_unknowns", "condition_lists_equivalent",
    },
    "return_normalization": {"rewrite_drops_composite_location_wrapper", "should_replay_canonicalized_return"},
    "pcode_sites": {"varnode_location_key", "is_zero_constant_varnode"},
    "phi_origins": {"expression_contains_phi"},
    "divergence_proofs": {"recursive_scc_certificate"},
    "parameters": {"is_void_type", "collect_parameters", "choose_richer_parameter_descriptors"},
    "region_facts": {"live_in_key"},
    "local_values": {"evaluate_varnode"},
}
FACADE_CALLBACKS = ( "extend_active_functions",
    "current_function_entry_address",
    "analysis_scope_key",
    "get_freshest_callee_parameters", "make_call_resolver", "bound_parameter_values_from_call_args",
    "bound_parameter_storage_values_from_call_args", "target_active_key", "resolve_target_function",
    "make_deferred_call_recorder", "is_semantically_lossless_effect_sensitive_rewrite",
    "direct_call_target_function_key", "coerce_runtime_target_ref",
    "make_tracked_return_value", "function_body_has_phase1_pure_return_forbidden_ops",
    "high_function_has_phase1_pure_return_forbidden_ops", "phase1_return_type_is_float", "decompile_with_broker",
)
# ``external_call_effect_policy`` (Issue #104 Gap 4): observation policy for
# external / thunk callees in the effect lane, configuration supplied by the analyzer.
SUPPLIERS = ("session", "program_value", "binary_id_value", "debug_flag", "external_call_effect_policy")


def _analyzer(debug=False):
    return ReturnAnalyzer(program=Mock(), debug=debug)


def test_collaborator_holds_only_its_dependencies():
    analyzer = _analyzer()
    service = analyzer._effect_integration
    assert set(vars(service)) == set(DIRECT) | set(FACADE_CALLBACKS) | set(SUPPLIERS) | {"debug_reporter", "program_access", "runtime_state"}
    for attr in DIRECT:
        assert getattr(service, attr) is getattr(analyzer, "_" + attr)
    assert service.debug_reporter is analyzer._debug_reporter
    assert service.program_access is analyzer._program_access, attr


def test_every_delegator_forwards_to_the_collaborator():
    analyzer = _analyzer()
    names = [n for n, _ in inspect.getmembers(EffectIntegrationService, predicate=inspect.isfunction) if n != "__init__"]
    assert len(names) == 28
    for name in names:
        sentinel = object()
        assert not isinstance(inspect.getattr_static(ReturnAnalyzer, "_" + name), (staticmethod, classmethod)), name
        with patch.object(analyzer._effect_integration, name, return_value=sentinel) as mocked:
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
    tree = ast.parse(inspect.getsource(ei_module))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "EffectIntegrationService")
    owned = {name: dep for dep, names in DIRECT.items() for name in names}
    seen = {}
    for node in ast.walk(cls):
        if isinstance(node, ast.Attribute) and node.attr in owned:
            base = node.value
            assert isinstance(base, ast.Attribute) and isinstance(base.value, ast.Name) and base.value.id == "self", node.attr
            seen.setdefault(node.attr, set()).add(base.attr)
    assert set(seen) == set(owned)
    assert all(v == {owned[k]} for k, v in seen.items())
    # facade 流の self._x 参照（呼び出し・bound method 渡しとも）が残っていない
    leftovers = {node.attr for node in ast.walk(cls)
                 if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id == "self" and node.attr.startswith("_")}
    assert leftovers == set()


def test_collaborator_never_passes_itself_where_the_facade_is_expected():
    """decompilation_broker.decompile_function(analyzer, ...) のように facade を第 1 引数に取る関数へ
    collaborator 自身を渡していないこと（subset で AttributeError として検出された欠陥の回帰ガード）。"""
    tree = ast.parse(inspect.getsource(ei_module))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "EffectIntegrationService")
    offenders = [ast.unparse(n)[:60] for n in ast.walk(cls) if isinstance(n, ast.Call)
                 and any(isinstance(a, ast.Name) and a.id == "self" for a in list(n.args) + [k.value for k in n.keywords])]
    assert offenders == []
    analyzer = _analyzer()
    with patch("scripts.function_tracer_pcode.ghidra.decompilation_broker.decompile_function") as broker:
        broker.return_value = "results"
        assert analyzer._effect_integration.decompile_with_broker("callee", 60, None, source_contract_id="c", semantic_owner="subordinate") == "results"
        broker.assert_called_once_with(analyzer, "callee", 60, None, source_contract_id="c", semantic_owner="subordinate")


def test_session_supplier_and_runtime_state_dependency_replace_the_per_field_suppliers():
    """6a-5: session は現在の child を動的に見る supplier、runtime state は analyzer 寿命の同一 owner を直接持つ。"""
    analyzer = _analyzer()
    service = analyzer._effect_integration
    state = analyzer._runtime_state
    analyzer._current_parameters = [{"name": "param_1"}]
    analyzer._current_effect_summary = object()
    analyzer._binary_id = "B-late"
    assert service.session() is analyzer._ensure_analysis_session()
    assert service.session().parameters is analyzer._current_parameters
    assert service.session().effect_summary is analyzer._current_effect_summary
    assert service.binary_id_value() == "B-late"
    assert service.program_value() is analyzer.program
    assert service.runtime_state is state
    service.runtime_state.effect_summary_cache[("k",)] = "summary"
    assert analyzer._effect_summary_cache == {("k",): "summary"}
    service.runtime_state.effect_summary_parameter_cache[("k",)] = []
    assert ("k",) in analyzer._effect_summary_parameter_cache
    service.runtime_state.direct_call_graph[("f",)] = set()
    service.runtime_state.direct_call_graph_complete_nodes.add(("f",))
    assert ("f",) in analyzer._direct_call_graph and ("f",) in analyzer._direct_call_graph_complete_nodes
    # nested context では session() が child を返し、runtime_state は同一
    with analyzer._analysis_context([{"name": "child"}], None):
        assert service.session() is analyzer._ensure_analysis_session()
        assert service.session().parameters == [{"name": "child"}]
        assert service.runtime_state is state
    assert service.session().parameters == [{"name": "param_1"}]
    assert service.debug_flag() is False
    analyzer.debug = True
    assert service.debug_flag() is True

def test_unextracted_helpers_dispatch_through_the_facade_at_call_time():
    analyzer = _analyzer()
    for attr in FACADE_CALLBACKS:
        sentinel = object()
        with patch.object(ReturnAnalyzer, "_" + attr, return_value=sentinel) as mocked:
            assert getattr(analyzer._effect_integration, attr)(Mock(), key=1) is sentinel
            mocked.assert_called_once()


def test_module_level_helpers_stay_module_level():
    assert callable(local_memory_key) and callable(observable_store_effects)
    assert OBSERVABLE_EFFECT_SURFACE_SOURCE == "observable_effects_and_return_value"
    for name in ("observable_store_effects", "OBSERVABLE_EFFECT_SURFACE_SOURCE"):
        assert not hasattr(EffectIntegrationService, name)
    # local_memory_key は module 関数が実装で、collaborator メソッドは委譲
    assert EffectIntegrationService.local_memory_key is not local_memory_key


def test_read_memory_value_is_passed_as_the_collaborator_bound_method():
    """family 内で bound method として下位コンポーネントへ渡す read_memory_value は collaborator 自身のもの。"""
    tree = ast.parse(inspect.getsource(ei_module))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "EffectIntegrationService")
    refs = [node for node in ast.walk(cls) if isinstance(node, ast.Attribute) and node.attr == "read_memory_value"]
    assert refs and all(isinstance(r.value, ast.Name) and r.value.id == "self" for r in refs)
    analyzer = _analyzer()
    with patch.object(analyzer._effect_integration, "read_memory_value", return_value=0x42):
        assert analyzer._read_memory_value(0, 4) == 0x42


def test_make_empty_effect_summary_matches_facade_result():
    analyzer = _analyzer()
    a = analyzer._make_empty_effect_summary([])
    b = analyzer._effect_integration.make_empty_effect_summary([])
    assert type(a) is type(b)

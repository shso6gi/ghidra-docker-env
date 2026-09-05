"""Phase 6a-5: collaborator 依存契約の回帰テスト。

- session: 現在の child AnalysisSession を **動的に** 見る supplier（_analysis_context の push/pop に追随）
- runtime_state: analyzer 寿命の同一 AnalysisRuntimeState owner を **直接** 持つ
- 残る lambda supplier は analyzer の設定値（debug / program / binary_id / enable_completed_recovery_proofs）と
  #77 の decompiler のみ
"""

from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer

CONFIG_SUPPLIERS = {"debug_flag", "program_value", "binary_id_value", "enable_completed_recovery_proofs_value", "decompiler_value"}


def _analyzer():
    return ReturnAnalyzer(program=Mock(), debug=False)


def _collaborators(analyzer):
    return {k: v for k, v in vars(analyzer).items()
            if type(v).__module__.startswith("scripts.function_tracer_pcode.analysis.returns.")}


def test_session_suppliers_follow_the_pushed_child_session():
    analyzer = _analyzer()
    holders = {k: v for k, v in _collaborators(analyzer).items() if "session" in vars(v)}
    assert {k for k in holders} == {"_expression_cases", "_placeholder_algebra", "_return_normalization", "_effect_integration", "_branch_guarded_while", "_return_paths"}
    parent = analyzer._ensure_analysis_session()
    for h in holders.values():
        assert h.session() is parent
    with analyzer._analysis_context([{"name": "child"}], None):
        child = analyzer._ensure_analysis_session()
        assert child is not parent
        for h in holders.values():
            assert h.session() is child
    for h in holders.values():
        assert h.session() is parent


def test_runtime_state_holders_share_the_single_owner_and_have_no_field_suppliers():
    analyzer = _analyzer()
    holders = {k: v for k, v in _collaborators(analyzer).items() if "runtime_state" in vars(v)}
    assert set(holders) == {"_divergence_proofs", "_effect_integration"}
    for h in holders.values():
        assert h.runtime_state is analyzer._runtime_state
    for v in _collaborators(analyzer).values():
        assert not any(k.endswith("_cache_value") or k.startswith("direct_call_graph") for k in vars(v)), vars(v).keys()


def test_only_configuration_and_decompiler_suppliers_remain_as_zero_arg_lambdas():
    """引数なしの lambda（= facade 状態の supplier）は設定値と decompiler のみ。
    可変長引数の lambda は未抽出 family への facade callback で、本テストの対象外（Phase 5 で個別に固定済み）。"""
    import inspect
    analyzer = _analyzer()
    zero_arg = set()
    for v in _collaborators(analyzer).values():
        for k, val in vars(v).items():
            if getattr(val, "__name__", "") == "<lambda>" and not inspect.signature(val).parameters:
                zero_arg.add(k)
    assert zero_arg <= CONFIG_SUPPLIERS, zero_arg - CONFIG_SUPPLIERS
    assert not any("current_" in k or k.endswith("_cache_value") for k in zero_arg)


REMOVED_SUPPLIERS = {
    "current_parameters", "_current_parameters", "current_parameters_value", "current_effect_summary_value",
    "current_blocked_return_path_conditions_value", "effect_summary_cache_value",
    "effect_summary_parameter_cache_value", "direct_call_graph_value", "direct_call_graph_complete_nodes_value",
}


def _collaborator_class_nodes():
    """returns package 内の collaborator class の AST node（module-level `_impl_` 関数は含めない）。"""
    import ast
    import glob
    import os
    from scripts.function_tracer_pcode.analysis.returns import analyzer as analyzer_module
    pkg = os.path.dirname(analyzer_module.__file__)
    for path in sorted(glob.glob(os.path.join(pkg, "*.py"))):
        if path.endswith("analyzer.py"):
            continue
        tree = ast.parse(open(path).read())
        for node in tree.body:
            if isinstance(node, ast.ClassDef) and (node.name.endswith("Service") or node.name in {"RegionFacts", "LocalValueResolver", "DebugReporter"}):
                yield os.path.basename(path), node


def test_removed_per_field_suppliers_are_gone_from_constructors_and_class_bodies():
    import ast
    offenders = []
    for fname, cls in _collaborator_class_nodes():
        init = next((n for n in cls.body if isinstance(n, ast.FunctionDef) and n.name == "__init__"), None)
        if init is not None:
            for arg in init.args.kwonlyargs + init.args.args:
                if arg.arg in REMOVED_SUPPLIERS:
                    offenders.append((fname, cls.name, "ctor", arg.arg))
        for node in ast.walk(cls):
            if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id == "self" and node.attr in REMOVED_SUPPLIERS:
                offenders.append((fname, cls.name, "body", node.attr))
    assert offenders == []


def test_no_collaborator_passes_itself_where_the_facade_is_expected():
    """#75 の broker 欠陥と同型の退行を全 collaborator で禁止する（class node だけを見るので module-level `_impl_` の
    正当な facade access は対象外）。"""
    import ast
    offenders = []
    for fname, cls in _collaborator_class_nodes():
        for node in ast.walk(cls):
            if isinstance(node, ast.Call) and any(isinstance(a, ast.Name) and a.id == "self" for a in list(node.args) + [k.value for k in node.keywords]):
                offenders.append((fname, cls.name, ast.unparse(node)[:60]))
    assert offenders == []


def test_static_checks_scan_at_least_the_expected_collaborators():
    names = {cls.name for _, cls in _collaborator_class_nodes()}
    assert {"EffectIntegrationService", "DivergenceProofService", "ReturnPathSelectionService", "BranchGuardedWhileProofService",
            "ExpressionCaseService", "PlaceholderAlgebraService", "ReturnNormalizationService", "BlockGraphService",
            "ProgramAccessService", "ConditionLogicService", "StackProtectorService", "PcodeSiteService", "PhiOriginService",
            "ParameterService", "RegionFacts", "LocalValueResolver", "DebugReporter"} <= names

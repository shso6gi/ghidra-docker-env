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

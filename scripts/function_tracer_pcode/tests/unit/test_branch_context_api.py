"""Phase 6c-1 (#93): stage runner → checker の branch 文脈を明示引数 ``branch_context`` でも渡す（dual-write）。
explicit ctx と legacy（``_active_*``）由来の effective ctx の parity を context matrix で固定する。"""

import ast
import inspect
from types import SimpleNamespace
from unittest.mock import Mock, patch

import pytest

from scripts.function_tracer_pcode.checker import checker as checker_module
from scripts.function_tracer_pcode.checker.branch_context import BranchCheckContext, build_branch_check_context
from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker, StageID, StageSpec
from scripts.function_tracer_pcode.core.render_smt import UnknownSmtExtensionWidthError
from scripts.function_tracer_pcode.proof.call_effect.preflight import CallProofDecisionMode
from scripts.function_tracer_pcode.proof.obligations import stage_runner as runner_module
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis
from scripts.function_tracer_pcode.tests.unit import test_obligation_stage_runner as runner_tests


def assert_same_context(explicit, implicit):
    """dataclass == だけに頼らない parity 比較。"""
    assert explicit.strategy is implicit.strategy
    assert explicit.production_branch_authority_lease is implicit.production_branch_authority_lease
    assert explicit.replan_plan is implicit.replan_plan
    assert explicit.comparison_session_id == implicit.comparison_session_id
    assert explicit.generation == implicit.generation
    assert explicit.branch_id == implicit.branch_id
    assert explicit.decision_mode == implicit.decision_mode


def _implicit_context_from_facade(checker, strategy):
    """check() が legacy 経路で組む effective ctx（呼び出し時点の _active_* から）。"""
    return build_branch_check_context(
        strategy=strategy,
        replan_plan=getattr(checker, "_active_pair_replan_plan", None),
        call_proof_generation=getattr(checker, "_call_proof_generation", 0),
        active_comparison_generation=getattr(checker, "_active_comparison_generation", None),
        active_comparison_session_id=getattr(checker, "_active_comparison_session_id", None),
        active_call_proof_branch_id=getattr(checker, "_active_call_proof_branch_id", None),
        decision_mode=getattr(checker, "call_proof_decision_mode", None),
        production_branch_authority_lease=getattr(checker, "_active_production_branch_authority_lease", None),
    )


# ---- API 形 --------------------------------------------------------------------------------------

def test_branch_context_is_a_keyword_only_argument_defaulting_to_none():
    p = inspect.signature(EquivalenceChecker.check).parameters["branch_context"]
    assert p.kind is inspect.Parameter.KEYWORD_ONLY and p.default is None
    assert "branch_context" in (EquivalenceChecker.check.__doc__ or "")


def _run_check_until_first_collaborator(checker, analysis, **kwargs):
    checker._call_effect_shadow_manifest = lambda *a, **k: (_ for _ in ()).throw(
        UnknownSmtExtensionWidthError(operator="INT_ZEXT", operand_bits=32))
    return checker.check(analysis, analysis, **kwargs)


def test_explicit_context_is_used_as_is_and_the_builder_is_not_called():
    analysis = create_mock_analysis("f", [])
    checker = EquivalenceChecker(strategy="pairwise", timeout=5, monolithic_timeout=5)
    ctx = BranchCheckContext(strategy=checker.pairwise_strategy, replan_plan=None, generation=41, comparison_session_id="S-explicit",
                             branch_id="S_PAIRWISE", decision_mode=checker.call_proof_decision_mode, production_branch_authority_lease=None)
    seen = {}
    real_prepare = checker_module.prepare_preflight_projection

    def spy_prepare(c, *a, **k):
        seen["ctx"] = c
        return real_prepare(c, *a, **k)

    with patch.object(checker_module, "build_branch_check_context") as builder, \
         patch.object(checker_module, "prepare_preflight_projection", side_effect=spy_prepare):
        _run_check_until_first_collaborator(checker, analysis, branch_context=ctx)
    builder.assert_not_called()
    assert seen["ctx"] is ctx


@pytest.mark.parametrize("replan", [None, object()])
def test_generation_increment_follows_the_explicit_context_replan_plan(replan):
    analysis = create_mock_analysis("f", [])
    checker = EquivalenceChecker(strategy="pairwise", timeout=5, monolithic_timeout=5)
    before = checker._call_proof_generation
    ctx = BranchCheckContext(strategy=checker.pairwise_strategy, replan_plan=replan, generation=7, comparison_session_id="S",
                             branch_id="S_PAIRWISE", decision_mode=checker.call_proof_decision_mode, production_branch_authority_lease=None)
    _run_check_until_first_collaborator(checker, analysis, branch_context=ctx)
    assert checker._call_proof_generation == before + (1 if replan is None else 0)
    assert ctx.generation == 7  # supplied value のまま（frozen）


def test_direct_call_without_context_still_builds_from_the_facade():
    analysis = create_mock_analysis("f", [])
    checker = EquivalenceChecker(strategy="pairwise", timeout=5, monolithic_timeout=5)
    seen = []
    real = checker_module.build_branch_check_context

    def spy(**kw):
        ctx = real(**kw); seen.append((kw, ctx)); return ctx

    with patch.object(checker_module, "build_branch_check_context", side_effect=spy):
        _run_check_until_first_collaborator(checker, analysis)
    kw, ctx = seen[0]
    assert kw["active_comparison_session_id"] is None and kw["active_call_proof_branch_id"] is None
    assert kw["production_branch_authority_lease"] is None and kw["replan_plan"] is None
    assert ctx.branch_id == "PairwiseStrategy" and ctx.production_branch_authority_lease is None
    assert ctx.generation == checker._call_proof_generation and len(ctx.comparison_session_id) == 32


# ---- runner path parity（matrix 1, 2） ---------------------------------------------------------

def _runner_checker(results_or_side_effect):
    checker = runner_tests._checker([])
    checker._call_proof_generation = 0
    checker.call_proof_decision_mode = CallProofDecisionMode.PREFLIGHT_PROJECTION
    checker.check = Mock(side_effect=results_or_side_effect)
    return checker


@pytest.mark.parametrize("stage_id, key, attr", [
    (StageID.S_PAIRWISE, "pairwise", "pairwise_strategy"),
    (StageID.S_MONOLITHIC_FALLBACK, "monolithic", "monolithic_strategy"),
    # S_LOOP_TEMPLATE_ABSTRACTION は runner の activation 条件（pairwise の query timeout）を満たさないと
    # 実行されないため、ここでは branch_id を差し替えた同じ builder 経路として loop_template_strategy を検査する
    (StageID.S_PAIRWISE, "loop_template_pairwise", "loop_template_strategy"),
])
def test_runner_passes_an_explicit_context_equal_to_the_legacy_effective_context(stage_id, key, attr):
    captured = []

    def execute(*args, **kwargs):
        checker_ref = captured_checker[0]
        captured.append((kwargs["branch_context"], _implicit_context_from_facade(checker_ref, kwargs["force_strategy"]),
                         kwargs["force_strategy"], getattr(checker_ref, "_active_production_branch_authority_lease", None)))
        return runner_tests._result(True)

    checker = _runner_checker(execute)
    captured_checker = [checker]
    checker.stage_plan = [StageSpec(stage_id, key, key)]
    runner_tests._run(checker, "_run_stage_plan")
    assert len(captured) == 1
    explicit, implicit, strategy, lease = captured[0]
    assert isinstance(explicit, BranchCheckContext)
    assert_same_context(explicit, implicit)
    assert explicit.strategy is getattr(checker, attr) is strategy
    assert explicit.branch_id == stage_id.value and explicit.production_branch_authority_lease is lease is not None
    assert explicit.replan_plan is None and explicit.generation == 1
    assert explicit.decision_mode == CallProofDecisionMode.PREFLIGHT_PROJECTION
    # dual-write: 呼び出し後に legacy 属性は restore/delete されている（runner の finally は不変）
    assert not hasattr(checker, "_active_call_proof_branch_id") and not hasattr(checker, "_active_production_branch_authority_lease")


def test_runner_replan_context_takes_the_successor_plan_precedence_and_keeps_the_branch_local_lease():
    src = inspect.getsource(runner_tests.test_completed_proof_replans_pairwise_on_successor_view_and_ledger)
    assert "checker._active_pair_replan_plan is successor_plan" in src  # 既存 seam（6c-3 で ctx 検査へ置換）
    from scripts.function_tracer_pcode.proof.obligations import PairLedgerBinding
    from scripts.function_tracer_pcode.checker.cause_identity import ProofRequirementContract, ProofRequirementId
    requirement = ProofRequirementId.create("return_coverage_completion", ("coverage", "f"), ProofRequirementContract("return coverage complete"))
    reason = SimpleNamespace(reason_id="return_coverage_gap", recovery_proof_kind="return_coverage_completion",
                             proof_requirement_ids=(requirement.to_dict(),), object_target_key=("coverage", "f"),
                             pair_or_case="(0,0)", stage="S_PAIRWISE")
    first = runner_tests._result(None, (reason,))
    first.completed_recovery_proof_evidence = [{"evidence": {"proof_requirement_id": requirement.to_dict(), "status": "complete",
                                                              "proof_source": "coverage_test_producer"}}]
    second = runner_tests._result(True)
    second.completed_recovery_proof_evidence = []
    strategy = SimpleNamespace(_return_coverage_proof_is_complete=lambda *_a: True,
                               _call_effect_summary_proof_is_complete=lambda *_a: False,
                               _recovery_proof_is_complete=lambda *_a: False)
    captured = []

    def execute(*_args, **kwargs):
        runtime = checker._obligation_runtime_session
        ctx = kwargs["branch_context"]
        captured.append((ctx, _implicit_context_from_facade(checker, kwargs["force_strategy"]),
                         getattr(checker, "_active_production_branch_authority_lease", None), checker._call_proof_generation))
        if len(captured) == 1:
            binding = PairLedgerBinding("session", "S_PAIRWISE", "surface", "projection", 1,
                                        runtime.current_view.view_id, runtime.premise_digest, 1)
            ledger = runtime.open_pair_ledger(binding, 1)
            first._prepared_dispatch_frame = SimpleNamespace(pair_disposition_ledger=ledger)
            return first
        successor_plan = runtime.pair_ledger_manager.pending_successor
        assert successor_plan is not None and ctx.replan_plan is successor_plan
        replacement_binding = PairLedgerBinding(successor_plan.comparison_session_id, successor_plan.branch_id, "new-surface",
                                                "new-projection", 2, successor_plan.derived_view_id, runtime.premise_digest, 2)
        runtime.open_pair_ledger(replacement_binding, 2)
        second._prepared_dispatch_frame = SimpleNamespace(pair_disposition_ledger=runtime.pair_ledger_manager.current)
        return second

    checker = _runner_checker(execute)
    checker.stage_plan = [StageSpec(StageID.S_PAIRWISE, "pairwise", "pairwise")]
    checker.pairwise_strategy = strategy
    final = runner_tests._run(checker, "_run_stage_plan")
    assert final.is_equivalent is True and len(captured) == 2
    (ctx1, imp1, lease1, _), (ctx2, imp2, lease2, _) = captured
    assert_same_context(ctx1, imp1)
    assert_same_context(ctx2, imp2)
    plan = ctx2.replan_plan
    # successor plan の precedence: session / generation / branch は plan の値（runner が今発行した session とは別）
    assert ctx2.comparison_session_id == plan.comparison_session_id and ctx2.generation == plan.frame_generation
    assert ctx2.branch_id == plan.branch_id
    # lease は replan branch で新しく発行された branch-local lease object そのもの（plan の identity と
    # lease 発行時の session は一致しないが、既存挙動の移送に限定し「整合するよう修正」しない）
    assert ctx2.production_branch_authority_lease is lease2 and lease2 is not lease1
    assert lease2.comparison_session_id != ctx2.comparison_session_id
    assert lease2.generation == 1 and ctx2.generation == plan.frame_generation
    # fake checker の generation counter は real check() が無いので変化しない（increment は check() の責務）
    assert captured[0][3] == 0 and captured[1][3] == 0


# ---- abstract recursive branch characterization（matrix 3） ---------------------------------

def test_abstract_recursive_branch_keeps_the_inner_strategy_class_branch_id_fallback():
    captured = []

    def abstraction(*_args, **kwargs):
        captured.append((dict(kwargs), _implicit_context_from_facade(checker, checker.pairwise_strategy),
                         hasattr(checker, "_active_call_proof_branch_id"),
                         getattr(checker, "_active_production_branch_authority_lease", None),
                         getattr(checker, "_active_comparison_session_id", None),
                         getattr(checker, "_active_comparison_generation", None)))
        return runner_tests._result(True)

    checker = _runner_checker([])
    checker.pairwise_strategy = checker_module.PairwiseStrategy.__new__(checker_module.PairwiseStrategy)
    checker._run_recursive_abstraction_stage = Mock(side_effect=abstraction)
    checker.stage_plan = [StageSpec(StageID.S_ABSTRACT_RECURSIVE_SUMMARY, "abstract", strategy="abstract_pairwise")]
    runner_tests._run(checker, "_run_stage_plan")
    assert len(captured) == 1
    kwargs, inner_effective, has_branch_id, lease, session, generation = captured[0]
    assert "branch_context" not in kwargs  # 6c-1: abstraction stage の signature は未変更
    assert has_branch_id is False  # runner は abstract branch で _active_call_proof_branch_id を set しない
    assert inner_effective.branch_id == "PairwiseStrategy"  # strategy class fallback（S_ABSTRACT_RECURSIVE_SUMMARY ではない）
    assert not inner_effective.branch_id.startswith("S_")
    assert inner_effective.production_branch_authority_lease is lease is not None
    assert inner_effective.comparison_session_id == session and inner_effective.generation == generation == 1
    checker.check.assert_not_called()


# ---- recurrence nested check（matrix 5、現行挙動の characterization） ---------------------------

def _run_with_forced_recurrence(checker, analysis, **check_kwargs):
    from scripts.function_tracer_pcode.checker import recurrence_promotion as rp
    from scripts.function_tracer_pcode.proof.recurrence_promotion import PairPromotionState
    attempt = SimpleNamespace(state=PairPromotionState.COMPOSED, left=SimpleNamespace(proposal="L"), right=None, failure=None)
    seen = []
    real = checker_module.build_branch_check_context

    def spy(**kw):
        ctx = real(**kw); seen.append(ctx); return ctx

    checker._recurrence_promotion_authority = lambda sr, *, comparison_session_id, branch_id: object()
    # fake attempt は receipt 生成が読む属性を持たないので、結果側の receipt 構築は instance seam で無効化する
    checker._recurrence_promotion_result_receipt = lambda sr: None
    # recurrence runtime には outer B 段が facade に保存した実物の runtime を返す（nested check の B 段が読む）
    with patch.object(rp, "promote_recurrence_pair", side_effect=lambda a1, a2, auth: (a1, a2, checker._obligation_runtime_session, attempt)), \
         patch.object(checker_module, "complete_recurrence_promotion_signals", return_value=True), \
         patch.object(checker_module, "build_branch_check_context", side_effect=spy):
        result = checker.check(analysis, analysis, **check_kwargs)
    return result, seen


def test_direct_checker_recurrence_recursion_rebuilds_a_fresh_direct_context():
    analysis = create_mock_analysis("f", [])
    checker = EquivalenceChecker(strategy="pairwise", timeout=5, monolithic_timeout=5)
    result, seen = _run_with_forced_recurrence(checker, analysis)
    assert result.error_message is None and len(seen) == 2
    outer, inner = seen
    assert inner.comparison_session_id != outer.comparison_session_id
    assert inner.generation == outer.generation + 1 and inner.branch_id == outer.branch_id == "PairwiseStrategy"
    assert inner.production_branch_authority_lease is None


def test_runner_supplied_facade_context_is_inherited_by_the_recurrence_recursion():
    analysis = create_mock_analysis("f", [])
    checker = EquivalenceChecker(strategy="pairwise", timeout=5, monolithic_timeout=5)
    lease = object()
    checker._active_production_branch_authority_lease = lease
    checker._active_comparison_session_id = "S-runner"
    checker._active_comparison_generation = 9
    checker._active_call_proof_branch_id = "S_PAIRWISE"
    try:
        result, seen = _run_with_forced_recurrence(checker, analysis)
    finally:
        for name in ("_active_production_branch_authority_lease", "_active_comparison_session_id",
                     "_active_comparison_generation", "_active_call_proof_branch_id"):
            delattr(checker, name)
    assert result.error_message is None and len(seen) == 2
    outer, inner = seen
    assert_same_context(outer, inner)
    assert inner.comparison_session_id == "S-runner" and inner.generation == 9 and inner.branch_id == "S_PAIRWISE"
    assert inner.production_branch_authority_lease is lease


# ---- 静的: runner 側の dual-write と check() の explicit 優先 ------------------------------------

def test_runner_builds_the_explicit_context_with_the_shared_builder_and_keeps_legacy_writes():
    src = inspect.getsource(runner_module)
    assert src.count("build_branch_check_context(") == 1
    assert "branch_context=explicit_context" in src
    for name in ("_active_production_branch_authority_lease", "_active_comparison_session_id",
                 "_active_comparison_generation", "_active_call_proof_branch_id", "_active_pair_replan_plan"):
        assert f"checker.{name} = " in src, name  # legacy set は 6c-3 まで残る
    src = inspect.getsource(EquivalenceChecker.check)
    fn = ast.parse("class _C:\n" + "\n".join("    " + l for l in src.splitlines())).body[0].body[0]
    calls = [n for n in ast.walk(fn) if isinstance(n, ast.Call) and getattr(n.func, "id", "") == "build_branch_check_context"]
    assert len(calls) == 1
    # ctx = branch_context if branch_context is not None else build_branch_check_context(...)
    assigns = [n for n in ast.walk(fn) if isinstance(n, ast.Assign) and any(getattr(t, "id", "") == "ctx" for t in n.targets)]
    assert len(assigns) == 1 and isinstance(assigns[0].value, ast.IfExp)
    assert ast.unparse(assigns[0].value.test) == "branch_context is not None" and ast.unparse(assigns[0].value.body) == "branch_context"

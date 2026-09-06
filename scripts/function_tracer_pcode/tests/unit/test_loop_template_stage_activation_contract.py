"""#102: S_LOOP_TEMPLATE_ABSTRACTION の runner-level activation contract。

real な EquivalenceChecker / _run_stage_plan / eligibility（_should_try_loop_template_stage）/
BranchActivationController / execute_branch / check() を通し、strategy の check だけを stub にする。
checker が受け取る明示 BranchCheckContext を、runner 側の独立した observable（issue された lease、
branch trace、呼び出し前後の _call_proof_generation）から field ごとに検査する。builder の再構築や mock による
自作 context の流し込みは行わない。"""

from types import SimpleNamespace

from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker, StageID
from scripts.function_tracer_pcode.proof.obligations import ActivationState
from scripts.function_tracer_pcode.proof.strategies.proof_gates._shared import StrategyResult
from scripts.function_tracer_pcode.smt import ParallelResult
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis

LOOP = StageID.S_LOOP_TEMPLATE_ABSTRACTION.value


def _unknown_result(**stats):
    return StrategyResult(is_equivalent=None, solver_results=ParallelResult(results=[]),
                          pairwise_debug_stats=dict(stats) if stats else None)


class _ObservingChecker(EquivalenceChecker):
    """runner → checker の明示 handoff を check() 境界で記録する（処理は実物の check() に委譲）。"""

    def __init__(self, *args, **kwargs):
        object.__setattr__(self, "deliveries", [])
        super().__init__(*args, **kwargs)

    def check(self, analysis1, analysis2, *args, **kwargs):
        ctx = kwargs.get("branch_context")
        lease = ctx.production_branch_authority_lease if ctx is not None else None
        self.deliveries.append(SimpleNamespace(
            ctx=ctx,
            force_strategy=kwargs.get("force_strategy"),
            lease_active_during_call=(lease.validates(require_active=True) if lease is not None else None),
            counter_before=self._call_proof_generation,
        ))
        result = super().check(analysis1, analysis2, *args, **kwargs)
        self.deliveries[-1].counter_after = self._call_proof_generation
        return result


def _build_checker(pairwise_stats):
    checker = _ObservingChecker(strategy="pairwise", timeout=5, monolithic_timeout=5, enable_template_abstraction=True)
    assert [s.stage_id for s in checker.stage_plan][:2] == [StageID.S_PAIRWISE, StageID.S_LOOP_TEMPLATE_ABSTRACTION]
    loop_calls = []
    checker.pairwise_strategy.check = lambda a1, a2, save_formula=False: _unknown_result(**pairwise_stats)
    checker.loop_template_strategy.check = lambda a1, a2, save_formula=False: loop_calls.append(
        getattr(checker.loop_template_strategy, "_obligation_runtime_session", None)) or _unknown_result()
    checker.monolithic_strategy.check = lambda a1, a2, save_formula=False: _unknown_result()
    # eligibility は実物に委譲し、判定の入力と戻り値だけを記録する（結果を差し替えない）
    eligibility = []
    real_eligibility = checker._should_try_loop_template_stage

    def observed_eligibility(last_result):
        decision = real_eligibility(last_result)
        eligibility.append((last_result, decision))
        return decision

    checker._should_try_loop_template_stage = observed_eligibility
    return checker, loop_calls, eligibility


def _run(checker):
    analysis = create_mock_analysis("f", [])
    return checker._run_stage_plan(analysis, analysis, "B1", "B2", False, None, 0, None, None)


def _record(checker, branch_id):
    return next(r for r in checker._last_obligation_branch_trace.records if r.branch_id == branch_id)


def test_pairwise_timeout_activates_the_loop_template_branch_with_a_runner_issued_context():
    checker, loop_calls, eligibility = _build_checker({"timeout_fallback_attempts": 3})
    result = _run(checker)

    # real eligibility が production の条件（timeout_fallback_attempts > 0）で True を返した
    assert len(eligibility) == 1
    last_result, decision = eligibility[0]
    assert decision is True and last_result.is_equivalent is None and last_result.error_message is None
    assert last_result.pairwise_debug_stats["timeout_fallback_attempts"] == 3
    # runner は result 取得後に controller.record() で COMPLETED を格納する（final trace）
    assert _record(checker, LOOP).activation_state == ActivationState.COMPLETED

    by_branch = {d.ctx.branch_id: d for d in checker.deliveries if d.ctx is not None}
    assert set(by_branch) >= {"S_PAIRWISE", LOOP}
    loop = by_branch[LOOP]
    pairwise = by_branch["S_PAIRWISE"]

    # identity / strategy
    assert loop.force_strategy is checker.loop_template_strategy
    assert loop.ctx.strategy is checker.loop_template_strategy
    assert len(loop_calls) == 1 and loop_calls[0] is not None  # strategy は runtime を束縛された状態で 1 回実行
    # branch id / replan
    assert loop.ctx.branch_id == LOOP and loop.ctx.replan_plan is None
    # session / generation: runner が issue した lease（独立した observable）と一致し、branch ごとに新しい session
    lease = loop.ctx.production_branch_authority_lease
    assert lease is not None and lease.branch_id == LOOP
    assert loop.ctx.comparison_session_id == lease.comparison_session_id
    assert loop.ctx.generation == lease.generation
    assert loop.ctx.comparison_session_id != pairwise.ctx.comparison_session_id
    assert lease is not pairwise.ctx.production_branch_authority_lease
    # authority lease lifecycle: strategy 実行中は active、branch 終了後は同じ lease が revoke 済み
    assert loop.lease_active_during_call is True
    assert lease.validates(require_active=False) is True and lease.validates(require_active=True) is False
    # call proof generation（Phase 6c の既存 contract）: runner は counter+1 を generation とし、
    # replan でない check() が 1 回 increment するので、呼び出し後の counter は context の generation に一致する
    assert loop.ctx.generation == loop.counter_before + 1
    assert loop.counter_after == loop.ctx.generation
    assert loop.ctx.decision_mode == checker.call_proof_decision_mode
    assert result is not None


def test_pairwise_without_timeout_leaves_the_loop_template_branch_inapplicable():
    checker, loop_calls, eligibility = _build_checker({})
    _run(checker)

    assert len(eligibility) == 1 and eligibility[0][1] is False  # real eligibility が False
    assert loop_calls == []  # loop_template strategy は呼ばれない
    assert not [d for d in checker.deliveries if d.ctx is not None and d.ctx.branch_id == LOOP]  # context は配送されない
    assert not [d for d in checker.deliveries if d.force_strategy is checker.loop_template_strategy]
    # execute_branch に入らないため lease もこの branch 用には発行されない（trace は inapplicable）
    assert _record(checker, LOOP).activation_state == ActivationState.INAPPLICABLE
    assert all(d.ctx.production_branch_authority_lease.branch_id != LOOP for d in checker.deliveries if d.ctx is not None)

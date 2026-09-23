"""Phase 6c (#93): stage runner → checker の branch 文脈は明示引数 ``branch_context`` のみで渡す。
6c-1 の oracle（runner が issue した lease の session / generation / branch と ctx の一致、replan precedence、abstract
recursive branch の inner branch_id fallback、再帰転送の provenance）を、6c-3 で legacy facade 属性を撤去した後も固定する。"""

import ast
import inspect
from types import SimpleNamespace
from unittest.mock import Mock, patch

import pytest

from scripts.function_tracer_pcode.checker import checker as checker_module
from scripts.function_tracer_pcode.proof.obligations.branch_context import BranchCheckContext, build_branch_check_context
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


LEGACY_FACADE_ATTRIBUTES = (
    "_active_production_branch_authority_lease",
    "_active_comparison_session_id",
    "_active_comparison_generation",
    "_active_call_proof_branch_id",
    "_active_pair_replan_plan",
)


def _assert_no_legacy_handoff(checker):
    """6c-3: runner は facade に branch 文脈を置かない（呼び出し時点でも属性が存在しない）。"""
    for name in LEGACY_FACADE_ATTRIBUTES:
        assert not hasattr(checker, name), name


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
def test_runner_passes_an_explicit_context_bound_to_the_issued_lease(stage_id, key, attr):
    captured = []

    def execute(*args, **kwargs):
        checker_ref = captured_checker[0]
        _assert_no_legacy_handoff(checker_ref)
        ctx = kwargs["branch_context"]
        captured.append((ctx, kwargs["force_strategy"], ctx.production_branch_authority_lease.validates(require_active=True)))
        return runner_tests._result(True)

    checker = _runner_checker(execute)
    captured_checker = [checker]
    checker.stage_plan = [StageSpec(stage_id, key, key)]
    runner_tests._run(checker, "_run_stage_plan")
    assert len(captured) == 1
    explicit, strategy, lease_active_during_call = captured[0]
    assert isinstance(explicit, BranchCheckContext)
    lease = explicit.production_branch_authority_lease
    assert lease_active_during_call is True and not lease.validates(require_active=True)  # finally で revoke 済み
    assert explicit.strategy is getattr(checker, attr) is strategy
    # ctx の session / generation / branch は runner が issue した lease と同じ値
    assert explicit.comparison_session_id == lease.comparison_session_id and explicit.generation == lease.generation == 1
    assert explicit.branch_id == lease.branch_id == stage_id.value
    assert explicit.replan_plan is None
    assert explicit.decision_mode == CallProofDecisionMode.PREFLIGHT_PROJECTION
    _assert_no_legacy_handoff(checker)


def test_runner_replan_context_takes_the_successor_plan_precedence_and_keeps_the_branch_local_lease():
    src = inspect.getsource(runner_tests.test_completed_proof_replans_pairwise_on_successor_view_and_ledger)
    assert 'branch_context"].replan_plan is successor_plan' in src  # 6c-3: 既存 seam は ctx 検査へ置換済み
    from scripts.function_tracer_pcode.proof.obligations import PairLedgerBinding
    from scripts.function_tracer_pcode.proof.cause_identity import ProofRequirementContract, ProofRequirementId
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
        _assert_no_legacy_handoff(checker)
        captured.append((ctx, kwargs["force_strategy"], ctx.production_branch_authority_lease, checker._call_proof_generation))
        if len(captured) == 1:
            binding = PairLedgerBinding("session", "S_PAIRWISE", "surface", "projection", 1,
                                        runtime.current_view.view_id, runtime.premise_digest, 1, "relation-digest")
            ledger = runtime.open_pair_ledger(binding, 1)
            first._prepared_dispatch_frame = SimpleNamespace(pair_disposition_ledger=ledger)
            return first
        successor_plan = runtime.pair_ledger_manager.pending_successor
        assert successor_plan is not None and ctx.replan_plan is successor_plan
        replacement_binding = PairLedgerBinding(successor_plan.comparison_session_id, successor_plan.branch_id, "new-surface",
                                                "new-projection", 2, successor_plan.derived_view_id, runtime.premise_digest, 2, "relation-digest")
        runtime.open_pair_ledger(replacement_binding, 2)
        second._prepared_dispatch_frame = SimpleNamespace(pair_disposition_ledger=runtime.pair_ledger_manager.current)
        return second

    checker = _runner_checker(execute)
    checker.stage_plan = [StageSpec(StageID.S_PAIRWISE, "pairwise", "pairwise")]
    checker.pairwise_strategy = strategy
    final = runner_tests._run(checker, "_run_stage_plan")
    assert final.is_equivalent is True and len(captured) == 2
    (ctx1, strat1, lease1, _), (ctx2, strat2, lease2, _) = captured
    assert strat1 is strat2 is strategy and ctx1.strategy is strategy and ctx2.strategy is strategy
    assert ctx1.replan_plan is None and ctx1.comparison_session_id == lease1.comparison_session_id
    plan = ctx2.replan_plan
    assert plan is not None  # successor plan は明示 context 経由でのみ渡る
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
        _assert_no_legacy_handoff(checker)
        ctx = kwargs["branch_context"]
        captured.append((ctx, ctx.production_branch_authority_lease.validates(require_active=True)))
        return runner_tests._result(True)

    checker = _runner_checker([])
    checker.pairwise_strategy = checker_module.PairwiseStrategy.__new__(checker_module.PairwiseStrategy)
    checker._run_recursive_abstraction_stage = Mock(side_effect=abstraction)
    checker.stage_plan = [StageSpec(StageID.S_ABSTRACT_RECURSIVE_SUMMARY, "abstract", strategy="abstract_pairwise")]
    runner_tests._run(checker, "_run_stage_plan")
    assert len(captured) == 1
    explicit, lease_active = captured[0]
    lease = explicit.production_branch_authority_lease
    assert lease_active is True and lease is not None
    # session / generation / lease は runner 由来（lease は outer stage id で発行される）
    assert explicit.comparison_session_id == lease.comparison_session_id and explicit.generation == lease.generation == 1
    assert lease.branch_id == StageID.S_ABSTRACT_RECURSIVE_SUMMARY.value
    # inner branch_id は strategy class fallback（outer の S_ABSTRACT_RECURSIVE_SUMMARY ではない）
    assert explicit.strategy is checker.pairwise_strategy and explicit.branch_id == "PairwiseStrategy"
    assert not explicit.branch_id.startswith("S_") and explicit.replan_plan is None
    checker.check.assert_not_called()
    _assert_no_legacy_handoff(checker)


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


def test_runner_supplied_context_is_forwarded_as_the_same_object_to_the_recurrence_recursion():
    analysis = create_mock_analysis("f", [])
    checker = EquivalenceChecker(strategy="pairwise", timeout=5, monolithic_timeout=5)
    lease = object()
    supplied = BranchCheckContext(strategy=checker.pairwise_strategy, replan_plan=None, generation=9, comparison_session_id="S-runner",
                                  branch_id="S_PAIRWISE", decision_mode=checker.call_proof_decision_mode, production_branch_authority_lease=lease)
    nested = []
    real_check = EquivalenceChecker.check

    def observing_check(self, a1, a2, *args, **kwargs):
        if getattr(self, "_active_recurrence_promotion_authority", None) is not None:
            nested.append(kwargs.get("branch_context"))
        return real_check(self, a1, a2, *args, **kwargs)

    with patch.object(EquivalenceChecker, "check", observing_check):
        result, seen = _run_with_forced_recurrence(checker, analysis, branch_context=supplied)
    assert result.error_message is None
    assert seen == []  # supplied ctx: outer も nested も builder を呼ばない
    assert nested == [supplied] and nested[0] is supplied


def test_direct_synthesized_context_is_not_forwarded_to_the_recurrence_recursion():
    analysis = create_mock_analysis("f", [])
    checker = EquivalenceChecker(strategy="pairwise", timeout=5, monolithic_timeout=5)
    nested = []
    real_check = EquivalenceChecker.check

    def observing_check(self, a1, a2, *args, **kwargs):
        if getattr(self, "_active_recurrence_promotion_authority", None) is not None:
            nested.append(kwargs.get("branch_context"))
        return real_check(self, a1, a2, *args, **kwargs)

    with patch.object(EquivalenceChecker, "check", observing_check):
        result, seen = _run_with_forced_recurrence(checker, analysis)
    assert result.error_message is None
    assert nested == [None]          # direct で組んだ ctx は固定転送しない
    assert len(seen) == 2 and seen[1].comparison_session_id != seen[0].comparison_session_id


def test_legacy_facade_attributes_are_gone_from_production_sources():
    """6c-3: 5 つの legacy 属性の set / restore / delete / read が production source に存在しない（repo-wide）。"""
    import pathlib
    from scripts import function_tracer_pcode as pkg
    root = pathlib.Path(pkg.__file__).parent
    offenders = []
    for path in root.rglob("*.py"):
        if "tests" in path.parts:
            continue
        text = path.read_text(encoding="utf-8")
        for name in LEGACY_FACADE_ATTRIBUTES:
            if name in text:
                offenders.append((str(path.relative_to(root)), name))
    assert offenders == []
    # check() / runner の source にも無い（6c-2 / 6c-3）
    for src in (inspect.getsource(EquivalenceChecker.check), inspect.getsource(runner_module)):
        for name in LEGACY_FACADE_ATTRIBUTES:
            assert name not in src, name


# ---- 静的: runner 側の dual-write と check() の explicit 優先 ------------------------------------

def test_runner_builds_the_explicit_context_with_the_shared_builder_only():
    src = inspect.getsource(runner_module)
    assert src.count("build_branch_check_context(") == 2  # normal branch + abstract recursive branch（6c-2）
    assert "branch_context=explicit_context" in src and "branch_context=inner_context" in src
    assert "active_call_proof_branch_id=None" in src  # abstract path: inner branch_id は strategy class fallback
    # 6c-3: replan の successor plan は execute_branch の引数 → builder の replan_plan= へ（facade を経由しない）
    assert "def execute_branch(replan_plan=None):" in src and "execute_branch(replan_plan=successor_plan)" in src
    assert src.count("replan_plan=replan_plan,") == 2
    src = inspect.getsource(EquivalenceChecker.check)
    fn = ast.parse("class _C:\n" + "\n".join("    " + l for l in src.splitlines())).body[0].body[0]
    calls = [n for n in ast.walk(fn) if isinstance(n, ast.Call) and getattr(n.func, "id", "") == "build_branch_check_context"]
    assert len(calls) == 1
    # ctx = branch_context if context_was_supplied else build_branch_check_context(<direct semantics>)
    assigns = [n for n in ast.walk(fn) if isinstance(n, ast.Assign) and any(getattr(t, "id", "") == "ctx" for t in n.targets)]
    assert len(assigns) == 1 and isinstance(assigns[0].value, ast.IfExp)
    assert ast.unparse(assigns[0].value.test) == "context_was_supplied" and ast.unparse(assigns[0].value.body) == "branch_context"
    direct_kw = {k.arg: ast.unparse(k.value) for k in calls[0].keywords}
    assert direct_kw["replan_plan"] == "None" and direct_kw["active_comparison_session_id"] == "None"
    assert direct_kw["active_comparison_generation"] == "None" and direct_kw["active_call_proof_branch_id"] == "None"
    assert direct_kw["production_branch_authority_lease"] == "None"
    # 再帰 self.check(...) は provenance-sensitive に転送する
    rec = [n for n in ast.walk(fn) if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and n.func.attr == "check"
           and ast.unparse(n.func.value) == "self"]
    assert len(rec) == 1
    assert {k.arg: ast.unparse(k.value) for k in rec[0].keywords}["branch_context"] == "ctx if context_was_supplied else None"
    # abstraction stage は branch_context を check() へ転送する
    abs_src = inspect.getsource(EquivalenceChecker._run_recursive_abstraction_stage)
    assert "branch_context=branch_context" in abs_src


# ---- authority lease lifetime: 発行直後に try/finally（revoke）へ入る ---------------------------------

def test_lease_issuance_is_immediately_followed_by_the_try_finally_that_revokes_it():
    """#96 レビュー: issue_production_branch_authority() 成功後から try/finally に入るまでに、例外を投げ得る
    処理（import を含む）を置かない。finally は同じ lease を revoke する。"""
    module = ast.parse(inspect.getsource(runner_module))
    fns = [n for n in ast.walk(module) if isinstance(n, ast.FunctionDef) and n.name == "execute_branch"]
    assert len(fns) == 1
    body = fns[0].body
    issue_idx = [i for i, st in enumerate(body) if isinstance(st, ast.Assign)
                 and isinstance(st.value, ast.Call) and ast.unparse(st.value.func) == "issue_production_branch_authority"]
    assert len(issue_idx) == 1
    i = issue_idx[0]
    assert ast.unparse(body[i].targets[0]) == "branch_lease"
    nxt = body[i + 1]
    assert isinstance(nxt, ast.Try), ast.unparse(nxt)[:60]  # 発行の直後の文が try
    assert [ast.unparse(st) for st in nxt.finalbody] == ["revoke_production_branch_authority(branch_lease)"]
    assert not nxt.handlers and not nxt.orelse
    # 発行より前の文だけが import / 局所計算（発行後に import は無い）
    assert all(not isinstance(st, (ast.Import, ast.ImportFrom)) for st in body[i + 1:])
    imports_before = [st for st in body[:i] if isinstance(st, ast.ImportFrom)]
    assert {n.name for st in imports_before for n in st.names} >= {
        "issue_production_branch_authority", "revoke_production_branch_authority", "build_branch_check_context"}


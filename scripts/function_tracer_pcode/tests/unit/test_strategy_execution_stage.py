"""Phase 6b-2 (#82): strategy 実行段の抽出。runtime の「使う/保存する」規則、facade write の位置、lease/frame/ledger の順序を固定する。"""

import ast
import inspect
from types import SimpleNamespace
from unittest.mock import Mock, patch

import pytest

from scripts.function_tracer_pcode.checker import strategy_execution as se
from scripts.function_tracer_pcode.proof.obligations.branch_context import BranchCheckContext
from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker
from scripts.function_tracer_pcode.proof.call_effect.preflight import CallProofDecisionMode
from scripts.function_tracer_pcode.proof.strategies.monolithic import MonolithicStrategy
from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis

RUNTIME_MOD = "scripts.function_tracer_pcode.proof.obligations.runtime.ObligationRuntimeSession"


def _runtime(pending=None):
    return SimpleNamespace(pair_ledger_manager=SimpleNamespace(pending_successor=pending))


# ---- prepare_strategy_runtime: 決定表 ----------------------------------------------------------

def test_no_existing_runtime_creates_one_and_stores_it_on_the_facade():
    fresh = object()
    with patch(RUNTIME_MOD + ".create", return_value=fresh) as create:
        prep = se.prepare_strategy_runtime(None, None, "a1", "a2")
    assert prep.runtime is fresh and prep.store_on_facade is True
    create.assert_called_once_with("a1", "a2")


def test_existing_runtime_without_pending_successor_is_reused_and_not_stored():
    existing = _runtime(pending=None)
    with patch(RUNTIME_MOD + ".create") as create:
        prep = se.prepare_strategy_runtime(existing, None, "a1", "a2")
    assert prep.runtime is existing and prep.store_on_facade is False
    create.assert_not_called()


def test_stale_pending_successor_without_replan_gets_a_branch_local_runtime_that_is_not_stored():
    existing = _runtime(pending=object())
    fresh = object()
    with patch(RUNTIME_MOD + ".create", return_value=fresh):
        prep = se.prepare_strategy_runtime(existing, None, "a1", "a2")
    assert prep.runtime is fresh and prep.runtime is not existing
    assert prep.store_on_facade is False   # branch-local: facade には保存しない


def test_pending_successor_with_replan_plan_reuses_the_existing_runtime():
    plan = object()
    existing = _runtime(pending=plan)
    with patch(RUNTIME_MOD + ".create") as create:
        prep = se.prepare_strategy_runtime(existing, plan, "a1", "a2")
    assert prep.runtime is existing and prep.store_on_facade is False
    create.assert_not_called()


# ---- check(): facade write の位置（静的） ----------------------------------------------------

def _check_fn():
    src = inspect.getsource(EquivalenceChecker.check)
    tree = ast.parse("class _C:\n" + "\n".join("    " + l for l in src.splitlines()))
    return tree.body[0].body[0], src


def test_obligation_runtime_store_is_guarded_and_precedes_run_strategy_branch():
    fn, src = _check_fn()
    stores = [n for n in ast.walk(fn) if isinstance(n, ast.Assign)
              and any(isinstance(t, ast.Attribute) and t.attr == "_obligation_runtime_session" for t in n.targets)]
    # B 段の保存（store_on_facade ガード付き）と D 段（recurrence runtime）の 2 箇所のみ
    assert len(stores) == 2
    guarded = [n for n in ast.walk(fn) if isinstance(n, ast.If) and "store_on_facade" in ast.unparse(n.test)]
    assert len(guarded) == 1 and any(isinstance(b, ast.Assign) for b in guarded[0].body) and not guarded[0].orelse
    b_store_line = guarded[0].body[0].lineno
    run_calls = [n for n in ast.walk(fn) if isinstance(n, ast.Call) and getattr(n.func, "id", "") == "run_strategy_branch"]
    assert len(run_calls) == 1 and b_store_line < run_calls[0].lineno
    # strategy.check の直接呼び出しは check() から消えている（段関数の中だけ）
    assert "strategy.check(" not in src
    # 段関数に setter callback を渡していない
    assert "setattr" not in src and "_obligation_runtime_session=" not in src


# ---- run_strategy_branch: lease / frame / ledger / gate の順序（動的） ---------------------------

class _RecordingPairwise(PairwiseStrategy):
    def __init__(self, events):
        self._events = events
        self._obligation_runtime_session = None

    def check(self, analysis1, analysis2, save_formula=False):
        self._events.append(("strategy.check", self._obligation_runtime_session))
        return SimpleNamespace(is_equivalent=None, comparison_execution_receipt=None)


def _ctx(strategy, branch_id="DirectCall", lease=None, replan=None):
    return BranchCheckContext(strategy=strategy, replan_plan=replan, generation=1, comparison_session_id="S",
                              branch_id=branch_id, decision_mode=CallProofDecisionMode.PREFLIGHT_PROJECTION,
                              production_branch_authority_lease=lease)


def _frame(input_correspondence=None):
    return SimpleNamespace(obligation_runtime=None, replan_successor_plan=None, pair_disposition_ledger=None,
                           receipt=None, cleanup_complete=False, close=Mock(name="frame.close"),
                           prepared=SimpleNamespace(input_correspondence=input_correspondence))


def _projection_prep(manifest=None, projection=None):
    return se.PreflightProjectionPreparation(source_pair="src", prepared_pair="prep",
                                             call_effect_shadow_manifest=manifest if manifest is not None else {},
                                             projection=projection)


def test_run_strategy_branch_order_pairwise_without_ledger_push_check_close_gate():
    """ledger の無い direct Pairwise（compatibility lease も無い）: finalize / revoke は起きない。"""
    events = []
    strategy = _RecordingPairwise(events)
    frame = _frame()
    runtime = object()
    with patch.object(se, "push_prepared_dispatch_frame", side_effect=lambda f: events.append(("push",)) or "tok"), \
         patch.object(se, "close_prepared_dispatch_frame", side_effect=lambda f, tok: events.append(("close", tok)) or True), \
         patch.object(se, "finalize_pairwise_comparison_receipt", side_effect=lambda f: events.append(("pairwise_finalize",))), \
         patch.object(se, "diagnostic_projection", side_effect=lambda m, f: m), \
         patch("scripts.function_tracer_pcode.proof.monolithic_authority.revoke_production_branch_authority",
               side_effect=lambda l: events.append(("revoke", l))):
        outcome = se.run_strategy_branch(_ctx(strategy), frame, runtime, "a1", "a2", False,
                                         locally_issued_branch_authority=None, call_effect_shadow_manifest={},
                                         debug_print=lambda m: events.append(("debug", m)),
                                         apply_preflight_final_gate=lambda *a, **k: events.append(("gate", k["cleanup_complete"])))
    names = [e[0] for e in events]
    assert names == ["debug", "push", "strategy.check", "close", "gate"]
    assert events[2][1] is runtime          # runtime は strategy.check より前に strategy へ束縛済み
    assert frame.obligation_runtime is runtime
    assert events[3][1] == "tok"
    assert outcome.cleanup_complete is True and outcome.strategy_result is not None
    assert outcome.preflight_gate_delta_diagnostic["comparison_branch"] == "DirectCall"


def test_run_strategy_branch_order_direct_pairwise_with_ledger_finalizes_before_and_after_close():
    """direct Pairwise + ledger あり（main の exact call sequence を基準）:
    push → strategy.check → pairwise finalize（receipt 未発行のときのみ、frame.receipt を設定）→ close
    → pairwise finalize（direct branch の finalization）→ final gate。revoke は無い（lease は Monolithic のみ）。"""
    events = []
    strategy = _RecordingPairwise(events)
    frame = _frame()
    frame.pair_disposition_ledger = object()
    receipts = []

    def finalize(f):
        # 実物と同じく frame.receipt を副作用で設定する（1 回目のガード `receipt is None` を消費する）
        receipt = SimpleNamespace(seq=len(receipts) + 1, receipt_before=f.receipt)
        receipts.append(receipt)
        f.receipt = receipt
        events.append(("pairwise_finalize", receipt.seq))
        return receipt

    with patch.object(se, "push_prepared_dispatch_frame", side_effect=lambda f: events.append(("push",)) or "tok"), \
         patch.object(se, "close_prepared_dispatch_frame", side_effect=lambda f, tok: events.append(("close", tok)) or True), \
         patch.object(se, "finalize_pairwise_comparison_receipt", side_effect=finalize), \
         patch.object(se, "diagnostic_projection", side_effect=lambda m, f: m), \
         patch("scripts.function_tracer_pcode.proof.monolithic_authority.revoke_production_branch_authority",
               side_effect=lambda l: events.append(("revoke", l))):
        outcome = se.run_strategy_branch(_ctx(strategy), frame, object(), "a1", "a2", False,
                                         locally_issued_branch_authority=None, call_effect_shadow_manifest={},
                                         debug_print=lambda m: None,
                                         apply_preflight_final_gate=lambda *a, **k: events.append(("gate", k["cleanup_complete"])))
    assert events == [("push",), ("strategy.check", frame.obligation_runtime), ("pairwise_finalize", 1),
                      ("close", "tok"), ("pairwise_finalize", 2), ("gate", True)]
    assert receipts[0].receipt_before is None and receipts[1].receipt_before is receipts[0]
    assert frame.receipt is receipts[1]
    assert outcome.strategy_result.comparison_execution_receipt is receipts[1]


def test_run_strategy_branch_order_direct_pairwise_with_preissued_receipt_finalizes_only_after_close():
    """strategy.check の中で receipt が既に発行されていれば、close 前の finalize は行わない。"""
    events = []
    strategy = _RecordingPairwise(events)
    frame = _frame()
    frame.pair_disposition_ledger = object()
    frame.receipt = "issued_by_strategy"
    with patch.object(se, "push_prepared_dispatch_frame", return_value="tok"), \
         patch.object(se, "close_prepared_dispatch_frame", side_effect=lambda f, tok: events.append(("close",)) or True), \
         patch.object(se, "finalize_pairwise_comparison_receipt", side_effect=lambda f: events.append(("pairwise_finalize",)) or "R"), \
         patch.object(se, "diagnostic_projection", side_effect=lambda m, f: m):
        se.run_strategy_branch(_ctx(strategy), frame, object(), "a1", "a2", False,
                               locally_issued_branch_authority=None, call_effect_shadow_manifest={},
                               debug_print=lambda m: None, apply_preflight_final_gate=lambda *a, **k: events.append(("gate",)))
    assert [e[0] for e in events] == ["strategy.check", "close", "pairwise_finalize", "gate"]


class _RecordingMonolithic(MonolithicStrategy):
    def __init__(self, events):
        self._events = events
        self._obligation_runtime_session = None

    def check(self, analysis1, analysis2, save_formula=False):
        self._events.append(("strategy.check", self._obligation_runtime_session))
        return SimpleNamespace(is_equivalent=None, comparison_execution_receipt=None)


def test_run_strategy_branch_order_direct_monolithic_with_locally_issued_lease():
    """production-valid な direct Monolithic（check() が compatibility lease を発行）:
    push → strategy.check → close → revoke（locally issued lease）→ monolithic finalize → final gate。"""
    events = []
    strategy = _RecordingMonolithic(events)
    frame = _frame()
    runtime = object()
    lease = object()
    with patch.object(se, "push_prepared_dispatch_frame", side_effect=lambda f: events.append(("push",)) or "tok"), \
         patch.object(se, "close_prepared_dispatch_frame", side_effect=lambda f, tok: events.append(("close", tok)) or True), \
         patch.object(se, "finalize_pairwise_comparison_receipt", side_effect=lambda f: events.append(("pairwise_finalize",))), \
         patch.object(se, "diagnostic_projection", side_effect=lambda m, f: m), \
         patch("scripts.function_tracer_pcode.proof.call_effect.preflight.finalize_monolithic_comparison_receipt",
               side_effect=lambda f: events.append(("monolithic_finalize",)) or "MR"), \
         patch("scripts.function_tracer_pcode.proof.monolithic_authority.revoke_production_branch_authority",
               side_effect=lambda l: events.append(("revoke", l))):
        outcome = se.run_strategy_branch(_ctx(strategy, branch_id="MonolithicStrategy", lease=lease), frame, runtime, "a1", "a2", False,
                                         locally_issued_branch_authority=lease, call_effect_shadow_manifest={},
                                         debug_print=lambda m: None,
                                         apply_preflight_final_gate=lambda *a, **k: events.append(("gate", k["cleanup_complete"])))
    assert events == [("push",), ("strategy.check", runtime), ("close", "tok"), ("revoke", lease),
                      ("monolithic_finalize",), ("gate", True)]
    assert outcome.strategy_result.comparison_execution_receipt == "MR"


def test_run_strategy_branch_revokes_the_lease_even_when_the_strategy_raises():
    events = []
    strategy = _RecordingMonolithic(events)
    strategy.check = lambda *a, **k: (_ for _ in ()).throw(RuntimeError("strategy boom"))
    lease = object()
    with patch.object(se, "push_prepared_dispatch_frame", side_effect=lambda f: events.append(("push",)) or "tok"), \
         patch.object(se, "close_prepared_dispatch_frame", side_effect=lambda f, tok: events.append(("close", tok)) or False), \
         patch("scripts.function_tracer_pcode.proof.monolithic_authority.revoke_production_branch_authority",
               side_effect=lambda l: events.append(("revoke", l))):
        with pytest.raises(RuntimeError, match="strategy boom"):
            se.run_strategy_branch(_ctx(strategy, branch_id="MonolithicStrategy", lease=lease), _frame(), object(), "a1", "a2", False,
                                   locally_issued_branch_authority=lease, call_effect_shadow_manifest={},
                                   debug_print=lambda m: None, apply_preflight_final_gate=lambda *a, **k: events.append(("gate",)))
    assert events == [("push",), ("close", "tok"), ("revoke", lease)]


def test_run_strategy_branch_skips_final_gate_when_stage_runner_owns_finalization():
    events = []
    strategy = _RecordingPairwise(events)
    with patch.object(se, "push_prepared_dispatch_frame", return_value="tok"), \
         patch.object(se, "close_prepared_dispatch_frame", return_value=True), \
         patch.object(se, "diagnostic_projection", side_effect=lambda m, f: m):
        se.run_strategy_branch(_ctx(strategy, branch_id="S_PAIRWISE"), _frame(), object(), "a1", "a2", False,
                               locally_issued_branch_authority=None, call_effect_shadow_manifest={},
                               debug_print=lambda m: None,
                               apply_preflight_final_gate=lambda *a, **k: events.append(("gate",)))
    assert ("gate",) not in events


def test_run_strategy_branch_rejects_a_missing_replan_successor_before_pushing_the_frame():
    plan = object()
    strategy = _RecordingPairwise([])
    runtime = _runtime(pending=object())  # 別の plan
    with patch.object(se, "push_prepared_dispatch_frame") as push:
        with pytest.raises(RuntimeError, match="pair_replan_successor_plan_missing"):
            se.run_strategy_branch(_ctx(strategy, replan=plan), _frame(), runtime, "a1", "a2", False,
                                   locally_issued_branch_authority=None, call_effect_shadow_manifest={},
                                   debug_print=lambda m: None, apply_preflight_final_gate=lambda *a, **k: None)
    push.assert_not_called()


def test_build_prepared_dispatch_frame_revokes_the_locally_issued_lease_when_the_frame_cannot_be_built():
    events = []
    with patch("scripts.function_tracer_pcode.proof.monolithic_authority.revoke_production_branch_authority",
               side_effect=lambda l: events.append(("revoke", l))), \
         patch.object(se, "PreparedDispatchFrame", side_effect=ValueError("frame boom")):
        with pytest.raises(ValueError, match="frame boom"):
            se.build_prepared_dispatch_frame(_ctx(Mock(spec=MonolithicStrategy)), _projection_prep(),
                                             trusted_proof_artifacts=lambda: (), branch_authority="LEASE",
                                             locally_issued_branch_authority="LEASE")
    assert events == [("revoke", "LEASE")]


def test_build_prepared_dispatch_frame_revokes_when_the_artifacts_supplier_fails_inside_the_try():
    """旧実装は tuple(self._last_internal_call_effect_artifacts) を try の中で評価していた。"""
    events = []
    with patch("scripts.function_tracer_pcode.proof.monolithic_authority.revoke_production_branch_authority",
               side_effect=lambda l: events.append(("revoke", l))), \
         patch.object(se, "PreparedDispatchFrame") as frame_cls:
        with pytest.raises(TypeError):
            se.build_prepared_dispatch_frame(_ctx(Mock(spec=MonolithicStrategy)), _projection_prep(),
                                             trusted_proof_artifacts=lambda: None, branch_authority="LEASE",
                                             locally_issued_branch_authority="LEASE")
    frame_cls.assert_not_called()
    assert events == [("revoke", "LEASE")]


def test_build_prepared_dispatch_frame_does_not_revoke_a_parent_lease():
    with patch("scripts.function_tracer_pcode.proof.monolithic_authority.revoke_production_branch_authority") as revoke, \
         patch.object(se, "PreparedDispatchFrame", side_effect=ValueError("frame boom")):
        with pytest.raises(ValueError):
            se.build_prepared_dispatch_frame(_ctx(Mock(spec=PairwiseStrategy)), _projection_prep(),
                                             trusted_proof_artifacts=lambda: (), branch_authority="parent",
                                             locally_issued_branch_authority=None)
    revoke.assert_not_called()


def test_prepare_preflight_projection_marks_projection_inconclusive_when_recovery_proofs_are_disabled():
    projection = SimpleNamespace(required=True, status="ok", root_blockers=(), covered_blockers=())
    with patch.object(se, "StrategySourceAnalysisPair") as pair_cls, \
         patch.object(se, "prepare_solver_surface", return_value=SimpleNamespace(analysis1="p1", analysis2="p2")), \
         patch.object(se, "validate_call_resolution_projection", return_value=projection), \
         patch.object(se, "replace", side_effect=lambda p, **kw: SimpleNamespace(**{**vars(p), **kw})) as rep:
        pair_cls.create.return_value = "source"
        prep = se.prepare_preflight_projection(_ctx(Mock(spec=PairwiseStrategy), lease="parent"), "a1", "a2", "b1", "b2",
                                               observation_contract_id="oc", trusted_proof_artifacts=lambda: (),
                                               enable_completed_recovery_proofs=False,
                                               call_effect_shadow_manifest=lambda *a: {"m": 1})
    rep.assert_called_once()
    assert prep.projection.status == "inconclusive" and prep.projection.root_blockers == ("completed_recovery_proofs_disabled",)
    assert prep.call_effect_shadow_manifest == {"m": 1} and prep.source_pair == "source"


def test_prepare_preflight_projection_reads_trusted_artifacts_after_the_manifest_refreshes_them():
    """facade の _last_internal_call_effect_artifacts は manifest 計算の副作用で更新される。
    旧実装は manifest 呼び出しの後に読んでいたので、先読み（stale）を退行として固定する。"""
    holder = {"artifacts": ("stale",)}

    def manifest(*args):
        holder["artifacts"] = ("fresh",)
        return {"m": 1}

    seen = {}

    def validate(manifest_arg, prepared, *, generation, trusted_proof_artifacts):
        seen["artifacts"] = trusted_proof_artifacts
        return SimpleNamespace(required=False)

    with patch.object(se, "StrategySourceAnalysisPair") as pair_cls, \
         patch.object(se, "prepare_solver_surface", return_value=SimpleNamespace(analysis1="p1", analysis2="p2")), \
         patch.object(se, "validate_call_resolution_projection", side_effect=validate):
        pair_cls.create.return_value = "source"
        se.prepare_preflight_projection(_ctx(Mock(spec=PairwiseStrategy), lease="parent"), "a1", "a2", "b1", "b2",
                                        observation_contract_id="oc", trusted_proof_artifacts=lambda: holder["artifacts"],
                                        enable_completed_recovery_proofs=True, call_effect_shadow_manifest=manifest)
    assert seen["artifacts"] == ("fresh",)


# ---- lease 発行は check() に残る（authority TCB が呼び出し元を pin するため） ------------------------

def test_lease_issuance_stays_in_check_between_projection_and_frame_construction():
    fn, src = _check_fn()
    se_tree = ast.parse(inspect.getsource(se))
    assert not [n for n in ast.walk(se_tree) if isinstance(n, ast.Call)
                and "issue_production_branch_authority" in ast.unparse(n.func)]
    issues = [n for n in ast.walk(fn) if isinstance(n, ast.Call) and getattr(n.func, "id", "") == "issue_production_branch_authority"]
    assert len(issues) == 1
    guards = [n for n in ast.walk(fn) if isinstance(n, ast.If)
              and "isinstance(strategy, MonolithicStrategy)" in ast.unparse(n.test) and "branch_authority is None" in ast.unparse(n.test)]
    assert len(guards) == 1 and not guards[0].orelse
    assert guards[0].lineno <= issues[0].lineno <= guards[0].end_lineno
    def _line(name):
        calls = [n for n in ast.walk(fn) if isinstance(n, ast.Call) and getattr(n.func, "id", "") == name]
        assert len(calls) == 1, name
        return calls[0].lineno
    assert _line("prepare_preflight_projection") < issues[0].lineno < _line("build_prepared_dispatch_frame") < _line("run_strategy_branch")


def test_direct_monolithic_check_still_issues_and_revokes_a_compatibility_lease():
    """issuer pin（EquivalenceChecker.check の code object）を実際に通す動的テスト。
    frame 構築を失敗させ、check() が発行した lease が builder 側で revoke されることまで見る。"""
    from scripts.function_tracer_pcode.proof import monolithic_authority as ma
    analysis = create_mock_analysis("f", [])
    checker = EquivalenceChecker(strategy="monolithic", timeout=5, monolithic_timeout=5)
    revoked = []
    real_revoke = ma.revoke_production_branch_authority

    def spy_revoke(lease):
        revoked.append(lease)
        real_revoke(lease)

    with patch.object(ma, "revoke_production_branch_authority", side_effect=spy_revoke), \
         patch.object(se, "PreparedDispatchFrame", side_effect=ValueError("frame boom")):
        result = checker.check(analysis, analysis)
    assert result.is_equivalent is None and "frame boom" in str(result.error_message)
    assert len(revoked) == 1
    lease = revoked[0]
    assert lease.branch_id == "MonolithicStrategy" and lease.runtime_view_digest == "direct_checker_compatibility_view"
    assert lease.validates(require_active=False) and not lease.validates(require_active=True)

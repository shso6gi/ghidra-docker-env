# -*- coding: utf-8 -*-
"""Issue #167: 比較に依存する authority の identity と lifetime。

比較の authority は ``ComparisonAuthorityBinding``（raw pair の identity と最終
InputCorrespondence の digest の組）で識別する。

* 同じ raw pair・同じ relation → 共有してよい。
* 同じ raw pair・違う relation → 共有しない。
* 違う raw pair・同じ relation → 共有しない（relation digest 単独は比較の identity ではない）。
* authority scope の無い証拠は採用しない。関数単体の事実は明示してどこでも使える。
* obligation runtime は 1 つの比較だけに仕え、artifact・dependency・producer・replanner・
  outcome・cache を別の比較と共有しない。
"""

from __future__ import annotations

import dataclasses
import hashlib
from types import SimpleNamespace
from unittest.mock import Mock, patch

import pytest

from scripts.function_tracer_pcode.checker.recovery_proofs import RecoveryProofMixin
from scripts.function_tracer_pcode.core import Expression, FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.core.evidence_authority import (
    AUTHORITY_SCOPE_KEY,
    COMPARISON_AUTHORITY_KEY,
    FUNCTION_UNARY,
    mark_function_unary,
    record_function_unary_evidence,
)
from scripts.function_tracer_pcode.proof.cause_identity import ProofRequirementContract, ProofRequirementId
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    OUTSIDE_COMPARISON,
    bind_evidence_to_comparison,
    build_input_correspondence_set,
    comparison_evidence,
    comparison_scope,
    current_comparison,
    merge_new_evidence,
    store_comparison_evidence,
)
from scripts.function_tracer_pcode.proof.obligations.model import FunctionProofOutcome
from scripts.function_tracer_pcode.proof.obligations.runtime import (
    ComparisonRuntimeMismatch,
    ObligationRuntimeSession,
)
from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot
from scripts.function_tracer_pcode.proof.obligations.stage_runner import branch_comparison
from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import comparison_binding_of


def _analysis(name, sizes, entry="0x1000"):
    return FunctionReturnAnalysis(
        function_name=name,
        entry_point=entry,
        parameters=[
            {"name": f"p{index}", "index": index, "size": size, "data_type": "int"}
            for index, size in enumerate(sizes)
        ],
        returns=[ReturnInfo("0x1010", Expression.parameter("p0", 0, data_type="int", size=sizes[0]), [])],
        return_type="int",
    )


def _comparisons():
    """A と、A と同じ relation の別 raw pair C と、A と raw pair は同じで relation が違う比較 B。"""

    pair_a = (_analysis("f", [4]), _analysis("g", [4]))
    pair_c = (_analysis("h", [4], entry="0x2000"), _analysis("k", [4], entry="0x2000"))
    a = comparison_binding_of(*pair_a)
    c = comparison_binding_of(*pair_c)
    b = comparison_binding_of(*pair_a, build_input_correspondence_set(_analysis("f", [4, 4]), _analysis("g", [4, 4])))
    return SimpleNamespace(a=a, b=b, c=c, pair_a=pair_a, pair_c=pair_c)


def test_the_binding_separates_raw_pairs_that_share_a_relation_digest():
    cmp = _comparisons()
    fingerprints = lambda pair: tuple(AnalysisSnapshot.from_function_analysis(item).semantic_fingerprint for item in pair)
    assert fingerprints(cmp.pair_a) != fingerprints(cmp.pair_c)
    assert cmp.a.input_correspondence_digest == cmp.c.input_correspondence_digest
    assert cmp.a != cmp.c and cmp.a.digest != cmp.c.digest
    # 同じ raw pair・同じ relation は、作り直しても同じ比較（branch 間で共有できる）。
    assert comparison_binding_of(*cmp.pair_a) == cmp.a
    assert comparison_binding_of(*cmp.pair_a).digest == cmp.a.digest
    # 同じ raw pair・違う relation は別の比較。
    assert cmp.a.raw_pair_digest == cmp.b.raw_pair_digest and cmp.a != cmp.b


def test_evidence_is_adopted_only_by_the_same_raw_pair_under_the_same_relation():
    cmp = _comparisons()
    record = bind_evidence_to_comparison({"proof_obligation_id": ("p",)}, cmp.a)
    with comparison_scope(comparison_binding_of(*cmp.pair_a)):
        assert comparison_evidence((record,)) == (record,)  # 正当な共有（別 branch）
    with comparison_scope(cmp.c):
        assert comparison_evidence((record,)) == ()  # 別 raw pair・同じ relation digest
    with comparison_scope(cmp.b):
        assert comparison_evidence((record,)) == ()  # 同じ raw pair・別 relation
    with comparison_scope(None):
        assert comparison_evidence((record,)) == ()
    assert comparison_evidence((record,)) == ()


def test_evidence_without_an_authority_scope_is_never_adopted():
    cmp = _comparisons()
    unscoped = {"proof_obligation_id": ("p",)}
    unknown_scope = {"proof_obligation_id": ("p",), AUTHORITY_SCOPE_KEY: "something_else"}
    with comparison_scope(cmp.a):
        assert comparison_evidence((unscoped, unknown_scope)) == ()
    assert comparison_evidence((unscoped, unknown_scope)) == ()


def test_function_unary_facts_are_explicit_and_usable_in_every_comparison():
    cmp = _comparisons()
    analysis = SimpleNamespace(completed_recovery_proof_evidence=())
    record_function_unary_evidence(analysis, {"proof_obligation_id": ("unary",)})
    (unary,) = analysis.completed_recovery_proof_evidence
    assert unary[AUTHORITY_SCOPE_KEY] == FUNCTION_UNARY
    for scope in (cmp.a, cmp.b, cmp.c):
        with comparison_scope(scope):
            assert comparison_evidence((unary,)) == (unary,)
    with pytest.raises(ValueError):
        mark_function_unary(bind_evidence_to_comparison({"proof_obligation_id": ("p",)}, cmp.a))
    with pytest.raises(ValueError):
        bind_evidence_to_comparison(dict(unary), cmp.a)


def test_evidence_made_outside_any_comparison_is_never_adopted():
    cmp = _comparisons()
    record = bind_evidence_to_comparison({"proof_obligation_id": ("p",)})
    assert record[COMPARISON_AUTHORITY_KEY] == OUTSIDE_COMPARISON
    with comparison_scope(cmp.a):
        assert comparison_evidence((record,)) == ()


def test_the_evidence_writer_binds_what_a_comparison_adds_and_keeps_the_rest():
    cmp = _comparisons()
    unary = mark_function_unary({"proof_obligation_id": ("unary",)})
    from_c = bind_evidence_to_comparison({"proof_obligation_id": ("c",)}, cmp.c)
    analysis = SimpleNamespace(completed_recovery_proof_evidence=(unary, from_c))
    with comparison_scope(cmp.a):
        store_comparison_evidence(analysis, [dict(unary), dict(from_c), {"proof_obligation_id": ("a",)}])
    records = analysis.completed_recovery_proof_evidence
    assert records[0][AUTHORITY_SCOPE_KEY] == FUNCTION_UNARY
    assert records[1][COMPARISON_AUTHORITY_KEY] == cmp.c.digest
    assert records[2][COMPARISON_AUTHORITY_KEY] == cmp.a.digest
    store_comparison_evidence(analysis, [*records, {"proof_obligation_id": ("outside",)}])
    assert analysis.completed_recovery_proof_evidence[-1][COMPARISON_AUTHORITY_KEY] == OUTSIDE_COMPARISON


def test_merging_keeps_records_of_the_same_proof_from_different_comparisons():
    cmp = _comparisons()
    from_a = bind_evidence_to_comparison({"proof_obligation_id": ("p",)}, cmp.a)
    from_c = bind_evidence_to_comparison({"proof_obligation_id": ["p"]}, cmp.c)
    merged = merge_new_evidence((from_a,), (from_c, dict(from_a)))
    assert [record[COMPARISON_AUTHORITY_KEY] for record in merged] == [cmp.a.digest, cmp.c.digest]
    assert merge_new_evidence(merged, (from_c,)) is None

    analysis = SimpleNamespace(completed_recovery_proof_evidence=(from_a,))
    checker = SimpleNamespace(enable_completed_recovery_proofs=True)
    result = SimpleNamespace(completed_recovery_proof_evidence=[
        {"side": "function1", "evidence": from_c},
        {"side": "function1", "evidence": from_a},
    ])
    RecoveryProofMixin._merge_completed_recovery_proofs_from_result(checker, analysis, analysis, result)
    assert [record[COMPARISON_AUTHORITY_KEY] for record in analysis.completed_recovery_proof_evidence] == [
        cmp.a.digest, cmp.c.digest,
    ]


# ---- obligation runtime: 1 つの runtime は 1 つの比較に仕える ------------------------------


def _requirement(name):
    return ProofRequirementId.create(
        "value_relation", ("pair_query", name), ProofRequirementContract(proposition=name),
    )


def _reason(requirement):
    return SimpleNamespace(
        reason_id="readonly_identity_missing", recovery_proof_kind="", stage="S_PAIRWISE",
        proof_requirement_ids=(requirement.to_dict(),), pair_or_case=None, object_target_key=None,
    )


def _runtime(pair):
    return ObligationRuntimeSession.create(*pair)


def _prove(runtime, comparison, requirement, reason, *, with_artifact):
    with comparison_scope(comparison):
        runtime.plan_proof_gates(
            SimpleNamespace(unknown_reasons=[reason]), {},
            lambda *_args: lambda: FunctionProofOutcome.EQUIVALENT,
        )
        while runtime.run_next()[0] is not None:
            pass
        if with_artifact:
            runtime.apply_completed_evidence(({"evidence": bind_evidence_to_comparison({
                "proof_requirement_id": requirement.to_dict(), "status": "complete", "proof_source": "test",
            })},))
        return runtime.outcome_for_reason(reason)


@pytest.mark.parametrize("other", ["b", "c"])
def test_an_artifact_of_another_comparison_never_validates_this_comparisons_requirement(other):
    cmp = _comparisons()
    requirement = _requirement("r")
    runtime = _runtime(cmp.pair_a)
    assert _prove(runtime, getattr(cmp, other), requirement, _reason(requirement), with_artifact=True) == (
        FunctionProofOutcome.EQUIVALENT
    )
    # A は同じ requirement R を使うが、A に束縛された artifact を持たない。
    with comparison_scope(cmp.a), pytest.raises(ComparisonRuntimeMismatch):
        runtime.outcome_for_reason(_reason(requirement))
    with pytest.raises(ComparisonRuntimeMismatch):
        _prove(runtime, cmp.a, requirement, _reason(requirement), with_artifact=False)
    # A は自分の runtime を使い、B / C の artifact を見ない。
    assert _prove(_runtime(cmp.pair_a), cmp.a, requirement, _reason(requirement), with_artifact=False) == (
        FunctionProofOutcome.INCONCLUSIVE
    )


def test_a_rescheduled_dependent_runs_only_its_own_comparisons_producer():
    cmp = _comparisons()
    runtime = _runtime(cmp.pair_a)
    gate, dependent = _requirement("gate"), _requirement("dependent")
    ran = []
    with comparison_scope(cmp.a):
        runtime.schedule(dependent, "value_relation", lambda: ran.append("A"), depends_on=(gate,))
        while runtime.run_next()[0] is not None:
            pass
    for other in (cmp.b, cmp.c):
        with comparison_scope(other), pytest.raises(ComparisonRuntimeMismatch):
            runtime.schedule(dependent, "value_relation", lambda: ran.append("other"), depends_on=(gate,))
    ran.clear()
    with comparison_scope(cmp.a):
        runtime.proof_outcomes[gate.to_key()] = FunctionProofOutcome.EQUIVALENT
        runtime.apply_completed_evidence(({"evidence": bind_evidence_to_comparison({
            "proof_requirement_id": gate.to_dict(), "status": "complete", "proof_source": "test",
        })},))
    while runtime.run_next()[0] is not None:
        pass
    assert ran == ["A"]


def test_replanners_and_cached_results_are_not_shared_across_comparisons():
    cmp = _comparisons()
    runtime = _runtime(cmp.pair_a)
    planned = []

    def replanner(label):
        def replan(*_args):
            planned.append((label, current_comparison()))
            return _requirement(f"replanned-{label}"), "value_relation", lambda: None
        return replan

    with comparison_scope(cmp.a):
        runtime.register_pair_query_replanner("(0,0)", "value_relation", replanner("A"))
        assert runtime.execute(_requirement("cached"), "value_relation", lambda: "result-of-A") == "result-of-A"
    for other in (cmp.b, cmp.c):
        with comparison_scope(other):
            for use in (
                lambda: runtime.register_pair_query_replanner("(0,0)", "value_relation", replanner("other")),
                lambda: runtime.register_target_query_replanner(("target",), replanner("other")),
                lambda: runtime.register_counterexample_safety_replanner("(0,0)", replanner("other")),
                lambda: runtime.execute(_requirement("cached"), "value_relation", lambda: "result-of-other"),
                lambda: runtime.plan_proof_gates(SimpleNamespace(unknown_reasons=[]), {}, lambda *_a: None),
                lambda: runtime.apply_completed_evidence(()),
            ):
                with pytest.raises(ComparisonRuntimeMismatch):
                    use()
    # 登録した比較の replanner だけが残り、登録した比較の範囲で計画する。
    with comparison_scope(cmp.b):
        runtime.pair_query_replanners[("(0,0)", "value_relation")]()
    assert planned == [("A", cmp.a)]
    # 別の比較は自分の runtime で自分の結果を得る。
    with comparison_scope(cmp.c):
        assert _runtime(cmp.pair_c).execute(_requirement("cached"), "value_relation", lambda: "result-of-C") == (
            "result-of-C"
        )


def test_deferred_producers_run_in_the_comparison_that_scheduled_them():
    cmp = _comparisons()
    runtime = _runtime(cmp.pair_a)
    seen = []
    with comparison_scope(cmp.a):
        runtime.schedule(_requirement("deferred"), "value_relation", lambda: seen.append(current_comparison()))
    runtime.run_next()  # 比較の外から実行しても、登録した比較の範囲で動く
    assert seen == [cmp.a]


def test_prepare_strategy_runtime_gives_each_comparison_its_own_runtime():
    from scripts.function_tracer_pcode.checker.strategy_execution import prepare_strategy_runtime

    cmp = _comparisons()
    raw_runtime = _runtime(cmp.pair_a)
    same = prepare_strategy_runtime(raw_runtime, None, *cmp.pair_a, cmp.a)
    assert same.runtime is raw_runtime and raw_runtime.comparison_binding == cmp.a
    # 同じ raw pair・同じ relation の別 branch は同じ runtime を共有する。
    assert prepare_strategy_runtime(raw_runtime, None, *cmp.pair_a, comparison_binding_of(*cmp.pair_a)).runtime is (
        raw_runtime
    )
    for other in (cmp.b, cmp.c):
        separate = prepare_strategy_runtime(raw_runtime, None, *cmp.pair_a, other)
        assert separate.runtime is not raw_runtime and separate.store_on_facade is False
        assert separate.runtime.comparison_binding == other
        with pytest.raises(RuntimeError, match="pair_replan_comparison_authority_changed"):
            prepare_strategy_runtime(raw_runtime, object(), *cmp.pair_a, other)
    assert raw_runtime.comparison_binding == cmp.a


def test_branch_gates_use_the_comparison_and_runtime_of_the_result():
    cmp = _comparisons()
    runner_runtime, inner_runtime = _runtime(cmp.pair_a), _runtime(cmp.pair_c)

    def result(comparison, runtime, pair):
        source = SimpleNamespace(analysis1=pair[0], analysis2=pair[1])
        frame = SimpleNamespace(source=source, comparison_binding=comparison, obligation_runtime=runtime)
        return SimpleNamespace(_prepared_dispatch_frame=frame)

    own = branch_comparison(result(cmp.a, runner_runtime, cmp.pair_a), runner_runtime, *cmp.pair_a)
    assert (own.binding, own.runtime, own.analysis1, own.analysis2) == (cmp.a, runner_runtime, *cmp.pair_a)
    # 別の比較の結果は、その比較の runtime と、その比較が比べた pair で扱う（gate の対象も）。
    other = branch_comparison(result(cmp.c, inner_runtime, cmp.pair_c), runner_runtime, *cmp.pair_a)
    assert (other.binding, other.runtime, other.analysis1, other.analysis2) == (cmp.c, inner_runtime, *cmp.pair_c)
    # frame の無い結果は、どの比較の state も読まない別の runtime で扱う。
    frameless = branch_comparison(SimpleNamespace(), runner_runtime, *cmp.pair_a)
    assert frameless.binding is None and frameless.runtime is not runner_runtime
    assert frameless.runtime.comparison_binding is None


@pytest.mark.parametrize("strategy_name", ["pairwise", "monolithic"])
def test_a_prepared_strategy_refuses_to_run_outside_its_frames_comparison(monkeypatch, strategy_name):
    from scripts.function_tracer_pcode.proof.call_effect import preflight
    from scripts.function_tracer_pcode.proof.strategies.monolithic import MonolithicStrategy
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy

    cmp = _comparisons()
    raw1, raw2 = cmp.pair_a
    frame = SimpleNamespace(
        prepared=SimpleNamespace(analysis1=raw1, analysis2=raw2, input_correspondence=cmp.a.relation),
        comparison_binding=cmp.a,
    )
    monkeypatch.setattr(preflight, "current_dispatch_depth", lambda: 1)
    monkeypatch.setattr(preflight, "consume_prepared_dispatch_frame", lambda *_args: frame)
    strategy = {"pairwise": PairwiseStrategy, "monolithic": MonolithicStrategy}[strategy_name](
        Mock(), Mock(), debug=False,
    )
    for scope in (None, cmp.b, cmp.c):
        with comparison_scope(scope), pytest.raises(RuntimeError, match="comparison_authority_scope_mismatch"):
            strategy.check(raw1, raw2)


def test_run_strategy_branch_runs_the_strategy_in_the_frames_comparison():
    from scripts.function_tracer_pcode.checker import strategy_execution as se
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy

    cmp = _comparisons()
    seen = []
    strategy = Mock(spec=PairwiseStrategy)
    strategy.check.side_effect = lambda *_args: seen.append(current_comparison()) or SimpleNamespace(
        is_equivalent=None, comparison_execution_receipt=None,
    )
    frame = SimpleNamespace(
        obligation_runtime=None, replan_successor_plan=None, pair_disposition_ledger=None, receipt=None,
        cleanup_complete=False, close=Mock(), comparison_binding=cmp.a,
    )
    ctx = SimpleNamespace(strategy=strategy, replan_plan=None, branch_id="S_PAIRWISE")
    with patch.object(se, "push_prepared_dispatch_frame", return_value="token"), \
         patch.object(se, "close_prepared_dispatch_frame", return_value=True), \
         patch.object(se, "diagnostic_projection", side_effect=lambda manifest, _frame: dict(manifest)):
        se.run_strategy_branch(
            ctx, frame, SimpleNamespace(), "a1", "a2", False,
            locally_issued_branch_authority=None, call_effect_shadow_manifest={},
            debug_print=lambda _message: None, apply_preflight_final_gate=Mock(),
        )
    assert seen == [cmp.a]
    assert current_comparison() is None


def test_a_producer_validated_closure_is_sealed_to_its_ledgers_comparison():
    from scripts.function_tracer_pcode.proof.obligations import pair_disposition
    from scripts.function_tracer_pcode.proof.obligations.pair_disposition import (
        PairLedgerBinding,
        ReadonlyIdentityClosureArtifact,
    )

    cmp = _comparisons()

    def ledger(comparison):
        return PairLedgerBinding(
            "session", "S_PAIRWISE", "surface", "projection", 1, ("view",), "premise", 1, comparison.digest,
        )

    ledger_a = ledger(cmp.a)
    digest = hashlib.sha256(b"x").hexdigest()
    payload = (
        ReadonlyIdentityClosureArtifact.PRODUCER_KIND, digest, digest, ledger_a.derived_view_id,
        ledger_a.premise_digest, ledger_a.graph_generation, ledger_a.comparison_authority_digest,
        "validated", ReadonlyIdentityClosureArtifact.schema_version,
    )
    artifact = ReadonlyIdentityClosureArtifact(
        digest, digest, ledger_a.derived_view_id, ledger_a.premise_digest, ledger_a.graph_generation,
        ledger_a.comparison_authority_digest, pair_disposition._closure_artifact_seal(payload),
    )
    assert artifact.validates(ledger_a) is True
    for other in (cmp.b, cmp.c):
        assert artifact.validates(ledger(other)) is False
        relabelled = dataclasses.replace(artifact, comparison_authority_digest=other.digest)
        assert relabelled.validates(ledger(other)) is False


def test_a_pair_ledger_of_another_comparison_cannot_open_in_this_runtime():
    from scripts.function_tracer_pcode.proof.obligations.pair_disposition import PairLedgerBinding

    cmp = _comparisons()
    runtime = _runtime(cmp.pair_a)
    runtime.claim_comparison(cmp.a)
    binding = PairLedgerBinding(
        "session", "S_PAIRWISE", "surface", "projection", 1,
        runtime.current_view.view_id, runtime.premise_digest, 1, cmp.c.digest,
    )
    with comparison_scope(cmp.a), pytest.raises(ComparisonRuntimeMismatch):
        runtime.open_pair_ledger(binding, 1)


def test_a_reason_is_answered_only_for_the_object_that_was_planned():
    """``id`` で引く reason の requirement は、計画した同じ object にだけ答える。"""

    cmp = _comparisons()
    runtime = _runtime(cmp.pair_a)
    requirement = _requirement("planned")
    planned = _reason(requirement)
    assert _prove(runtime, cmp.a, requirement, planned, with_artifact=True) == FunctionProofOutcome.EQUIVALENT
    impostor = _reason(requirement)
    # 同じ id を名乗る別 object（id の再利用）を再現する。
    runtime.reason_requirements[id(impostor)] = runtime.reason_requirements[id(planned)]
    with comparison_scope(cmp.a):
        assert runtime.outcome_for_reason(impostor) == FunctionProofOutcome.INCONCLUSIVE
        assert runtime.outcome_for_reason(planned) == FunctionProofOutcome.EQUIVALENT


def test_a_runtime_serving_a_comparison_is_not_read_from_outside_it():
    cmp = _comparisons()
    runtime = _runtime(cmp.pair_a)
    requirement = _requirement("r")
    reason = _reason(requirement)
    assert _prove(runtime, cmp.a, requirement, reason, with_artifact=True) == FunctionProofOutcome.EQUIVALENT
    for read in (
        lambda: runtime.outcome_for_reason(reason),
        lambda: runtime.apply_completed_evidence(()),
        lambda: runtime.plan_proof_gates(SimpleNamespace(unknown_reasons=[]), {}, lambda *_a: None),
    ):
        with pytest.raises(ComparisonRuntimeMismatch):
            read()  # 比較の外
        with comparison_scope(None), pytest.raises(ComparisonRuntimeMismatch):
            read()  # binding の無い範囲


def test_the_comparisons_own_annotations_do_not_change_the_raw_pair_it_compares():
    from scripts.function_tracer_pcode.proof.call_effect.preflight import StrategySourceAnalysisPair
    from scripts.function_tracer_pcode.proof.obligations.snapshot import record_comparison_annotation

    cmp = _comparisons()
    left, right = cmp.pair_a
    source = StrategySourceAnalysisPair.create(left, right)
    record_comparison_annotation(left, "return_case_coverage_gap")
    # 比較が書き戻した観測は、比較対象の raw pair を変えない（同じ比較の branch は共有できる）。
    assert source.comparison_identity_is_current()
    assert comparison_binding_of(left, right) == cmp.a
    # semantic fingerprint には入る（blocker を知らずに作った証明と区別する既存の identity）。
    assert not source.is_unchanged()
    # 登録していない note は比較の観測として書けない。書き換えられた raw pair は別の比較。
    with pytest.raises(ValueError, match="unregistered comparison annotation"):
        record_comparison_annotation(left, "some_other_note")
    left.analysis_notes.append("indirect_control_flow_unresolved")
    assert not source.comparison_identity_is_current()
    assert comparison_binding_of(left, right) != cmp.a


def test_the_runners_runtime_serves_only_comparisons_of_its_own_raw_pair():
    """stage runner の runtime は、先に使った比較ではなく runner 自身の raw pair の比較に仕える。"""

    from scripts.function_tracer_pcode.checker.strategy_execution import prepare_strategy_runtime

    cmp = _comparisons()
    runner_runtime = _runtime(cmp.pair_a)
    runner_runtime.reserve_for_its_raw_pair()
    # 再帰抽象化の抽象 pair の比較（別 raw pair）が先に facade の runtime に来ても使わせない。
    abstract = prepare_strategy_runtime(runner_runtime, None, *cmp.pair_c, cmp.c)
    assert abstract.runtime is not runner_runtime and runner_runtime.comparison_binding is None
    # runner 自身の raw pair の比較だけが使う（同じ raw pair・別 relation は別の比較）。
    assert prepare_strategy_runtime(runner_runtime, None, *cmp.pair_a, cmp.a).runtime is runner_runtime
    assert prepare_strategy_runtime(runner_runtime, None, *cmp.pair_a, cmp.b).runtime is not runner_runtime
    # 予約していない runtime（recurrence promotion が後継の比較に渡すもの）は、最初の比較に仕える。
    handed_over = _runtime(cmp.pair_a)
    assert prepare_strategy_runtime(handed_over, None, *cmp.pair_c, cmp.c).runtime is handed_over

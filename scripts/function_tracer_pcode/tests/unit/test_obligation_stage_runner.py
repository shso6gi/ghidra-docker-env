from types import SimpleNamespace
from unittest.mock import Mock

from scripts.function_tracer_pcode.equivalence.checker import (
    EquivalenceChecker,
    StageID,
    StageSpec,
)
from scripts.function_tracer_pcode.equivalence.obligations import (
    ActivationState,
    ShadowComparisonReport,
    SolverOutcomeClass,
    ProductionShadowValidator,
    project_proof_gates,
    PairLedgerBinding,
)
from scripts.function_tracer_pcode.equivalence.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
)
from scripts.function_tracer_pcode.equivalence.obligations.stage_runner import (
    merge_stage_debug_statistics,
)


def _result(value, reasons=()):
    return SimpleNamespace(
        is_equivalent=value,
        stage_path=[],
        unknown_reasons=list(reasons),
        error_message=None,
        pairwise_debug_stats={},
        root_blockers=[],
        counterexample=None,
        is_timeout=lambda: False,
    )


def test_stage_debug_statistics_project_only_terminal_dispositions() -> None:
    accumulated = {}
    pairwise = _result(None)
    pairwise.pairwise_stats = {
        "total_pairs": 4,
        "unsat_pairs": 3,
        "sat_pairs": 0,
        "unknown_pairs": 1,
        "error_pairs": 0,
    }
    pairwise.pairwise_debug_stats = {
        "unsat_results": 3,
        "sat_results": 0,
        "unknown_results": 1,
    }
    merge_stage_debug_statistics(accumulated, pairwise)

    monolithic = _result(False)
    monolithic.pairwise_stats = {
        "total_pairs": 4,
        "unsat_pairs": 3,
        "sat_pairs": 1,
        "unknown_pairs": 0,
        "error_pairs": 0,
    }
    monolithic.pairwise_debug_stats = {
        "monolithic_split_planned_regions": 4,
    }
    merge_stage_debug_statistics(accumulated, monolithic)

    assert monolithic.pairwise_debug_stats["unsat_results"] == 3
    assert monolithic.pairwise_debug_stats["sat_results"] == 1
    assert monolithic.pairwise_debug_stats["unknown_results"] == 0
    assert monolithic.pairwise_debug_stats["stage_attempt_unsat_results"] == 3
    assert monolithic.pairwise_debug_stats["stage_attempt_sat_results"] == 0
    assert monolithic.pairwise_debug_stats["stage_attempt_unknown_results"] == 1


def _analysis(binary_id):
    return SimpleNamespace(
        binary_id=binary_id,
        function_ref=None,
        function_name="f",
        entry_point="0x1000",
        analysis_view_identity=None,
        partition_revision=0,
        get_equivalence_blocking_unsafety_reasons=lambda: (),
    )


def _checker(results):
    checker = object.__new__(EquivalenceChecker)
    checker.stage_plan = [
        StageSpec(StageID.S_PAIRWISE, "pairwise", "pairwise"),
        StageSpec(StageID.S_MONOLITHIC_FALLBACK, "monolithic", "monolithic"),
    ]
    checker.pairwise_strategy = object()
    checker.monolithic_strategy = object()
    checker.loop_template_strategy = object()
    checker.check = Mock(side_effect=results)
    checker._debug_print = Mock()
    checker._merge_completed_recovery_proofs_from_result = Mock()
    checker._should_skip_monolithic_fallback = Mock(return_value=False)
    return checker


def _run(checker, method_name):
    return getattr(checker, method_name)(
        _analysis("B1"), _analysis("B2"), "B1", "B2", False,
        None, 0, None, None,
    )


def test_obligation_runner_short_circuits_after_pairwise_not_eq():
    checker = _checker([_result(False)])
    result = _run(checker, "_run_stage_plan")
    assert result.is_equivalent is False
    assert checker.check.call_count == 1
    assert checker._last_obligation_branch_trace.records[-1].activation_state == ActivationState.SHORT_CIRCUITED


def test_timeout_contradiction_cannot_short_circuit_as_equivalent() -> None:
    stale = _result(True)
    stale.is_timeout = lambda: True
    recovered = _result(True)
    checker = _checker([stale, recovered])

    result = _run(checker, "_run_stage_plan")

    assert checker.check.call_count == 2
    assert stale.is_equivalent is None
    assert stale.pairwise_debug_stats[
        "timeout_decisive_state_contradiction"
    ] == 1
    assert result.is_equivalent is True
    assert result.stage_path == ["S_PAIRWISE", "S_MONOLITHIC_FALLBACK"]


def test_short_circuit_marks_correct_later_branch_when_an_earlier_branch_was_inapplicable():
    checker = _checker([_result(False)])
    checker.stage_plan.insert(
        0,
        StageSpec(StageID.S_LOOP_TEMPLATE_ABSTRACTION, "loop", "loop_template_pairwise"),
    )
    checker._should_try_loop_template_stage = Mock(return_value=False)
    _run(checker, "_run_stage_plan")
    records = checker._last_obligation_branch_trace.records
    assert [record.branch_id for record in records] == [
        "S_LOOP_TEMPLATE_ABSTRACTION",
        "S_PAIRWISE",
        "S_MONOLITHIC_FALLBACK",
    ]
    assert records[-1].activation_state == ActivationState.SHORT_CIRCUITED


def test_proof_gate_projection_adapts_existing_recovery_kinds():
    reasons = [
        SimpleNamespace(
            recovery_proof_kind="return_coverage_completion",
            reason_id="return_coverage_gap",
        ),
        SimpleNamespace(
            recovery_proof_kind="call_effect_summary_proof",
            reason_id="equivalence_blocking_unsafety",
        ),
    ]
    gates = project_proof_gates(_result(None, reasons))
    assert [(gate.gate_kind, gate.outcome) for gate in gates] == [
        ("call_effect", "inconclusive"),
        ("return_coverage", "inconclusive"),
    ]


def test_final_inconclusive_result_has_no_terminal_proof_branch():
    checker = _checker([_result(None), _result(None)])
    result = _run(checker, "_run_stage_plan")
    assert result.is_equivalent is None
    assert checker._last_obligation_branch_trace.terminal_branch is None
    assert checker._last_obligation_branch_trace.policy_version == "obligation-sequential-v1"


def test_monolithic_applicability_gate_is_recorded_as_inapplicable():
    checker = _checker([_result(None)])
    checker.stage_plan.insert(
        1,
        StageSpec(StageID.S_ABSTRACT_RECURSIVE_SUMMARY, "recursive", "abstract_pairwise"),
    )
    checker._run_recursive_abstraction_stage = Mock(return_value=None)
    checker._should_skip_monolithic_fallback = Mock(return_value=True)
    result = _run(checker, "_run_stage_plan")
    assert result.is_equivalent is None
    records = checker._last_obligation_branch_trace.records
    assert records[-1].branch_id == "S_MONOLITHIC_FALLBACK"
    assert records[-1].activation_state == ActivationState.INAPPLICABLE


def test_monolithic_only_inapplicable_plan_returns_typed_unknown() -> None:
    checker = _checker([])
    checker.stage_plan = [
        StageSpec(StageID.S_MONOLITHIC_FALLBACK, "monolithic", "monolithic")
    ]
    checker._should_skip_monolithic_fallback = Mock(return_value=True)

    result = _run(checker, "_run_stage_plan")

    assert result.is_equivalent is None
    assert result.error_message is None
    assert result.unknown_reasons[0].evidence_refs[0] == "monolithic_branch_inapplicable"


def test_shadow_compares_proof_actions_not_only_reason_labels():
    left = _result(None)
    right = _result(None)
    left.unknown_recovery_actions = [SimpleNamespace(to_dict=lambda: {"status": "pending"})]
    right.unknown_recovery_actions = [SimpleNamespace(to_dict=lambda: {"status": "complete"})]
    left.completed_recovery_proof_evidence = []
    right.completed_recovery_proof_evidence = []
    left.debug_trace = None
    right.debug_trace = None
    comparison = ShadowComparisonReport.compare(left, right)
    assert not comparison.compatible
    assert comparison.differences == ("proof_action_surface",)


def test_shadow_ignores_raw_model_identity_for_same_decisive_projection():
    left = _result(False)
    right = _result(False)
    left.solver_status = "SAT"
    right.solver_status = "SAT"
    left.counterexample = {
        "model": {"x": 1},
        "normalized_observable_projection": ("return", 7),
        "replay_outcome": "safe_decisive",
    }
    right.counterexample = {
        "model": {"x": 99},
        "normalized_observable_projection": ("return", 7),
        "replay_outcome": "safe_decisive",
    }

    comparison = ShadowComparisonReport.compare(left, right)

    assert comparison.compatible
    assert comparison.legacy.decisiveness_surface.outcome_class == (
        SolverOutcomeClass.SAT_DECISIVE_NOT_EQ.value
    )


def test_shadow_rejects_decisive_to_inconclusive_sat_transition():
    decisive = _result(False)
    inconclusive = _result(None)
    decisive.solver_status = "SAT"
    inconclusive.solver_status = "SAT"
    decisive.counterexample = {
        "normalized_observable_projection": ("return", 7),
        "replay_outcome": "safe_decisive",
    }
    inconclusive.counterexample = {
        "normalized_observable_projection": ("return", 7),
        "replay_outcome": "unsafe_inconclusive",
    }

    comparison = ShadowComparisonReport.compare(decisive, inconclusive)

    assert not comparison.compatible
    assert "decisiveness_surface" in comparison.differences


def test_checker_deduplicates_unary_width_completion_across_retries():
    checker = object.__new__(EquivalenceChecker)
    checker.enable_completed_recovery_proofs = True
    requirement = ProofRequirementId.create(
        "unary_return_width_relation",
        ("return-member", 1),
        ProofRequirementContract("return width relation"),
    ).to_dict()
    evidence = {
        "proof_requirement_id": requirement,
        "proof_status": "verified",
        "proof_artifact_ref": ("width-artifact", 1),
    }
    left = SimpleNamespace(
        function_name="f",
        binary_id="B1",
        completed_recovery_proof_evidence=(evidence,),
    )
    right = SimpleNamespace(
        function_name="f",
        binary_id="B2",
        completed_recovery_proof_evidence=(),
    )
    duplicate = {
        "side": "function1",
        "function_name": "f",
        "binary_name": "B1",
        "binary_id": "B1",
        "evidence": dict(evidence),
    }

    payload = checker._completed_recovery_proof_payload(
        left,
        right,
        "B1",
        "B2",
        extra_records=(duplicate, duplicate),
    )

    assert len(payload) == 1


def test_production_gate_producer_and_aggregator_close_unknown_to_eq():
    requirement = ProofRequirementId.create(
        "return_coverage_completion",
        ("coverage", "f"),
        ProofRequirementContract("return coverage complete"),
    )
    reason = SimpleNamespace(
        reason_id="return_coverage_gap",
        recovery_proof_kind="return_coverage_completion",
        proof_requirement_ids=(requirement.to_dict(),),
        object_target_key=("coverage", "f"),
        pair_or_case=None,
        stage="S_PAIRWISE",
    )
    result = _result(None, (reason,))
    result.pairwise_stats = {
        "total_pairs": 1,
        "unsat_pairs": 1,
        "sat_pairs": 0,
        "unknown_pairs": 0,
        "error_pairs": 0,
    }
    result.decision_gated_by_pending_proof = True
    result.completed_recovery_proof_evidence = [{
        "evidence": {
            "proof_requirement_id": requirement.to_dict(),
            "status": "complete",
            "proof_source": "coverage_test_producer",
        },
    }]
    strategy = SimpleNamespace(
        _return_coverage_proof_is_complete=lambda *_args: True,
        _call_effect_summary_proof_is_complete=lambda *_args: False,
        _recovery_proof_is_complete=lambda *_args: False,
    )
    checker = _checker([result])
    checker.stage_plan = [StageSpec(StageID.S_PAIRWISE, "pairwise", "pairwise")]
    checker.pairwise_strategy = strategy

    final = _run(checker, "_run_stage_plan")

    assert final.is_equivalent is True
    assert final.unknown_reasons == []
    runtime = checker._obligation_runtime_session
    assert runtime.artifacts[0].requirement_id == requirement
    assert any(event.kind == "return_coverage" for event in runtime.events)


def test_completed_proof_replans_pairwise_on_successor_view_and_ledger():
    requirement = ProofRequirementId.create(
        "return_coverage_completion",
        ("coverage", "f"),
        ProofRequirementContract("return coverage complete"),
    )
    reason = SimpleNamespace(
        reason_id="return_coverage_gap",
        recovery_proof_kind="return_coverage_completion",
        proof_requirement_ids=(requirement.to_dict(),),
        object_target_key=("coverage", "f"),
        pair_or_case="(0,0)",
        stage="S_PAIRWISE",
    )
    first = _result(None, (reason,))
    first.completed_recovery_proof_evidence = [{
        "evidence": {
            "proof_requirement_id": requirement.to_dict(),
            "status": "complete",
            "proof_source": "coverage_test_producer",
        },
    }]
    second = _result(True)
    second.completed_recovery_proof_evidence = []
    strategy = SimpleNamespace(
        _return_coverage_proof_is_complete=lambda *_args: True,
        _call_effect_summary_proof_is_complete=lambda *_args: False,
        _recovery_proof_is_complete=lambda *_args: False,
    )
    checker = _checker([])
    checker.stage_plan = [StageSpec(StageID.S_PAIRWISE, "pairwise", "pairwise")]
    checker.pairwise_strategy = strategy
    calls = []
    replanned_ledgers = []

    def execute(*_args, **_kwargs):
        runtime = checker._obligation_runtime_session
        calls.append(runtime.current_view.view_id)
        if len(calls) == 1:
            binding = PairLedgerBinding(
                "session", "S_PAIRWISE", "surface", "projection", 1,
                runtime.current_view.view_id, runtime.premise_digest, 1,
            )
            ledger = runtime.open_pair_ledger(binding, 1)
            first._prepared_dispatch_frame = SimpleNamespace(
                pair_disposition_ledger=ledger
            )
            return first
        successor_plan = runtime.pair_ledger_manager.pending_successor
        assert successor_plan is not None
        assert checker._active_pair_replan_plan is successor_plan
        replacement_binding = PairLedgerBinding(
            successor_plan.comparison_session_id,
            successor_plan.branch_id,
            "new-surface",
            "new-projection",
            2,
            successor_plan.derived_view_id,
            successor_plan.premise_digest,
            2,
        )
        replanned_ledgers.append(
            runtime.open_pair_ledger(
                replacement_binding,
                2,
            )
        )
        return second

    checker.check = Mock(side_effect=execute)

    final = _run(checker, "_run_stage_plan")

    runtime = checker._obligation_runtime_session
    assert final.is_equivalent is True
    assert len(calls) == 2
    assert replanned_ledgers == [runtime.pair_ledger_manager.current]
    assert calls[0] != calls[1]
    assert runtime.pair_ledger_manager.history
    assert runtime.pair_ledger_manager.history[0].binding.derived_view_id == calls[0]
    assert any(
        event.event == "pair_ledger_replan_required"
        for event in runtime.events
    )


def test_production_shadow_validator_runs_final_workflows_and_hashes_surfaces():
    def finalized():
        result = _result(True)
        result.unknown_recovery_actions = []
        result.completed_recovery_proof_evidence = []
        result.debug_trace = None
        result.to_dict = lambda: {
            "is_equivalent": True,
            "stage_path": tuple(result.stage_path),
        }
        return result

    report = ProductionShadowValidator.run(finalized, finalized)
    assert report.comparison.compatible
    assert report.legacy_surface_hash == report.obligation_surface_hash

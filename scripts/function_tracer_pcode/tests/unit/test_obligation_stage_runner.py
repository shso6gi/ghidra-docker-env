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
    ProductionShadowValidator,
    project_proof_gates,
)
from scripts.function_tracer_pcode.equivalence.cause_identity import (
    ProofRequirementContract,
    ProofRequirementId,
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


def _analysis(binary_id):
    return SimpleNamespace(
        binary_id=binary_id,
        function_ref=None,
        function_name="f",
        entry_point="0x1000",
        analysis_view_identity=None,
        partition_revision=0,
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


def test_obligation_runner_matches_legacy_pairwise_unknown_monolithic_eq():
    legacy_checker = _checker([_result(None), _result(True)])
    first = _result(None)
    first.call_effect_shadow_manifest = {"mode": "typed_relational_call_effect_proof"}
    second = _result(True)
    second.call_effect_shadow_manifest = None
    obligation_checker = _checker([first, second])
    legacy = _run(legacy_checker, "_run_stage_plan_legacy")
    obligation = _run(obligation_checker, "_run_stage_plan")
    comparison = ShadowComparisonReport.compare(legacy, obligation)
    assert comparison.compatible, comparison.differences
    assert obligation_checker._last_obligation_branch_trace.terminal_branch == "S_MONOLITHIC_FALLBACK"
    assert obligation.call_effect_shadow_manifest == first.call_effect_shadow_manifest
    assert [record.activation_state for record in obligation_checker._last_obligation_branch_trace.records] == [
        ActivationState.COMPLETED,
        ActivationState.COMPLETED,
    ]


def test_obligation_runner_short_circuits_after_pairwise_not_eq():
    checker = _checker([_result(False)])
    result = _run(checker, "_run_stage_plan")
    assert result.is_equivalent is False
    assert checker.check.call_count == 1
    assert checker._last_obligation_branch_trace.records[-1].activation_state == ActivationState.SHORT_CIRCUITED


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
        _return_width_bridge_proof_is_complete=lambda *_args: False,
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

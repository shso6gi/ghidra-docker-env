from dataclasses import replace

import pytest

from scripts.function_tracer_pcode.equivalence.v2.call_effect import (
    CALL_EFFECT_REASON_REGISTRY,
    CALL_EFFECT_REASON_SPECS,
    CALL_EFFECT_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.equivalence.v2.contracts import (
    CauseOccurrence,
    CauseOccurrenceAuthority,
    ProofRequirement,
    authority_digest,
)
from scripts.function_tracer_pcode.equivalence.v2.loop_recurrence import (
    LOOP_REASON_REGISTRY,
    LOOP_REASON_SPECS,
    LOOP_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.equivalence.v2.reducer import ShadowLifecycleReducer
from scripts.function_tracer_pcode.equivalence.v2.registry import (
    SatisfactionBindingFactory,
    SemanticCauseIdentityFactory,
)
from scripts.function_tracer_pcode.equivalence.v2.stream import (
    CauseObservedEventAuthority,
    EventIntent,
    EventRecorder,
    EventType,
)
from scripts.function_tracer_pcode.equivalence.v2.subordinate_decompilation import (
    EXPECTED_SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY_DIGEST,
    SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY,
    SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY_DIGEST,
    SUBORDINATE_DECOMPILATION_ADAPTER_ROWS,
    SubordinateParentAuthorityError,
    SubordinateParentBinding,
    SubordinateParentBindingRequiredDiagnostic,
    SubordinateParentNotLive,
    SubordinateProcessAssignmentFactory,
    validate_subordinate_adapter_registry,
)
from scripts.function_tracer_pcode.equivalence.v2.operational_extraction import (
    OPERATIONAL_REASON_REGISTRY,
    OPERATIONAL_RECOVERY_REGISTRY,
    OperationalBlockerSignal,
    OperationalCompletionSignal,
    OperationalExtractionPilotEncoder,
)
from scripts.function_tracer_pcode.equivalence.v2.pilot import (
    ProductionDualWritePilotSession,
    ProductionPilotExecutionIdentity,
)
from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
    CompositeProductionSignalEncoder,
    production_signal_scope,
)
from scripts.function_tracer_pcode.analysis.decompilation_broker import (
    LIFECYCLE_HELPER_SOURCE_CONTRACT,
    decompile_function,
)


def _prefix_for(
    row, *, duplicate=False, producer_id=None, domain=None,
    result_occurrence_id="result-1", source_snapshot_fingerprint="snapshot",
):
    if row.parent_registry_id == "call-effect-memory-v2":
        reasons = CALL_EFFECT_REASON_REGISTRY
        recovery = CALL_EFFECT_RECOVERY_REGISTRY
        spec = CALL_EFFECT_REASON_SPECS[row.parent_reason_id]
    else:
        reasons = LOOP_REASON_REGISTRY
        recovery = LOOP_RECOVERY_REGISTRY
        spec = LOOP_REASON_SPECS[row.parent_reason_id]
    if domain is not None:
        from scripts.function_tracer_pcode.equivalence.v2.registry import SealedReasonRegistry
        reasons = SealedReasonRegistry.build((
            replace(reasons.get(row.parent_reason_id), domain=domain),
        ))
    definition = recovery.get(spec.contract_definition_id, 1)
    bindings = {}
    for slot in definition.requirement_slots:
        proof_kind = (
            row.parent_proof_kind
            if row.parent_proof_kind in slot.allowed_proof_kinds
            else sorted(slot.allowed_proof_kinds)[0]
        )
        requirement_id = (
            "q-" + row.adapter_id
            if proof_kind == row.parent_proof_kind
            else "q-" + row.adapter_id + "-" + slot.name
        )
        bindings[slot.name] = ProofRequirement(
            requirement_id, proof_kind,
            ("subordinate-target", row.adapter_id, slot.name),
        )
    bound = SatisfactionBindingFactory(recovery).bind(
        contract_definition_id=definition.contract_definition_id,
        contract_version=definition.contract_version,
        bindings=bindings,
    )
    cause = SemanticCauseIdentityFactory(reasons).create(
        reason_id=row.parent_reason_id,
        identity_scope=spec.identity_scope,
        target_kind=spec.target_kind,
        canonical_target_key=("subordinate", row.adapter_id),
        missing_semantic_fact=("missing", row.parent_proof_kind),
        semantic_proposition=("requires", row.parent_proof_kind),
        observation_surface=("source", row.source_contract_id),
        active_semantic_precondition=("live", True),
        correspondence_contract=("exact",),
    )
    occurrence = CauseOccurrence(
        "occ-" + row.adapter_id, cause, row.parent_reason_id,
        "target-" + row.adapter_id, spec.target_kind, spec.identity_scope,
        definition.contract_definition_id, definition.contract_version,
        definition.normalized_expression_digest, bound.bound_expression_digest,
        tuple(sorted(bound.requirement_ids())), ("typed-evidence",), "typed",
        source_snapshot_fingerprint,
        producer_id or row.parent_producer_contract_ids[0], "attempt-1",
    )
    authority = CauseOccurrenceAuthority(occurrence, bound)
    recorder = EventRecorder(
        stream_id="stream-" + row.adapter_id,
        result_occurrence_id=result_occurrence_id,
        source_snapshot_fingerprint=source_snapshot_fingerprint,
    )
    recorder.append(EventIntent(
        EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)
    ))
    if duplicate:
        duplicate_occurrence = replace(
            occurrence,
            occurrence_id=occurrence.occurrence_id + "-duplicate",
            attempt_id="attempt-2",
        )
        recorder.append(EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(CauseOccurrenceAuthority(duplicate_occurrence, bound)),
        ))
    prefix = recorder.prefix_view()
    projection = ShadowLifecycleReducer(
        reason_registry=reasons, recovery_registry=recovery,
    ).replay_prefix(prefix)
    return projection, prefix


def test_subordinate_adapter_registry_is_exact_and_digest_pinned():
    from scripts.function_tracer_pcode.equivalence.v2 import execution_authority

    validate_subordinate_adapter_registry()
    assert not hasattr(
        execution_authority, "issue_subordinate_process_requirement_assignment"
    )
    assert len(SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY) == 6
    assert tuple(row.terminal_priority for row in SUBORDINATE_DECOMPILATION_ADAPTER_ROWS) == tuple(range(191, 197))
    assert SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY_DIGEST == EXPECTED_SUBORDINATE_DECOMPILATION_ADAPTER_REGISTRY_DIGEST


@pytest.mark.parametrize("row", SUBORDINATE_DECOMPILATION_ADAPTER_ROWS)
def test_each_adapter_joins_one_exact_live_parent_requirement(row):
    projection, prefix = _prefix_for(row)
    factory = SubordinateProcessAssignmentFactory("result-1")
    receipt = factory.issue_for_source(
        projection, prefix, row.source_contract_id
    )
    receipt.validate_against(projection, prefix=prefix, factory=factory)
    assert receipt.adapter_id == row.adapter_id
    assert receipt.parent_reason_id == row.parent_reason_id
    assert receipt.parent_proof_kind == row.parent_proof_kind
    assert receipt.proof_requirement_id == "q-" + row.adapter_id


def test_adapter_rejects_missing_wrong_source_and_cross_result():
    row = SUBORDINATE_DECOMPILATION_ADAPTER_ROWS[0]
    projection, prefix = _prefix_for(row)
    factory = SubordinateProcessAssignmentFactory("result-1")
    with pytest.raises(SubordinateParentAuthorityError) as exc_info:
        factory.issue_for_source(projection, prefix, "unknown-source")
    diagnostic = exc_info.value.diagnostic
    assert diagnostic.diagnostic_kind == "SUBORDINATE_ADAPTER_ROW_MISSING"
    assert diagnostic.adapter_row_count == 0
    assert diagnostic.parent_proof_kind_match_q_count == 0
    assert diagnostic.c_q_candidate_count == 0
    assert diagnostic.prefix_chain_digest == prefix.prefix_chain_digest
    assert diagnostic.projection_digest == projection.prefix_projection_digest
    assert diagnostic.diagnostic_digest in str(exc_info.value)
    with pytest.raises(ValueError, match="another result"):
        SubordinateProcessAssignmentFactory("result-2").issue_for_source(
            projection, prefix, row.source_contract_id
        )


def test_adapter_rejects_ambiguous_live_parent_requirements():
    row = SUBORDINATE_DECOMPILATION_ADAPTER_ROWS[0]
    projection, prefix = _prefix_for(row, duplicate=True)
    with pytest.raises(SubordinateParentAuthorityError) as exc_info:
        SubordinateProcessAssignmentFactory("result-1").issue_for_source(
            projection, prefix, row.source_contract_id
        )
    diagnostic = exc_info.value.diagnostic
    assert diagnostic.diagnostic_kind == "PARENT_C_Q_AMBIGUOUS"
    assert diagnostic.parent_proof_kind_match_q_count == 2
    assert diagnostic.binding_match_q_count == 2
    assert diagnostic.c_q_candidate_count == 2
    assert len(diagnostic.occurrence_ids) == 2
    assert diagnostic.parent_producers == row.parent_producer_contract_ids


def test_adapter_requires_and_honors_exact_parent_binding_when_candidates_are_valid():
    row = SUBORDINATE_DECOMPILATION_ADAPTER_ROWS[0]
    projection, prefix = _prefix_for(row, duplicate=True)
    q_rows = tuple(
        item for item in projection.q_open_base
        if item.proof_kind == row.parent_proof_kind
    )
    assert len(q_rows) == 2
    q_row = q_rows[0]
    binding = SubordinateParentBinding(
        "result-1",
        q_row.occurrence_id,
        q_row.cause_id,
        q_row.proof_requirement_id,
        q_row.semantic_target_digest,
    )
    factory = SubordinateProcessAssignmentFactory("result-1")
    receipt = factory.issue_for_source(
        projection, prefix, row.source_contract_id,
        parent_binding=binding,
    )
    assert receipt.occurrence_id == q_row.occurrence_id
    assert receipt.proof_requirement_id == q_row.proof_requirement_id
    wrong_binding = replace(
        binding, proof_requirement_id="proof-requirement-not-live"
    )
    with pytest.raises(SubordinateParentAuthorityError) as exc_info:
        factory.issue_for_source(
            projection, prefix, row.source_contract_id,
            parent_binding=wrong_binding,
        )
    assert exc_info.value.diagnostic.diagnostic_kind == (
        "PARENT_C_Q_BINDING_MISMATCH"
    )
    assert exc_info.value.diagnostic.parent_proof_kind_match_q_count == 2
    assert exc_info.value.diagnostic.binding_match_q_count == 0
    assert "requested_parent_binding_not_found" in (
        exc_info.value.diagnostic.mismatch_reasons
    )


def test_assignment_tampering_and_stale_prefix_are_rejected():
    row = SUBORDINATE_DECOMPILATION_ADAPTER_ROWS[0]
    projection, prefix = _prefix_for(row)
    factory = SubordinateProcessAssignmentFactory("result-1")
    receipt = factory.issue_for_source(
        projection, prefix, row.source_contract_id
    )
    with pytest.raises(TypeError, match="exact factory membership"):
        replace(receipt, terminal_priority=999).validate_against(
            projection, prefix=prefix, factory=factory
        )
    with pytest.raises(TypeError, match="exact factory membership"):
        replace(receipt).validate_against(projection, prefix=prefix, factory=factory)
    other, other_prefix = _prefix_for(SUBORDINATE_DECOMPILATION_ADAPTER_ROWS[1])
    with pytest.raises(ValueError):
        receipt.validate_against(other, prefix=other_prefix, factory=factory)


def test_adapter_rejects_wrong_domain_and_unregistered_parent_producer():
    row = SUBORDINATE_DECOMPILATION_ADAPTER_ROWS[0]
    factory = SubordinateProcessAssignmentFactory("result-1")
    with pytest.raises(SubordinateParentAuthorityError) as exc_info:
        wrong_projection, wrong_prefix = _prefix_for(
            row, domain="wrong_parent_domain"
        )
        factory.issue_for_source(
            wrong_projection, wrong_prefix, row.source_contract_id
        )
    assert exc_info.value.diagnostic.diagnostic_kind == (
        "PARENT_C_Q_CONTRACT_MISMATCH"
    )
    assert "parent_domain_mismatch" in exc_info.value.diagnostic.mismatch_reasons
    with pytest.raises(SubordinateParentAuthorityError) as exc_info:
        wrong_projection, wrong_prefix = _prefix_for(
            row, producer_id="caller-invented-producer"
        )
        factory.issue_for_source(
            wrong_projection, wrong_prefix, row.source_contract_id
        )
    assert exc_info.value.diagnostic.diagnostic_kind == (
        "PARENT_C_Q_CONTRACT_MISMATCH"
    )
    assert "parent_producer_mismatch" in exc_info.value.diagnostic.mismatch_reasons


def test_adapter_reports_typed_not_live_parent_diagnostic():
    row = SUBORDINATE_DECOMPILATION_ADAPTER_ROWS[0]
    projection, prefix = _prefix_for(row)
    projection = replace(projection, q_open_base=())
    q_open_base_digest = authority_digest(())
    projection = replace(
        projection,
        q_open_base_digest=q_open_base_digest,
        prefix_projection_digest=authority_digest({
            "finality": "PREFIX",
            "event_stream_prefix_digest": projection.event_stream_prefix_digest,
            "result_occurrence_id": projection.result_occurrence_id,
            "snapshot_digest": projection.snapshot_digest,
            "c_active_base_digest": authority_digest(projection.c_active_base),
            "q_open_base_digest": q_open_base_digest,
            "blocker_eligibility_base_digest": authority_digest(
                projection.blocker_eligibility_base
            ),
            "satisfaction_projection_digest": authority_digest(
                projection.satisfaction_projection
            ),
        }),
    )
    with pytest.raises(SubordinateParentNotLive) as exc_info:
        SubordinateProcessAssignmentFactory("result-1").issue_for_source(
            projection, prefix, row.source_contract_id
        )
    assert exc_info.value.diagnostic.diagnostic_kind == "PARENT_C_Q_NOT_LIVE"
    assert exc_info.value.diagnostic.parent_proof_kind_match_q_count == 0
    assert exc_info.value.diagnostic.c_q_candidate_count == 0


def _broker_session_with_parent(row):
    from scripts.function_tracer_pcode.equivalence.v2.registry import (
        SealedReasonRegistry,
        SealedRecoveryRegistry,
    )
    from scripts.function_tracer_pcode.equivalence.v2.return_outcome import (
        RETURN_OUTCOME_REASON_REGISTRY, RETURN_OUTCOME_RECOVERY_REGISTRY,
    )
    from scripts.function_tracer_pcode.equivalence.v2.sat_safety import (
        SAT_SAFETY_REASON_REGISTRY, SAT_SAFETY_RECOVERY_REGISTRY,
        SatSafetyPilotEncoder,
    )
    from scripts.function_tracer_pcode.equivalence.v2.abi_width_readonly import (
        ABI_WIDTH_READONLY_REASON_REGISTRY,
        ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        SatSafetyBlockerProductionSignal,
    )

    identity = ProductionPilotExecutionIdentity.create({"case": "subordinate-broker"})
    parent_projection, parent_prefix = _prefix_for(
        row,
        result_occurrence_id=identity.result_occurrence_id,
        source_snapshot_fingerprint=identity.source_snapshot_fingerprint,
    )
    parent_reasons = (
        CALL_EFFECT_REASON_REGISTRY
        if row.parent_registry_id == "call-effect-memory-v2"
        else LOOP_REASON_REGISTRY
    )
    parent_recovery = (
        CALL_EFFECT_RECOVERY_REGISTRY
        if row.parent_registry_id == "call-effect-memory-v2"
        else LOOP_RECOVERY_REGISTRY
    )
    reasons = SealedReasonRegistry.build((
        *parent_reasons.snapshot(),
        *OPERATIONAL_REASON_REGISTRY.snapshot(),
        *RETURN_OUTCOME_REASON_REGISTRY.snapshot(),
        *SAT_SAFETY_REASON_REGISTRY.snapshot(),
        *ABI_WIDTH_READONLY_REASON_REGISTRY.snapshot(),
    ))
    recovery = SealedRecoveryRegistry.build((
        *parent_recovery.snapshot(),
        *OPERATIONAL_RECOVERY_REGISTRY.snapshot(),
        *RETURN_OUTCOME_RECOVERY_REGISTRY.snapshot(),
        *SAT_SAFETY_RECOVERY_REGISTRY.snapshot(),
        *ABI_WIDTH_READONLY_RECOVERY_REGISTRY.snapshot(),
    ))
    operational = OperationalExtractionPilotEncoder()
    session = ProductionDualWritePilotSession(
        identity,
        ShadowLifecycleReducer(reason_registry=reasons, recovery_registry=recovery),
        CompositeProductionSignalEncoder({
            OperationalBlockerSignal: operational,
            OperationalCompletionSignal: operational,
            SatSafetyBlockerProductionSignal: SatSafetyPilotEncoder(),
        }),
    )
    event = parent_prefix.events[0]
    session.emit(EventIntent(event.header.event_type, event.authority_payload))
    return session, parent_projection


@pytest.mark.parametrize("row", SUBORDINATE_DECOMPILATION_ADAPTER_ROWS)
def test_subordinate_broker_binds_live_parent_without_completing_it(row):
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_operational_extraction import (
        BrokerAnalyzer, BrokerDecompiler, Function, Program, Result,
    )

    session, _ = _broker_session_with_parent(row)
    manager = type("Manager", (), {"getFunctions": lambda self, forward: iter(())})()
    program = Program(manager)
    function = Function(program=program)
    raw = Result(completed=True, function=function)
    decompiler = BrokerDecompiler(raw)
    analyzer = BrokerAnalyzer(program, decompiler)
    session.domain_signal_state["operational_program_binary_identities"] = {
        id(program): "sha256:binary",
    }
    with production_signal_scope(session):
        observed = decompile_function(
            analyzer, function, 60, None,
            source_contract_id=row.source_contract_id,
            semantic_owner="subordinate",
        )
    assert observed is raw
    assert decompiler.calls == 1
    assert raw.high_call_count == 0
    assert session.domain_signal_error_details == []
    executions = session.domain_signal_state["subordinate_decompilation_executions"]
    assert len(executions) == 1
    assignment, invocation_binding, execution = executions[0]
    assignment_factory = session.domain_signal_state[
        "subordinate_decompilation_assignment_factories"
    ][session.identity.result_occurrence_id]
    assignment_factory.validate_invocation_binding(invocation_binding)
    assignment_factory.validate_execution(execution)
    with pytest.raises(TypeError, match="exact factory membership"):
        assignment_factory.validate_invocation_binding(replace(invocation_binding))
    with pytest.raises(TypeError, match="exact factory membership"):
        assignment_factory.validate_execution(replace(execution))
    assert assignment.adapter_id == row.adapter_id
    assert invocation_binding.proof_requirement_id == assignment.proof_requirement_id
    assert execution.disposition == "COMPLETED"
    projection = session.reducer.replay_prefix(session.recorder.prefix_view())
    assert len(projection.c_active_base) == 1
    assert any(
        item.proof_requirement_id == assignment.proof_requirement_id
        for item in projection.q_open_base
    )
    assert len(session.recorder.prefix_view().events) == 1
    assert session.domain_signal_error_kinds == []


def test_subordinate_broker_parent_authority_failure_blocks_raw_decompile_and_projects_unknown():
    from scripts.function_tracer_pcode.equivalence.v2.contracts import Outcome
    from scripts.function_tracer_pcode.equivalence.v2.pilot import run_dual_write_pilot
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_operational_extraction import (
        BrokerAnalyzer, BrokerDecompiler, Function, Program, Result,
    )

    row = SUBORDINATE_DECOMPILATION_ADAPTER_ROWS[0]
    session, parent_projection = _broker_session_with_parent(row)
    q_row = parent_projection.q_open_base[0]
    tampered_binding = SubordinateParentBinding(
        session.identity.result_occurrence_id,
        q_row.occurrence_id,
        q_row.cause_id,
        q_row.proof_requirement_id + "-tampered",
        q_row.semantic_target_digest,
    )
    manager = type("Manager", (), {"getFunctions": lambda self, forward: iter(())})()
    program = Program(manager)
    function = Function(program=program)
    raw = Result(completed=True, function=function)
    decompiler = BrokerDecompiler(raw)
    analyzer = BrokerAnalyzer(program, decompiler)
    session.domain_signal_state["operational_program_binary_identities"] = {
        id(program): "sha256:binary",
    }
    with production_signal_scope(session):
        observed = decompile_function(
            analyzer, function, 60, None,
            source_contract_id=row.source_contract_id,
            semantic_owner="subordinate",
            parent_binding=tampered_binding,
        )

    assert observed is not raw
    assert not observed.decompileCompleted()
    assert observed.getHighFunction() is None
    assert decompiler.calls == 0
    assert "subordinate_decompilation_executions" not in session.domain_signal_state
    diagnostics = session.domain_signal_state[
        "subordinate_parent_authority_diagnostics"
    ]
    assert len(diagnostics) == 1
    assert diagnostics[0]["diagnostic_kind"] == "PARENT_C_Q_BINDING_MISMATCH"
    assert session.domain_signal_error_details == []

    projection = session.reducer.replay_prefix(session.recorder.prefix_view())
    assert any(
        row.reason_id == "subordinate_parent_authority_unproven"
        for row in projection.c_active_base
    )
    pilot = run_dual_write_pilot(
        legacy_outcome=Outcome.UNKNOWN,
        reducer=session.reducer,
        stream=session.recorder.prefix_view().to_sealed_stream(),
    )
    assert pilot.candidate.decision_receipt.outcome is Outcome.UNKNOWN


def test_subordinate_broker_contract_authority_failure_projects_error_without_raw_decompile(
    monkeypatch,
):
    from scripts.function_tracer_pcode.equivalence.v2.contracts import Outcome
    from scripts.function_tracer_pcode.equivalence.v2.pilot import run_dual_write_pilot
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_operational_extraction import (
        BrokerAnalyzer, BrokerDecompiler, Function, Program, Result,
    )

    row = SUBORDINATE_DECOMPILATION_ADAPTER_ROWS[0]
    wrong_projection, wrong_prefix = _prefix_for(
        row, domain="wrong_parent_domain"
    )
    with pytest.raises(SubordinateParentAuthorityError) as exc_info:
        SubordinateProcessAssignmentFactory("result-1").issue_for_source(
            wrong_projection, wrong_prefix, row.source_contract_id
        )
    authority_error = exc_info.value

    def reject_authority(self, *args, **kwargs):
        raise authority_error

    monkeypatch.setattr(
        SubordinateProcessAssignmentFactory,
        "issue_for_source",
        reject_authority,
    )
    session, _ = _broker_session_with_parent(row)
    manager = type("Manager", (), {"getFunctions": lambda self, forward: iter(())})()
    program = Program(manager)
    function = Function(program=program)
    raw = Result(completed=True, function=function)
    decompiler = BrokerDecompiler(raw)
    analyzer = BrokerAnalyzer(program, decompiler)
    session.domain_signal_state["operational_program_binary_identities"] = {
        id(program): "sha256:binary",
    }
    with production_signal_scope(session):
        observed = decompile_function(
            analyzer, function, 60, None,
            source_contract_id=row.source_contract_id,
            semantic_owner="subordinate",
        )

    assert observed.authority_error_kind == "operational_authority_invalid"
    assert not observed.decompileCompleted()
    assert decompiler.calls == 0
    assert session.domain_signal_error_details == []
    assert session.recorder.prefix_view().events[-1].header.event_type is EventType.ERROR
    pilot = run_dual_write_pilot(
        legacy_outcome=Outcome.UNKNOWN,
        reducer=session.reducer,
        stream=session.recorder.prefix_view().to_sealed_stream(),
    )
    assert pilot.candidate.decision_receipt.outcome is Outcome.ERROR


def test_subordinate_broker_without_live_parent_uses_standalone_operational_owner():
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_operational_extraction import (
        BrokerAnalyzer, BrokerDecompiler, Function, Program, Result,
    )

    row = SUBORDINATE_DECOMPILATION_ADAPTER_ROWS[0]
    session, _ = _broker_session_with_parent(row)
    # Complete the only parent Q before the subordinate invocation.
    authority = session.recorder.prefix_view().events[0].authority_payload.occurrence_authority
    requirement = authority.bound_contract.slot_bindings[0][1]
    from scripts.function_tracer_pcode.equivalence.v2.contracts import RequirementCompletionReceipt
    from scripts.function_tracer_pcode.equivalence.v2.stream import RequirementCompletedEventAuthority
    completion = RequirementCompletionReceipt(
        authority.occurrence.cause_id.value,
        authority.occurrence.occurrence_id,
        requirement.requirement_id,
        authority.bound_contract.contract_definition_id,
        authority.bound_contract.contract_version,
        authority.bound_contract.bound_expression_digest,
        "proof-artifact-no-parent", "applicability-no-parent",
    )
    session.emit(EventIntent(
        EventType.REQUIREMENT_COMPLETED,
        RequirementCompletedEventAuthority(completion),
    ))
    manager = type("Manager", (), {"getFunctions": lambda self, forward: iter(())})()
    program = Program(manager)
    function = Function(program=program)
    raw = Result(completed=True, function=function)
    decompiler = BrokerDecompiler(raw)
    analyzer = BrokerAnalyzer(program, decompiler)
    session.domain_signal_state["operational_program_binary_identities"] = {
        id(program): "sha256:binary",
    }
    with production_signal_scope(session):
        observed = decompile_function(
            analyzer, function, 60, None,
            source_contract_id=LIFECYCLE_HELPER_SOURCE_CONTRACT,
            semantic_owner="subordinate",
        )
    assert observed.decompileCompleted()
    assert decompiler.calls == 1
    assert "subordinate_decompilation_executions" not in session.domain_signal_state
    assert session.domain_signal_error_kinds == []
    projection = session.reducer.replay_prefix(session.recorder.prefix_view())
    assert projection.c_active_base == ()
    assert projection.q_open_base == ()


def test_subordinate_timeout_is_observed_without_parent_completion_or_slice6_event():
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_operational_extraction import (
        BrokerAnalyzer, BrokerDecompiler, Function, Program, Result,
    )

    row = SUBORDINATE_DECOMPILATION_ADAPTER_ROWS[0]
    session, _ = _broker_session_with_parent(row)
    manager = type("Manager", (), {"getFunctions": lambda self, forward: iter(())})()
    program = Program(manager)
    function = Function(program=program)
    raw = Result(timed_out=True, function=function)
    decompiler = BrokerDecompiler(raw)
    analyzer = BrokerAnalyzer(program, decompiler)
    session.domain_signal_state["operational_program_binary_identities"] = {
        id(program): "sha256:binary",
    }
    with production_signal_scope(session):
        observed = decompile_function(
            analyzer, function, 60, None,
            source_contract_id=row.source_contract_id,
            semantic_owner="subordinate",
        )
    assert observed is raw
    execution = session.domain_signal_state[
        "subordinate_decompilation_executions"
    ][0][2]
    assert execution.disposition == "TIMED_OUT"
    assert execution.completed_artifact_digest is None
    projection = session.reducer.replay_prefix(session.recorder.prefix_view())
    assert any(
        item.proof_requirement_id == execution.proof_requirement_id
        for item in projection.q_open_base
    )
    assert len(session.recorder.prefix_view().events) == 1


@pytest.mark.parametrize("parent_live", (True, False))
def test_subordinate_raw_exception_is_exact_and_never_emits_slice6_event(parent_live):
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_operational_extraction import (
        BrokerAnalyzer, Function, Program,
    )
    from scripts.function_tracer_pcode.equivalence.v2.contracts import RequirementCompletionReceipt
    from scripts.function_tracer_pcode.equivalence.v2.stream import RequirementCompletedEventAuthority

    class RaisingDecompiler:
        def __init__(self, error):
            self.error = error
            self.calls = 0

        def decompileFunction(self, function, timeout, monitor):
            self.calls += 1
            raise self.error

    row = SUBORDINATE_DECOMPILATION_ADAPTER_ROWS[0]
    session, _ = _broker_session_with_parent(row)
    expected_events = 1
    if not parent_live:
        authority = session.recorder.prefix_view().events[0].authority_payload.occurrence_authority
        requirement = authority.bound_contract.slot_bindings[0][1]
        completion = RequirementCompletionReceipt(
            authority.occurrence.cause_id.value,
            authority.occurrence.occurrence_id,
            requirement.requirement_id,
            authority.bound_contract.contract_definition_id,
            authority.bound_contract.contract_version,
            authority.bound_contract.bound_expression_digest,
            "proof-artifact-no-parent-exception",
            "applicability-no-parent-exception",
        )
        session.emit(EventIntent(
            EventType.REQUIREMENT_COMPLETED,
            RequirementCompletedEventAuthority(completion),
        ))
        expected_events = 4
    manager = type("Manager", (), {"getFunctions": lambda self, forward: iter(())})()
    program = Program(manager)
    function = Function(program=program)
    error = RuntimeError("raw subordinate decompiler failure")
    decompiler = RaisingDecompiler(error)
    analyzer = BrokerAnalyzer(program, decompiler)
    session.domain_signal_state["operational_program_binary_identities"] = {
        id(program): "sha256:binary",
    }
    with production_signal_scope(session):
        with pytest.raises(RuntimeError) as caught:
            decompile_function(
                analyzer, function, 60, None,
                source_contract_id=row.source_contract_id,
                semantic_owner="subordinate",
            )
    assert caught.value is error
    assert decompiler.calls == 1
    assert len(session.recorder.prefix_view().events) == expected_events
    allowed_types = {EventType.CAUSE_OBSERVED, EventType.REQUIREMENT_COMPLETED}
    if not parent_live:
        allowed_types.add(EventType.ERROR)
    assert all(
        event.header.event_type in allowed_types
        for event in session.recorder.prefix_view().events
    )
    if parent_live:
        assert session.domain_signal_error_kinds
    else:
        assert session.domain_signal_error_kinds == []


def _subordinate_runtime_case(tmp_path, row, result, *, extra_signal=None):
    import os

    from scripts.function_tracer_pcode.equivalence.v2.process_supervisor import (
        DurableCheckpointStore,
        ProcessSupervisorAuthorityFactory,
    )
    from scripts.function_tracer_pcode.equivalence.v2.process_worker_runtime import (
        ProcessWorkerRuntime,
    )
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_operational_extraction import (
        BrokerAnalyzer, BrokerDecompiler, Function, Program,
    )

    session, _ = _broker_session_with_parent(row)
    if extra_signal is not None:
        session.emit_domain_signal(extra_signal)
    manager = type("Manager", (), {
        "getFunctions": lambda self, forward: iter(())
    })()
    program = Program(manager)
    function = Function(program=program)
    result.function = function
    analyzer = BrokerAnalyzer(program, BrokerDecompiler(result))
    session.domain_signal_state["operational_program_binary_identities"] = {
        id(program): "sha256:binary",
    }
    process_factory = ProcessSupervisorAuthorityFactory(
        supervisor_signing_key_id="supervisor-key-v1",
        supervisor_signing_key=b"s" * 32,
        worker_signing_key_id="worker-key-v1",
        worker_signing_key=b"w" * 32,
    )
    prefix = session.recorder.prefix_view()
    launch = process_factory.issue_launch(
        result_occurrence_id=session.identity.result_occurrence_id,
        manifest_entry_preimage_digest="manifest-preimage",
        execution_nonce="execution-nonce-1",
        child_pid=os.getpid(), child_start_token="test-start-token",
        stream_id=prefix.stream_id,
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
        deadline_policy_digest="deadline-policy-digest",
    )
    store = DurableCheckpointStore(
        tmp_path, process_factory, "execution-nonce-1"
    )
    store.persist_launch(launch)
    session.domain_signal_state[
        "unknown_taxonomy_v2_process_worker_runtime"
    ] = ProcessWorkerRuntime.for_testing(
        process_factory=process_factory, store=store, launch=launch,
        worker_start_token="test-start-token",
    )
    return session, store, analyzer, function


def _consume_subordinate_resolved(session, store, *, process_factory=None):
    from scripts.function_tracer_pcode.equivalence.v2.process_census import (
        ProcessAttemptCensusFactory,
        consume_durable_supervisor_projection,
    )
    from scripts.function_tracer_pcode.equivalence.v2.process_supervisor_command import (
        COMMAND_SCHEMA,
    )

    active = session.domain_signal_state["process_worker_checkpoint_records"][0]
    if process_factory is None:
        process_factory = active.runtime.process_factory
    census_factory = ProcessAttemptCensusFactory(
        session.identity.result_occurrence_id
    )
    membership = census_factory.register_subordinate(
        active.invocation, active.operational_factory,
        assignment=active.assignment,
        assignment_factory=active.assignment_factory,
        projection=active.projection, prefix=active.prefix,
    )
    state = store.read_state()
    body = {
        "status": "RESOLVED",
        "authority_kind": "CheckpointStateTransitionReceipt",
        "launch_receipt_digest": active.runtime.launch.receipt_digest,
        "finalization_bundle_digest": state.receipt_digest,
        "child_returncode": 0,
        "projection_schema": COMMAND_SCHEMA,
    }
    consumed = consume_durable_supervisor_projection(
        {**body, "projection_digest": authority_digest(body)},
        store=store, process_authority_factory=process_factory,
        census_factory=census_factory, membership=membership,
    )
    return consumed, census_factory.seal()


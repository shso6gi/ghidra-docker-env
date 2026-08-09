import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
from types import SimpleNamespace
from enum import Enum

import pytest

from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    make_production_unknown_reason,
)

from scripts.function_tracer_pcode.equivalence.v2.contracts import (
    CauseOccurrence,
    CauseOccurrenceAuthority,
    IdentityScope,
    ProofRequirement,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementSlotDefinition,
    SatisfactionContractDefinition,
    all_of,
    authority_digest,
    canonical_value,
    requirement_slot,
)
from scripts.function_tracer_pcode.equivalence.v2.phase7_cutover import (
    ActivationDisposition,
    ExpectedActivationContract,
    ExpectedActivationLedgerFactory,
    ExpectedCauseSlotContract,
    ProducerActivationLedgerFactory,
    ProducerActivationReceipt,
    ProducerSiteContract,
    RETIRED_UMBRELLA_REASON_IDS,
    SealedProducerSiteRegistry,
    TypedResultProjectionFactory,
    TypedResultProjectionReceipt,
    TerminalTimeoutCandidateSelectionReceipt,
    TerminalTimeoutAssignmentFactory,
    VerifiedFinalizationBundleFactory,
    typed_cause_coverage,
)
from scripts.function_tracer_pcode.equivalence.v2.phase7_runtime import (
    Phase7ProductionRuntime,
    runtime_from_audited_manifest,
)
from scripts.function_tracer_pcode.equivalence.v2.pilot import (
    ProductionDualWritePilotConnector,
    ProductionPilotExecutionIdentity,
)
from scripts.function_tracer_pcode.equivalence.v2.process_supervisor import (
    PROCESS_DURABLE_REASON_REGISTRY,
    PROCESS_DURABLE_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
    CompositeProductionSignalEncoder,
    SatSafetyBlockerProductionSignal,
    emit_sat_safety_signal,
    production_signal_scope,
)
from scripts.function_tracer_pcode.equivalence.v2 import production_boundary
from scripts.function_tracer_pcode.equivalence.v2.sat_safety import (
    SatSafetyPilotEncoder,
)
from scripts.function_tracer_pcode.equivalence.v2.reducer import ShadowLifecycleReducer
from scripts.function_tracer_pcode.equivalence.v2.codecs import StrictV2JsonCodec
from scripts.function_tracer_pcode.equivalence.strategies.proof_gates.sat_safety import (
    _v2_observe_sat_unsafety_reason,
)
from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    make_internal_v2_reason_diagnostic,
)
from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
from scripts.function_tracer_pcode.model import (
    Expression,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from scripts.function_tracer_pcode.equivalence.v2.registry import (
    SealedReasonRegistry,
    SealedRecoveryRegistry,
    SemanticCauseIdentityFactory,
    SatisfactionBindingFactory,
)
from scripts.function_tracer_pcode.equivalence.v2.stream import (
    CauseObservedEventAuthority,
    EventIntent,
    EventRecorder,
    EventType,
    GenericReceiptBoundSolverExecutionEventAuthority,
    ReceiptBoundSolverExecutionEventAuthority,
    outcome_stage_requirement_id,
)
from scripts.function_tracer_pcode.validation.phase7_cutover_validation import (
    build_phase7_cutover_validation,
    validate_phase7_cutover_validation,
)
from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_call_effect import (
    _execution_receipt,
    _membership,
)
from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase6_return_outcome import (
    _execution_receipt as _outcome_execution_receipt,
)


def _json_authority_value(value):
    if isinstance(value, Enum):
        return value.value
    if isinstance(value, dict):
        return {str(key): _json_authority_value(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [_json_authority_value(item) for item in value]
    return value


def _persistable_authority(value):
    return _json_authority_value({
        name: getattr(value, name)
        for name in value.__dataclass_fields__
        if not name.startswith("_")
    })


def site_registry(*, slots=("cause-a", "cause-b")):
    slot_contracts = tuple(ExpectedCauseSlotContract(
        slot, frozenset(("typed-semantic-cause",)), "test-domain",
        "test-target", IdentityScope.RELATIONAL.value,
    ) for slot in slots)
    return SealedProducerSiteRegistry((ProducerSiteContract(
        "site-1", "source-sha", "test-domain",
        frozenset((ActivationDisposition.ELIGIBLE, ActivationDisposition.DECISIVE)),
        slot_contracts,
    ),))


def activation_authority(*, slots=("cause-a", "cause-b")):
    registry = site_registry(slots=slots)
    expected_factory = ExpectedActivationLedgerFactory(
        registry, ledger_id="expected-ledger-1", result_occurrence_id="result-1",
        expected=(ExpectedActivationContract(
            "activation-1", "site-1", "attempt-1", "producer-1",
            ActivationDisposition.ELIGIBLE,
        ),),
    )
    factory = expected_factory.open_runtime_ledger()
    factory.record(expected_factory.ledger.authorities[0])
    ledger = factory.seal()
    return factory, ledger, ledger.receipts[0]


def registries(reason_id="typed-semantic-cause"):
    reason = ReasonDefinition(
        reason_id, "test-domain", "semantic", "blocks_decision",
        frozenset(("test-target",)), ("source_snapshot",), frozenset(), True,
        "test-policy", RecoveryAddressability.NO_PROOF_RECOVERY,
    )
    contract = SatisfactionContractDefinition(
        "unused-recovery", 1,
        (RequirementSlotDefinition("proof", frozenset(("test-proof",))),),
        requirement_slot("proof"),
    )
    return SealedReasonRegistry.build((reason,)), SealedRecoveryRegistry.build((contract,))


def occurrence_authority(
    reason_registry, *, occurrence_id="occ-1", producer_id="producer-1",
    attempt_id="attempt-1",
):
    cause = SemanticCauseIdentityFactory(reason_registry).create(
        reason_id="typed-semantic-cause",
        identity_scope=IdentityScope.RELATIONAL,
        target_kind="test-target",
        canonical_target_key=("target", 1),
        missing_semantic_fact=("missing", "proof"),
        semantic_proposition=("semantic_relation", "unproven"),
        observation_surface=("return",),
        active_semantic_precondition=("branch", "active"),
        correspondence_contract=("ordered_pair",),
    )
    occurrence = CauseOccurrence(
        occurrence_id, cause, cause.reason_id, "target-1", "test-target",
        IdentityScope.RELATIONAL, None, None, None, None, (), ("evidence",),
        "typed", "snapshot-1", producer_id, attempt_id,
    )
    return CauseOccurrenceAuthority(occurrence, None)


def finalization_authority(
    reason_registry=None, recovery_registry=None, authority=None,
    activation_factory=None, emission_binding=None,
):
    if reason_registry is None or recovery_registry is None:
        reason_registry, recovery_registry = registries()
    authority = authority or occurrence_authority(reason_registry)
    if activation_factory is None or emission_binding is None:
        activation_factory, _, activation = activation_authority(slots=("cause-a",))
        emission_binding = activation_factory.bind_emission(
            activation=activation, expected_cause_slot_id="cause-a",
            occurrence_authority=authority,
        )
    factory = VerifiedFinalizationBundleFactory(reason_registry, recovery_registry)
    recorder = factory.open_recorder(
        stream_id="stream-1", result_occurrence_id="result-1",
        source_snapshot_fingerprint="snapshot-1",
    )
    factory.append_cause_observed(
        recorder=recorder, emission_binding=emission_binding,
        activation_factory=activation_factory,
    )
    return factory, factory.issue(recorder)


def timeout_finalization_authority(
    *, duplicate=False, status="timeout", include_nonterminal_timeout=False,
    include_outcome_terminal=False, distinct_queries=False,
):
    outcome_receipt = (
        _outcome_execution_receipt("same_kind_consistency", "timeout")
        if include_outcome_terminal else None
    )
    outcome_requirement_id = (
        outcome_stage_requirement_id(outcome_receipt.to_authority_dict())
        if outcome_receipt is not None else None
    )
    reason = ReasonDefinition(
        "typed-semantic-cause", "test-domain", "semantic", "blocks_decision",
        frozenset(("test-target",)), ("source_snapshot",),
        frozenset(("test-proof",)), True, "test-policy",
        RecoveryAddressability.REQUIREMENT_REQUIRED,
    )
    contract = SatisfactionContractDefinition(
        "timeout-recovery", 1,
        tuple((
            RequirementSlotDefinition("a", frozenset(("test-proof",))),
            RequirementSlotDefinition("b", frozenset(("test-proof",))),
        ) + ((RequirementSlotDefinition("c", frozenset(("test-proof",))),)
             if outcome_requirement_id else ())),
        all_of(
            requirement_slot("a"), requirement_slot("b"),
            *((requirement_slot("c"),) if outcome_requirement_id else ()),
        ),
    )
    reason_registry = SealedReasonRegistry.build((reason,))
    recovery_registry = SealedRecoveryRegistry.build((contract,))
    bound = SatisfactionBindingFactory(recovery_registry).bind(
        contract_definition_id="timeout-recovery", contract_version=1,
        bindings={
            "a": ProofRequirement("q-a", "test-proof", ("a",)),
            "b": ProofRequirement("q-b", "test-proof", ("b",)),
            **({"c": ProofRequirement(
                outcome_requirement_id, "test-proof", ("c",)
            )} if outcome_requirement_id else {}),
        },
    )
    cause = SemanticCauseIdentityFactory(reason_registry).create(
        reason_id="typed-semantic-cause", identity_scope=IdentityScope.RELATIONAL,
        target_kind="test-target", canonical_target_key=("target", 1),
        missing_semantic_fact=("missing", "proof"),
        semantic_proposition=("semantic_relation", "unproven"),
        observation_surface=("return",),
        active_semantic_precondition=("branch", "active"),
        correspondence_contract=("ordered_pair",),
    )
    occurrence = CauseOccurrence(
        "occ-timeout", cause, cause.reason_id, "target-1", "test-target",
        IdentityScope.RELATIONAL, bound.contract_definition_id,
        bound.contract_version, bound.normalized_expression_digest,
        bound.bound_expression_digest,
        tuple(("q-a", "q-b") + ((outcome_requirement_id,) if outcome_requirement_id else ())),
        ("evidence",),
        "typed", "snapshot-1", "producer-1", "attempt-1",
    )
    factory = VerifiedFinalizationBundleFactory(reason_registry, recovery_registry)
    recorder = factory.open_recorder(
        stream_id="timeout-stream", result_occurrence_id="result-1",
        source_snapshot_fingerprint="snapshot-1",
    )
    activation_factory, _, activation = activation_authority(slots=("cause-a",))
    authority = CauseOccurrenceAuthority(occurrence, bound)
    emission_binding = activation_factory.bind_emission(
        activation=activation, expected_cause_slot_id="cause-a",
        occurrence_authority=authority,
    )
    factory.append_cause_observed(
        recorder=recorder, emission_binding=emission_binding,
        activation_factory=activation_factory,
    )
    if include_nonterminal_timeout:
        history = _execution_receipt(
            status="timeout",
            membership=_membership(status="timeout", requirement="q-a"),
        )
        recorder.append(EventIntent(
            EventType.SOLVER_TIMEOUT,
            GenericReceiptBoundSolverExecutionEventAuthority(
                "q-a", history.to_authority_dict(), False,
            ),
        ))
    requirements = ("q-a", "q-a") if duplicate else ("q-a", "q-b")
    event_type = EventType.SOLVER_TIMEOUT if status == "timeout" else EventType.SOLVER_UNKNOWN
    for requirement in requirements:
        receipt = _execution_receipt(
            status=status,
            membership=_membership(status=status, requirement=requirement),
            query=(
                f"(assert (= query_{requirement} query_{requirement}))\n(check-sat)"
                if distinct_queries else None
            ),
        )
        recorder.append(EventIntent(
            event_type,
            GenericReceiptBoundSolverExecutionEventAuthority(
                requirement, receipt.to_authority_dict(), status == "timeout",
            ),
        ))
    if outcome_receipt is not None:
        recorder.append(EventIntent(
            EventType.SOLVER_TIMEOUT,
            ReceiptBoundSolverExecutionEventAuthority(
                outcome_requirement_id,
                outcome_receipt.to_authority_dict(),
                True,
            ),
        ))
    return factory, factory.issue(recorder)


def test_retired_reason_set_is_exact_and_does_not_include_typed_domain_reasons():
    assert RETIRED_UMBRELLA_REASON_IDS == {
        "unknown", "solver_unknown_timeout", "unresolved_expression",
        "equivalence_blocking_unsafety", "sat_unsafety",
        "loop_summary_proof_missing", "outcome_partition_unknown",
        "method_b_closure_blocked",
    }
    assert "typed-semantic-cause" not in RETIRED_UMBRELLA_REASON_IDS


def test_phase7_stored_cutover_artifact_is_current_and_closes_coverage():
    root = Path(__file__).resolve().parents[4]
    path = root / "artifacts/unknown_taxonomy_v2/phase7/cutover-validation.json"
    stored = json.loads(path.read_text(encoding="utf-8"))
    validate_phase7_cutover_validation(root, stored)
    assert stored == json.loads(json.dumps(build_phase7_cutover_validation(root)))
    assert stored["production_umbrella_generation"] == 0
    assert stored["production_umbrella_routing"] == 0
    assert stored["status"] == "phase7_integration_validation_pending_fixed_review"
    assert stored["contract_fixture_coverage"]["eligible_cause_slot_count"] == 6
    assert stored["contract_fixture_coverage"]["v2_native_typed_cause_coverage"] == 1.0
    assert stored["production_runtime_coverage"][
        "v2_native_typed_cause_coverage"
    ] == 1.0
    assert stored["production_runtime_coverage"]["eligible_cause_slot_count"] == 2
    assert len(stored["fixture_domains"]) == 6
    assert stored["production_runtime_unknown"]["final_outcome"] == "UNKNOWN"
    assert stored["production_runtime_unknown"]["active_cause_count"] == 1
    assert stored["production_runtime_unknown"]["open_requirement_count"] == 1
    assert stored["production_runtime_unknown"][
        "terminal_timeout_assignment_count"
    ] == 0
    assert stored["production_runtime_timeout"]["final_outcome"] == "TIMEOUT"
    assert stored["production_runtime_timeout"]["terminal_timeout_event_count"] == 1
    assert stored["production_runtime_timeout"]["timeout_derived_reason_count"] == 0
    declared_skips = stored["cross_slice_validation"][
        "declared_external_fixture_skips"
    ]
    assert len(declared_skips) == 3
    assert {
        row["reason"] for row in declared_skips
    } == {"requires the external 411-summary legacy diagnostic fixture"}


def test_phase7_cutover_artifact_rejects_tampered_coverage():
    root = Path(__file__).resolve().parents[4]
    stored = build_phase7_cutover_validation(root)
    tampered = copy.deepcopy(stored)
    tampered["contract_fixture_coverage"]["covered_cause_slot_count"] = 5
    with pytest.raises(ValueError, match="artifact drifted"):
        validate_phase7_cutover_validation(root, tampered)


def test_real_sat_producer_activation_issues_factory_owned_projection():
    root = Path(__file__).resolve().parents[4]
    source_path = (
        root / "scripts/function_tracer_pcode/equivalence/strategies/"
        "proof_gates/sat_safety.py"
    )
    site_registry = SealedProducerSiteRegistry((ProducerSiteContract(
        "sat-safety-blocker-observed",
        hashlib.sha256(source_path.read_bytes()).hexdigest(),
        "sat_safety",
        frozenset((ActivationDisposition.ELIGIBLE,)),
        (ExpectedCauseSlotContract(
            "sat-analysis-safety-cause",
            frozenset(("counterexample_analysis_safety_unproven",)),
            "sat_safety", "counterexample_safety_gate",
            IdentityScope.RELATIONAL.value,
        ),),
    ),))
    target = ("phase7-real-sat-target",)
    signal = SatSafetyBlockerProductionSignal(
        action="OBSERVED",
        reason_id="counterexample_analysis_safety_unproven",
        canonical_target_key=(
            target, ("safety_gate_ref", "analysis_safety_gap")
        ),
        missing_semantic_fact=(
            "counterexample_safety_gate_unproven", "analysis_safety_gap"
        ),
        evidence_refs=("analysis_safety_gap",),
        producer_id="sat_unsafety_reason_producer",
    )

    def runtime_factory(identity):
        expected_factory = ExpectedActivationLedgerFactory(
            site_registry,
            ledger_id="phase7-real-sat-expected",
            result_occurrence_id=identity.result_occurrence_id,
            expected=(ExpectedActivationContract(
                "phase7-real-sat-activation",
                "sat-safety-blocker-observed",
                identity.execution_identity_digest,
                "sat_unsafety_reason_producer",
                ActivationDisposition.ELIGIBLE,
            ),),
        )
        return Phase7ProductionRuntime(
            expected_factory,
            {Phase7ProductionRuntime.signal_digest(
                "sat-safety-blocker-observed", signal
            ):
             expected_factory.ledger.authorities[0]},
        )

    encoder = SatSafetyPilotEncoder()
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            SatSafetyBlockerProductionSignal: encoder,
        }),
        phase7_runtime_factory=runtime_factory,
    )
    session = connector.begin({"case": "phase7-real-sat-producer"})
    internal = make_internal_v2_reason_diagnostic(
        "counterexample_analysis_safety_unproven",
        stage="S_SAT_SAFETY",
        evidence_refs=("analysis_safety_gap",),
        object_target_key=target,
    )
    with production_signal_scope(session):
        _v2_observe_sat_unsafety_reason(internal)
        assert emit_sat_safety_signal(
            signal,
            producer_site_manifest_id="sat-safety-blocker-observed",
        ) == 0
    assert session.domain_signal_error_details == []
    result = SimpleNamespace(
        is_equivalent=None,
        error_message=None,
        failure_status=None,
        failure_message=None,
        unknown_reasons=[internal],
        unknown_recovery_actions=[],
        is_timeout=lambda: False,
    )

    connector.finish(session, result, case_id="phase7-real-sat")

    runtime = session.phase7_runtime_result
    assert runtime.coverage["v2_native_typed_cause_coverage"] == 1.0
    assert runtime.decision_receipt.outcome.value == "UNKNOWN"
    assert runtime.terminal_timeout_assignment_receipt is None
    assert len(runtime.projection_receipts) == 1
    assert result.unknown_reason_projection_mode == "V2_CANONICAL"
    assert result.unknown_reasons[0].typed_cause_key["authority_class"] == (
        "V2_FACTORY_PROJECTION"
    )
    assert result.legacy_unknown_reasons[0].typed_cause_key["authority_class"] == (
        "LEGACY_DIAGNOSTIC"
    )


def test_discovered_activation_rejects_reason_owned_by_another_sat_site():
    root = Path(__file__).resolve().parents[4]
    manifest = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )).read_text(encoding="utf-8"))
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            SatSafetyBlockerProductionSignal: SatSafetyPilotEncoder(),
        }),
        phase7_runtime_factory=lambda identity: runtime_from_audited_manifest(
            manifest, identity
        ),
    )
    session = connector.begin({"case": "phase7-wrong-site-reason"})
    signal = SatSafetyBlockerProductionSignal(
        action="OBSERVED",
        reason_id="counterexample_partition_replay_ambiguous",
        canonical_target_key=("ambiguous-partition",),
        missing_semantic_fact=("unique_counterexample_partition_witness", False),
        evidence_refs=("partition_replay_ambiguous",),
        producer_id="sat_unsafety_reason_producer",
    )
    session.phase7_runtime.record_pre_emission_activation(
        "sat-safety-blocker-observed", signal
    )
    intents = tuple(session.domain_signal_encoder(session, signal))
    with pytest.raises(
        ValueError, match="site-exact alternative slot"
    ):
        session.phase7_runtime.buffer_signal_intents(
            "sat-safety-blocker-observed", signal, intents
        )


def test_real_solver_checker_unknown_uses_all_site_activation_census(tmp_path):
    root = Path(__file__).resolve().parents[4]
    producer_manifest = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )).read_text(encoding="utf-8"))
    fixture_root = root / "scripts/function_tracer_pcode/tests/fixtures"
    left_source = fixture_root / "phase7_sat_left.c"
    right_source = fixture_root / "phase7_sat_right.c"
    left_binary = tmp_path / "phase7-sat-left"
    right_binary = tmp_path / "phase7-sat-right"
    for source, binary in (
        (left_source, left_binary), (right_source, right_binary)
    ):
        subprocess.run(
            ("gcc", "-O0", "-c", "-o", str(binary), str(source)),
            check=True, capture_output=True, text=True,
        )
    content_identities = (
        hashlib.sha256(left_binary.read_bytes()).hexdigest(),
        hashlib.sha256(right_binary.read_bytes()).hexdigest(),
    )

    def runtime_factory(identity):
        return runtime_from_audited_manifest(
            producer_manifest, identity,
        )

    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            SatSafetyBlockerProductionSignal: SatSafetyPilotEncoder(),
        }),
        phase7_runtime_factory=runtime_factory,
    )
    session = connector.begin({
        "case": "phase7-real-z3-checker-unknown",
        "binary1_content_identity": content_identities[0],
        "binary2_content_identity": content_identities[1],
        "function_name1": "phase7_sat_witness",
        "function_name2": "phase7_sat_witness",
    })

    def analysis(name, value, notes=()):
        result = FunctionReturnAnalysis(
            function_name=name,
            entry_point="0x1000",
            parameters=[],
            returns=[ReturnInfo(
                "0x1010", Expression.constant(value, size=4), []
            )],
            return_type="int",
            analysis_notes=list(notes),
        )
        result.return_abi_facts = {
            "schema_version": 1,
            "calling_convention": {
                "status": "PRESENT",
                "value": ("ghidra_calling_convention_v1", "default"),
                "source": "phase7-test",
            },
            "declared_or_effective_return_type": {
                "status": "PRESENT",
                "value": ("ghidra_return_type_v1", "/int", 4),
                "source": "phase7-test",
            },
            "return_storage_descriptor": {
                "status": "PRESENT",
                "value": (
                    "ghidra_return_storage_v1",
                    ((
                        "ghidra_return_storage_member_v1",
                        "register", 0, 8,
                    ),),
                ),
                "source": "phase7-test",
            },
        }
        return result

    checker = EquivalenceChecker(
        strategy="monolithic", timeout=5, monolithic_timeout=5,
        enable_rewrite=False,
    )
    with production_signal_scope(session):
        result = checker.check(
            analysis("phase7_sat_witness", 7, ("symbolic_post_state_reads",)),
            analysis("phase7_sat_witness", 8),
        )
    connector.finish(session, result, case_id="phase7-real-z3-checker-unknown")

    runtime = session.phase7_runtime_result
    query_receipts = result.call_proof_terminal_provenance[
        "query_execution_receipts"
    ]
    assert result.is_equivalent is None
    assert result.error_message is None
    assert result.unknown_reason_projection_mode == "V2_CANONICAL"
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        "counterexample_analysis_safety_unproven"
    ]
    assert any(
        receipt["disposition"] == "sat"
        and "(check-sat)" in receipt["formula_text"]
        for receipt in query_receipts
    )
    assert runtime.decision_receipt.outcome.value == "UNKNOWN"
    assert runtime.static_producer_site_count == producer_manifest["site_count"]
    assert runtime.static_producer_site_count > 0
    assert runtime.expected_activation_count == 1
    assert runtime.runtime_activation_count == 1
    assert runtime.discovered_activation_count == 1
    assert runtime.not_reached_activation_count == 0
    assert runtime.coverage["eligible_cause_slot_count"] == 1
    assert runtime.coverage["covered_cause_slot_count"] == 1

    evidence_path = os.environ.get("PHASE7_SAT_EVIDENCE_PATH")
    if evidence_path:
        stream_codec = StrictV2JsonCodec(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        )
        typed = runtime.projection_receipts[0]
        body = {
            "manifest_kind": "unknown-taxonomy-v2-phase7-real-sat-unknown-v1",
            "producer_manifest_digest": producer_manifest["manifest_digest"],
            "producer_site_count": producer_manifest["site_count"],
            "expected_activation_ledger_digest": (
                runtime.expected_activation_ledger_digest
            ),
            "runtime_activation_ledger_digest": (
                runtime.runtime_activation_ledger_digest
            ),
            "expected_activation_count": runtime.expected_activation_count,
            "runtime_activation_count": runtime.runtime_activation_count,
            "not_reached_activation_count": runtime.not_reached_activation_count,
            "static_producer_site_count": runtime.static_producer_site_count,
            "discovered_activation_count": runtime.discovered_activation_count,
            "selected_activation_count": 1,
            "selected_site_id": "sat-safety-blocker-observed",
            "binary_content_identities": content_identities,
            "binary_sha256": content_identities,
            "source_paths": (
                left_source.relative_to(root).as_posix(),
                right_source.relative_to(root).as_posix(),
            ),
            "source_sha256": (
                hashlib.sha256(left_source.read_bytes()).hexdigest(),
                hashlib.sha256(right_source.read_bytes()).hexdigest(),
            ),
            "function_pair": (
                "phase7_sat_witness", "phase7_sat_witness"
            ),
            "compiler_argv": ("gcc", "-O0", "-c"),
            "query_execution_receipts": query_receipts,
            "sealed_event_stream": json.loads(stream_codec.dumps(
                runtime.finalization_bundle.sealed_event_stream
            )),
            "c_active_rows": tuple(
                _persistable_authority(row)
                for row in runtime.finalization_bundle.lifecycle_projection.c_active_base
            ),
            "q_open_rows": tuple(
                _persistable_authority(row)
                for row in runtime.finalization_bundle.lifecycle_projection.q_open_base
            ),
            "typed_projection_receipt": _persistable_authority(typed),
            "decision_receipt": _persistable_authority(
                runtime.decision_receipt
            ),
            "active_cause_count": len(
                runtime.finalization_bundle.lifecycle_projection.c_active_base
            ),
            "open_requirement_count": len(
                runtime.finalization_bundle.lifecycle_projection.q_open_base
            ),
            "coverage": dict(runtime.coverage),
            "final_outcome": runtime.decision_receipt.outcome.value,
            "terminal_timeout_receipt_count": 0,
            "terminal_timeout_assignment_count": 0,
            "result_projection": {
                "is_equivalent": result.is_equivalent,
                "error_message": result.error_message,
                "reason_ids": tuple(
                    reason.reason_id for reason in result.unknown_reasons
                ),
                "projection_mode": result.unknown_reason_projection_mode,
            },
        }
        output = Path(evidence_path)
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(
            {**body, "artifact_digest": authority_digest(body)},
            indent=2, sort_keys=True,
        ) + "\n", encoding="utf-8")


def test_dynamic_census_rejects_a_run_without_discovered_activation():
    root = Path(__file__).resolve().parents[4]
    manifest = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )).read_text(encoding="utf-8"))
    identity = ProductionPilotExecutionIdentity.create({
        "case": "phase7-selected-site-missing",
    })
    runtime = runtime_from_audited_manifest(
        manifest, identity,
    )

    with pytest.raises(
        ValueError, match="no discovered producer activations"
    ):
        runtime.finalize(
            stream_id="missing-selected-site",
            result_occurrence_id=identity.result_occurrence_id,
            source_snapshot_fingerprint=identity.source_snapshot_fingerprint,
        )


def test_production_boundary_fails_closed_when_expected_activation_is_missing(
    monkeypatch,
):
    site_registry = SealedProducerSiteRegistry((ProducerSiteContract(
        "missing-activation-site", "source-sha", "sat_safety",
        frozenset((ActivationDisposition.ELIGIBLE,)),
        (ExpectedCauseSlotContract(
            "missing-activation-cause",
            frozenset(("counterexample_analysis_safety_unproven",)),
            "sat_safety", "counterexample_safety_target",
            IdentityScope.RELATIONAL.value,
        ),),
    ),))

    def runtime_factory(identity):
        expected_factory = ExpectedActivationLedgerFactory(
            site_registry,
            ledger_id="missing-activation-ledger",
            result_occurrence_id=identity.result_occurrence_id,
            expected=(ExpectedActivationContract(
                "missing-activation", "missing-activation-site",
                identity.execution_identity_digest, "producer-1",
                ActivationDisposition.ELIGIBLE,
            ),),
        )
        return Phase7ProductionRuntime(
            expected_factory,
            {Phase7ProductionRuntime.signal_digest(
                "missing-activation-site", "expected-signal"
            ): expected_factory.ledger.authorities[0]},
        )

    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        ),
        phase7_runtime_factory=runtime_factory,
    )
    checker = SimpleNamespace(
        v2_dual_write_pilot_connector=connector,
        observation_contract=SimpleNamespace(contract_id="contract-1"),
        _active_binary_content_identities=("binary-1", "binary-2"),
    )
    internal = make_internal_v2_reason_diagnostic(
        "counterexample_analysis_safety_unproven",
        stage="S_SAT_SAFETY",
        evidence_refs=("analysis_safety_gap",),
        object_target_key=("missing-activation-target",),
    )
    result = SimpleNamespace(
        is_equivalent=None,
        error_message=None,
        failure_status=None,
        failure_message=None,
        unknown_reasons=[internal],
        unknown_recovery_actions=["legacy-action"],
        is_timeout=lambda: False,
    )
    monkeypatch.setattr(
        production_boundary,
        "_run_legacy_check_from_binaries",
        lambda *_args, **_kwargs: result,
    )

    actual = production_boundary.run_check_from_binaries_with_v2_pilot(
        checker, object(), object(), "left", "right"
    )

    assert actual.error_message == "V2_PROJECTION_AUTHORITY_INVALID"
    assert actual.unknown_reasons == []
    assert actual.unknown_recovery_actions == []
    assert actual.legacy_unknown_reasons == [internal]
    assert actual.v2_dual_write_pilot["status"] == "SHADOW_EVIDENCE_INCOMPLETE"


def test_operational_binary_identity_projects_real_cli_sha256_tuple():
    digest = "a" * 64

    assert production_boundary._operational_binary_content_identity(
        ("sha256", digest)
    ) == f"sha256:{digest}"
    with pytest.raises(ValueError, match="not canonical"):
        production_boundary._operational_binary_content_identity(
            ("sha256", "short")
        )
    with pytest.raises(ValueError, match="not canonical"):
        production_boundary._operational_binary_content_identity(
            ("md5", digest)
        )


def test_legacy_error_uses_typed_boundary_kind_not_arbitrary_status(monkeypatch):
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        )
    )
    checker = SimpleNamespace(
        v2_dual_write_pilot_connector=connector,
        observation_contract=SimpleNamespace(contract_id="contract-1"),
        _active_binary_content_identities=("binary-1", "binary-2"),
    )
    result = SimpleNamespace(
        is_equivalent=None,
        error_message="volatile diagnostic",
        failure_status="strategy-name-from-compatibility-layer",
        failure_message="detail",
        unknown_reasons=[],
        unknown_recovery_actions=[],
        is_timeout=lambda: False,
    )
    monkeypatch.setattr(
        production_boundary,
        "_run_legacy_check_from_binaries",
        lambda *_args, **_kwargs: result,
    )

    actual = production_boundary.run_check_from_binaries_with_v2_pilot(
        checker, object(), object(), "left", "right"
    )

    authority = actual.v2_legacy_error_authority
    authority.validate()
    assert authority.error_kind is (
        production_boundary.LegacyBoundaryErrorKind.COMPATIBILITY_ERROR
    )
    assert authority.legacy_failure_status == (
        "strategy-name-from-compatibility-layer"
    )
    assert actual.final_outcome == "ERROR"
    assert actual._v2_dual_write_evidence.pilot_result.error_receipts[
        0
    ].error_kind == "legacy_compatibility_error"


def test_supervisor_nonce_prebinds_production_identity(monkeypatch):
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        RESULT_ENTRY_OCCURRENCE_NONCE_ENV,
    )

    nonce = "a" * 48
    monkeypatch.setenv(RESULT_ENTRY_OCCURRENCE_NONCE_ENV, nonce)
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        )
    )

    session = connector.begin({"case": "supervisor-prebound-identity"})
    expected = ProductionPilotExecutionIdentity.create({
        "case": "supervisor-prebound-identity",
        "result_entry_occurrence_nonce": nonce,
    })

    assert session.identity == expected


def test_coverage_denominator_is_expected_cause_slot_not_surviving_occurrence():
    activation_factory, ledger, activation = activation_authority()
    reason_registry, recovery_registry = registries()
    authority = occurrence_authority(reason_registry)
    binding = activation_factory.bind_emission(
        activation=activation, expected_cause_slot_id="cause-a",
        occurrence_authority=authority,
    )
    finalization_factory, bundle = finalization_authority(
        reason_registry, recovery_registry, authority, activation_factory, binding
    )
    emitted = finalization_factory.emitted_for(binding)
    projection_factory = activation_factory.open_projection_factory(finalization_factory)
    first = projection_factory.issue(
        activation=activation, expected_cause_slot_id="cause-a",
        bundle=bundle, emission_binding=binding, emitted_cause=emitted,
    )
    census = typed_cause_coverage(
        ledger, activation_factory, projection_factory, (first,)
    )
    assert census["eligible_cause_slot_count"] == 2
    assert census["covered_cause_slot_count"] == 1
    assert census["v2_native_typed_cause_coverage"] == 0.5
    assert census["missing_cause_slots"] == ((activation.activation_id, "cause-b"),)


def test_projection_requires_owned_activation_and_verified_finalization_bundle():
    activation_factory, _, activation = activation_authority(slots=("cause-a",))
    reason_registry, recovery_registry = registries()
    authority = occurrence_authority(reason_registry)
    binding = activation_factory.bind_emission(
        activation=activation, expected_cause_slot_id="cause-a",
        occurrence_authority=authority,
    )
    finalization_factory, bundle = finalization_authority(
        reason_registry, recovery_registry, authority, activation_factory, binding
    )
    emitted = finalization_factory.emitted_for(binding)
    projection_factory = activation_factory.open_projection_factory(finalization_factory)
    copied_activation = copy.copy(activation)
    with pytest.raises(ValueError, match="activation is not factory-owned"):
        projection_factory.issue(
            activation=copied_activation, expected_cause_slot_id="cause-a",
            bundle=bundle, emission_binding=binding, emitted_cause=emitted,
        )
    copied_bundle = copy.copy(bundle)
    with pytest.raises(ValueError, match="bundle is not verifier-owned"):
        projection_factory.issue(
            activation=activation, expected_cause_slot_id="cause-a",
            bundle=copied_bundle, emission_binding=binding, emitted_cause=emitted,
        )


def test_direct_or_codec_style_stream_cannot_be_adopted_as_finalization_authority():
    reason_registry, recovery_registry = registries()
    raw = EventRecorder(
        stream_id="stream-1", result_occurrence_id="result-1",
        source_snapshot_fingerprint="snapshot-1",
    )
    raw.append(EventIntent(
        EventType.CAUSE_OBSERVED,
        CauseObservedEventAuthority(occurrence_authority(reason_registry)),
    ))
    stream = raw.seal()
    factory = VerifiedFinalizationBundleFactory(reason_registry, recovery_registry)
    with pytest.raises(ValueError, match="not verifier-factory-owned"):
        factory.issue(stream)


def test_cause_observation_requires_pre_emission_consumption_and_binding_is_single_use():
    activation_factory, _, activation = activation_authority(slots=("cause-a",))
    reason_registry, recovery_registry = registries()
    authority = occurrence_authority(reason_registry)
    binding = activation_factory.bind_emission(
        activation=activation, expected_cause_slot_id="cause-a",
        occurrence_authority=authority,
    )
    first_factory = VerifiedFinalizationBundleFactory(reason_registry, recovery_registry)
    recorder = first_factory.open_recorder(
        stream_id="stream-a", result_occurrence_id="result-1",
        source_snapshot_fingerprint="snapshot-1",
    )
    with pytest.raises(ValueError, match="pre-emission binding consumption"):
        recorder.append(EventIntent(
            EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)
        ))
    first_factory.append_cause_observed(
        recorder=recorder, emission_binding=binding,
        activation_factory=activation_factory,
    )
    second_factory = VerifiedFinalizationBundleFactory(reason_registry, recovery_registry)
    second_recorder = second_factory.open_recorder(
        stream_id="stream-b", result_occurrence_id="result-1",
        source_snapshot_fingerprint="snapshot-1",
    )
    with pytest.raises(ValueError, match="already consumed"):
        second_factory.append_cause_observed(
            recorder=second_recorder, emission_binding=binding,
            activation_factory=activation_factory,
        )
    bypass_factory = VerifiedFinalizationBundleFactory(reason_registry, recovery_registry)
    bypass_recorder = bypass_factory.open_recorder(
        stream_id="stream-c", result_occurrence_id="result-1",
        source_snapshot_fingerprint="snapshot-1",
    )
    bypass_recorder._recorder.append(EventIntent(
        EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)
    ))
    with pytest.raises(ValueError, match="emitted-binding census differ"):
        bypass_factory.issue(bypass_recorder)


def test_projection_slot_is_exactly_once_and_receipt_is_not_publicly_constructible():
    activation_factory, _, activation = activation_authority(slots=("cause-a",))
    reason_registry, recovery_registry = registries()
    authority = occurrence_authority(reason_registry)
    binding = activation_factory.bind_emission(
        activation=activation, expected_cause_slot_id="cause-a",
        occurrence_authority=authority,
    )
    finalization_factory, bundle = finalization_authority(
        reason_registry, recovery_registry, authority, activation_factory, binding
    )
    emitted = finalization_factory.emitted_for(binding)
    projection_factory = activation_factory.open_projection_factory(finalization_factory)
    projection = projection_factory.issue(
        activation=activation, expected_cause_slot_id="cause-a",
        bundle=bundle, emission_binding=binding, emitted_cause=emitted,
    )
    compatibility = make_production_unknown_reason(
        projection, projection_factory=projection_factory,
    )
    assert compatibility.reason_id == projection.reason_id
    assert compatibility.typed_cause_key["receipt_digest"] == projection.receipt_digest
    with pytest.raises(ValueError, match="not issuer-owned"):
        make_production_unknown_reason(
            copy.copy(projection), projection_factory=projection_factory,
        )
    with pytest.raises(ValueError, match="one-to-one"):
        projection_factory.issue(
            activation=activation, expected_cause_slot_id="cause-a",
            bundle=bundle, emission_binding=binding, emitted_cause=emitted,
        )
    with pytest.raises(ValueError, match="factory-issued"):
        ProducerActivationReceipt(*("x",) * 11)
    with pytest.raises(ValueError, match="factory-issued"):
        TypedResultProjectionReceipt(*("x",) * 15)
    with pytest.raises(ValueError, match="already has a projection issuer"):
        activation_factory.open_projection_factory(finalization_factory)
    with pytest.raises(ValueError, match="activation-ledger-issued"):
        TypedResultProjectionFactory(activation_factory, finalization_factory)


def test_slot_contract_rejects_retired_reason_and_projection_reason_mismatch():
    with pytest.raises(ValueError, match="only typed reason IDs"):
        ExpectedCauseSlotContract(
            "slot", frozenset(("solver_unknown_timeout",)), "test-domain",
            "test-target", IdentityScope.RELATIONAL.value,
        )
    registry = SealedProducerSiteRegistry((ProducerSiteContract(
        "site-1", "source-sha", "test-domain",
        frozenset((ActivationDisposition.ELIGIBLE,)),
        (ExpectedCauseSlotContract(
            "cause-a", frozenset(("different-typed-cause",)), "test-domain",
            "test-target", IdentityScope.RELATIONAL.value,
        ),),
    ),))
    expected_factory = ExpectedActivationLedgerFactory(
        registry, ledger_id="expected-ledger", result_occurrence_id="result-1",
        expected=(ExpectedActivationContract(
            "activation-1", "site-1", "attempt-1", "producer-1",
            ActivationDisposition.ELIGIBLE,
        ),),
    )
    activation_factory = expected_factory.open_runtime_ledger()
    activation_factory.record(expected_factory.ledger.authorities[0])
    activation = activation_factory.seal().receipts[0]
    reason_registry, _ = registries()
    with pytest.raises(ValueError, match="expected producer/attempt/slot"):
        activation_factory.bind_emission(
            activation=activation, expected_cause_slot_id="cause-a",
            occurrence_authority=occurrence_authority(reason_registry),
        )


def test_emission_binding_rejects_wrong_producer_attempt_with_same_semantics():
    activation_factory, _, activation = activation_authority(slots=("cause-a",))
    reason_registry, _ = registries()
    for authority in (
        occurrence_authority(reason_registry, producer_id="foreign-producer"),
        occurrence_authority(reason_registry, attempt_id="foreign-attempt"),
    ):
        with pytest.raises(ValueError, match="expected producer/attempt/slot"):
            activation_factory.bind_emission(
                activation=activation, expected_cause_slot_id="cause-a",
                occurrence_authority=authority,
            )


def test_timeout_assignment_tuple_must_match_execution_and_all_rows_are_live():
    finalization_factory, bundle = finalization_authority()
    with pytest.raises(ValueError, match="every exact receipt-bound candidate"):
        finalization_factory.open_timeout_assignment_factory().issue(bundle)


def test_multi_requirement_timeout_is_derived_from_exact_receipt_bound_events():
    finalization_factory, bundle = timeout_finalization_authority(
        include_nonterminal_timeout=True
    )
    factory = finalization_factory.open_timeout_assignment_factory()
    receipt = factory.issue(bundle)
    assert factory.owns(receipt)
    assert receipt.assignment_requirement_ids == ("q-a", "q-b")
    assert len(receipt.execution_event_digests) == 2
    assert len(receipt.execution_receipt_digests) == 2
    with pytest.raises(ValueError, match="already has a timeout selection"):
        factory.issue(bundle)
    with pytest.raises(ValueError, match="already has a timeout issuer"):
        finalization_factory.open_timeout_assignment_factory()


def _terminal_candidate_view(bundle):
    timeout_candidates = tuple(
        (
            event.header.sequence_number,
            event.authority_payload.proof_requirement_id,
            event.authority_digest,
        )
        for event in bundle.sealed_event_stream.events
        if event.header.event_type is EventType.SOLVER_TIMEOUT
        and event.authority_payload.terminal_candidate is True
    )
    payload = {
        "result_occurrence_id": bundle.lifecycle_projection.result_occurrence_id,
        "lifecycle_projection_digest": (
            bundle.lifecycle_projection.lifecycle_projection_digest
        ),
        "timeout_candidates": timeout_candidates,
        "counterexample_event_digests": (),
        "error_event_digests": (),
        "competing_decisive_event_digests": (),
    }
    return SimpleNamespace(**payload, view_digest=authority_digest(payload))


def test_timeout_assignment_promotes_only_attempt_aware_selected_execution():
    finalization_factory, bundle = timeout_finalization_authority(
        distinct_queries=True
    )
    assignment_factory = finalization_factory.open_timeout_assignment_factory()
    with pytest.raises(ValueError, match="events are not one execution"):
        assignment_factory.issue(bundle)

    view = _terminal_candidate_view(bundle)
    selected_event = tuple(
        event for event in bundle.sealed_event_stream.events
        if event.header.event_type is EventType.SOLVER_TIMEOUT
        and event.authority_payload.proof_requirement_id == "q-b"
    )[0]
    selection = TerminalTimeoutCandidateSelectionReceipt.issue(
        bundle.sealed_event_stream,
        view,
        event_sequence_number=selected_event.header.sequence_number,
        proof_requirement_id="q-b",
    )
    receipt = assignment_factory.issue(
        bundle,
        candidate_selection=selection,
        candidate_selection_stream=bundle.sealed_event_stream,
        terminal_candidate_view=view,
    )
    assert receipt.assignment_requirement_ids == ("q-b",)
    assert receipt.execution_event_digests == (selected_event.authority_digest,)
    assert (
        receipt.terminal_candidate_selection_receipt_digest
        == selection.receipt_digest
    )


def test_timeout_candidate_selection_rejects_execution_identity_tampering():
    _, bundle = timeout_finalization_authority(distinct_queries=True)
    view = _terminal_candidate_view(bundle)
    selected_event = tuple(
        event for event in bundle.sealed_event_stream.events
        if event.header.event_type is EventType.SOLVER_TIMEOUT
    )[-1]
    selection = TerminalTimeoutCandidateSelectionReceipt.issue(
        bundle.sealed_event_stream,
        view,
        event_sequence_number=selected_event.header.sequence_number,
        proof_requirement_id=selected_event.authority_payload.proof_requirement_id,
    )
    forged = copy.deepcopy(selection)
    object.__setattr__(forged, "execution_identity_digest", "forged-execution")
    with pytest.raises(ValueError, match="selection authority differs"):
        forged.validate_against(bundle.sealed_event_stream, view)


def test_timeout_selection_rejects_non_timeout_duplicate_and_cross_factory_bundle():
    unknown_factory, unknown_bundle = timeout_finalization_authority(status="unknown")
    with pytest.raises(ValueError, match="every exact receipt-bound candidate"):
        unknown_factory.open_timeout_assignment_factory().issue(unknown_bundle)
    duplicate_factory, duplicate_bundle = timeout_finalization_authority(duplicate=True)
    with pytest.raises(ValueError, match="contains duplicates"):
        duplicate_factory.open_timeout_assignment_factory().issue(duplicate_bundle)
    owner_factory, owner_bundle = timeout_finalization_authority()
    foreign_factory, _ = timeout_finalization_authority()
    with pytest.raises(ValueError, match="not verifier-owned"):
        foreign_factory.open_timeout_assignment_factory().issue(owner_bundle)
    with pytest.raises(ValueError, match="finalization-authority-issued"):
        TerminalTimeoutAssignmentFactory(owner_factory)
    mixed_factory, mixed_bundle = timeout_finalization_authority(
        include_outcome_terminal=True
    )
    with pytest.raises(ValueError, match="lacks result-bound generic receipt"):
        mixed_factory.open_timeout_assignment_factory().issue(mixed_bundle)


def test_activation_disposition_conservation_is_explicit_and_eligible_slots_are_frozen():
    registry = site_registry(slots=("cause-a",))
    expected_factory = ExpectedActivationLedgerFactory(
        registry, ledger_id="expected-ledger", result_occurrence_id="result-1",
        expected=(
            ExpectedActivationContract(
                "activation-eligible", "site-1", "eligible", "producer-1",
                ActivationDisposition.ELIGIBLE,
            ),
            ExpectedActivationContract(
                "activation-decisive", "site-1", "decisive", "producer-1",
                ActivationDisposition.DECISIVE,
            ),
        ),
    )
    factory = expected_factory.open_runtime_ledger()
    for authority in expected_factory.ledger.authorities:
        factory.record(authority)
    ledger = factory.seal()
    assert tuple(row.expected_disposition for row in ledger.receipts) == (
        ActivationDisposition.DECISIVE, ActivationDisposition.ELIGIBLE,
    ) or tuple(row.expected_disposition for row in ledger.receipts) == (
        ActivationDisposition.ELIGIBLE, ActivationDisposition.DECISIVE,
    )
    by_disposition = {row.expected_disposition: row for row in ledger.receipts}
    assert by_disposition[ActivationDisposition.ELIGIBLE].expected_cause_slot_ids == ("cause-a",)
    assert by_disposition[ActivationDisposition.DECISIVE].expected_cause_slot_ids == ()


def test_runtime_activation_census_rejects_omission_and_caller_disposition_api():
    registry = site_registry(slots=("cause-a",))
    expected_factory = ExpectedActivationLedgerFactory(
        registry, ledger_id="expected-ledger", result_occurrence_id="result-1",
        expected=(
            ExpectedActivationContract(
                "activation-a", "site-1", "attempt-a", "producer-1",
                ActivationDisposition.ELIGIBLE,
            ),
            ExpectedActivationContract(
                "activation-b", "site-1", "attempt-b", "producer-1",
                ActivationDisposition.DECISIVE,
            ),
        ),
    )
    runtime = expected_factory.open_runtime_ledger()
    runtime.record(expected_factory.ledger.authorities[0])
    with pytest.raises(ValueError, match="differs from expected ledger"):
        runtime.seal()
    with pytest.raises(TypeError):
        runtime.record(  # type: ignore[call-arg]
            manifest_site_id="site-1", branch_or_attempt_id="attempt-b",
            disposition=ActivationDisposition.ELIGIBLE,
        )


def test_one_occurrence_cannot_cover_two_expected_activations_or_forged_ledger():
    registry = site_registry(slots=("cause-a",))
    expected_factory = ExpectedActivationLedgerFactory(
        registry, ledger_id="expected-ledger", result_occurrence_id="result-1",
        expected=(
            ExpectedActivationContract(
                "activation-a", "site-1", "attempt-1", "producer-1",
                ActivationDisposition.ELIGIBLE,
            ),
            ExpectedActivationContract(
                "activation-b", "site-1", "attempt-1", "producer-1",
                ActivationDisposition.ELIGIBLE, 2,
            ),
        ),
    )
    runtime = expected_factory.open_runtime_ledger()
    for expected in expected_factory.ledger.authorities:
        runtime.record(expected)
    ledger = runtime.seal()
    reason_registry, _ = registries()
    authority = occurrence_authority(reason_registry)
    runtime.bind_emission(
        activation=ledger.receipts[0], expected_cause_slot_id="cause-a",
        occurrence_authority=authority,
    )
    with pytest.raises(ValueError, match="cannot cover multiple"):
        runtime.bind_emission(
            activation=ledger.receipts[1], expected_cause_slot_id="cause-a",
            occurrence_authority=authority,
        )
    copied_ledger = copy.copy(ledger)
    finalization_factory, bundle = finalization_authority()
    projection_factory = runtime.open_projection_factory(finalization_factory)
    with pytest.raises(ValueError, match="ledger is not factory-owned"):
        typed_cause_coverage(
            copied_ledger, runtime, projection_factory, (),
        )

# -*- coding: utf-8 -*-

import json
from dataclasses import replace

import pytest

from scripts.function_tracer_pcode.equivalence.v2.census_contract import (
    CensusEntry,
    CensusManifest,
)
from scripts.function_tracer_pcode.equivalence.v2.codecs import StrictV2JsonCodec
from scripts.function_tracer_pcode.equivalence.v2.contracts import (
    BlockerEligibilityBaseRow,
    CActiveBaseRow,
    CauseOccurrence,
    CauseOccurrenceAuthority,
    CauseIdV2,
    CauseTransformationEvent,
    CauseTransformationProofReceipt,
    CensusMode,
    IdentityScope,
    ProofRequirement,
    QOpenBaseRow,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementCompletionReceipt,
    RequirementSlotDefinition,
    ResultKind,
    SatisfactionContractDefinition,
    TransformationKind,
    VerifiedLifecycleProjection,
    all_of,
    authority_digest,
    bind_satisfaction_contract,
    requirement_slot,
)
from scripts.function_tracer_pcode.equivalence.v2.decision import (
    DecisiveProofKind,
    DecisiveProofReceipt,
    ErrorReceipt,
    FinalizationAuthority,
    TerminalTimeoutReceipt,
    finalize_decision,
)
from scripts.function_tracer_pcode.equivalence.v2.legacy_codec import (
    LegacyMappingCertainty,
    LegacyRecord,
    SealedLegacyMappingRegistry,
)
from scripts.function_tracer_pcode.equivalence.v2.registry import (
    SatisfactionBindingFactory,
    SealedReasonRegistry,
    SealedRecoveryRegistry,
    SemanticCauseIdentityFactory,
)
from scripts.function_tracer_pcode.equivalence.v2.stream import (
    CauseObservedEventAuthority,
    CauseTransformedEventAuthority,
    DecisiveProofEventAuthority,
    ErrorEventAuthority,
    EventIntent,
    EventRecorder,
    EventType,
    ProcessExecutionEventAuthority,
    RequirementCompletedEventAuthority,
    SolverExecutionEventAuthority,
    StageObservationEventAuthority,
)


def _reason(reason_id="return_width_bridge_missing"):
    return ReasonDefinition(
        reason_id=reason_id,
        domain="return_observation",
        reason_class="proof_obligation",
        decision_effect="blocks_equivalence",
        allowed_target_kinds=frozenset(("relational_return",)),
        required_evidence_contract=("left_width", "right_width"),
        allowed_proof_kinds=frozenset(("bridge", "safety")),
        terminal_eligibility=False,
        canonicalization_policy_id="return-width-v1",
        recovery_addressability=RecoveryAddressability.REQUIREMENT_REQUIRED,
    )


def _contract():
    return SatisfactionContractDefinition(
        "return-width-recovery",
        1,
        (
            RequirementSlotDefinition("A", frozenset(("bridge",))),
            RequirementSlotDefinition("C", frozenset(("safety",))),
        ),
        all_of(requirement_slot("A"), requirement_slot("C")),
    )


def _bound():
    definition = _contract()
    bound = SatisfactionBindingFactory(
        SealedRecoveryRegistry.build((definition,))
    ).bind(
        contract_definition_id=definition.contract_definition_id,
        contract_version=definition.contract_version,
        bindings={
            "A": ProofRequirement("req-A", "bridge", ("return", "left")),
            "C": ProofRequirement("req-C", "safety", ("return", "right")),
        },
    )
    return definition, bound


def _codec():
    return StrictV2JsonCodec(
        reason_registry=SealedReasonRegistry.build((_reason(),)),
        recovery_registry=SealedRecoveryRegistry.build((_contract(),)),
    )


def _cause():
    return SemanticCauseIdentityFactory(SealedReasonRegistry.build((_reason(),))).create(
        reason_id="return_width_bridge_missing",
        identity_scope=IdentityScope.RELATIONAL,
        target_kind="relational_return",
        canonical_target_key=("left", "right"),
        missing_semantic_fact="canonical return equality",
        semantic_proposition=("eq", "left", "right"),
        observation_surface=("return", 64),
        active_semantic_precondition=("reachable", True),
        correspondence_contract=("ordered",),
    )


def _occurrence_authority():
    cause = _cause()
    definition, bound = _bound()
    occurrence = CauseOccurrence(
        "occ", cause, cause.reason_id, "target", "relational_return",
        IdentityScope.RELATIONAL, definition.contract_definition_id,
        definition.contract_version, definition.normalized_expression_digest,
        bound.bound_expression_digest, tuple(sorted(bound.requirement_ids())),
        ("evidence",), "typed", "snapshot", "producer", "attempt",
    )
    return CauseOccurrenceAuthority(occurrence, bound)


def _projection(active=True):
    causes = (
        CActiveBaseRow(
            "result-1", "occ-1", "cause-1", "return_width_bridge_missing",
            "return_observation", "blocks_equivalence", "relational_return",
        ),
    ) if active else ()
    requirements = (
        QOpenBaseRow("result-1", "occ-1", "cause-1", "req-A", "bridge", "target-digest"),
    ) if active else ()
    eligibility = (
        BlockerEligibilityBaseRow("result-1", "occ-1", "cause-1"),
    ) if active else ()
    return VerifiedLifecycleProjection.seal(
        result_occurrence_id="result-1",
        snapshot_digest="snapshot",
        c_active_base=causes,
        q_open_base=requirements,
        blocker_eligibility_base=eligibility,
        satisfaction_projection={"live": ("req-A",) if active else ()},
    )


def _decision_and_manifest():
    projection = _projection(active=False)
    proof = DecisiveProofReceipt.create(
        result_occurrence_id="result-1",
        lifecycle_projection_digest=projection.lifecycle_projection_digest,
        proof_kind=DecisiveProofKind.EQ_CLOSURE,
        proof_artifact_digest="eq-proof",
    )
    decision = finalize_decision(FinalizationAuthority(
        "result-1", projection, decisive_proof_receipts=(proof,),
    ))
    entry = CensusEntry(
        "result-1", ResultKind.V2_NATIVE, ("domain",), ("left", "right"),
        ("f", "f"), "stream", projection.lifecycle_projection_digest,
        decision.receipt_digest, "artifact",
    )
    manifest = CensusManifest(
        "manifest", CensusMode.V2_CANONICAL, "head", "config", (entry,),
        generated_at="diagnostic-time",
    )
    return projection, proof, decision, entry, manifest


def test_sealed_registries_reject_duplicates_and_exact_lookup_has_no_suffix_normalization():
    reason = _reason()
    with pytest.raises(ValueError, match="duplicate"):
        SealedReasonRegistry.build((reason, reason))
    registry = SealedReasonRegistry.build((reason,))
    assert registry.get(reason.reason_id) == reason
    with pytest.raises(KeyError, match="exact"):
        registry.get("prefix:return_width_bridge_missing")
    contract = _contract()
    with pytest.raises(ValueError, match="duplicate"):
        SealedRecoveryRegistry.build((contract, contract))
    with pytest.raises(KeyError, match="exact"):
        SealedRecoveryRegistry.build((contract,)).get(contract.contract_definition_id, 2)
    with pytest.raises(ValueError, match="factory-issued"):
        SealedReasonRegistry({reason.reason_id: reason})
    with pytest.raises(ValueError, match="factory-issued"):
        SealedRecoveryRegistry({(contract.contract_definition_id, 1): contract})
    with pytest.raises(ValueError, match="reason definition schema"):
        replace(reason, schema_version=2.0)
    with pytest.raises(ValueError, match="satisfaction contract schema"):
        replace(contract, schema_version=3)
    with pytest.raises(TypeError, match="positive exact integer"):
        replace(contract, contract_version=1.0)
    with pytest.raises(TypeError, match="exact boolean"):
        replace(reason, terminal_eligibility=1)


def test_semantic_factory_validates_registry_target_and_binding_factory_is_typed():
    factory = SemanticCauseIdentityFactory(SealedReasonRegistry.build((_reason(),)))
    with pytest.raises(ValueError, match="target kind"):
        factory.create(
            reason_id="return_width_bridge_missing", identity_scope=IdentityScope.RELATIONAL,
            target_kind="wrong", canonical_target_key="target",
            missing_semantic_fact="missing", semantic_proposition="p",
            observation_surface="surface", active_semantic_precondition="pre",
            correspondence_contract="corr",
        )
    definition, bound = _bound()
    bound.validate_against(definition)
    with pytest.raises(ValueError, match="sealed registry factory"):
        CauseIdV2.create(
            identity_scope=IdentityScope.RELATIONAL, reason_id="unregistered",
            canonical_target_key="target", missing_semantic_fact="missing",
            semantic_proposition="p", observation_surface="surface",
            active_semantic_precondition="pre", correspondence_contract="corr",
        )
    with pytest.raises(ValueError, match="sealed registry factory"):
        bind_satisfaction_contract(definition, {
            "A": ProofRequirement("req-A", "bridge", "target"),
            "C": ProofRequirement("req-C", "safety", "target"),
        })


def test_legacy_reader_is_byte_for_byte_lossless_and_projection_is_non_authoritative():
    raw = '{ "reason_id" : "old:timeout", "detail" : [1, 2] }\n'
    record = LegacyRecord.read(raw)
    assert record.write_lossless() == raw
    mapping = SealedLegacyMappingRegistry.build((
        ("old:timeout", None, LegacyMappingCertainty.UMBRELLA),
    ))
    projection = mapping.project(record)
    assert projection.raw_reason_id == "old:timeout"
    assert projection.mapped_reason_id is None
    assert projection.mapping_certainty == LegacyMappingCertainty.UMBRELLA
    assert projection.non_authoritative is True
    unmapped = mapping.project(LegacyRecord.read('{"reason_id":"return_width_bridge_missing:suffix"}'))
    assert unmapped.mapping_certainty == LegacyMappingCertainty.UNMAPPED
    with pytest.raises(ValueError, match="factory-issued"):
        SealedLegacyMappingRegistry({})
    with pytest.raises(ValueError, match="duplicate"):
        SealedLegacyMappingRegistry.build((
            ("same", "one", LegacyMappingCertainty.EXACT),
            ("same", "two", LegacyMappingCertainty.AMBIGUOUS),
        ))
    with pytest.raises(ValueError, match="lossless reader"):
        LegacyRecord(raw, {"reason_id": "different"})


def test_strict_codec_round_trips_event_projection_receipts_relations_and_manifest():
    codec = _codec()
    recorder = EventRecorder(
        stream_id="stream", result_occurrence_id="result-1",
        source_snapshot_fingerprint="snapshot",
    )
    recorder.append(EventIntent(
        EventType.CAUSE_OBSERVED,
        CauseObservedEventAuthority(_occurrence_authority()),
    ))
    stream = recorder.seal()
    projection, proof, decision, entry, manifest = _decision_and_manifest()
    active_projection = _projection()
    timeout = TerminalTimeoutReceipt.create(
        result_occurrence_id="result-1",
        lifecycle_projection_digest=active_projection.lifecycle_projection_digest,
        proof_requirement_id="req-A", execution_event_digest="event",
    )
    error = ErrorReceipt.create(
        result_occurrence_id="result-1",
        lifecycle_projection_digest=projection.lifecycle_projection_digest,
        error_kind="internal", error_artifact_digest="error",
    )
    for value in (
        _reason(), _cause(), ProofRequirement("req", "bridge", ("target",)),
        _occurrence_authority(),
        stream, projection, active_projection,
        active_projection.c_active_base, active_projection.q_open_base,
        active_projection.blocker_eligibility_base, proof, timeout, error,
        decision, entry, manifest,
    ):
        if isinstance(value, tuple):
            for row in value:
                assert codec.loads(codec.dumps(row)) == row
        else:
            assert codec.loads(codec.dumps(value)) == value


def test_strict_codec_round_trips_occurrence_completion_and_transformation_models():
    codec = _codec()
    cause = _cause()
    definition, bound = _bound()
    occurrence = CauseOccurrence(
        "occ", cause, cause.reason_id, "target", "relational_return",
        IdentityScope.RELATIONAL, definition.contract_definition_id,
        definition.contract_version, definition.normalized_expression_digest,
        bound.bound_expression_digest, tuple(sorted(bound.requirement_ids())),
        ("evidence",), "typed", "snapshot", "producer", "attempt",
    )
    completion = RequirementCompletionReceipt(
        cause.value, "occ", "req-A", definition.contract_definition_id,
        definition.contract_version, bound.bound_expression_digest,
        "proof", "applicability",
    )
    event = CauseTransformationEvent(
        TransformationKind.REPLACEMENT, ("old",), ("new",),
        "receipt", "stage", "snapshot",
    )
    transformation_receipt = CauseTransformationProofReceipt(
        "receipt", (("old", "old-cause"),), (("new", "new-cause"),),
        (("old-req", "new-req"),), "snapshot", True,
    )
    occurrence_authority = CauseOccurrenceAuthority(occurrence, bound)
    for value in (occurrence_authority, completion, event, transformation_receipt):
        assert codec.loads(codec.dumps(value)) == value


def test_event_payload_union_rejects_wrong_type_status_and_unbound_cause():
    with pytest.raises(TypeError, match="exact occurrence authority"):
        CauseObservedEventAuthority("not-authority")
    with pytest.raises(TypeError, match="exact completion receipt"):
        RequirementCompletedEventAuthority("not-receipt")
    with pytest.raises(TypeError, match="exact CauseObserved"):
        EventIntent(EventType.CAUSE_OBSERVED, {"occurrence": "not-typed"})
    with pytest.raises(ValueError, match="status differ"):
        EventIntent(
            EventType.SOLVER_TIMEOUT,
            SolverExecutionEventAuthority("req", "solver", "UNKNOWN"),
        )
    cause = _cause()
    definition, bound = _bound()
    forged_occurrence = CauseOccurrence(
        "occ", cause, cause.reason_id, "target", "relational_return",
        IdentityScope.RELATIONAL, definition.contract_definition_id,
        definition.contract_version, definition.normalized_expression_digest,
        "forged-bound-digest", tuple(sorted(bound.requirement_ids())),
        ("evidence",), "typed", "snapshot", "producer", "attempt",
    )
    with pytest.raises(ValueError, match="differs from bound"):
        CauseOccurrenceAuthority(forged_occurrence, bound)


def test_all_event_payload_variants_round_trip_as_typed_authority():
    codec = _codec()
    occurrence_authority = _occurrence_authority()
    occurrence = occurrence_authority.occurrence
    bound = occurrence_authority.bound_contract
    completion = RequirementCompletionReceipt(
        occurrence.cause_id.value, occurrence.occurrence_id, "req-A",
        bound.contract_definition_id, bound.contract_version,
        bound.bound_expression_digest, "proof", "applicability",
    )
    transformation = CauseTransformationEvent(
        TransformationKind.REPLACEMENT, ("old",), ("new",),
        "transform-proof", "stage", "snapshot",
    )
    transformation_proof = CauseTransformationProofReceipt(
        "transform-proof", (("old", "old-cause"),),
        (("new", "new-cause"),), (("old-req", "new-req"),),
        "snapshot", True,
    )
    intents = (
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(occurrence_authority)),
        EventIntent(EventType.REQUIREMENT_COMPLETED, RequirementCompletedEventAuthority(completion)),
        EventIntent(EventType.CAUSE_TRANSFORMED, CauseTransformedEventAuthority(transformation, transformation_proof)),
        EventIntent(EventType.SOLVER_UNKNOWN, SolverExecutionEventAuthority("req-A", "s1", "UNKNOWN")),
        EventIntent(EventType.SOLVER_TIMEOUT, SolverExecutionEventAuthority("req-A", "s2", "TIMEOUT", 1000)),
        EventIntent(EventType.SOLVER_ERROR, SolverExecutionEventAuthority("req-A", "s3", "ERROR")),
        EventIntent(EventType.PROCESS_TIMEOUT, ProcessExecutionEventAuthority("req-A", "p1")),
        EventIntent(EventType.CANCELLED, ProcessExecutionEventAuthority("req-A", "p2")),
        EventIntent(EventType.NORMALIZATION_NO_CHANGE, StageObservationEventAuthority("normalize", "a1")),
        EventIntent(EventType.REWRITE_NO_CHANGE, StageObservationEventAuthority("rewrite", "a2")),
        EventIntent(EventType.EQ_CLOSURE, DecisiveProofEventAuthority("eq-proof")),
        EventIntent(EventType.COUNTEREXAMPLE, DecisiveProofEventAuthority("cex-proof")),
        EventIntent(EventType.ERROR, ErrorEventAuthority("internal", "error-proof")),
    )
    recorder = EventRecorder(
        stream_id="all-events", result_occurrence_id="result-1",
        source_snapshot_fingerprint="snapshot",
    )
    for intent in intents:
        recorder.append(intent)
    stream = recorder.seal()
    decoded = codec.loads(codec.dumps(stream))
    assert decoded == stream
    assert tuple(type(event.authority_payload) for event in decoded.events) == tuple(
        type(intent.authority_payload) for intent in intents
    )


def test_strict_codec_rejects_tamper_unknown_fields_types_and_schema():
    codec = _codec()
    raw = codec.dumps(_projection())
    envelope = json.loads(raw)
    envelope["payload"]["snapshot_digest"] = "tampered"
    with pytest.raises(ValueError, match="payload digest"):
        codec.loads(json.dumps(envelope))
    envelope = json.loads(raw)
    envelope["extra"] = True
    with pytest.raises(ValueError, match="fields differ"):
        codec.loads(json.dumps(envelope))
    envelope = json.loads(raw)
    envelope["schema_version"] = 1
    with pytest.raises(ValueError, match="schema"):
        codec.loads(json.dumps(envelope))
    envelope = json.loads(raw)
    envelope["object_type"] = "LegacyProjection"
    with pytest.raises(ValueError, match="unknown strict"):
        codec.loads(json.dumps(envelope))
    with pytest.raises(TypeError, match="unregistered"):
        codec.dumps({"reason_id": "return_width_bridge_missing"})
    with pytest.raises(ValueError, match="duplicate strict"):
        codec.loads('{"schema_version":2,"schema_version":2}')
    with pytest.raises(TypeError, match="unregistered"):
        codec.dumps(_occurrence_authority().occurrence)
    with pytest.raises(ValueError, match="projection"):
        codec.dumps(replace(_projection(), lifecycle_projection_digest="forged"))
    invalid_proof_projection = VerifiedLifecycleProjection.seal(
        result_occurrence_id="result-1", snapshot_digest="snapshot",
        c_active_base=_projection().c_active_base,
        q_open_base=(replace(_projection().q_open_base[0], proof_kind="not-registered"),),
        blocker_eligibility_base=_projection().blocker_eligibility_base,
        satisfaction_projection={},
    )
    with pytest.raises(ValueError, match="proof kind"):
        codec.dumps(invalid_proof_projection)

    unknown_factory = SemanticCauseIdentityFactory(
        SealedReasonRegistry.build((_reason("different"),))
    )
    unknown_cause = unknown_factory.create(
        reason_id="different", identity_scope=IdentityScope.RELATIONAL,
        target_kind="relational_return", canonical_target_key="target",
        missing_semantic_fact="missing", semantic_proposition="p",
        observation_surface="surface", active_semantic_precondition="pre",
        correspondence_contract="corr",
    )
    with pytest.raises(KeyError, match="unknown exact"):
        codec.dumps(unknown_cause)


def test_strict_codec_rejects_exact_type_and_inner_schema_coercion():
    with pytest.raises(TypeError, match="exact strings"):
        QOpenBaseRow("result", "occ", "cause", "req", 123, "target-digest")
    with pytest.raises(TypeError, match="result occurrence"):
        VerifiedLifecycleProjection.seal(
            result_occurrence_id=123, snapshot_digest=456, c_active_base=(),
            q_open_base=(), blocker_eligibility_base=(), satisfaction_projection={},
        )
    codec = _codec()
    recorder = EventRecorder(
        stream_id="stream", result_occurrence_id="result-1",
        source_snapshot_fingerprint="snapshot",
    )
    recorder.append(EventIntent(
        EventType.CAUSE_OBSERVED,
        CauseObservedEventAuthority(_occurrence_authority()),
    ))
    stream = recorder.seal()
    envelope = json.loads(codec.dumps(stream))
    envelope["payload"]["events"][0]["header"]["schema_version"] = "2"
    envelope["payload_digest"] = authority_digest(envelope["payload"])
    with pytest.raises(TypeError, match="exact integer 2"):
        codec.loads(json.dumps(envelope))
    cause_envelope = json.loads(codec.dumps(_cause()))
    cause_envelope["payload"]["schema_version"] = "2"
    cause_envelope["payload_digest"] = authority_digest(cause_envelope["payload"])
    with pytest.raises(TypeError, match="exact integer 2"):
        codec.loads(json.dumps(cause_envelope))
    float_schema = json.loads(codec.dumps(_cause()))
    float_schema["payload"]["schema_version"] = 2.0
    float_schema["payload_digest"] = authority_digest(float_schema["payload"])
    with pytest.raises(TypeError, match="exact integer 2"):
        codec.loads(json.dumps(float_schema))
    with pytest.raises(ValueError, match="registry-factory"):
        replace(_cause(), schema_version=2.0)
    forged_stream = replace(
        stream, envelope=replace(stream.envelope, schema_version=3)
    )
    with pytest.raises(ValueError, match="envelope schema"):
        forged_stream.validate()
    with pytest.raises(ValueError, match="envelope schema"):
        codec.dumps(forged_stream)


def test_phase2_models_do_not_change_existing_final_decision_path():
    codec = _codec()
    projection, _, decision, _, _ = _decision_and_manifest()
    decoded = codec.loads(codec.dumps(decision))
    assert decoded.outcome == decision.outcome
    assert projection.c_active_base == ()

from dataclasses import replace
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.equivalence.v2.abi_width_readonly import (
    ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY,
    ABI_WIDTH_READONLY_PRODUCER_STAGE_REGISTRY_DIGEST,
    ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS,
    ABI_WIDTH_READONLY_PRODUCTION_SOURCE_REASON_IDS,
    ABI_WIDTH_READONLY_REASON_REGISTRY,
    ABI_WIDTH_READONLY_REASON_SPECS,
    ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
    EXPECTED_ABI_WIDTH_READONLY_COMMON_REGISTRY_DIGEST,
    EXPECTED_ABI_WIDTH_READONLY_PRODUCER_STAGE_REGISTRY_DIGEST,
    AbiWidthReadonlyBlockerSignal,
    AbiWidthReadonlyCapability,
    AbiWidthReadonlyDisposition,
    AbiWidthReadonlyPilotEncoder,
    AbiWidthReadonlyProducerStageSpec,
    ReturnAbiAuthorityInvalid,
    AbiWidthReadonlySolverExecutionBatchSignal,
    AbiWidthReadonlySolverQueryAuthority,
    ReturnAbiProvenanceArtifact,
    ReturnAbiRelationArtifact,
    ReturnAbiRelationStatus,
    ReturnHighBitRelationProofArtifact,
    ReturnObservationProjectionSeed,
    ReturnObservationNeedSeed,
    ProjectionNotFormable,
    ReturnObservationContractArtifact,
    FunctionReturnAbiSeed,
    ReturnWidthProvenanceArtifact,
    SameFunctionReturnWidthRelationArtifact,
    ReadonlyReductionObjectSetSeed,
    ReadonlyCorrespondenceFactSet,
    ResolvedReadonlyObjectSetSeed,
    ReadonlyStorageIdentityArtifact,
    ReadonlyObjectCorrespondenceArtifact,
    abi_width_readonly_registry_authority_dict,
    classify_readonly_source,
    classify_summary_width_source,
    classify_width_blocker,
    validate_abi_width_readonly_registry_conservation,
    validate_abi_width_readonly_production_source_conservation,
    summary_abi_width_signals_from_acceptance,
    assess_return_abi_pair,
)
from scripts.function_tracer_pcode.equivalence.v2.contracts import (
    IdentityScope,
    Outcome,
    authority_digest,
)
from scripts.function_tracer_pcode.equivalence.v2.stream import EventType
from scripts.function_tracer_pcode.equivalence.return_width_surface import (
    ExtensionEvidenceSource,
    FunctionReturnWidthSeed,
    FunctionReturnWidthTargetId,
    GuardRegionFact,
    GuardRegionTargetId,
    PairReturnObservationSeed,
    PairReturnObservationTargetId,
    build_top_level_observation_contract,
)
from scripts.function_tracer_pcode.equivalence.return_width_pipeline import (
    PreparedFunctionReturnWidths,
    prepare_pair_return_observation,
)
from scripts.function_tracer_pcode.model import FunctionReturnAnalysis


def _session(result_id="result-1"):
    return SimpleNamespace(identity=SimpleNamespace(
        result_occurrence_id=result_id,
        source_snapshot_fingerprint="source-snapshot",
        execution_identity_digest="execution-identity",
    ))


def _width_seed(side, *, missing=(), function_identity=None):
    guard_target = GuardRegionTargetId(
        ("return-member", side), (("guard-slot", side),)
    )
    target = FunctionReturnWidthTargetId(
        function_identity or ("function", side), ("return-member", side), guard_target
    )
    return FunctionReturnWidthSeed(
        target,
        GuardRegionFact("complete", (("guard", side),)),
        None if "return_storage_fact" in missing else 64,
        None if "payload_width_fact" in missing else 32,
        ("storage", side, 64),
        ("payload", side, 32),
        ("return_type_provenance", ("declared_return_type_width", 32)),
        ExtensionEvidenceSource(
            "unsupported" if "extension_evidence_fact" in missing else "zero_extend",
            ("storage-value", side),
            ("payload-value", side),
            (("producer", side),),
            "certified_flow" if "extension_evidence_fact" not in missing else None,
        ),
        tuple(missing),
    )


def _projection_parts():
    left = _width_seed("left")
    right = _width_seed("right")
    target = PairReturnObservationTargetId(
        "top_level_return",
        left.target_id,
        right.target_id,
        (left.target_id.function_identity, right.target_id.function_identity),
    )
    pair = PairReturnObservationSeed(
        target,
        left.digest,
        right.digest,
        "top_level_return",
        target.semantic_anchors,
    )
    return left, right, ReturnObservationProjectionSeed.from_pair_seed(left, right, pair)


def _projection_seed():
    return _projection_parts()[2]


def _slice5_fixture_projection_parts(high_bit):
    function_name = "slice5_high_bit_projection"

    def analysis(side):
        return FunctionReturnAnalysis(
            function_name,
            "0x1000" if side == "left" else "0x2000",
            [],
            [],
            binary_id="sha256:" + high_bit[f"{side}_binary_sha256"],
        )

    left_analysis, right_analysis = analysis("left"), analysis("right")

    def seed(side, analysis_item, raw_width, extension_kind, detail=()):
        target = FunctionReturnWidthTargetId(
            analysis_item.outcome_function_identity(),
            ("slice5-fixture-return", side, function_name, raw_width),
            GuardRegionTargetId(
                ("slice5-fixture-return", side, function_name, raw_width),
                (("unconditional", function_name),),
            ),
        )
        return FunctionReturnWidthSeed(
            target,
            GuardRegionFact("complete", (("unconditional", function_name),)),
            64,
            32,
            (
                "abi_normalized_return_storage_v1",
                ("raw_binary_return_width", raw_width),
                ("normalized_storage_width", 64),
                ("binary_content_identity", "sha256", high_bit[f"{side}_binary_sha256"]),
            ),
            ("slice5-fixture-payload", side, function_name, 32),
            (
                "slice5_fixture_abi_relation_v1",
                ("raw_width", raw_width),
                ("normalized_width", 64),
            ),
            ExtensionEvidenceSource(
                extension_kind,
                ("slice5-fixture-storage-value", side),
                ("slice5-fixture-payload-value", side),
                (("source_sha256", high_bit[f"{side}_source_sha256"]),),
                "certified_source_and_binary_fixture",
                tuple(detail),
                (
                    "slice5_fixture_binding_v1",
                    high_bit[f"{side}_binary_sha256"],
                    high_bit[f"{side}_source_sha256"],
                    function_name,
                    raw_width,
                ),
            ),
        )

    left = seed("left", left_analysis, 32, "zero_extend")
    right = seed(
        "right",
        right_analysis,
        64,
        "zero_extend_or_mask:1099511627776",
    )
    target = PairReturnObservationTargetId(
        "top_level_return",
        left.target_id,
        right.target_id,
        (
            left.target_id.function_identity,
            right.target_id.function_identity,
            ("raw_return_widths", 32, 64),
        ),
    )
    pair = PairReturnObservationSeed(
        target,
        left.digest,
        right.digest,
        "top_level_return",
        target.semantic_anchors,
    )
    projection = ReturnObservationProjectionSeed.from_pair_seed(left, right, pair)
    return left_analysis, right_analysis, left, right, projection


def _readonly_seed(
    *, identified=False, right_pointer_index=0,
    right_term_offset_delta=0, right_reduction_kind="memory_sum",
    pointer_kind="parameter", owner_specific_parameter=False,
):
    from scripts.function_tracer_pcode.model import (
        Expression,
        LocationBaseRef,
        ReadonlyReductionRef,
        ReadonlyReductionTermRef,
        ReadonlyReductionWitness,
        ReductionAccumulatorProof,
        ReturnInfo,
    )
    from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import (
        ReturnCase,
    )

    analyses = []
    cases = []
    for side in ("left", "right"):
        pointer_index = right_pointer_index if side == "right" else 0
        reduction_kind = (
            right_reduction_kind if side == "right" else "memory_sum"
        )
        offset_delta = right_term_offset_delta if side == "right" else 0
        if pointer_kind == "storage":
            pointer_base = LocationBaseRef.storage(
                space_name="ram", offset=0x1000, size=8
            )
        else:
            pointer_base = LocationBaseRef.parameter(
                "base",
                index=pointer_index,
                owner_program_id=(1 if side == "left" else 2)
                if owner_specific_parameter else None,
                owner_entry_offset=0x1000 if owner_specific_parameter else None,
            )
        analysis = FunctionReturnAnalysis(
            f"readonly-{side}", f"0x{1 if side == 'left' else 2}000",
            [], [], binary_id=f"binary-{side}",
        )
        witness = ReadonlyReductionWitness(
            exact_count=2,
            terms=(
                ReadonlyReductionTermRef(
                    byte_offset=offset_delta, access_size=4
                ),
                ReadonlyReductionTermRef(
                    byte_offset=4 + offset_delta, access_size=4
                ),
            ),
        )
        proof = ReductionAccumulatorProof(
            reduction_kind=reduction_kind,
            pointer_base_ref=pointer_base,
            count_parameter_name="count",
            count_parameter_index=1,
            limit_expr=Expression.parameter("count", 4),
            result_size=4,
            stride=4,
            element_size=4,
            exact_return_witnesses=(witness,),
            return_region_value_proven=True,
        )
        ref = ReadonlyReductionRef(
            reduction_kind=reduction_kind,
            pointer_base_ref=pointer_base,
            count_parameter_name="count",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            semantic_witnesses=(witness,),
            accumulator_proof=proof if identified else None,
        )
        value = Expression.intrinsic(
            "READONLY_SUM", (), size=4, runtime_ref=ref, opcode=0xF001
        )
        ret = ReturnInfo(address=f"0x{1 if side == 'left' else 2}008", value=value, conditions=[])
        analyses.append(analysis)
        cases.append(ReturnCase(0, [], value, ret, program_is_big_endian=False))
    return ReadonlyReductionObjectSetSeed.from_analyses_and_cases(
        analyses[0], analyses[1], cases[0], cases[1]
    )


def _run_readonly_solver_fixture(monkeypatch, case_id, statuses):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        execute_abi_width_readonly_solver_query,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    key_id = "abi-width-fixture-" + case_id
    install_execution_authority_signing_key(key_id, (case_id.encode() * 32)[:32])
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "abi-width-policy-" + case_id, 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    monkeypatch.setattr(
        execution_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult(
                f"solver-{index}", status, elapsed_time=timeout,
                model={} if status.name == "SAT" else None,
            )
            for index, status in enumerate(statuses)
        ]),
    )
    encoder = AbiWidthReadonlyPilotEncoder(enable_solver_execution=True)
    composite = CompositeProductionSignalEncoder({
        AbiWidthReadonlyBlockerSignal: encoder,
        AbiWidthReadonlySolverExecutionBatchSignal: encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": case_id})
    resolved = ResolvedReadonlyObjectSetSeed.from_live_completion_closure(
        session, _readonly_seed(identified=True), ()
    )
    blocker = AbiWidthReadonlyBlockerSignal.from_readonly_object_sets(resolved)
    with production_signal_scope(session):
        session.emit_domain_signal(blocker)
        query = (
            AbiWidthReadonlySolverQueryAuthority
            .from_readonly_correspondence_theorem(session, blocker, resolved)
        )
        session.domain_signal_state["readonly_solver_fixture_authority"] = (
            blocker, query, resolved
        )
        emitted = execute_abi_width_readonly_solver_query(
            blocker, query, resolved, (), configured_timeout_ms=1000
        )
    return connector, session, encoder, emitted


def _abi_relation_artifact(
    source_snapshot="source-snapshot", *, include_unary=False,
    right_extension_kind="zero_extend", fixture=None,
):
    def analysis(side):
        return FunctionReturnAnalysis(
            f"function-{side}", f"0x{1 if side == 'left' else 2}000",
            [], [], binary_id=f"binary-{side}",
        )

    if fixture is None:
        left_analysis, right_analysis = analysis("left"), analysis("right")
        left = _width_seed(
            "left", function_identity=left_analysis.outcome_function_identity()
        )
        right = _width_seed(
            "right", function_identity=right_analysis.outcome_function_identity()
        )
    else:
        left_analysis, right_analysis, left, right, projection = (
            _slice5_fixture_projection_parts(fixture)
        )
    if fixture is None and right_extension_kind != "zero_extend":
        right = replace(
            right,
            extension_evidence_source=ExtensionEvidenceSource(
                right_extension_kind,
                ("storage-value", "right"),
                ("payload-value", "right"),
                (("producer", "right"),),
                "certified_flow",
            ),
        )
    if fixture is None:
        target = PairReturnObservationTargetId(
            "top_level_return", left.target_id, right.target_id,
            (left.target_id.function_identity, right.target_id.function_identity),
        )
        pair = PairReturnObservationSeed(
            target, left.digest, right.digest, "top_level_return", target.semantic_anchors
        )
        projection = ReturnObservationProjectionSeed.from_pair_seed(left, right, pair)
    artifacts = []
    abi_seeds = []
    for side, analysis_item, seed in (
        ("left", left_analysis, left), ("right", right_analysis, right)
    ):
        analysis_item.return_abi_facts = {
            "schema_version": 1,
            "calling_convention": {"status": "MISSING", "value": None, "source": "test-ghidra-prototype"},
            "declared_or_effective_return_type": {"status": "PRESENT", "value": ("ghidra_return_type_v1", "/int", 4), "source": "test-ghidra-type"},
            "return_storage_descriptor": {"status": "PRESENT", "value": ("ghidra_return_storage_v1", (("ghidra_return_storage_member_v1", "register", 0 if side == "left" else 8, 8),)), "source": "test-ghidra-storage"},
        }
        missing = FunctionReturnAbiSeed.from_analysis_and_width_seed(
            analysis_item, seed
        )
        abi_seeds.append(missing)
        blocker = AbiWidthReadonlyBlockerSignal.from_return_abi_seed(
            missing, "calling_convention"
        )
        artifacts.append(ReturnAbiProvenanceArtifact.from_ghidra_facts(
            blocker,
            missing,
            source_snapshot_fingerprint=source_snapshot,
            missing_slot="calling_convention",
            calling_convention_key=("cc", seed.target_id.function_identity),
            return_type_key=("return-type", 32),
            return_storage_key=seed.storage_identity,
            provenance_refs=(("ghidra-api", seed.target_id.function_identity),),
        ))
    blocker = AbiWidthReadonlyBlockerSignal.from_projection_seed(
        "return_abi_relation_unproven", projection
    )
    relation = ReturnAbiRelationArtifact.from_projection_seed(
        blocker,
        projection,
        left_abi_artifact=artifacts[0],
        right_abi_artifact=artifacts[1],
        source_snapshot_fingerprint=source_snapshot,
        calling_conventions_individually_valid=True,
        storage_projection_related=True,
        observation_applicable=True,
    )
    if include_unary:
        return projection, relation, tuple(artifacts), tuple(abi_seeds)
    return projection, relation


def _rematerialize_slice5_lifecycle_matrix():
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )

    rows = {}
    for reason_id in ABI_WIDTH_READONLY_REASON_SPECS:
        encoder = AbiWidthReadonlyPilotEncoder()
        session = ProductionDualWritePilotConnector(
            ShadowLifecycleReducer(
                reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
                recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
            ),
            domain_signal_encoder=encoder,
        ).begin({"case": "slice5-lifecycle-" + reason_id})
        snapshot = session.identity.source_snapshot_fingerprint

        if reason_id == "return_width_provenance_unavailable":
            seed = _width_seed("matrix-width", missing=("return_storage_fact",))
            blocker = AbiWidthReadonlyBlockerSignal.from_width_seed(
                seed, "return_storage_fact"
            )
            artifact = ReturnWidthProvenanceArtifact.from_validated_fact(
                blocker, seed, source_snapshot_fingerprint=snapshot,
                slot="return_storage_fact", positive_width=64,
            )
            completion = encoder.complete_return_width_provenance
        elif reason_id == "return_width_relation_unproven":
            identity = ("function", "matrix-width-relation")
            first = _width_seed("matrix-first", function_identity=identity)
            second = _width_seed("matrix-second", function_identity=identity)
            blocker = AbiWidthReadonlyBlockerSignal.from_same_function_width_seeds(
                first, second
            )
            artifact = SameFunctionReturnWidthRelationArtifact.from_validated_relation(
                blocker, first, second, source_snapshot_fingerprint=snapshot,
                observation_width=32, total=True,
                observation_preserving=True, injective_lossless=True,
            )
            completion = encoder.complete_same_function_return_width_relation
        elif reason_id == "return_abi_provenance_unavailable":
            _projection, _relation, artifacts, seeds = _abi_relation_artifact(
                snapshot, include_unary=True
            )
            blocker = AbiWidthReadonlyBlockerSignal.from_return_abi_seed(
                seeds[0], "calling_convention"
            )
            artifact = artifacts[0]
            completion = encoder.complete_return_abi_provenance
        elif reason_id in {
            "return_observation_contract_unproven",
            "return_abi_relation_unproven",
            "return_high_bit_relation_unproven",
        }:
            projection, abi_relation = _abi_relation_artifact(snapshot)
            blocker = AbiWidthReadonlyBlockerSignal.from_projection_seed(
                reason_id, projection
            )
            if reason_id == "return_observation_contract_unproven":
                artifact = ReturnObservationContractArtifact.from_projection_seed(
                    blocker, projection,
                    derivation="common_validated_semantic_payload_width",
                    projection_policy="identity",
                    source_snapshot_fingerprint=snapshot,
                )
                completion = encoder.complete_return_observation_contract
            elif reason_id == "return_abi_relation_unproven":
                artifact = abi_relation
                completion = encoder.complete_return_abi_relation
            else:
                artifact = ReturnHighBitRelationProofArtifact.from_structural_theorem(
                    blocker, projection, abi_relation,
                    source_snapshot_fingerprint=snapshot,
                    theorem_id="validated_zero_extend_projection_v1",
                    validated_premises=(
                        ("left", "zero_extend"),
                        ("right", "zero_extend"),
                    ),
                )
                completion = encoder.complete_return_high_bit_relation
        elif reason_id == "readonly_storage_identity_unproven":
            seed = _readonly_seed()
            blocker = AbiWidthReadonlyBlockerSignal.from_readonly_member(
                seed, "left", 0
            )
            artifact = ReadonlyStorageIdentityArtifact.from_validated_storage(
                blocker, seed, side="left", member_index=0,
                source_snapshot_fingerprint=snapshot,
                address_space="ram", width=4, endian="little",
                readonly_block=True, provenance_refs=(("matrix-memory",),),
                reachable_use_proof=("matrix-all-reachable-uses",),
            )
            completion = encoder.complete_readonly_storage_identity
        else:
            resolved = ResolvedReadonlyObjectSetSeed.from_live_completion_closure(
                session, _readonly_seed(identified=True), ()
            )
            blocker = AbiWidthReadonlyBlockerSignal.from_readonly_object_sets(
                resolved
            )
            artifact = ReadonlyObjectCorrespondenceArtifact.from_unique_total_mapping(
                blocker, resolved,
                mapping=tuple(zip(
                    (authority_digest(item) for item in resolved.left_member_keys),
                    (authority_digest(item) for item in resolved.right_member_keys),
                )),
                source_snapshot_fingerprint=snapshot,
                operator_preserved=True,
                roles_order_multiplicity_preserved=True,
                count_identity_proved=True,
                guard_iteration_proved=True,
                load_shape_proved=True,
                value_observation_proved=True,
                finite_witness_complete=True,
            )
            completion = encoder.complete_readonly_object_correspondence

        assert session.emit_domain_signal(blocker) == 1
        observed = session.preview_lifecycle_projection()
        session.emit(completion(session, blocker, artifact))
        completed = session.preview_lifecycle_projection()
        sealed = session.recorder.seal()
        rows[reason_id] = {
            "proof_kind": ABI_WIDTH_READONLY_REASON_SPECS[reason_id].proof_kind,
            "observed": {
                "c_active": len(observed.c_active_base),
                "q_open": len(observed.q_open_base),
            },
            "completed": {
                "c_active": len(completed.c_active_base),
                "q_open": len(completed.q_open_base),
            },
            "completion_entrypoint": completion.__name__,
            "sealed_event_stream_digest": sealed.envelope.authority_chain_digest,
        }
    return rows


def _rematerialize_slice5_aggregation_gates(monkeypatch):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.census_contract import (
        ActiveOccurrenceMaterialization,
        CensusEntry,
        CensusManifest,
        CensusStatus,
        CoverageInputs,
    )
    from scripts.function_tracer_pcode.equivalence.v2.contracts import (
        CensusMode,
        RecoveryAddressability,
        ResultKind,
    )
    from scripts.function_tracer_pcode.equivalence.v2.shadow_compare import (
        build_shadow_census_preview,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverStatus
    from scripts.function_tracer_pcode.equivalence.v2.stream import (
        DecisiveProofEventAuthority,
        EventIntent,
    )

    nonce_counter = iter(range(1, 1000))
    monkeypatch.setattr(
        execution_module.secrets,
        "token_hex",
        lambda size: f"{next(nonce_counter):0{size * 2}x}",
    )

    def run(case_id, statuses, legacy_is_equivalent):
        connector, session, encoder, _emitted = _run_readonly_solver_fixture(
            monkeypatch, case_id, statuses
        )
        encoder.finalize_open_execution_history(session)
        if legacy_is_equivalent is True:
            session.emit(EventIntent(
                EventType.EQ_CLOSURE,
                DecisiveProofEventAuthority("slice5-recovered-timeout-eq-proof"),
            ))
        evidence = connector.finish(
            session,
            SimpleNamespace(
                error_message=None,
                is_equivalent=legacy_is_equivalent,
                failure_status=None,
                failure_message=None,
                is_timeout=lambda: False,
            ),
            case_id=case_id,
        )
        pilot = evidence.pilot_result
        projection = pilot.reduction.projection
        snapshot = pilot.reduction.snapshot
        return ({
            "decision": pilot.candidate.decision_receipt.outcome.value,
            "c_active": len(projection.c_active_base),
            "q_open": len(projection.q_open_base),
            "terminal_timeout_events": pilot.terminal_timeout_receipt_count,
            "observed_nonterminal_timeout_events": (
                pilot.observed_nonterminal_timeout_event_count
            ),
        }, pilot)

    terminal, terminal_pilot = run(
        "slice5-artifact-terminal-timeout", (SolverStatus.TIMEOUT,), None
    )
    recovered, recovered_pilot = run(
        "slice5-artifact-recovered-timeout",
        (SolverStatus.TIMEOUT, SolverStatus.UNSAT),
        True,
    )
    unknown, unknown_pilot = run(
        "slice5-artifact-solver-unknown", (SolverStatus.UNKNOWN,), None
    )
    conflict, conflict_pilot = run(
        "slice5-artifact-sat-unsat-conflict",
        (SolverStatus.SAT, SolverStatus.UNSAT),
        None,
    )
    pilots = (
        terminal_pilot, recovered_pilot, unknown_pilot, conflict_pilot
    )
    entries = tuple(CensusEntry(
        pilot.reduction.snapshot.result_occurrence_id,
        ResultKind.V2_NATIVE,
        ("slice5-aggregation",),
        ("typed-fixture",),
        ("readonly-correspondence",),
        pilot.reduction.snapshot.event_stream_authority_digest,
        pilot.reduction.projection.lifecycle_projection_digest,
        pilot.candidate.decision_receipt.receipt_digest,
        authority_digest((
            "slice5-aggregation-result",
            pilot.reduction.snapshot.result_occurrence_id,
            pilot.pilot_receipt_digest,
        )),
    ) for pilot in pilots)
    manifest = CensusManifest(
        "slice5-aggregation-manifest",
        CensusMode.V2_CANONICAL,
        "29376ea952073e52185cb1821eebb6d04a383ef3",
        authority_digest(("slice5-aggregation-config", 1)),
        entries,
    )
    active_rows = tuple(
        row for pilot in pilots
        for row in pilot.reduction.projection.c_active_base
    )
    coverage = CoverageInputs(tuple(
        ActiveOccurrenceMaterialization(
            row.result_occurrence_id, row.occurrence_id, row.cause_id,
            RecoveryAddressability.REQUIREMENT_REQUIRED,
        )
        for row in active_rows
    ))
    census = build_shadow_census_preview(
        manifest,
        tuple(pilot.candidate for pilot in pilots),
        tuple(pilot.reduction.projection for pilot in pilots),
        tuple(pilot.sealed_event_stream for pilot in pilots),
        coverage_inputs=coverage,
    )
    assert census.status is CensusStatus.VALID
    metrics = census.canonical_metrics
    assert metrics is not None
    result_ids = [entry.result_occurrence_id for entry in manifest.entries]
    decision_ids = tuple(
        pilot.candidate.decision_receipt.result_occurrence_id for pilot in pilots
    )
    q_rows = tuple(
        row for pilot in pilots
        for row in pilot.reduction.projection.q_open_base
    )
    active_keys = {
        (row.result_occurrence_id, row.occurrence_id, row.cause_id)
        for row in active_rows
    }
    return {
        "semantic_relation": "C_active",
        "proof_relation": "Q_open",
        "terminal_timeout": terminal,
        "recovered_timeout": recovered,
        "solver_unknown": unknown,
        "parallel_sat_unsat_conflict": conflict,
        "canonical_manifest": {
            "manifest_authority_digest": manifest.manifest_authority_digest,
            "manifest_entry_count": len(manifest.entries),
            "result_occurrence_ids": result_ids,
            "decision_receipt_digests": [
                entry.decision_receipt_digest for entry in manifest.entries
            ],
            "exactly_one_decision_receipt_per_result": (
                len(set(decision_ids)) == len(decision_ids)
                and set(decision_ids) == set(result_ids)
            ),
            "all_q_open_foreign_keys_resolve_to_c_active": all(
                (row.result_occurrence_id, row.occurrence_id, row.cause_id)
                in active_keys for row in q_rows
            ),
        },
        "canonical_metrics": {
            key: metrics[key] for key in (
                "decision_counts",
                "final_unknown_results",
                "final_timeout_results",
                "active_blocker_occurrences",
                "unique_open_requirements",
                "terminal_timeout_events",
                "observed_nonterminal_timeout_events",
            )
        },
        "conservation": {
            "sum_decision_counts_equals_manifest_entries": (
                sum(metrics["decision_counts"].values()) == len(manifest.entries)
            ),
            "terminal_timeout_events_equals_final_timeout_results": (
                metrics["terminal_timeout_events"]
                == metrics["final_timeout_results"]
            ),
        },
    }


def test_slice5_registry_is_exact_and_digest_bound():
    validate_abi_width_readonly_registry_conservation()
    assert len(ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS) == 8
    assert len(ABI_WIDTH_READONLY_REASON_SPECS) == 8
    assert ABI_WIDTH_READONLY_PRODUCER_STAGE_REGISTRY_DIGEST == (
        EXPECTED_ABI_WIDTH_READONLY_PRODUCER_STAGE_REGISTRY_DIGEST
    )
    assert ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY.normalized_registry_digest == (
        EXPECTED_ABI_WIDTH_READONLY_COMMON_REGISTRY_DIGEST
    )
    assert authority_digest(abi_width_readonly_registry_authority_dict()) == (
        EXPECTED_ABI_WIDTH_READONLY_PRODUCER_STAGE_REGISTRY_DIGEST
    )
    assert tuple(row.proof_stage for row in ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS) == tuple(
        row.proof_kind for row in ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS
    )


def test_slice5_producer_capability_normalizes_legacy_string_at_construction():
    spec = replace(
        ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS[0],
        capability="STRUCTURAL_ONLY",
    )
    assert type(spec.capability) is AbiWidthReadonlyCapability
    assert spec.capability is AbiWidthReadonlyCapability.STRUCTURAL_ONLY
    assert spec.to_authority_tuple() == (
        AbiWidthReadonlyProducerStageSpec(
            spec.producer_contract_id,
            spec.producer_version,
            spec.proof_stage,
            spec.proof_kind,
            AbiWidthReadonlyCapability.STRUCTURAL_ONLY,
            spec.execution_issuer_id,
            spec.allowed_statuses,
            spec.terminal_eligible_statuses,
            spec.terminal_priority,
        ).to_authority_tuple()
    )


@pytest.mark.parametrize("value", ("not-a-sealed-capability",))
def test_slice5_producer_capability_rejects_invalid_string(value):
    with pytest.raises(ValueError, match="capability is not sealed"):
        replace(ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS[0], capability=value)


@pytest.mark.parametrize("value", (None, 1, object()))
def test_slice5_producer_capability_rejects_non_string_non_enum(value):
    with pytest.raises(TypeError, match="exact Enum or string"):
        replace(ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS[0], capability=value)


def test_slice5_producer_capability_rejects_another_enum():
    from enum import Enum

    class OtherCapability(Enum):
        STRUCTURAL_ONLY = "STRUCTURAL_ONLY"

    with pytest.raises(TypeError, match="exact Enum or string"):
        replace(
            ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS[0],
            capability=OtherCapability.STRUCTURAL_ONLY,
        )


def test_slice5_normalized_capability_registry_digest_mismatch_is_not_accepted():
    tampered = replace(
        ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS[0],
        capability="STRUCTURAL_OR_SOLVER_UNSAT",
    )
    assert type(tampered.capability) is AbiWidthReadonlyCapability
    authority = abi_width_readonly_registry_authority_dict()
    tampered_digest = authority_digest({
        **authority,
        "rows": (tampered.to_authority_tuple(),) + tuple(
            row.to_authority_tuple()
            for row in ABI_WIDTH_READONLY_PRODUCER_STAGE_SPECS[1:]
        ),
    })
    assert tampered_digest != EXPECTED_ABI_WIDTH_READONLY_PRODUCER_STAGE_REGISTRY_DIGEST


def test_slice5_solver_batch_transaction_is_semantic_and_idempotent():
    encoder = AbiWidthReadonlyPilotEncoder()
    session = SimpleNamespace(
        identity=SimpleNamespace(result_occurrence_id="result-transaction"),
        domain_signal_state={},
    )

    def batch(attempt_id, receipt_digest, attempt_ordinal=1):
        return SimpleNamespace(
            membership=SimpleNamespace(
                execution_identity_digest=attempt_id,
                attempt_group_identity="attempt-group",
                attempt_ordinal=attempt_ordinal,
                proof_requirement_id="proof-q",
            ),
            query_authority=SimpleNamespace(authority_digest="query-digest"),
            execution_receipts=(
                SimpleNamespace(receipt_digest=receipt_digest),
            ),
        )

    first = batch("attempt-1", "receipt-1")
    replay = batch("attempt-1", "receipt-1")
    assert encoder._register_solver_batch_transaction(
        session, first, ("intent",), {"fresh_receipt_digests": ()}
    ) == ("intent",)
    assert encoder._register_solver_batch_transaction(
        session, replay, ("intent",), {"fresh_receipt_digests": ()}
    ) == ("intent",)
    assert len(session.domain_signal_state[
        "abi_width_pending_emission_transactions"
    ]) == 1
    assert encoder._register_solver_batch_transaction(
        session,
        batch("attempt-1", "receipt-retry", attempt_ordinal=2),
        ("retry-intent",),
        {"fresh_receipt_digests": ()},
    ) == ("retry-intent",)
    assert len(session.domain_signal_state[
        "abi_width_pending_emission_transactions"
    ]) == 2

    with pytest.raises(ValueError, match="identity conflicts"):
        encoder._register_solver_batch_transaction(
            session,
            batch("attempt-1", "receipt-2"),
            ("intent",),
            {"fresh_receipt_digests": ()},
        )


def test_slice5_pilot_suppresses_post_commit_and_concurrent_resends():
    from concurrent.futures import ThreadPoolExecutor

    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )

    bootstrap_encoder = AbiWidthReadonlyPilotEncoder()
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=bootstrap_encoder,
    )
    session = connector.begin({"case": "slice5-resend-authority"})
    blocker = AbiWidthReadonlyBlockerSignal.from_width_seed(
        _width_seed("resend", missing=("return_storage_fact",)),
        "return_storage_fact",
    )
    intent = bootstrap_encoder(session, blocker)[0]

    class ReplayEncoder:
        def __init__(self, event_intent):
            self.event_intent = event_intent
            self.committed = False
            self.encode_calls = 0

        def __call__(self, _session, _signal):
            self.encode_calls += 1
            return (self.event_intent,)

        def is_committed_signal_replay(self, _session, _signal, _intents=()):
            return self.committed

        def commit_emitted_signal(self, _session, _signal, _intents):
            self.committed = True

    replay_encoder = ReplayEncoder(intent)
    session.domain_signal_encoder = replay_encoder
    signal = SimpleNamespace(transaction_id="semantic-resend-1")

    assert session.emit_domain_signal(signal) == 1
    prefix = session.recorder.prefix_view()
    baseline = (
        session.recorder.event_count,
        prefix.prefix_chain_digest,
        len(session.preview_lifecycle_projection().c_active_base),
        len(session.preview_lifecycle_projection().q_open_base),
    )
    assert session.emit_domain_signal(signal) == 0

    with ThreadPoolExecutor(max_workers=8) as executor:
        results = tuple(executor.map(
            session.emit_domain_signal,
            (signal,) * 8,
        ))
    assert results == (0,) * 8
    assert replay_encoder.encode_calls == 10
    prefix_after = session.recorder.prefix_view()
    assert (
        session.recorder.event_count,
        prefix_after.prefix_chain_digest,
        len(session.preview_lifecycle_projection().c_active_base),
        len(session.preview_lifecycle_projection().q_open_base),
    ) == baseline


def test_slice5_actual_solver_batch_resends_are_stream_idempotent(monkeypatch):
    from concurrent.futures import ThreadPoolExecutor

    from scripts.function_tracer_pcode.smt.interface import SolverStatus

    captured = []
    captured_intents = []
    original_commit = AbiWidthReadonlyPilotEncoder.commit_emitted_signal

    def capture_batch_commit(encoder, session, signal, intents):
        if type(signal) is AbiWidthReadonlySolverExecutionBatchSignal:
            captured.append(signal)
            captured_intents.append(tuple(intents))
        return original_commit(encoder, session, signal, intents)

    monkeypatch.setattr(
        AbiWidthReadonlyPilotEncoder,
        "commit_emitted_signal",
        capture_batch_commit,
    )
    _connector, session, encoder, emitted = _run_readonly_solver_fixture(
        monkeypatch,
        "actual-solver-batch-resend",
        (SolverStatus.UNSAT,),
    )
    assert emitted == 1
    assert len(captured) == 1
    assert len(captured_intents) == 1
    batch = captured[0]
    initial_intents = captured_intents[0]
    assert initial_intents
    assert encoder.is_committed_signal_replay(
        session, batch, initial_intents
    )

    prefix = session.recorder.prefix_view()
    baseline = (
        session.recorder.event_count,
        prefix.prefix_chain_digest,
        len(session.preview_lifecycle_projection().c_active_base),
        len(session.preview_lifecycle_projection().q_open_base),
    )

    def must_not_commit():
        raise AssertionError("committed solver batch was republished")

    assert session.emit_many(
        initial_intents, must_not_commit, transaction_signal=batch
    ) == ()
    changed_intents = (
        replace(initial_intents[0], diagnostic_payload={"replay": "tampered"}),
        *initial_intents[1:],
    )
    with pytest.raises(
        ValueError, match="committed transaction intents changed"
    ):
        session.emit_many(
            changed_intents, must_not_commit, transaction_signal=batch
        )
    with ThreadPoolExecutor(max_workers=8) as executor:
        results = tuple(executor.map(
            lambda _index: session.emit_many(
                initial_intents, must_not_commit, transaction_signal=batch
            ),
            range(8),
        ))
    assert results == ((),) * 8
    prefix_after = session.recorder.prefix_view()
    assert (
        session.recorder.event_count,
        prefix_after.prefix_chain_digest,
        len(session.preview_lifecycle_projection().c_active_base),
        len(session.preview_lifecycle_projection().q_open_base),
    ) == baseline


def test_slice5_phase7_runtime_replay_rolls_back_activation_and_finalizes():
    from concurrent.futures import ThreadPoolExecutor
    from dataclasses import dataclass

    from scripts.function_tracer_pcode.equivalence.v2.phase7_runtime import (
        runtime_from_audited_manifest,
    )
    from scripts.function_tracer_pcode.equivalence.v2.stream import (
        ErrorEventAuthority,
        EventIntent,
    )

    @dataclass(frozen=True)
    class ReplaySignal:
        value: str
        producer_id: str = "phase7-replay-producer"

        def _phase7_signal_authority(self):
            return {"value": self.value, "producer_id": self.producer_id}

    class ReplayEncoder:
        def __init__(self):
            self.committed = False
            self.commit_count = 0
            self.rollback_count = 0

        def __call__(self, _session, _signal):
            return (EventIntent(
                EventType.ERROR,
                ErrorEventAuthority("phase7-replay-error", "phase7-replay-artifact"),
            ),)

        def is_committed_signal_replay(self, _session, _signal, _intents=()):
            return self.committed

        def commit_emitted_signal(self, _session, _signal, _intents):
            self.commit_count += 1
            self.committed = True

        def rollback_emitted_signal(self, _session, _signal):
            self.rollback_count += 1

    signal = ReplaySignal("same-semantic-signal")
    site = {
        "producer_site_manifest_id": "phase7-replay-site",
        "source_sha256": "phase7-replay-source",
        "domain": "phase7_replay_test",
        "allowed_dispositions": ["OPERATIONAL_ERROR_NO_SEMANTIC_CAUSE"],
        "allowed_producer_ids": ["phase7-replay-producer"],
        "expected_cause_slots": [],
    }
    manifest_body = {
        "manifest_kind": "unknown-taxonomy-v2-phase7-producer-sites-v2",
        "site_count": 1,
        "sites": [site],
    }
    manifest = {
        **manifest_body,
        "manifest_digest": authority_digest(manifest_body),
    }
    encoder = ReplayEncoder()

    def runtime_factory(identity):
        return runtime_from_audited_manifest(manifest, identity)

    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )

    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=encoder,
        phase7_runtime_factory=runtime_factory,
    )
    session = connector.begin({"case": "phase7-runtime-replay"})

    def emit_with_activation():
        # This mirrors the production wrapper boundary: activation is opened
        # before the shared domain publication path is entered.
        with session.domain_signal_transaction():
            session.record_phase7_pre_emission_activation(
                "phase7-replay-site", signal
            )
            return session.emit_domain_signal(signal)

    assert emit_with_activation() == 1
    assert encoder.commit_count == 1
    baseline = (
        session.recorder.event_count,
        session.recorder.prefix_view().prefix_chain_digest,
    )

    assert emit_with_activation() == 0
    assert encoder.commit_count == 1
    assert encoder.rollback_count == 0
    assert session._phase7_signal_transactions == {}
    assert session.phase7_runtime._pending == {}
    assert len(session.phase7_runtime._materialized) == 1

    with ThreadPoolExecutor(max_workers=8) as executor:
        results = tuple(executor.map(
            lambda _index: emit_with_activation(), range(8)
        ))
    assert results == (0,) * 8
    assert encoder.commit_count == 1
    assert encoder.rollback_count == 0
    assert session._phase7_signal_transactions == {}
    assert session.phase7_runtime._pending == {}
    assert len(session.phase7_runtime._materialized) == 1
    assert (
        session.recorder.event_count,
        session.recorder.prefix_view().prefix_chain_digest,
    ) == baseline

    result = SimpleNamespace(
        is_equivalent=None,
        error_message="phase7-replay-error",
        failure_status=None,
        failure_message=None,
        unknown_reasons=[],
        unknown_recovery_actions=[],
        is_timeout=lambda: False,
    )
    evidence = connector.finish(
        session, result, case_id="phase7-runtime-replay"
    )
    assert session.phase7_runtime_result.decision_receipt.outcome is Outcome.ERROR
    assert session.phase7_runtime._signal_transactions == {}
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.ERROR


def test_slice5_production_source_coverage_is_conserved():
    validate_abi_width_readonly_production_source_conservation()
    owned = {
        reason_id
        for reason_ids in ABI_WIDTH_READONLY_PRODUCTION_SOURCE_REASON_IDS.values()
        for reason_id in reason_ids
    }
    assert owned == set(ABI_WIDTH_READONLY_REASON_SPECS)


def test_slice5_width_source_matrix_is_exact_and_fail_closed():
    assert classify_width_blocker("unary_width", "return_storage_fact").reason_ids == (
        "return_width_provenance_unavailable",
    )
    assert classify_width_blocker("unary_abi", "calling_convention").reason_ids == (
        "return_abi_provenance_unavailable",
    )
    projection = classify_width_blocker(
        "pair_width_compatibility", "projection_applicability"
    )
    assert projection.reason_ids == (
        "return_observation_contract_unproven",
        "return_high_bit_relation_unproven",
    )
    assert classify_width_blocker("pair_width_compatibility", "other").disposition is (
        AbiWidthReadonlyDisposition.INFRASTRUCTURE_INVALID
    )


def test_slice5_summary_deferred_sources_have_one_owner():
    assert classify_summary_width_source(
        "summary_return_candidate_invalid:return_width_missing"
    ).reason_ids == ("return_width_provenance_unavailable",)
    assert classify_summary_width_source(
        "summary_return_overlap_unproven:return_width_mismatch"
    ).reason_ids == ("return_width_relation_unproven",)
    assert classify_summary_width_source("summary_return_candidate_invalid:value_missing").disposition is (
        AbiWidthReadonlyDisposition.INFRASTRUCTURE_INVALID
    )


@pytest.mark.parametrize(
    ("source", "disposition", "reasons"),
    (
        ("semantic_key_missing", AbiWidthReadonlyDisposition.TYPED_SLICE5_CAUSE, ("readonly_storage_identity_unproven",)),
        ("semantic_key_mismatch", AbiWidthReadonlyDisposition.TYPED_SLICE5_CAUSE, ("readonly_object_correspondence_unproven",)),
        ("readonly_contract_result_width_mismatch", AbiWidthReadonlyDisposition.TYPED_SLICE5_CAUSE, ("return_observation_contract_unproven", "return_high_bit_relation_unproven")),
        ("readonly_contract_missing_effect_profile", AbiWidthReadonlyDisposition.REFINED_TO_SLICE3, ()),
        ("readonly_contract_missing_loop", AbiWidthReadonlyDisposition.REFINED_TO_SLICE4, ()),
        ("readonly_contract_type_mismatch", AbiWidthReadonlyDisposition.INFRASTRUCTURE_INVALID, ()),
    ),
)
def test_slice5_readonly_source_disposition_is_disjoint(source, disposition, reasons):
    result = classify_readonly_source(source)
    assert result.disposition is disposition
    assert result.reason_ids == reasons


def test_projection_seed_is_factory_only_nonproof_authority():
    seed = _projection_seed()
    assert seed.candidate_observation_width == 32
    assert not hasattr(seed, "proved")
    assert not hasattr(seed, "completion_receipt")
    with pytest.raises(TypeError, match="factory issued"):
        ReturnObservationProjectionSeed(
            pair_target_key=("pair",),
            left_seed_digest="left",
            right_seed_digest="right",
            candidate_observation_width=32,
            derivation="declared",
            left_storage_width=32,
            right_storage_width=32,
            left_payload_width=32,
            right_payload_width=32,
            left_extension_kind="same_width",
            right_extension_kind="same_width",
            guard_contract=("guard",),
            source_snapshot_pair=("snapshots",),
            prepared_snapshot_digest="prepared",
        )
    with pytest.raises(TypeError, match="factory issued"):
        replace(seed, seed_digest="forged")


def test_need_seed_without_common_positive_width_conserves_unknown_frontier():
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )

    left = _width_seed("left")
    right = replace(
        _width_seed("right"),
        payload_width=16,
        payload_value_identity=("payload", "right", 16),
        calling_convention_fact=(
            "return_type_provenance", ("declared_return_type_width", 16)
        ),
    )
    target = PairReturnObservationTargetId(
        "top_level_return", left.target_id, right.target_id,
        (left.target_id.function_identity, right.target_id.function_identity),
    )
    pair = PairReturnObservationSeed(
        target, left.digest, right.digest, "top_level_return",
        target.semantic_anchors,
    )
    need = ReturnObservationNeedSeed.from_pair_seed(left, right, pair)
    blocker = AbiWidthReadonlyBlockerSignal.from_observation_need_seed(need)
    encoder = AbiWidthReadonlyPilotEncoder()
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            AbiWidthReadonlyBlockerSignal: encoder,
        }),
    )
    session = connector.begin({"case": "need-seed-no-common-width"})
    assert session.emit_domain_signal(blocker) == 1
    result = SimpleNamespace(
        is_equivalent=True, error_message=None, failure_status=None,
        failure_message=None, unknown_reasons=[], unknown_recovery_actions=[],
        is_timeout=lambda: False,
    )
    evidence = connector.finish(
        session, result, case_id="need-seed-no-common-width"
    )
    projection = evidence.pilot_result.reduction.projection
    assert evidence.pilot_result.candidate.decision_receipt.outcome is Outcome.UNKNOWN
    assert {row.reason_id for row in projection.c_active_base} == {
        "return_observation_contract_unproven"
    }
    assert {row.proof_kind for row in projection.q_open_base} == {
        "return_observation_contract"
    }


def test_projection_seed_rejects_cross_target_and_reverse_is_ordered():
    left = _width_seed("left")
    right = _width_seed("right")
    target = PairReturnObservationTargetId(
        "top_level_return", left.target_id, right.target_id,
        (left.target_id.function_identity, right.target_id.function_identity),
    )
    pair = PairReturnObservationSeed(
        target, left.digest, right.digest, "top_level_return", target.semantic_anchors
    )
    with pytest.raises(ValueError, match="pair/unary authority differs"):
        ReturnObservationProjectionSeed.from_pair_seed(
            left, right, replace(pair, left_seed_digest="forged")
        )
    forward = ReturnObservationProjectionSeed.from_pair_seed(left, right, pair)
    reverse_target = PairReturnObservationTargetId(
        "top_level_return", right.target_id, left.target_id,
        (right.target_id.function_identity, left.target_id.function_identity),
    )
    reverse_pair = PairReturnObservationSeed(
        reverse_target,
        right.digest,
        left.digest,
        "top_level_return",
        reverse_target.semantic_anchors,
    )
    reverse = ReturnObservationProjectionSeed.from_pair_seed(
        right, left, reverse_pair
    )
    assert forward.seed_digest != reverse.seed_digest


def test_pair_source_provenance_does_not_split_semantic_cause():
    encoder = AbiWidthReadonlyPilotEncoder()
    session = _session()
    seed = _projection_seed()
    first = encoder.authority_for_signal(
        session,
        AbiWidthReadonlyBlockerSignal.from_projection_seed(
            "return_high_bit_relation_unproven",
            seed,
            producer_id="source-code-A",
        ),
    )
    second = encoder.authority_for_signal(
        session,
        AbiWidthReadonlyBlockerSignal.from_projection_seed(
            "return_high_bit_relation_unproven",
            seed,
            producer_id="source-code-B",
        ),
    )
    assert first.occurrence.cause_id == second.occurrence.cause_id
    assert first.occurrence.proof_requirement_ids == second.occurrence.proof_requirement_ids


def test_abi_and_high_bit_are_independent_cause_and_q_rows():
    encoder = AbiWidthReadonlyPilotEncoder()
    session = _session()
    seed = _projection_seed()
    abi = encoder.authority_for_signal(
        session,
        AbiWidthReadonlyBlockerSignal.from_projection_seed(
            "return_abi_relation_unproven", seed
        ),
    )
    high = encoder.authority_for_signal(
        session,
        AbiWidthReadonlyBlockerSignal.from_projection_seed(
            "return_high_bit_relation_unproven", seed
        ),
    )
    assert abi.occurrence.cause_id != high.occurrence.cause_id
    assert abi.occurrence.proof_requirement_ids != high.occurrence.proof_requirement_ids
    assert abi.occurrence.reason_id == "return_abi_relation_unproven"
    assert high.occurrence.reason_id == "return_high_bit_relation_unproven"
    assert abi.occurrence.identity_scope is IdentityScope.RELATIONAL


def test_completion_artifacts_are_exact_factory_issued_and_fail_closed():
    seed = _width_seed("left", missing=("return_storage_fact",))
    blocker = AbiWidthReadonlyBlockerSignal.from_width_seed(
        seed, "return_storage_fact"
    )
    artifact = ReturnWidthProvenanceArtifact.from_validated_fact(
        blocker,
        seed,
        source_snapshot_fingerprint="source-snapshot",
        slot="return_storage_fact",
        positive_width=64,
    )
    assert artifact.reason_id == "return_width_provenance_unavailable"
    assert artifact.registry_digest == ABI_WIDTH_READONLY_PRODUCER_STAGE_REGISTRY_DIGEST
    with pytest.raises(ValueError, match="positive exact width"):
        ReturnWidthProvenanceArtifact.from_validated_fact(
            blocker,
            seed,
            source_snapshot_fingerprint="source-snapshot",
            slot="return_storage_fact",
            positive_width=0,
        )
    with pytest.raises(TypeError, match="exact-factory issued"):
        ReturnWidthProvenanceArtifact()


def test_observation_completion_requires_exact_high_bit_dependency_for_projection():
    seed, abi_relation = _abi_relation_artifact()
    observation = AbiWidthReadonlyBlockerSignal.from_projection_seed(
        "return_observation_contract_unproven", seed
    )
    high_blocker = AbiWidthReadonlyBlockerSignal.from_projection_seed(
        "return_high_bit_relation_unproven", seed
    )
    high = ReturnHighBitRelationProofArtifact.from_structural_theorem(
        high_blocker,
        seed,
        abi_relation,
        source_snapshot_fingerprint="source-snapshot",
        theorem_id="validated_zero_extend_projection_v1",
        validated_premises=(("left", "zero_extend"), ("right", "zero_extend")),
    )
    with pytest.raises(ValueError, match="lacks high-bit proof"):
        ReturnObservationContractArtifact.from_projection_seed(
            observation,
            seed,
            derivation="common_validated_semantic_payload_width",
            projection_policy="truncate_to_observation",
            source_snapshot_fingerprint="source-snapshot",
        )
    artifact = ReturnObservationContractArtifact.from_projection_seed(
        observation,
        seed,
        derivation="common_validated_semantic_payload_width",
        projection_policy="truncate_to_observation",
        source_snapshot_fingerprint="source-snapshot",
        high_bit_dependency=high,
    )
    assert artifact.dependency_artifact_digests == (high.artifact_digest,)


def test_completion_rechecks_live_c_and_q_before_issuing_receipt():
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )

    encoder = AbiWidthReadonlyPilotEncoder()
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=encoder,
    )
    session = connector.begin({"case": "slice5-live-completion"})
    seed, abi_relation = _abi_relation_artifact(
        session.identity.source_snapshot_fingerprint
    )
    blocker = AbiWidthReadonlyBlockerSignal.from_projection_seed(
        "return_high_bit_relation_unproven", seed
    )
    artifact = ReturnHighBitRelationProofArtifact.from_structural_theorem(
        blocker,
        seed,
        abi_relation,
        source_snapshot_fingerprint=session.identity.source_snapshot_fingerprint,
        theorem_id="validated_zero_extend_projection_v1",
        validated_premises=(("left", "zero_extend"), ("right", "zero_extend")),
    )
    with pytest.raises(ValueError, match="live C_active"):
        encoder.complete_return_high_bit_relation(session, blocker, artifact)
    assert session.emit_domain_signal(blocker) == 1
    intent = encoder.complete_return_high_bit_relation(session, blocker, artifact)
    assert intent.event_type is EventType.REQUIREMENT_COMPLETED
    session.emit(intent)
    projection = session.preview_lifecycle_projection()
    assert projection.c_active_base == ()
    assert projection.q_open_base == ()
    with pytest.raises(ValueError, match="live C_active"):
        encoder.complete_return_high_bit_relation(session, blocker, artifact)


def test_exact_artifact_dependencies_reject_digest_side_slot_and_registry_bypass():
    seed, abi_relation, unary, abi_seeds = _abi_relation_artifact(include_unary=True)
    observation = AbiWidthReadonlyBlockerSignal.from_projection_seed(
        "return_observation_contract_unproven", seed
    )
    with pytest.raises(ValueError, match="targets another seed"):
        ReturnObservationContractArtifact.from_projection_seed(
            observation,
            seed,
            derivation="common_validated_semantic_payload_width",
            projection_policy="truncate_to_observation",
            source_snapshot_fingerprint="source-snapshot",
            high_bit_dependency="arbitrary-digest",
        )
    high_blocker = AbiWidthReadonlyBlockerSignal.from_projection_seed(
        "return_high_bit_relation_unproven", seed
    )
    with pytest.raises(ValueError, match="exact ABI relation"):
        ReturnHighBitRelationProofArtifact.from_structural_theorem(
            high_blocker,
            seed,
            None,
            source_snapshot_fingerprint="source-snapshot",
            theorem_id="same_width_identity_v1",
            validated_premises=(("same-width", True),),
        )
    abi_blocker = AbiWidthReadonlyBlockerSignal.from_projection_seed(
        "return_abi_relation_unproven", seed
    )
    with pytest.raises(ValueError, match="unary target dependencies"):
        ReturnAbiRelationArtifact.from_projection_seed(
            abi_blocker,
            seed,
            left_abi_artifact=unary[1],
            right_abi_artifact=unary[0],
            source_snapshot_fingerprint="source-snapshot",
            calling_conventions_individually_valid=True,
            storage_projection_related=True,
            observation_applicable=True,
        )
    missing = abi_seeds[0]
    slot_blocker = AbiWidthReadonlyBlockerSignal.from_return_abi_seed(
        missing, "calling_convention"
    )
    with pytest.raises(ValueError, match="not MISSING"):
        ReturnAbiProvenanceArtifact.from_ghidra_facts(
            slot_blocker,
            missing,
            source_snapshot_fingerprint="source-snapshot",
            missing_slot="return_storage_descriptor",
            calling_convention_key=("cc",),
            return_type_key=("type",),
            return_storage_key=("storage",),
            provenance_refs=(("api",),),
        )
    with pytest.raises(TypeError, match="exact-factory issued"):
        replace(abi_relation, registry_digest="forged")


def test_same_missing_site_slot_dedups_but_distinct_slots_do_not_merge():
    encoder = AbiWidthReadonlyPilotEncoder()
    session = _session()
    seed = _width_seed(
        "left", missing=("return_storage_fact", "payload_width_fact")
    )
    first_signal = AbiWidthReadonlyBlockerSignal.from_width_seed(
        seed, "return_storage_fact"
    )
    first = encoder.authority_for_signal(session, first_signal)
    duplicate = encoder.authority_for_signal(session, first_signal)
    other = encoder.authority_for_signal(
        session,
        AbiWidthReadonlyBlockerSignal.from_width_seed(seed, "payload_width_fact"),
    )
    assert first.occurrence.cause_id == duplicate.occurrence.cause_id
    assert first.occurrence.occurrence_id == duplicate.occurrence.occurrence_id
    assert first.occurrence.cause_id != other.occurrence.cause_id


def test_encoder_emits_only_exact_cause_observation():
    encoder = AbiWidthReadonlyPilotEncoder()
    intents = encoder(
        _session(),
        AbiWidthReadonlyBlockerSignal.from_width_seed(
            _width_seed("left", missing=("return_storage_fact",)),
            "return_storage_fact",
        ),
    )
    assert len(intents) == 1
    assert intents[0].event_type is EventType.CAUSE_OBSERVED
    with pytest.raises(TypeError, match="exact blocker signal"):
        encoder(_session(), object())


def test_return_width_production_source_dual_writes_exact_unary_c_and_q():
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )

    encoder = AbiWidthReadonlyPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        AbiWidthReadonlyBlockerSignal: encoder,
    })
    session = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    ).begin({"case": "slice5-production-width"})
    with production_signal_scope(session):
        result = build_top_level_observation_contract(
            _width_seed("left", missing=("return_storage_fact",)),
            _width_seed("right"),
        )
    assert result.blockers[0].missing_slot == "return_storage_fact"
    projection = session.preview_lifecycle_projection()
    assert [row.reason_id for row in projection.c_active_base] == [
        "return_width_provenance_unavailable"
    ]
    assert [row.proof_kind for row in projection.q_open_base] == [
        "return_width_provenance"
    ]
    assert session.domain_signal_error_kinds == []


def test_exact_abi_width_blocker_retransmission_is_producer_idempotent():
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        emit_abi_width_readonly_signal,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )

    signal = AbiWidthReadonlyBlockerSignal.from_width_seed(
        _width_seed("left", missing=("return_storage_fact",)),
        "return_storage_fact",
    )
    session = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            AbiWidthReadonlyBlockerSignal: AbiWidthReadonlyPilotEncoder(),
        }),
    ).begin({"case": "abi-width-identical-retransmission"})

    with production_signal_scope(session):
        assert emit_abi_width_readonly_signal(signal) == 1
        assert emit_abi_width_readonly_signal(signal) == 0

    assert session.recorder.event_count == 1
    projection = session.preview_lifecycle_projection()
    assert len(projection.c_active_base) == 1
    assert len(projection.q_open_base) == 1
    assert session.domain_signal_error_details == []


def test_actual_abi_width_wrapper_replay_and_concurrent_replay_are_phase7_safe():
    from concurrent.futures import ThreadPoolExecutor

    from scripts.function_tracer_pcode.equivalence.v2.phase7_runtime import (
        runtime_from_audited_manifest,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        emit_abi_width_readonly_signal,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )

    root = Path(__file__).resolve().parents[4]
    complete_manifest = json.loads((root / (
        "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )).read_text(encoding="utf-8"))
    site_id = "return-width-unary-provenance-blocker"
    site = next(
        row for row in complete_manifest["sites"]
        if row["producer_site_manifest_id"] == site_id
    )
    manifest_body = {
        "manifest_kind": complete_manifest["manifest_kind"],
        "site_count": 1,
        "sites": [site],
    }
    manifest = {
        **manifest_body,
        "manifest_digest": authority_digest(manifest_body),
    }
    signal = AbiWidthReadonlyBlockerSignal.from_width_seed(
        _width_seed("actual-wrapper", missing=("return_storage_fact",)),
        "return_storage_fact",
    )

    def make_session(case_id):
        encoder = CompositeProductionSignalEncoder({
            AbiWidthReadonlyBlockerSignal: AbiWidthReadonlyPilotEncoder(),
        })
        connector = ProductionDualWritePilotConnector(
            ShadowLifecycleReducer(
                reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
                recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
            ),
            domain_signal_encoder=encoder,
            phase7_runtime_factory=lambda identity: (
                runtime_from_audited_manifest(manifest, identity)
            ),
        )
        return connector, connector.begin({"case": case_id})

    def emit_actual(session):
        with production_signal_scope(session):
            return emit_abi_width_readonly_signal(
                signal, producer_site_manifest_id=site_id
            )

    _, sequential = make_session(
        "abi-width-actual-wrapper-sequential"
    )
    assert emit_actual(sequential) == 1
    baseline = (
        sequential.recorder.event_count,
        sequential.recorder.prefix_view().prefix_chain_digest,
        len(sequential.preview_lifecycle_projection().c_active_base),
        len(sequential.preview_lifecycle_projection().q_open_base),
    )
    assert emit_actual(sequential) == 0
    assert (
        sequential.recorder.event_count,
        sequential.recorder.prefix_view().prefix_chain_digest,
        len(sequential.preview_lifecycle_projection().c_active_base),
        len(sequential.preview_lifecycle_projection().q_open_base),
    ) == baseline
    assert sequential._phase7_signal_transactions == {}
    assert sequential.phase7_runtime._pending == {}
    assert len(sequential.phase7_runtime._materialized) == 1
    assert sequential.domain_signal_error_details == []

    connector, concurrent = make_session(
        "abi-width-actual-wrapper-concurrent"
    )
    with ThreadPoolExecutor(max_workers=8) as executor:
        results = tuple(executor.map(
            lambda _index: emit_actual(concurrent), range(8)
        ))
    assert sorted(results) == [0] * 7 + [1]
    concurrent_projection = concurrent.preview_lifecycle_projection()
    assert (
        concurrent.recorder.event_count,
        len(concurrent_projection.c_active_base),
        len(concurrent_projection.q_open_base),
    ) == (1, 1, 1)
    assert concurrent._phase7_signal_transactions == {}
    assert concurrent.phase7_runtime._pending == {}
    assert len(concurrent.phase7_runtime._materialized) == 1
    assert concurrent.domain_signal_error_details == []

    legacy = SimpleNamespace(
        is_equivalent=None,
        error_message=None,
        failure_status=None,
        failure_message=None,
        is_timeout=lambda: False,
    )
    evidence = connector.finish(
        concurrent, legacy, case_id="abi-width-actual-wrapper-concurrent"
    )
    assert concurrent.phase7_runtime_result.decision_receipt.outcome is Outcome.UNKNOWN
    assert concurrent.phase7_runtime._signal_transactions == {}
    evidence.validate()


def test_conflicting_abi_width_blocker_retransmission_is_rejected(monkeypatch):
    from scripts.function_tracer_pcode.equivalence.v2.contracts import (
        CauseOccurrenceAuthority,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        emit_abi_width_readonly_signal,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )

    signal = AbiWidthReadonlyBlockerSignal.from_width_seed(
        _width_seed("left", missing=("return_storage_fact",)),
        "return_storage_fact",
    )
    encoder = AbiWidthReadonlyPilotEncoder()
    session = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            AbiWidthReadonlyBlockerSignal: encoder,
        }),
    ).begin({"case": "abi-width-conflicting-retransmission"})

    with production_signal_scope(session):
        assert emit_abi_width_readonly_signal(signal) == 1
        original = encoder.authority_for_signal(session, signal)
        conflicting = CauseOccurrenceAuthority(
            replace(
                original.occurrence,
                evidence_refs=original.occurrence.evidence_refs + (
                    "conflicting-retransmission",
                ),
            ),
            original.bound_contract,
        )
        monkeypatch.setattr(
            encoder,
            "authority_for_signal",
            lambda active_session, active_signal: conflicting,
        )
        with pytest.raises(
            ValueError,
            match="ABI/width occurrence retransmission authority conflicts",
        ):
            emit_abi_width_readonly_signal(signal)

    assert session.recorder.event_count == 1
    assert session.domain_signal_error_details == []


@pytest.mark.parametrize(
    ("left", "right", "expected_reasons"),
    (
        (
            replace(_width_seed("left"), calling_convention_fact=("declared_return_type_width", 32)),
            replace(_width_seed("right"), payload_width=64,
                    calling_convention_fact=("declared_return_type_width", 64)),
            ("return_observation_contract_unproven",),
        ),
        (
            replace(_width_seed("left"), calling_convention_fact=("declared_return_type_width", 128)),
            replace(_width_seed("right"), calling_convention_fact=("declared_return_type_width", 128)),
            (
                "return_high_bit_relation_unproven",
                "return_observation_contract_unproven",
            ),
        ),
    ),
)
def test_return_width_pair_sources_dual_write_disjoint_relational_causes(
    left, right, expected_reasons
):
    from scripts.function_tracer_pcode.equivalence.v2.pilot import ProductionDualWritePilotConnector
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import ShadowLifecycleReducer

    encoder = AbiWidthReadonlyPilotEncoder()
    session = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            AbiWidthReadonlyBlockerSignal: encoder,
        }),
    ).begin({"case": expected_reasons})
    with production_signal_scope(session):
        result = build_top_level_observation_contract(left, right)
    assert result.blockers
    projection = session.preview_lifecycle_projection()
    assert tuple(sorted(row.reason_id for row in projection.c_active_base)) == expected_reasons
    assert len(projection.q_open_base) == len(expected_reasons)
    assert session.domain_signal_error_kinds == []
    scheduled = session.domain_signal_state.get(
        "abi_width_pending_solver_candidates", {}
    )
    if "return_high_bit_relation_unproven" in expected_reasons:
        assert len(scheduled) == 1
        assert next(iter(scheduled.values()))[0].reason_id == (
            "return_high_bit_relation_unproven"
        )
    else:
        assert scheduled == {}


def test_unformable_projection_seed_is_typed_unknown_not_shadow_error():
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )

    left = replace(
        _width_seed("left"),
        calling_convention_fact=("declared_return_type_width", 128),
    )
    right = replace(
        _width_seed("right"),
        payload_width=16,
        payload_value_identity=("payload", "right", 16),
        calling_convention_fact=("declared_return_type_width", 128),
    )
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            AbiWidthReadonlyBlockerSignal: AbiWidthReadonlyPilotEncoder(),
        }),
    )
    session = connector.begin({"case": "unformable-return-projection"})

    with production_signal_scope(session):
        blocked = build_top_level_observation_contract(left, right)

    assert blocked.blockers[0].missing_slot == "projection_applicability"
    assert session.domain_signal_error_kinds == []
    assert session.domain_signal_error_details == []
    projection = session.preview_lifecycle_projection()
    assert [row.reason_id for row in projection.c_active_base] == [
        "return_observation_contract_unproven"
    ]
    assert [row.proof_kind for row in projection.q_open_base] == [
        "return_observation_contract"
    ]

    result = SimpleNamespace(
        is_equivalent=True,
        error_message=None,
        failure_status=None,
        failure_message=None,
        unknown_reasons=[],
        unknown_recovery_actions=[],
        is_timeout=lambda: False,
    )
    evidence = connector.finish(
        session, result, case_id="unformable-return-projection"
    )
    assert (
        evidence.pilot_result.candidate.decision_receipt.outcome
        is Outcome.UNKNOWN
    )


def test_summary_width_deferred_occurrences_expand_to_exact_slice5_signals():
    from scripts.function_tracer_pcode.analysis.summary_returns import (
        _summary_blocker_occurrence,
        accept_summary_return_candidates,
    )
    from scripts.function_tracer_pcode.model import ReturnInfo
    from scripts.function_tracer_pcode.tests.unit.test_summary_return_candidates import (
        _analysis_with_exact_returns,
        _empty_effect_summary,
        _summary_const,
        _with_summary_proof,
    )

    analysis = _analysis_with_exact_returns(effect_summary=_empty_effect_summary())
    summary_return = _with_summary_proof(ReturnInfo(
        address="0x1008", value=_summary_const(2), conditions=[],
        pcode_identity="summary:width",
    ))
    accepted = accept_summary_return_candidates(
        analysis, [summary_return], summary_note="counted_loop_summary"
    )
    candidate = accepted.candidates[0]
    occurrences = (
        _summary_blocker_occurrence(
            analysis,
            "summary_return_candidate_invalid:return_width_missing",
            candidate=candidate,
        ),
        _summary_blocker_occurrence(
            analysis,
            "summary_return_overlap_unproven:return_width_mismatch",
            candidate=candidate,
            peer_return=analysis.returns[0],
        ),
    )
    signals = summary_abi_width_signals_from_acceptance(
        analysis, replace(accepted, blocker_occurrences=occurrences)
    )
    assert tuple(signal.reason_id for signal in signals) == (
        "return_width_provenance_unavailable",
        "return_width_relation_unproven",
    )
    assert signals[0].identity_scope is IdentityScope.UNARY
    assert signals[1].identity_scope is IdentityScope.UNARY
    assert signals[0].canonical_target_key[0] == "return_site_slot_v2"
    assert signals[1].canonical_target_key[0] == "same_function_return_pair_v2"


def test_typed_abi_assessment_distinguishes_missing_malformed_proved_and_unproven():
    def analysis_and_seed(side, *, calling_status="PRESENT", storage_suffix="same"):
        analysis = FunctionReturnAnalysis(
            f"fn-{side}", f"0x{10 if side == 'left' else 20}00", [], [],
            binary_id=f"bin-{side}",
        )
        analysis.return_abi_facts = {
            "schema_version": 1,
            "calling_convention": {
                "status": calling_status,
                "value": ("ghidra_calling_convention_v1", "default") if calling_status == "PRESENT" else None,
                "source": "getModelName",
            },
            "declared_or_effective_return_type": {
                "status": "PRESENT", "value": ("ghidra_return_type_v1", "/int", 4), "source": "getReturnType",
            },
            "return_storage_descriptor": {
                "status": "PRESENT", "value": ("ghidra_return_storage_v1", (("ghidra_return_storage_member_v1", "register", 0 if storage_suffix == "same" else 8, 8),)),
                "source": "getReturnStorage",
            },
        }
        return analysis, _width_seed(
            side, function_identity=analysis.outcome_function_identity()
        )

    left_analysis, left = analysis_and_seed("left")
    right_analysis, right = analysis_and_seed("right")
    pair = PairReturnObservationSeed(
        PairReturnObservationTargetId(
            "top_level_return", left.target_id, right.target_id,
            (left.target_id.function_identity, right.target_id.function_identity),
        ),
        left.digest, right.digest, "top_level_return",
        (left.target_id.function_identity, right.target_id.function_identity),
    )
    proved = assess_return_abi_pair(
        left_analysis, right_analysis, left, right, pair
    )
    assert proved.relation_assessment.status is ReturnAbiRelationStatus.PROVED
    assert [signal.reason_id for signal in proved.signals] == [
        "return_abi_relation_unproven"
    ]

    right_analysis.return_abi_facts["return_storage_descriptor"]["value"] = (
        "ghidra_return_storage_v1",
        (("ghidra_return_storage_member_v1", "register", 8, 8),),
    )
    right_analysis.return_abi_facts["calling_convention"]["value"] = (
        "ghidra_calling_convention_v1", "different-architecture-abi"
    )
    cross_abi = assess_return_abi_pair(
        left_analysis, right_analysis, left, right, pair
    )
    assert cross_abi.relation_assessment.status is ReturnAbiRelationStatus.PROVED
    assert [signal.reason_id for signal in cross_abi.signals] == [
        "return_abi_relation_unproven"
    ]

    narrow_right = replace(right, storage_width=16)
    narrow_pair = replace(pair, right_seed_digest=narrow_right.digest)
    unproven = assess_return_abi_pair(
        left_analysis, right_analysis, left, narrow_right, narrow_pair
    )
    assert unproven.relation_assessment.status is ReturnAbiRelationStatus.UNPROVEN
    assert [signal.reason_id for signal in unproven.signals] == [
        "return_abi_relation_unproven"
    ]

    right_analysis.return_abi_facts["calling_convention"] = {
        "status": "MISSING", "value": None, "source": "getModelName"
    }
    missing = assess_return_abi_pair(
        left_analysis, right_analysis, left, right, pair
    )
    assert missing.relation_assessment is None
    assert [signal.reason_id for signal in missing.signals] == [
        "return_abi_provenance_unavailable"
    ]

    right_analysis.return_abi_facts["calling_convention"] = {
        "status": "PRESENT", "value": None, "source": "getModelName"
    }
    with pytest.raises(ValueError, match="MALFORMED"):
        assess_return_abi_pair(left_analysis, right_analysis, left, right, pair)


@pytest.mark.parametrize(
    ("right_calling_status", "right_storage", "expected_reasons", "expected_errors"),
    (
        ("MISSING", "same", ("return_abi_provenance_unavailable",), ()),
        ("PRESENT", "different", ("return_abi_relation_unproven",), ()),
        ("PRESENT", "same", ("return_abi_relation_unproven",), ()),
        ("MALFORMED", "same", (), ()),
    ),
)
def test_prepare_pair_return_observation_routes_typed_abi_authority(
    right_calling_status, right_storage, expected_reasons, expected_errors
):
    malformed = right_calling_status == "MALFORMED"
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )

    def analysis_and_seed(side, *, calling_status="PRESENT", storage="same"):
        analysis = FunctionReturnAnalysis(
            f"fn-{side}", f"0x{10 if side == 'left' else 20}00", [], [],
            binary_id=f"bin-{side}",
        )
        value = (
            ("ghidra_calling_convention_v1", "default")
            if calling_status == "PRESENT"
            else None
        )
        analysis.return_abi_facts = {
            "schema_version": 1,
            "calling_convention": {
                "status": calling_status,
                "value": value,
                "source": "getModelName",
            },
            "declared_or_effective_return_type": {
                "status": "PRESENT",
                "value": ("ghidra_return_type_v1", "/int", 4),
                "source": "getReturnType",
            },
            "return_storage_descriptor": {
                "status": "PRESENT",
                "value": ("ghidra_return_storage_v1", (("ghidra_return_storage_member_v1", "register", 0 if storage == "same" else 8, 8),)),
                "source": "getReturnStorage",
            },
        }
        return analysis, _width_seed(
            side, function_identity=analysis.outcome_function_identity()
        )

    left_analysis, left_seed = analysis_and_seed("left")
    right_analysis, right_seed = analysis_and_seed(
        "right", calling_status=right_calling_status, storage=right_storage
    )
    left_case, right_case = object(), object()
    incomplete_proof = SimpleNamespace(complete=False, blocker_kind="test-stop")
    left_prepared = PreparedFunctionReturnWidths(
        {id(left_case): left_seed}, {id(left_case): incomplete_proof}
    )
    right_prepared = PreparedFunctionReturnWidths(
        {id(right_case): right_seed}, {id(right_case): incomplete_proof}
    )
    session = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder({
            AbiWidthReadonlyBlockerSignal: AbiWidthReadonlyPilotEncoder(),
        }),
    ).begin({"case": "typed-abi-production-route"})
    with production_signal_scope(session):
        if malformed:
            with pytest.raises(ReturnAbiAuthorityInvalid):
                prepare_pair_return_observation(
                    left_analysis,
                    right_analysis,
                    left_case,
                    right_case,
                    left_prepared,
                    right_prepared,
                    return_coverage_ids=(),
                )
            result = None
        else:
            result = prepare_pair_return_observation(
                left_analysis,
                right_analysis,
                left_case,
                right_case,
                left_prepared,
                right_prepared,
                return_coverage_ids=(),
            )
        first_event_count = session.recorder.event_count
        if expected_reasons:
            repeated = prepare_pair_return_observation(
                left_analysis,
                right_analysis,
                left_case,
                right_case,
                left_prepared,
                right_prepared,
                return_coverage_ids=(),
            )
            assert repeated.status == "blocked"
            assert session.recorder.event_count == first_event_count
    if result is not None:
        assert result.status == "blocked"
    if expected_reasons:
        projection = session.preview_lifecycle_projection()
        assert tuple(row.reason_id for row in projection.c_active_base) == expected_reasons
        assert len(projection.q_open_base) == len(expected_reasons)
    else:
        assert session.recorder.event_count == 0
    assert tuple(session.domain_signal_error_kinds) == (() if malformed else expected_errors)


def test_return_abi_facts_survive_views_and_serialization():
    analysis = FunctionReturnAnalysis("fn", "0x1000", [], [], binary_id="bin")
    analysis.return_abi_facts = {
        "schema_version": 1,
        "calling_convention": {
            "status": "PRESENT", "value": ("ghidra_calling_convention_v1", "default"), "source": "api"
        },
    }
    accepted = analysis.with_accepted_return_partition([])
    diagnostics = analysis.with_summary_return_diagnostics()
    assert accepted.return_abi_facts == analysis.return_abi_facts
    assert diagnostics.return_abi_facts == analysis.return_abi_facts
    assert accepted.return_abi_facts is not analysis.return_abi_facts
    assert "return_abi_facts" in analysis.to_dict()


def test_ghidra_abi_fact_extractor_seals_present_missing_and_malformed():
    from scripts.function_tracer_pcode.analysis.analyzer_services.session_helpers_1 import (
        _sealed_return_abi_facts,
    )
    sealed_return_abi_facts = _sealed_return_abi_facts

    class Space:
        def getName(self):
            return "register"

    class Address:
        def getAddressSpace(self):
            return Space()

        def getOffset(self):
            return 16

    class Varnode:
        def getAddress(self):
            return Address()

        def getSize(self):
            return 8

    class Storage:
        def getVarnodes(self):
            return (Varnode(),)

    class Prototype:
        def getModelName(self):
            return "default"

        def getReturnStorage(self):
            return Storage()

    class ReturnType:
        def getPathName(self):
            return "/int"

        def getLength(self):
            return 4

    present = sealed_return_abi_facts(Prototype(), ReturnType(), "int")
    assert {present[name]["status"] for name in (
        "calling_convention",
        "declared_or_effective_return_type",
        "return_storage_descriptor",
    )} == {"PRESENT"}

    missing = sealed_return_abi_facts(object(), None, None)
    assert {missing[name]["status"] for name in (
        "calling_convention",
        "declared_or_effective_return_type",
        "return_storage_descriptor",
    )} == {"MISSING"}
    legacy_only = sealed_return_abi_facts(object(), None, "legacy int display")
    assert legacy_only["declared_or_effective_return_type"]["status"] == "MISSING"

    class NoneCallingPrototype:
        def getModelName(self):
            return None

    none_calling = sealed_return_abi_facts(NoneCallingPrototype(), None, None)
    assert none_calling["calling_convention"]["status"] == "MISSING"

    class MissingStoragePrototype:
        def getReturnStorage(self):
            return None

    none_storage = sealed_return_abi_facts(
        MissingStoragePrototype(), None, None
    )
    assert none_storage["return_storage_descriptor"]["status"] == "MISSING"

    class EmptyStorage:
        def getVarnodes(self):
            return ()

    class EmptyStoragePrototype:
        def getReturnStorage(self):
            return EmptyStorage()

    empty_storage = sealed_return_abi_facts(
        EmptyStoragePrototype(), None, None
    )
    assert empty_storage["return_storage_descriptor"]["status"] == "MISSING"

    class BrokenPrototype:
        def getModelName(self):
            raise RuntimeError("bad calling convention")

        def getReturnStorage(self):
            raise RuntimeError("bad storage")

    malformed = sealed_return_abi_facts(BrokenPrototype(), None, None)
    assert malformed["calling_convention"]["status"] == "MALFORMED"
    assert malformed["return_storage_descriptor"]["status"] == "MALFORMED"

    class InvalidSpace(Space):
        def getName(self):
            return ""

    class InvalidAddress(Address):
        def getAddressSpace(self):
            return InvalidSpace()

    class InvalidVarnode(Varnode):
        def getAddress(self):
            return InvalidAddress()

        def getSize(self):
            return 0

    class InvalidStorage(Storage):
        def getVarnodes(self):
            return (InvalidVarnode(),)

    class InvalidStoragePrototype(Prototype):
        def getReturnStorage(self):
            return InvalidStorage()

    invalid_storage = sealed_return_abi_facts(
        InvalidStoragePrototype(), ReturnType(), "int"
    )
    assert invalid_storage["return_storage_descriptor"]["status"] == "MALFORMED"


def test_empty_and_explicit_missing_abi_facts_are_typed_unknown_not_invalid():
    from scripts.function_tracer_pcode.analysis.analyzer_services import session_helpers_1
    sealed_return_abi_facts = getattr(session_helpers_1, "_sealed_return_abi_facts")

    analysis = FunctionReturnAnalysis("fn", "0x1000", [], [], binary_id="bin")
    width_seed = _width_seed(
        "left", function_identity=analysis.outcome_function_identity()
    )

    raw_empty = FunctionReturnAbiSeed.from_analysis_and_width_seed(
        analysis, width_seed
    )
    assert raw_empty.malformed_slots == ()
    assert raw_empty.missing_slots == (
        "calling_convention",
        "declared_or_effective_return_type",
        "return_storage_descriptor",
    )

    analysis.return_abi_facts = sealed_return_abi_facts(object(), None, None)
    explicit_missing = FunctionReturnAbiSeed.from_analysis_and_width_seed(
        analysis, width_seed
    )
    assert explicit_missing.malformed_slots == ()
    assert explicit_missing.missing_slots == (
        "calling_convention",
        "declared_or_effective_return_type",
        "return_storage_descriptor",
    )
    assert not explicit_missing.complete


@pytest.mark.parametrize(
    ("slot", "value"),
    (
        ("calling_convention", ["ghidra_calling_convention_v1", "default"]),
        ("calling_convention", ("wrong_tag", "default")),
        ("declared_or_effective_return_type", ("wrong_tag", "/int", 4)),
        ("declared_or_effective_return_type", ("ghidra_return_type_v1", "/int", -1)),
        ("return_storage_descriptor", ("wrong_tag", ())),
        ("return_storage_descriptor", ("ghidra_return_storage_v1", [["ghidra_return_storage_member_v1", "register", 0, 8]])),
        ("return_storage_descriptor", ("ghidra_return_storage_v1", (("ghidra_return_storage_member_v1", "", 0, 8),))),
        ("return_storage_descriptor", ("ghidra_return_storage_v1", (("ghidra_return_storage_member_v1", "register", 0, 0),))),
        ("return_storage_descriptor", ("ghidra_return_storage_v1", (("ghidra_return_storage_member_v1", "register", 0, 8), ("ghidra_return_storage_member_v1", "register", 0, 8)))),
    ),
)
def test_present_abi_fact_schema_rejects_mutable_wrong_tag_and_invalid_values(slot, value):
    analysis = FunctionReturnAnalysis("fn", "0x1000", [], [], binary_id="bin")
    analysis.return_abi_facts = {
        "schema_version": 1,
        "calling_convention": {
            "status": "PRESENT",
            "value": ("ghidra_calling_convention_v1", "default"),
            "source": "getModelName",
        },
        "declared_or_effective_return_type": {
            "status": "PRESENT",
            "value": ("ghidra_return_type_v1", "/int", 4),
            "source": "getReturnType",
        },
        "return_storage_descriptor": {
            "status": "PRESENT",
            "value": ("ghidra_return_storage_v1", (("ghidra_return_storage_member_v1", "register", 0, 8),)),
            "source": "getReturnStorage",
        },
    }
    analysis.return_abi_facts[slot]["value"] = value
    seed = FunctionReturnAbiSeed.from_analysis_and_width_seed(
        analysis,
        _width_seed("left", function_identity=analysis.outcome_function_identity()),
    )
    assert seed.malformed_slots == (slot,)
    assert not seed.complete


def test_abi_projection_only_catches_typed_nonformability():
    def analysis_and_seed(side, payload=32):
        analysis = FunctionReturnAnalysis(
            f"fn-{side}", f"0x{1 if side == 'left' else 2}000", [], [],
            binary_id=f"bin-{side}",
        )
        analysis.return_abi_facts = {
            "schema_version": 1,
            "calling_convention": {"status": "PRESENT", "value": ("ghidra_calling_convention_v1", "default"), "source": "getModelName"},
            "declared_or_effective_return_type": {"status": "PRESENT", "value": ("ghidra_return_type_v1", "/int", 4), "source": "getReturnType"},
            "return_storage_descriptor": {"status": "PRESENT", "value": ("ghidra_return_storage_v1", (("ghidra_return_storage_member_v1", "register", 0, 8),)), "source": "getReturnStorage"},
        }
        seed = replace(
            _width_seed(side, function_identity=analysis.outcome_function_identity()),
            payload_width=payload,
            payload_value_identity=("payload", side, payload),
        )
        return analysis, seed

    left_analysis, left = analysis_and_seed("left")
    right_analysis, right = analysis_and_seed("right", payload=64)
    target = PairReturnObservationTargetId(
        "top_level_return", left.target_id, right.target_id,
        (left.target_id.function_identity, right.target_id.function_identity),
    )
    pair = PairReturnObservationSeed(
        target, left.digest, right.digest, "top_level_return", target.semantic_anchors
    )
    nonformable = assess_return_abi_pair(
        left_analysis, right_analysis, left, right, pair
    )
    assert nonformable.relation_assessment is None

    with pytest.raises(ValueError, match="pair/unary authority differs") as exc:
        assess_return_abi_pair(
            left_analysis, right_analysis, left, right,
            replace(pair, left_seed_digest="forged"),
        )
    assert not isinstance(exc.value, ProjectionNotFormable)

    incomplete = _width_seed(
        "left", missing=("payload_width_fact",),
        function_identity=left_analysis.outcome_function_identity(),
    )
    incomplete_target = PairReturnObservationTargetId(
        "top_level_return", incomplete.target_id, right.target_id,
        (incomplete.target_id.function_identity, right.target_id.function_identity),
    )
    incomplete_pair = PairReturnObservationSeed(
        incomplete_target, incomplete.digest, right.digest,
        "top_level_return", incomplete_target.semantic_anchors,
    )
    incomplete_assessment = assess_return_abi_pair(
        left_analysis, right_analysis, incomplete, right, incomplete_pair
    )
    assert incomplete_assessment.relation_assessment is None


def test_all_eight_reasons_have_independent_c_and_q_with_n_readonly_members():
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )

    encoder = AbiWidthReadonlyPilotEncoder()
    session = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=encoder,
    ).begin({"case": "slice5-all-reasons-and-n-readonly"})

    missing_width = _width_seed("missing", missing=("return_storage_fact",))
    same_function = ("function", "same-function")
    first_width = _width_seed("first", function_identity=same_function)
    second_width = _width_seed("second", function_identity=same_function)
    projection, _abi_relation, _abi_artifacts, abi_seeds = (
        _abi_relation_artifact(include_unary=True)
    )
    readonly = _readonly_seed()
    resolved_base = _readonly_seed(identified=True)
    resolved = ResolvedReadonlyObjectSetSeed.from_live_completion_closure(
        session, resolved_base, ()
    )
    signals = (
        AbiWidthReadonlyBlockerSignal.from_width_seed(
            missing_width, "return_storage_fact"
        ),
        AbiWidthReadonlyBlockerSignal.from_same_function_width_seeds(
            first_width, second_width
        ),
        AbiWidthReadonlyBlockerSignal.from_return_abi_seed(
            abi_seeds[0], "calling_convention"
        ),
        AbiWidthReadonlyBlockerSignal.from_projection_seed(
            "return_observation_contract_unproven", projection
        ),
        AbiWidthReadonlyBlockerSignal.from_projection_seed(
            "return_abi_relation_unproven", projection
        ),
        AbiWidthReadonlyBlockerSignal.from_projection_seed(
            "return_high_bit_relation_unproven", projection
        ),
        *(
            AbiWidthReadonlyBlockerSignal.from_readonly_member(
                readonly, "left", index
            )
            for index in range(len(readonly.left_member_keys))
        ),
        AbiWidthReadonlyBlockerSignal.from_readonly_object_sets(resolved),
    )
    for signal in signals:
        assert session.emit_domain_signal(signal) == 1
    lifecycle = session.preview_lifecycle_projection()
    assert len(lifecycle.c_active_base) == len(signals) == 9
    assert len(lifecycle.q_open_base) == len(signals)
    assert {row.reason_id for row in lifecycle.c_active_base} == set(
        ABI_WIDTH_READONLY_REASON_SPECS
    )
    readonly_c = tuple(
        row for row in lifecycle.c_active_base
        if row.reason_id == "readonly_storage_identity_unproven"
    )
    readonly_q = tuple(
        row for row in lifecycle.q_open_base
        if row.proof_kind == "readonly_storage_identity"
    )
    assert len(readonly_c) == len(readonly.left_member_keys) == 2
    assert len(readonly_q) == len(readonly.left_member_keys)
    assert len({row.cause_id for row in readonly_c}) == 2
    assert len({row.proof_requirement_id for row in readonly_q}) == 2


def test_n_readonly_completions_promote_one_resolved_relational_cause_in_order():
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )

    encoder = AbiWidthReadonlyPilotEncoder()
    session = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=encoder,
    ).begin({"case": "readonly-unary-to-relational-promotion"})
    seed = _readonly_seed()
    encoder.register_readonly_promotion(session, seed)
    dependencies = []
    for side, indices in (
        ("left", seed.left_unresolved_member_indices),
        ("right", seed.right_unresolved_member_indices),
    ):
        for index in indices:
            blocker = AbiWidthReadonlyBlockerSignal.from_readonly_member(
                seed, side, index
            )
            session.emit_domain_signal(blocker)
            if not dependencies:
                with pytest.raises(ValueError, match="address/width/endian"):
                    ReadonlyStorageIdentityArtifact.from_validated_storage(
                        blocker,
                        seed,
                        side=side,
                        member_index=index,
                        source_snapshot_fingerprint=(
                            session.identity.source_snapshot_fingerprint
                        ),
                        address_space="other",
                        width=99,
                        endian="big",
                        readonly_block=True,
                        provenance_refs=(("wrong-memory-block",),),
                        reachable_use_proof=("wrong-reachable-use",),
                    )
            artifact = ReadonlyStorageIdentityArtifact.from_validated_storage(
                blocker,
                seed,
                side=side,
                member_index=index,
                source_snapshot_fingerprint=(
                    session.identity.source_snapshot_fingerprint
                ),
                address_space="ram",
                width=4,
                endian="little",
                readonly_block=True,
                provenance_refs=(("memory-block", side, index),),
                reachable_use_proof=("all-reachable-uses", side, index),
            )
            intent = encoder.complete_readonly_storage_identity(
                session, blocker, artifact
            )
            receipt = intent.authority_payload.completion_receipt
            expected_dependency_error = (
                "live-session completed"
                if len(dependencies) + 1 == (
                    len(seed.left_unresolved_member_indices)
                    + len(seed.right_unresolved_member_indices)
                )
                else "cardinality"
            )
            with pytest.raises(ValueError, match=expected_dependency_error):
                ResolvedReadonlyObjectSetSeed.from_live_completion_closure(
                    session, seed, (*dependencies, (blocker, artifact, receipt))
                )
            session.emit(intent)
            dependencies.append((blocker, artifact, receipt))

    before_promotion = session.preview_lifecycle_projection()
    assert before_promotion.c_active_base == ()
    assert before_promotion.q_open_base == ()
    encoder.finalize_derived_promotions(session)
    after = session.preview_lifecycle_projection()
    assert [row.reason_id for row in after.c_active_base] == [
        "readonly_object_correspondence_unproven"
    ]
    assert [row.proof_kind for row in after.q_open_base] == [
        "readonly_object_correspondence"
    ]
    events = session.recorder.prefix_view().events
    assert events[-1].header.event_type is EventType.CAUSE_OBSERVED
    completed_sequences = tuple(
        event.header.sequence_number for event in events
        if event.header.event_type is EventType.REQUIREMENT_COMPLETED
    )
    assert len(completed_sequences) == len(dependencies)
    assert max(completed_sequences) < events[-1].header.sequence_number
    resolved = tuple(
        session.domain_signal_state[
            "abi_width_readonly_resolved_readonly_seeds"
        ].values()
    )
    assert len(resolved) == 1
    assert len(resolved[0].dependency_artifact_digests) == len(dependencies) == 4
    facts = ReadonlyCorrespondenceFactSet.from_resolved_seed(resolved[0])
    assert len(facts.shared_value_authority_rows) == 2
    relational_blocker = AbiWidthReadonlyBlockerSignal.from_readonly_object_sets(
        resolved[0]
    )
    query = AbiWidthReadonlySolverQueryAuthority.from_readonly_correspondence_theorem(
        session, relational_blocker, resolved[0]
    )
    assert query.theorem_body[5] == facts.shared_value_authority_rows
    with pytest.raises(ValueError, match="cardinality"):
        ResolvedReadonlyObjectSetSeed.from_live_completion_closure(
            session, seed, dependencies[:-1]
        )
    encoder.finalize_derived_promotions(session)
    assert len(session.recorder.prefix_view().events) == len(events)


def test_high_bit_solver_unsat_uses_live_abi_completion_and_common_issuer(
    monkeypatch,
):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        execute_abi_width_readonly_solver_query,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    key_id = "abi-width-highbit-unsat-key"
    install_execution_authority_signing_key(key_id, b"h" * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "abi-width-highbit-unsat-policy", 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    monkeypatch.setattr(
        execution_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.UNSAT, elapsed_time=timeout),
        ]),
    )
    encoder = AbiWidthReadonlyPilotEncoder(enable_solver_execution=True)
    composite = CompositeProductionSignalEncoder({
        AbiWidthReadonlyBlockerSignal: encoder,
        AbiWidthReadonlySolverExecutionBatchSignal: encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": "highbit-common-issuer-unsat"})
    projection, abi_relation = _abi_relation_artifact(
        session.identity.source_snapshot_fingerprint
    )
    abi_blocker = AbiWidthReadonlyBlockerSignal.from_projection_seed(
        "return_abi_relation_unproven", projection
    )
    high_blocker = AbiWidthReadonlyBlockerSignal.from_projection_seed(
        "return_high_bit_relation_unproven", projection
    )
    with production_signal_scope(session):
        session.emit_domain_signal(abi_blocker)
        abi_intent = encoder.complete_return_abi_relation(
            session, abi_blocker, abi_relation
        )
        abi_receipt = abi_intent.authority_payload.completion_receipt
        session.emit(abi_intent)
        session.emit_domain_signal(high_blocker)
        query = AbiWidthReadonlySolverQueryAuthority.from_high_bit_theorem(
            session,
            high_blocker,
            projection,
            (abi_blocker, abi_relation, abi_receipt),
        )
        emitted_count = execute_abi_width_readonly_solver_query(
            high_blocker,
            query,
            projection,
            (abi_relation,),
            configured_timeout_ms=1000,
        )
        assert emitted_count == 1, session.domain_signal_error_details
    lifecycle = session.preview_lifecycle_projection()
    assert lifecycle.c_active_base == ()
    assert lifecycle.q_open_base == ()
    assert session.domain_signal_state[
        "abi_width_readonly_completion_candidates"
    ][-1][1].proof_body[0] == "return_high_bit_solver_unsat_v2"


def test_readonly_correspondence_solver_unsat_uses_resolved_seed(monkeypatch):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        execute_abi_width_readonly_solver_query,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    key_id = "abi-width-readonly-unsat-key"
    install_execution_authority_signing_key(key_id, b"r" * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "abi-width-readonly-unsat-policy", 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    monkeypatch.setattr(
        execution_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.UNSAT, elapsed_time=timeout),
        ]),
    )
    encoder = AbiWidthReadonlyPilotEncoder(enable_solver_execution=True)
    composite = CompositeProductionSignalEncoder({
        AbiWidthReadonlyBlockerSignal: encoder,
        AbiWidthReadonlySolverExecutionBatchSignal: encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": "readonly-common-issuer-unsat"})
    base = _readonly_seed(identified=True)
    resolved = ResolvedReadonlyObjectSetSeed.from_live_completion_closure(
        session, base, ()
    )
    blocker = AbiWidthReadonlyBlockerSignal.from_readonly_object_sets(resolved)
    with production_signal_scope(session):
        session.emit_domain_signal(blocker)
        query = (
            AbiWidthReadonlySolverQueryAuthority
            .from_readonly_correspondence_theorem(session, blocker, resolved)
        )
        assert execute_abi_width_readonly_solver_query(
            blocker,
            query,
            resolved,
            (),
            configured_timeout_ms=1000,
        ) == 1
    lifecycle = session.preview_lifecycle_projection()
    assert lifecycle.c_active_base == ()
    assert lifecycle.q_open_base == ()
    artifact = session.domain_signal_state[
        "abi_width_readonly_completion_candidates"
    ][-1][1]
    assert type(artifact) is ReadonlyObjectCorrespondenceArtifact
    assert artifact.proof_body[0] == "readonly_correspondence_solver_unsat_v2"


def test_readonly_theorem_uses_real_solver_for_nontrivial_unsat_and_near_miss_sat():
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverStatus
    from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver

    def rendered(**seed_kwargs):
        encoder = AbiWidthReadonlyPilotEncoder()
        session = ProductionDualWritePilotConnector(
            ShadowLifecycleReducer(
                reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
                recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
            ),
            domain_signal_encoder=encoder,
        ).begin({"case": f"readonly-real-z3-{seed_kwargs}"})
        resolved = ResolvedReadonlyObjectSetSeed.from_live_completion_closure(
            session,
            _readonly_seed(identified=True, **seed_kwargs),
            (),
        )
        blocker = AbiWidthReadonlyBlockerSignal.from_readonly_object_sets(resolved)
        assert session.emit_domain_signal(blocker) == 1
        return AbiWidthReadonlySolverQueryAuthority.from_readonly_correspondence_theorem(
            session, blocker, resolved
        )

    solver = Z3Solver(timeout=5)
    available, message = solver.check_availability()
    assert available, message
    positive_query = rendered(right_pointer_index=0)
    positive = solver.check_equivalence_direct(positive_query.query_text)
    near_miss = solver.check_equivalence_direct(
        rendered(pointer_kind="storage").query_text
    )
    assert positive.status is SolverStatus.UNSAT
    assert near_miss.status is SolverStatus.SAT
    assert positive_query.theorem_body[5]
    assert "(assert (= left_" not in positive_query.query_text
    with pytest.raises(ProjectionNotFormable, match="program-independent"):
        rendered(owner_specific_parameter=True)
    with pytest.raises(ProjectionNotFormable, match="shared-input"):
        rendered(right_pointer_index=2)


def test_readonly_correspondence_fact_factory_rejects_wrong_operator_role_and_forgery():
    with pytest.raises(TypeError, match="factory issued"):
        ReadonlyCorrespondenceFactSet()
    for seed in (
        _readonly_seed(
            identified=True, right_reduction_kind="memory_xor"
        ),
        _readonly_seed(
            identified=True, right_term_offset_delta=4
        ),
    ):
        resolved = ResolvedReadonlyObjectSetSeed.from_live_completion_closure(
            _session("readonly-fact-negative"), seed, ()
        )
        with pytest.raises(ProjectionNotFormable):
            ReadonlyCorrespondenceFactSet.from_resolved_seed(resolved)


def test_readonly_solver_timeout_terminalizes_to_timeout_not_unknown(monkeypatch):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        execute_abi_width_readonly_solver_query,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    key_id = "abi-width-readonly-timeout-key"
    install_execution_authority_signing_key(key_id, b"t" * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "abi-width-readonly-timeout-policy", 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    monkeypatch.setattr(
        execution_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult("z3", SolverStatus.TIMEOUT, elapsed_time=timeout),
        ]),
    )
    encoder = AbiWidthReadonlyPilotEncoder(enable_solver_execution=True)
    composite = CompositeProductionSignalEncoder({
        AbiWidthReadonlyBlockerSignal: encoder,
        AbiWidthReadonlySolverExecutionBatchSignal: encoder,
    })
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": "readonly-terminal-timeout"})
    resolved = ResolvedReadonlyObjectSetSeed.from_live_completion_closure(
        session, _readonly_seed(identified=True), ()
    )
    blocker = AbiWidthReadonlyBlockerSignal.from_readonly_object_sets(resolved)
    with production_signal_scope(session):
        session.emit_domain_signal(blocker)
        query = (
            AbiWidthReadonlySolverQueryAuthority
            .from_readonly_correspondence_theorem(session, blocker, resolved)
        )
        assert execute_abi_width_readonly_solver_query(
            blocker, query, resolved, (), configured_timeout_ms=1000
        ) == 1
    evidence = connector.finish(
        session,
        SimpleNamespace(
            error_message=None,
            is_equivalent=None,
            failure_status=None,
            failure_message=None,
            is_timeout=lambda: False,
        ),
        case_id="readonly-terminal-timeout",
    )
    assert evidence.pilot_result.candidate.decision_receipt.outcome.value == "TIMEOUT"
    assert len(
        evidence.pilot_result.reduction.snapshot.terminal_timeout_event_digests
    ) == 1
    assert len(evidence.pilot_result.reduction.projection.c_active_base) == 1
    assert len(evidence.pilot_result.reduction.projection.q_open_base) == 1


@pytest.mark.parametrize(
    ("case_id", "statuses", "expected_event_types", "expected_live"),
    (
        ("readonly-unknown", ("UNKNOWN",), (EventType.SOLVER_UNKNOWN,), True),
        ("readonly-error", ("ERROR",), (EventType.SOLVER_ERROR,), True),
        (
            "readonly-recovered-timeout",
            ("TIMEOUT", "UNSAT"),
            (EventType.SOLVER_TIMEOUT, EventType.REQUIREMENT_COMPLETED),
            False,
        ),
    ),
)
def test_readonly_solver_noncompletion_and_recovered_timeout_histories(
    monkeypatch, case_id, statuses, expected_event_types, expected_live
):
    from scripts.function_tracer_pcode.smt.interface import SolverStatus

    connector, session, encoder, emitted = _run_readonly_solver_fixture(
        monkeypatch,
        case_id,
        tuple(SolverStatus[name] for name in statuses),
    )
    assert emitted == len(expected_event_types)
    encoder.finalize_open_execution_history(session)
    lifecycle = session.preview_lifecycle_projection()
    assert bool(lifecycle.c_active_base) is expected_live
    assert bool(lifecycle.q_open_base) is expected_live
    semantic_events = tuple(
        event.header.event_type
        for event in session.recorder.prefix_view().events
        if event.header.event_type in {
            EventType.SOLVER_UNKNOWN,
            EventType.SOLVER_TIMEOUT,
            EventType.SOLVER_ERROR,
            EventType.REQUIREMENT_COMPLETED,
        }
    )
    assert semantic_events == expected_event_types
    if "recovered" in case_id:
        assert len(session.domain_signal_state["abi_width_solver_census"].events) == 2
        assert semantic_events.count(EventType.SOLVER_TIMEOUT) == 1


def test_receiptless_retry_supersedes_prior_timeout_in_terminal_selection(
    monkeypatch,
):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        SolverExecutionEvidenceBundle,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        execute_abi_width_readonly_solver_query,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverStatus

    _connector, session, encoder, emitted = _run_readonly_solver_fixture(
        monkeypatch, "readonly-timeout-receiptless", (SolverStatus.TIMEOUT,)
    )
    assert emitted == 1
    blocker, query, resolved = session.domain_signal_state[
        "readonly_solver_fixture_authority"
    ]

    def fail_after_attempt_start(_runner, _query, timeout):
        assert timeout == 1
        raise RuntimeError("fixture receipt formation failure")

    monkeypatch.setattr(
        execution_module, "_PINNED_PARALLEL_RUN_IMPL", fail_after_attempt_start
    )
    with production_signal_scope(session):
        with pytest.raises(RuntimeError, match="receipt formation"):
            execute_abi_width_readonly_solver_query(
                blocker, query, resolved, (), configured_timeout_ms=1000
            )
    encoder.finalize_open_execution_history(session)
    census = session.domain_signal_state["abi_width_solver_census"]
    assert len(census.events) == 2
    assert census.events[0].execution_receipt.observed_status == "timeout"
    assert census.events[1].execution_receipt is None
    assert census.events[1].receiptless_attempt.failure_kind == "RuntimeError"

    lifecycle = session.preview_lifecycle_projection()
    assert len(lifecycle.c_active_base) == 1
    assert len(lifecycle.q_open_base) == 1
    terminalizations = encoder.finalize_terminal_timeout_bindings(
        session, session.recorder.seal()
    )
    assert terminalizations == ()
    assert session.domain_signal_state[
        "abi_width_terminal_timeout_selection"
    ] is None
    registry, bundle = session.execution_authority_evidence_bundles[-1]
    assert registry is ABI_WIDTH_READONLY_COMMON_EXECUTION_STAGE_REGISTRY
    restored = SolverExecutionEvidenceBundle.from_persisted(
        bundle.to_authority_dict(registry), registry=registry
    )
    assert restored.evidence_digest == bundle.evidence_digest
    assert restored.census.events[1].receiptless_attempt.attempt_digest == (
        census.events[1].receiptless_attempt.attempt_digest
    )


def test_duplicate_semantic_query_keeps_one_identity_and_distinct_retry_attempts(
    monkeypatch,
):
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        execute_abi_width_readonly_solver_query,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverStatus

    _connector, session, encoder, emitted = _run_readonly_solver_fixture(
        monkeypatch, "readonly-duplicate-semantic-query", (SolverStatus.UNKNOWN,)
    )
    assert emitted == 1
    blocker, query, resolved = session.domain_signal_state[
        "readonly_solver_fixture_authority"
    ]
    with production_signal_scope(session):
        assert execute_abi_width_readonly_solver_query(
            blocker, query, resolved, (), configured_timeout_ms=1000
        ) == 1
    encoder.finalize_open_execution_history(session)
    events = session.domain_signal_state["abi_width_solver_census"].events
    assert len(events) == 2
    assert tuple(event.membership.attempt_ordinal for event in events) == (1, 2)
    assert len({
        event.execution_receipt.query_authority_digest for event in events
    }) == 1
    assert len({
        event.execution_receipt.receipt_digest for event in events
    }) == 2
    assert len({query.authority_digest}) == 1


def test_parallel_duplicate_unsat_selects_exactly_one_completion_authority(
    monkeypatch,
):
    from scripts.function_tracer_pcode.smt.interface import SolverStatus

    _connector, session, encoder, emitted = _run_readonly_solver_fixture(
        monkeypatch,
        "readonly-parallel-duplicate-unsat",
        (SolverStatus.UNSAT, SolverStatus.UNSAT),
    )
    assert emitted == 1
    assert len(session.domain_signal_state[
        "abi_width_readonly_completion_candidates"
    ]) == 1
    assert session.domain_signal_state[
        "abi_width_pending_emission_transactions"
    ] == {}
    assert session.preview_lifecycle_projection().c_active_base == ()
    encoder.finalize_open_execution_history(session)
    assert len(session.domain_signal_state["abi_width_solver_census"].events) == 2


def test_parallel_sat_unsat_conflict_never_completes_or_hands_off(
    monkeypatch,
):
    from scripts.function_tracer_pcode.smt.interface import SolverStatus

    _connector, session, encoder, emitted = _run_readonly_solver_fixture(
        monkeypatch,
        "readonly-parallel-sat-unsat-conflict",
        (SolverStatus.SAT, SolverStatus.UNSAT),
    )
    assert emitted == 0
    assert len(session.preview_lifecycle_projection().c_active_base) == 1
    assert "abi_width_model_bound_refutation_artifacts" not in session.domain_signal_state
    conflicts = session.domain_signal_state["abi_width_solver_decisive_conflicts"]
    assert len(conflicts) == 1
    assert len(conflicts[0]["sat_receipt_digests"]) == 1
    assert len(conflicts[0]["unsat_receipt_digests"]) == 1
    encoder.finalize_open_execution_history(session)
    assert len(session.domain_signal_state["abi_width_solver_census"].events) == 2


def test_dependency_ready_production_scheduler_executes_registered_readonly_query(
    monkeypatch,
):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    key_id = "abi-width-readonly-scheduler-key"
    install_execution_authority_signing_key(key_id, b"r" * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "abi-width-readonly-scheduler-policy", 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    scheduler_calls = {"count": 0}

    def receiptless_then_unsat(_runner, _query, timeout):
        scheduler_calls["count"] += 1
        if scheduler_calls["count"] == 1:
            raise RuntimeError("scheduler receiptless retry fixture")
        return ParallelResult(results=[
            SolverResult("z3", SolverStatus.UNSAT, elapsed_time=timeout)
        ])

    monkeypatch.setattr(
        execution_module, "_PINNED_PARALLEL_RUN_IMPL", receiptless_then_unsat
    )
    encoder = AbiWidthReadonlyPilotEncoder(enable_solver_execution=True)
    composite = CompositeProductionSignalEncoder({
        AbiWidthReadonlyBlockerSignal: encoder,
        AbiWidthReadonlySolverExecutionBatchSignal: encoder,
    })
    session = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=ABI_WIDTH_READONLY_REASON_REGISTRY,
            recovery_registry=ABI_WIDTH_READONLY_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=composite,
    ).begin({"case": "readonly-production-scheduler"})
    resolved = ResolvedReadonlyObjectSetSeed.from_live_completion_closure(
        session, _readonly_seed(identified=True), ()
    )
    blocker = AbiWidthReadonlyBlockerSignal.from_readonly_object_sets(resolved)
    assert session.emit_domain_signal(blocker) == 1
    encoder.register_solver_candidate(session, blocker, resolved)
    encoder.finalize_open_execution_history(session)
    assert session.preview_lifecycle_projection().c_active_base == ()
    census = session.domain_signal_state["abi_width_solver_census"]
    assert len(census.events) == 2
    assert census.events[0].receiptless_attempt is not None
    assert census.events[1].execution_receipt.observed_status == "unsat"
    assert tuple(event.membership.attempt_ordinal for event in census.events) == (1, 2)
    assert len(session.domain_signal_state[
        "abi_width_solver_scheduler_failures"
    ]) == 1
    assert len(session.domain_signal_state[
        "abi_width_readonly_completion_candidates"
    ]) == 1
    assert session.domain_signal_state[
        "abi_width_pending_emission_transactions"
    ] == {}


def _run_fixture_bound_high_bit_sat_authority(
    monkeypatch, high_bit, case_id, *, inject_transaction_failure=False,
    inject_commit_failure=False, inject_partial_commit_failure=False,
):
    import scripts.function_tracer_pcode.equivalence.v2.execution_authority as execution_module
    from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
        ExecutionAuthorityDeploymentPolicy,
        ModelBoundRelationalRefutationArtifact,
        activate_execution_authority_deployment,
        install_execution_authority_signing_key,
    )
    from scripts.function_tracer_pcode.equivalence.v2.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
        CompositeProductionSignalEncoder,
        SatSafetyBlockerProductionSignal,
        execute_abi_width_readonly_solver_query,
        production_signal_scope,
    )
    from scripts.function_tracer_pcode.equivalence.v2.reducer import (
        ShadowLifecycleReducer,
    )
    from scripts.function_tracer_pcode.equivalence.v2.registry import (
        SealedReasonRegistry,
        SealedRecoveryRegistry,
    )
    from scripts.function_tracer_pcode.equivalence.v2.sat_safety import (
        SAT_SAFETY_REASON_REGISTRY,
        SAT_SAFETY_RECOVERY_REGISTRY,
        SatSafetyPilotEncoder,
    )
    from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
    from scripts.function_tracer_pcode.smt.parallel import ParallelResult

    nonce_seed = hashlib.sha256(case_id.encode()).hexdigest()
    nonce_counter = {"value": 0}

    def deterministic_token_hex(length):
        nonce_counter["value"] += 1
        material = hashlib.sha256(
            f"{nonce_seed}:{nonce_counter['value']}".encode()
        ).hexdigest()
        return material[: length * 2]

    monkeypatch.setattr(execution_module.secrets, "token_hex", deterministic_token_hex)
    key_id = "abi-width-highbit-sat-key-" + authority_digest(case_id)[:12]
    install_execution_authority_signing_key(key_id, b"s" * 32)
    activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
        "abi-width-highbit-sat-policy", 1, "test-owner", "test-source",
        key_id, (), 3600, "test-revocation",
    ))
    monkeypatch.setattr(
        execution_module,
        "_PINNED_PARALLEL_RUN_IMPL",
        lambda _runner, _query, timeout: ParallelResult(results=[
            SolverResult(
                "z3", SolverStatus.SAT, elapsed_time=timeout,
                model={"left_payload": 128, "right_payload": 128},
            ),
        ]),
    )
    encoder = AbiWidthReadonlyPilotEncoder(enable_solver_execution=True)
    safety_encoder = SatSafetyPilotEncoder()
    composite = CompositeProductionSignalEncoder({
        AbiWidthReadonlyBlockerSignal: encoder,
        AbiWidthReadonlySolverExecutionBatchSignal: encoder,
        SatSafetyBlockerProductionSignal: safety_encoder,
    })
    if inject_commit_failure:
        def fail_transaction_commit(_session, signal, _intents):
            if type(signal) is AbiWidthReadonlySolverExecutionBatchSignal:
                raise RuntimeError("injected atomic commit failure")

        monkeypatch.setattr(composite, "commit_emitted_signal", fail_transaction_commit)
    if inject_partial_commit_failure:
        original_sat_commit = composite.commit_sat_safety_transformed_observation

        def fail_after_sat_observation(target_session, signal):
            original_sat_commit(target_session, signal)
            raise RuntimeError("injected failure after SAT-safety observation")

        monkeypatch.setattr(
            composite,
            "commit_sat_safety_transformed_observation",
            fail_after_sat_observation,
        )
    reason_registry = SealedReasonRegistry.build((
        *ABI_WIDTH_READONLY_REASON_REGISTRY.snapshot(),
        *SAT_SAFETY_REASON_REGISTRY.snapshot(),
    ))
    recovery_registry = SealedRecoveryRegistry.build((
        *ABI_WIDTH_READONLY_RECOVERY_REGISTRY.snapshot(),
        *SAT_SAFETY_RECOVERY_REGISTRY.snapshot(),
    ))
    connector = ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=reason_registry,
            recovery_registry=recovery_registry,
        ),
        domain_signal_encoder=composite,
    )
    session = connector.begin({"case": case_id})
    projection, abi_relation = _abi_relation_artifact(
        session.identity.source_snapshot_fingerprint,
        fixture=high_bit,
    )
    abi_blocker = AbiWidthReadonlyBlockerSignal.from_projection_seed(
        "return_abi_relation_unproven", projection
    )
    high_blocker = AbiWidthReadonlyBlockerSignal.from_projection_seed(
        "return_high_bit_relation_unproven", projection
    )
    with production_signal_scope(session):
        session.emit_domain_signal(abi_blocker)
        abi_intent = encoder.complete_return_abi_relation(
            session, abi_blocker, abi_relation
        )
        abi_receipt = abi_intent.authority_payload.completion_receipt
        session.emit(abi_intent)
        session.emit_domain_signal(high_blocker)
        query = AbiWidthReadonlySolverQueryAuthority.from_high_bit_theorem(
            session,
            high_blocker,
            projection,
            (abi_blocker, abi_relation, abi_receipt),
        )
        if inject_transaction_failure:
            original_append_many = session.recorder.append_many

            def fail_replacement_transaction(intents):
                batch = tuple(intents)
                if len(batch) == 2:
                    raise RuntimeError("injected atomic append failure")
                return original_append_many(batch)

            session.recorder.append_many = fail_replacement_transaction
        emitted_count = execute_abi_width_readonly_solver_query(
            high_blocker,
            query,
            projection,
            (abi_relation,),
            configured_timeout_ms=1000,
        )
        if (
            inject_transaction_failure
            or inject_commit_failure
            or inject_partial_commit_failure
        ):
            assert emitted_count == 0
        else:
            assert emitted_count == 2, session.domain_signal_error_details
    lifecycle = session.preview_lifecycle_projection()
    if (
        inject_transaction_failure
        or inject_commit_failure
        or inject_partial_commit_failure
    ):
        assert {row.reason_id for row in lifecycle.c_active_base} == {
            "return_high_bit_relation_unproven",
        }
        assert {row.proof_kind for row in lifecycle.q_open_base} == {
            "return_high_bit_relation",
        }
        assert "abi_width_high_bit_sat_transformations" not in (
            session.domain_signal_state
        )
        assert "abi_width_model_bound_refutation_artifacts" not in (
            session.domain_signal_state
        )
        assert session.domain_signal_state.get(
            "abi_width_solver_execution_receipts", set()
        ) == set()
        assert session.domain_signal_state.get("sat_safety_observed", set()) == set()
        return {"atomic_failure_preserved_original_frontier": True}
    assert {row.reason_id for row in lifecycle.c_active_base} == {
        "counterexample_analysis_safety_unproven",
    }
    assert {row.proof_kind for row in lifecycle.q_open_base} == {
        "counterexample_safety",
    }
    assert len(session.domain_signal_state[
        "abi_width_high_bit_sat_transformations"
    ]) == 1
    assert len(session.domain_signal_state[
        "abi_width_model_bound_refutation_artifacts"
    ]) == 1
    assert type(session.domain_signal_state[
        "abi_width_model_bound_refutation_artifacts"
    ][0]) is ModelBoundRelationalRefutationArtifact
    encoder.finalize_open_execution_history(session)
    census = session.domain_signal_state["abi_width_solver_census"]
    model_artifact = session.domain_signal_state[
        "abi_width_model_bound_refutation_artifacts"
    ][0]
    sat_events = tuple(
        event for event in census.events
        if event.execution_receipt is not None
        and event.execution_receipt.observed_status == "sat"
    )
    selected_events = tuple(
        event for event in sat_events
        if event.execution_receipt.receipt_digest
        == model_artifact.sat_execution_receipt.receipt_digest
    )
    assert len(selected_events) == 1
    event = selected_events[0]
    c_rows = tuple(lifecycle.c_active_base)
    q_rows = tuple(lifecycle.q_open_base)
    return {
        "projection_seed_digest": projection.seed_digest,
        "projection_source_snapshot_pair": json.loads(json.dumps(
            projection.source_snapshot_pair
        )),
        "projection_pair_target_digest": authority_digest(projection.pair_target_key),
        "raw_return_widths": [32, 64],
        "normalized_storage_widths": [
            projection.left_storage_width,
            projection.right_storage_width,
        ],
        "extension_relations": [
            projection.left_extension_kind,
            projection.right_extension_kind,
        ],
        "abi_relation_artifact_digest": abi_relation.artifact_digest,
        "abi_completion_receipt_digest": authority_digest(abi_receipt),
        "high_bit_cause_rows_digest": authority_digest(c_rows),
        "live_requirement_rows_digest": authority_digest(q_rows),
        "query_authority_digest": query.authority_digest,
        "solver_membership_digest": authority_digest(event.membership),
        "sat_execution_receipt_digest": authority_digest(event.execution_receipt),
        "model_safety_handoff_digest": authority_digest(model_artifact),
        "active_reason_ids": sorted(row.reason_id for row in lifecycle.c_active_base),
        "open_proof_kinds": sorted(row.proof_kind for row in lifecycle.q_open_base),
    }


def test_high_bit_solver_sat_atomically_replaces_q_with_model_safety(monkeypatch):
    root = Path(__file__).resolve().parents[1]
    payload = json.loads((root / (
        "fixtures/unknown_taxonomy_v2/phase6/"
        "slice5_representative_validation.json"
    )).read_text(encoding="utf-8"))
    high_bit = payload["compiled_fixture_evidence"][
        "slice5_return_high_bit_near_miss"
    ]
    evidence = _run_fixture_bound_high_bit_sat_authority(
        monkeypatch, high_bit, "slice5-highbit-typed-authority-test"
    )
    assert evidence["projection_seed_digest"] == high_bit[
        "shared_authority_chain"
    ]["projection_seed_digest"]
    assert evidence["active_reason_ids"] == [
        "counterexample_analysis_safety_unproven"
    ]
    assert evidence["open_proof_kinds"] == ["counterexample_safety"]


def test_high_bit_sat_append_failure_preserves_original_cause_and_q(monkeypatch):
    root = Path(__file__).resolve().parents[1]
    payload = json.loads((root / (
        "fixtures/unknown_taxonomy_v2/phase6/"
        "slice5_representative_validation.json"
    )).read_text(encoding="utf-8"))
    high_bit = payload["compiled_fixture_evidence"][
        "slice5_return_high_bit_near_miss"
    ]
    evidence = _run_fixture_bound_high_bit_sat_authority(
        monkeypatch, high_bit, "slice5-highbit-atomic-append-failure",
        inject_transaction_failure=True,
    )
    assert evidence["atomic_failure_preserved_original_frontier"] is True


def test_high_bit_sat_commit_failure_preserves_original_cause_and_q(monkeypatch):
    root = Path(__file__).resolve().parents[1]
    payload = json.loads((root / (
        "fixtures/unknown_taxonomy_v2/phase6/"
        "slice5_representative_validation.json"
    )).read_text(encoding="utf-8"))
    high_bit = payload["compiled_fixture_evidence"][
        "slice5_return_high_bit_near_miss"
    ]
    evidence = _run_fixture_bound_high_bit_sat_authority(
        monkeypatch, high_bit, "slice5-highbit-atomic-commit-failure",
        inject_commit_failure=True,
    )
    assert evidence["atomic_failure_preserved_original_frontier"] is True


def test_high_bit_sat_partial_commit_failure_rolls_back_every_ledger(monkeypatch):
    root = Path(__file__).resolve().parents[1]
    payload = json.loads((root / (
        "fixtures/unknown_taxonomy_v2/phase6/"
        "slice5_representative_validation.json"
    )).read_text(encoding="utf-8"))
    high_bit = payload["compiled_fixture_evidence"][
        "slice5_return_high_bit_near_miss"
    ]
    evidence = _run_fixture_bound_high_bit_sat_authority(
        monkeypatch, high_bit, "slice5-highbit-partial-commit-failure",
        inject_partial_commit_failure=True,
    )
    assert evidence["atomic_failure_preserved_original_frontier"] is True


def test_high_bit_mask_relation_rejects_noncanonical_decimal_spellings():
    for kind in (
        "zero_extend_or_mask:01099511627776",
        "zero_extend_or_mask:١٠٩٩٥١١٦٢٧٧٦",
    ):
        with pytest.raises(ValueError, match="mask is not canonical"):
            AbiWidthReadonlySolverQueryAuthority._extended_payload(
                "payload", 32, 64, kind
            )

# -*- coding: utf-8 -*-

from dataclasses import replace
import ast
import copy
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.v2.call_effect import (
    CALL_EFFECT_ARTIFACT_CAPABILITY_REGISTRY,
    CALL_EFFECT_FAILURE_RULES,
    CALL_EFFECT_REASON_REGISTRY,
    CALL_EFFECT_REASON_SPECS,
    CALL_EFFECT_RECOVERY_REGISTRY,
    CALL_EFFECT_PRODUCER_EXCEPTION_PATTERNS,
    CALL_EFFECT_PRODUCER_OUTPUT_PATTERNS,
    CALL_EFFECT_PRODUCER_PATTERN_DISPOSITIONS,
    PURE_CALL_CONTRACT,
    CALL_EFFECT_PRODUCTION_STAGE_REGISTRY,
    CallEffectPilotEncoder,
    FailureDisposition,
    classify_failure,
)
from scripts.function_tracer_pcode.equivalence.call_effect_obligations import (
    ArtifactObjectIdentity,
)
from scripts.function_tracer_pcode.equivalence.v2.contracts import (
    CensusMode,
    IdentityScope,
    ProofRequirement,
)
from scripts.function_tracer_pcode.equivalence.v2.census_contract import (
    CensusManifest,
    join_outcome_relations,
)
from scripts.function_tracer_pcode.equivalence.v2.decision import FinalizationAuthority
from scripts.function_tracer_pcode.equivalence.v2.execution_authority import (
    ExecutionAuthorityDeploymentPolicy,
    GenericSolverExecutionReceipt,
    ModelBoundRelationalRefutationArtifact,
    NONPRODUCTION_TEST_SOLVER_EXECUTION_ISSUER,
    PINNED_RELATIONAL_WITNESS_VERIFIER,
    ProducerAttemptMembership,
    ProducerStageContract,
    ProducerStageRegistry,
    TerminalTimeoutCandidate,
    TerminalLifecycleProjectionAuthority,
    TerminalTimeoutSelectionReceipt,
    activate_execution_authority_deployment,
    decode_persisted_execution_receipt,
    install_execution_authority_signing_key,
)
from scripts.function_tracer_pcode.smt.interface import SolverResult, SolverStatus
from scripts.function_tracer_pcode.equivalence.v2.frontier import evaluate_live_frontier
from scripts.function_tracer_pcode.equivalence.v2.contracts import authority_digest
from scripts.function_tracer_pcode.equivalence.v2.registry import SatisfactionBindingFactory
from scripts.function_tracer_pcode.equivalence.v2.codecs import StrictV2JsonCodec
from scripts.function_tracer_pcode.equivalence.v2.production_signals import (
    CallEffectBlockerProductionSignal,
    CompositeProductionSignalEncoder,
)
from scripts.function_tracer_pcode.equivalence.v2.reducer import ShadowLifecycleReducer
from scripts.function_tracer_pcode.equivalence.v2.pilot import ProductionDualWritePilotConnector
from scripts.function_tracer_pcode.equivalence.v2.stream import (
    EventIntent,
    EventRecorder,
    EventType,
    GenericReceiptBoundSolverExecutionEventAuthority,
)


def _stage(proof_stage="guard_relation", priority=10):
    return ProducerStageContract(
        "call-effect-domain-v1",
        "typed-call-effect-solver-v1",
        "1",
        proof_stage,
        "nonproduction-test-solver-results-v1",
        frozenset(("proved", "unknown", "timeout", "error", "refuted")),
        frozenset(("timeout",)),
        priority,
    )


def _registry(*contracts):
    return ProducerStageRegistry(1, tuple(contracts or (_stage(),)))


def _deployment_policy(
    active_key_id, *, version=1, retained=(), retention_window_seconds=86400
):
    return ExecutionAuthorityDeploymentPolicy(
        "call-effect-execution-authority",
        version,
        "equivalence-runtime-owner",
        "deployment-secret-store",
        active_key_id,
        tuple(retained),
        retention_window_seconds,
        "immediate-remove-from-verification-set",
    )


def _membership(*, status="timeout", stage="guard_relation", ordinal=1, requirement="req-guard"):
    return ProducerAttemptMembership(
        "call-effect-domain-v1",
        "typed-call-effect-solver-v1",
        "1",
        stage,
        requirement,
        "obligation-1",
        "observation-contract",
        status,
        f"attempt-{ordinal}",
        ordinal,
        "execution-identity",
    )


def _execution_receipt(*, status="timeout", membership=None, model=None, query=None):
    membership = membership or _membership(status=status)
    captured_model = {"x": 1} if status == "sat" and model is None else model
    solver_status = SolverStatus[status.upper()]
    return NONPRODUCTION_TEST_SOLVER_EXECUTION_ISSUER.issue_results(
        registry=_registry(_stage(membership.proof_stage)),
        result_occurrence_id="result-1",
        membership=membership,
        invocation_identity="invocation-1",
        first_invocation_ordinal=1,
        query=query or "(assert violation)\n(check-sat)",
        configured_timeout_ms=1000,
        results=(SolverResult(
            "fixture", solver_status, elapsed_time=0.009, model=captured_model
        ),),
    )[0]


def _census(registry, *rows):
    ledger = begin_solver_execution_ledger(registry, "result-1")
    for membership, receipt in rows:
        ledger.append_nonproduction_fixture(membership, receipt)
    return ledger.seal()


def _refutation(**overrides):
    membership = _membership(status="refuted")
    original_query = "\n".join((
        "(declare-const x Int)", "(assert true)",
        "(assert true)", "(check-sat)",
    ))
    execution = _execution_receipt(
        status="sat", membership=membership, query=original_query
    )
    registry = _registry()
    premise = {"assertions": ("(assert true)",)}
    stage_input = {
        "declarations": ("(declare-const x Int)",),
    }
    replay = PINNED_RELATIONAL_WITNESS_VERIFIER.issue(
        execution,
        registry=registry,
        membership=membership,
        obligation_id="obligation-1",
        prepared_surface_digest="prepared-surface",
        observation_contract_id="observation-contract",
        normalized_assertion="true",
        premise=premise,
        stage_input=stage_input,
        model={"x": 1},
        configured_timeout_ms=1000,
        nonproduction_replay_results=(SolverResult(
            "fixture", SolverStatus.SAT, elapsed_time=0.003, model={"x": 1}
        ),),
    )
    payload = {
        "obligation_id": "obligation-1",
        "source_snapshot_digests": ("left-snapshot", "right-snapshot"),
        "prepared_surface_digest": "prepared-surface",
        "observation_contract_id": "observation-contract",
        "normalized_assertion": "true",
        "premise": premise,
        "stage_input": stage_input,
        "applicability": replay.applicability_authority,
        "producer_version": "typed-call-effect-producer-v1",
        "encoding_version": "typed-call-effect-encoding-v1",
        "dependency_proof_ids": ("dependency-proof",),
        "sat_execution_receipt": execution,
        "replay_receipt": replay,
        "registry": registry,
        "membership": membership,
    }
    payload.update(overrides)
    return ModelBoundRelationalRefutationArtifact.create(**payload)


def _function_string_outputs(path, function_name, *, class_name=None):
    tree = ast.parse(Path(path).read_text())
    scope = tree
    if class_name is not None:
        scope = next(
            node for node in tree.body
            if isinstance(node, ast.ClassDef) and node.name == class_name
        )
    function = next(
        node for node in scope.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        and node.name == function_name
    )
    values = set()
    for node in ast.walk(function):
        if (
            isinstance(node, ast.Return)
            and isinstance(node.value, ast.Constant)
            and isinstance(node.value.value, str)
        ):
            values.add(node.value.value)
        if (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "append"
            and node.args
            and isinstance(node.args[0], ast.Constant)
            and isinstance(node.args[0].value, str)
        ):
            values.add(node.args[0].value)
    return values


def _producer_patterns(path):
    tree = ast.parse(Path(path).read_text())
    outputs, exceptions = set(), set()

    def normalized(value):
        if isinstance(value, ast.Constant) and isinstance(value.value, str):
            return value.value
        if isinstance(value, ast.JoinedStr):
            return "".join(
                item.value
                if isinstance(item, ast.Constant) and isinstance(item.value, str)
                else "{}"
                for item in value.values
            )
        return None

    for node in ast.walk(tree):
        if (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "append"
            and node.args
        ):
            value = normalized(node.args[0])
            if value is not None and ":" in value:
                outputs.add(value.split(":", 1)[1])
        if (
            isinstance(node, ast.Raise)
            and isinstance(node.exc, ast.Call)
            and node.exc.args
        ):
            value = normalized(node.exc.args[0])
            if value is not None:
                exceptions.add(value)
    build_inputs = next(
        node for node in tree.body
        if isinstance(node, ast.FunctionDef) and node.name == "_build_inputs"
    )

    def visit_direct(statement):
        if isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            return
        if isinstance(statement, ast.Return):
            for item in ast.walk(statement.value):
                value = normalized(item)
                if value is not None:
                    outputs.add(value)
            return
        for child in ast.iter_child_nodes(statement):
            visit_direct(child)

    for statement in build_inputs.body:
        visit_direct(statement)
    return outputs, exceptions


def test_reason_and_recovery_registries_exactly_cover_specs():
    assert {item.reason_id for item in CALL_EFFECT_REASON_REGISTRY.snapshot()} == set(
        CALL_EFFECT_REASON_SPECS
    )
    contracts = {
        item.contract_definition_id for item in CALL_EFFECT_RECOVERY_REGISTRY.snapshot()
    }
    assert {
        spec.contract_definition_id
        for spec in CALL_EFFECT_REASON_SPECS.values()
        if spec.contract_definition_id is not None
    } == contracts


def test_requirement_proof_kinds_have_one_reason_owner():
    owners = {}
    for spec in CALL_EFFECT_REASON_SPECS.values():
        for proof_kind in spec.proof_kinds:
            assert proof_kind not in owners, (proof_kind, owners.get(proof_kind), spec.reason_id)
            owners[proof_kind] = spec.reason_id
    assert owners["call_effect_correspondence"] == "call_effect_correspondence_unproven"
    assert owners["memory_effect_order_extraction"] == "memory_effect_order_extraction_incomplete"
    assert owners["memory_effect_order_correspondence"] == "memory_effect_order_unproven"


def test_every_failure_rule_is_exactly_classified_with_declared_scope():
    for key, expected in CALL_EFFECT_FAILURE_RULES.items():
        observed = classify_failure(
            key.source_contract,
            key.failure_code,
            identity_scope=expected.expected_scope,
        )
        assert observed == expected
    with pytest.raises(ValueError, match="unclassified"):
        classify_failure("primary_proof_stage", "new_unreviewed_failure", identity_scope=IdentityScope.UNARY)


def test_current_source_failure_inventory_has_zero_unclassified_values():
    obligations = Path(
        "scripts/function_tracer_pcode/equivalence/call_effect_obligations.py"
    )
    preflight = Path(
        "scripts/function_tracer_pcode/equivalence/call_effect_preflight.py"
    )
    primary = _function_string_outputs(obligations, "_primary_proof_stage")
    assert primary == {
        key.failure_code
        for key in CALL_EFFECT_FAILURE_RULES
        if key.source_contract == "primary_proof_stage"
    }
    infrastructure = {
        key.failure_code
        for key, classification in CALL_EFFECT_FAILURE_RULES.items()
        if classification.disposition == FailureDisposition.INFRASTRUCTURE_INVALID
    }
    for class_name in (
        "UseDomainCoverageMapping",
        "InternalSolverProofArtifact",
        "StructuralCoverageCertificate",
    ):
        assert _function_string_outputs(
            obligations, "verification_failure", class_name=class_name
        ).issubset(infrastructure)
    preflight_roots = _function_string_outputs(
        preflight, "validate_call_resolution_projection"
    ) & {
        "non_call_effect_unsafety_present",
        "unsupported_call_effect_present",
        "caller_memory_relation_not_proven",
        "call_semantic_projection_incomplete",
        "structural_coverage_certificate_incomplete",
        "call_effect_stage_proofs_incomplete",
        "legacy_blocker_replacement_not_ready",
    }
    classified_codes = {key.failure_code for key in CALL_EFFECT_FAILURE_RULES}
    assert preflight_roots
    assert preflight_roots - classified_codes == set()


def test_call_effect_producer_outputs_and_exceptions_have_exact_inventory():
    outputs, exceptions = _producer_patterns(
        "scripts/function_tracer_pcode/equivalence/call_effect_producer.py"
    )
    assert outputs == CALL_EFFECT_PRODUCER_OUTPUT_PATTERNS
    assert exceptions == CALL_EFFECT_PRODUCER_EXCEPTION_PATTERNS
    assert set(CALL_EFFECT_PRODUCER_PATTERN_DISPOSITIONS) == outputs | exceptions
    assert set(CALL_EFFECT_PRODUCER_PATTERN_DISPOSITIONS.values()) == {
        "INFRASTRUCTURE_INVALID", "TYPED_SOLVER_OUTCOME", "TYPED_SEMANTIC_INPUT_GAP"
    }


def test_failure_scope_mismatch_and_infrastructure_semantic_claim_rejected():
    with pytest.raises(ValueError, match="scope differs"):
        classify_failure(
            "primary_proof_stage",
            "abi_argument_relation_missing",
            identity_scope=IdentityScope.UNARY,
        )
    with pytest.raises(ValueError, match="cannot claim semantic scope"):
        classify_failure(
            "infrastructure",
            "comparison_receipt_invalid",
            identity_scope=IdentityScope.RELATIONAL,
        )
    assert classify_failure(
        "infrastructure", "comparison_receipt_invalid"
    ).disposition == FailureDisposition.INFRASTRUCTURE_INVALID


def test_structural_coverage_unary_relational_and_invalid_are_separate():
    assert classify_failure(
        "structural_coverage",
        "left_pcode_census_incomplete",
        identity_scope=IdentityScope.UNARY,
    ).reason_id == "effect_observation_coverage_incomplete"
    assert classify_failure(
        "structural_coverage",
        "uncovered_right_fact_ids_present",
        identity_scope=IdentityScope.RELATIONAL,
    ).reason_id == "effect_endpoint_correspondence_unproven"
    assert classify_failure(
        "structural_coverage", "orphan_legacy_blockers_present"
    ).disposition == FailureDisposition.INFRASTRUCTURE_INVALID


def test_pure_call_any_of_frontier_is_relational_and_effect_free():
    spec = CALL_EFFECT_REASON_SPECS["pure_call_semantics_unproven"]
    assert spec.identity_scope == IdentityScope.RELATIONAL
    assert "call_effect_correspondence" not in spec.proof_kinds
    bindings = {
        slot.name: ProofRequirement("req-" + slot.name, slot.name, ("obligation", slot.name))
        for slot in PURE_CALL_CONTRACT.requirement_slots
    }
    bound = SatisfactionBindingFactory(CALL_EFFECT_RECOVERY_REGISTRY).bind(
        contract_definition_id=PURE_CALL_CONTRACT.contract_definition_id,
        contract_version=PURE_CALL_CONTRACT.contract_version,
        bindings=bindings,
    )
    empty = evaluate_live_frontier(PURE_CALL_CONTRACT, bound, ())
    assert empty.live_open_requirements == frozenset(item.requirement_id for item in bindings.values())
    inline_done = evaluate_live_frontier(
        PURE_CALL_CONTRACT, bound, (bindings["inline_region_semantic_proof"].requirement_id,)
    )
    assert bindings["callee_summary_semantic_proof"].requirement_id not in inline_done.live_open_requirements
    assert bindings["call_guard_relation"].requirement_id in inline_done.live_open_requirements


def test_artifact_capability_registry_rejects_unregistered_and_refutation_completion():
    class FakeLease:
        pass

    with pytest.raises(TypeError, match="exact type"):
        CALL_EFFECT_ARTIFACT_CAPABILITY_REGISTRY.authorize_observe(
            FakeLease(),
            reason_id="pure_call_semantics_unproven",
            identity_scope=IdentityScope.RELATIONAL,
        )
    artifact = _refutation()
    with pytest.raises(ValueError, match="validation failed"):
        CALL_EFFECT_ARTIFACT_CAPABILITY_REGISTRY.authorize_observe(
            artifact,
            reason_id="pure_call_semantics_unproven",
            identity_scope=IdentityScope.RELATIONAL,
        )
    with pytest.raises(ValueError, match="validation failed"):
        CALL_EFFECT_ARTIFACT_CAPABILITY_REGISTRY.authorize_completion(
            artifact,
            reason_id="pure_call_semantics_unproven",
            identity_scope=IdentityScope.RELATIONAL,
            proof_kind="call_guard_relation",
        )
    with pytest.raises(ValueError, match="reason/scope"):
        CALL_EFFECT_ARTIFACT_CAPABILITY_REGISTRY.authorize_observe(
            artifact,
            reason_id="effect_observation_coverage_incomplete",
            identity_scope=IdentityScope.UNARY,
        )


def test_artifact_identity_near_miss_is_fail_closed():
    incomplete = ArtifactObjectIdentity(None, None)
    with pytest.raises(TypeError, match="exact type"):
        CALL_EFFECT_ARTIFACT_CAPABILITY_REGISTRY.authorize_observe(
            incomplete,
            reason_id="expression_translation_incomplete",
            identity_scope=IdentityScope.UNARY,
            validation_context={
                "target_identity": incomplete.stable_key(),
                "source_snapshot_digest": "snapshot",
            },
        )


def test_stage_registry_is_sealed_and_priority_is_total():
    registry = _registry(_stage("guard_relation", 10), _stage("return_relation", 20))
    assert registry.get(
        "call-effect-domain-v1", "typed-call-effect-solver-v1", "1", "guard_relation"
    ).terminal_priority == 10
    with pytest.raises(ValueError, match="total order"):
        _registry(_stage("guard_relation", 10), _stage("return_relation", 10))
    with pytest.raises(KeyError, match="unregistered"):
        registry.get("call-effect-domain-v1", "typed-call-effect-solver-v1", "1", "new-stage")


def test_execution_receipt_key_id_supports_stable_rotation_and_old_key_verification():
    install_execution_authority_signing_key(
        "deployment-key-v1", b"1" * 32
    )
    startup_v1 = activate_execution_authority_deployment(
        _deployment_policy("deployment-key-v1")
    )
    assert startup_v1.startup_mode == "fail_closed"
    receipt = _execution_receipt()
    assert receipt.signing_key_id == "deployment-key-v1"
    install_execution_authority_signing_key(
        "deployment-key-v2", b"2" * 32
    )
    startup_v2 = activate_execution_authority_deployment(
        _deployment_policy(
            "deployment-key-v2", version=2, retained=("deployment-key-v1",)
        )
    )
    assert startup_v2.retained_verification_key_ids == ("deployment-key-v1",)
    decoded = decode_persisted_execution_receipt(receipt.to_authority_dict())
    assert decoded.receipt_digest == receipt.receipt_digest
    activate_execution_authority_deployment(
        _deployment_policy("deployment-key-v2", version=3)
    )
    with pytest.raises(ValueError, match="outside retention policy"):
        decode_persisted_execution_receipt(receipt.to_authority_dict())
    with pytest.raises(ValueError, match="unavailable signing keys"):
        activate_execution_authority_deployment(
            _deployment_policy("missing-deployment-key", version=4)
        )
    with pytest.raises(ValueError, match="ephemeral"):
        _deployment_policy("process-ephemeral-v1", version=4)


def test_call_effect_blocker_signal_rejects_caller_claimed_arm_and_producer():
    with pytest.raises(TypeError, match="proof-input factory issued"):
        CallEffectBlockerProductionSignal(
            "primary_proof_stage",
            "relational_call_effect_stage_proofs_missing",
            "obligation-1",
            "observation-contract",
            "left-fact",
            "right-fact",
            "callee_summary_semantic_proof",
            "structural-certificate",
            "internal_typed_pure_direct_call_stage_producer",
        )
    with pytest.raises(TypeError, match="exact typed proof input"):
        CallEffectBlockerProductionSignal.from_proof_input(object())


def test_generic_execution_event_round_trip_revalidates_signed_receipt():
    receipt = _execution_receipt(status="timeout")
    recorder = EventRecorder(
        stream_id="generic-receipt-stream",
        result_occurrence_id="result-1",
        source_snapshot_fingerprint="snapshot",
    )
    recorder.append(EventIntent(
        EventType.SOLVER_TIMEOUT,
        GenericReceiptBoundSolverExecutionEventAuthority(
            receipt.proof_requirement_id,
            receipt.to_authority_dict(),
            True,
        ),
    ))
    prefix = recorder.prefix_view()
    recorder.append(EventIntent(
        EventType.SOLVER_TIMEOUT,
        GenericReceiptBoundSolverExecutionEventAuthority(
            receipt.proof_requirement_id,
            receipt.to_authority_dict(),
            True,
        ),
    ))
    stream = recorder.seal()
    assert prefix.finality == "PREFIX"
    assert len(prefix.events) == 1
    assert len(stream.events) == 2
    assert prefix.prefix_chain_digest != stream.envelope.authority_chain_digest
    codec = StrictV2JsonCodec(
        reason_registry=CALL_EFFECT_REASON_REGISTRY,
        recovery_registry=CALL_EFFECT_RECOVERY_REGISTRY,
    )
    decoded = codec.loads(codec.dumps(stream))
    assert decoded == stream
    payload = copy.deepcopy(receipt.to_authority_dict())
    payload["proof_requirement_id"] = "forged-requirement"
    with pytest.raises(ValueError, match="runner result seal"):
        GenericReceiptBoundSolverExecutionEventAuthority(
            "forged-requirement", payload, True
        )


def test_attempt_membership_rejects_unsealed_status_and_stage():
    registry = _registry()
    _membership().validate_against(registry)
    with pytest.raises(ValueError, match="status is not sealed"):
        _membership(status="invented").validate_against(registry)
    with pytest.raises(KeyError, match="unregistered"):
        _membership(stage="new-stage").validate_against(registry)


def test_timeout_candidate_must_join_q_open_and_attempt_exactly():
    registry = _registry()
    membership = _membership()
    receipt = _execution_receipt(membership=membership)
    candidate = TerminalTimeoutCandidate(membership, receipt, 7)
    with pytest.raises(ValueError, match="not live"):
        candidate.validate_against(
            registry, TerminalLifecycleProjectionAuthority.create("result-1", ("req-other",))
        )
    with pytest.raises(ValueError, match="exactly join"):
        TerminalTimeoutCandidate(
            replace(membership, attempt_group_identity="other-attempt"), receipt, 7
        ).validate_against(
            registry, TerminalLifecycleProjectionAuthority.create("result-1", ("req-guard",))
        )


def test_model_bound_refutation_requires_replay_model_output_and_exact_digest():
    artifact = _refutation()
    artifact.validate()
    with pytest.raises(ValueError, match="applicability differs"):
        _refutation(applicability={"witnessed_violation": False})
    with pytest.raises(TypeError, match="factory/codec issued"):
        replace(artifact, premise_digest="other-premise")
    with pytest.raises(TypeError, match="factory/codec issued"):
        replace(artifact.replay_receipt, replay_status="unchecked")


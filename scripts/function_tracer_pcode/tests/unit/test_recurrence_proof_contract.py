import json
import pytest
from dataclasses import replace
from types import SimpleNamespace

from scripts.function_tracer_pcode.equivalence.obligations.cache import (
    ValidatedUnaryArtifactCache,
    ValidatedUnaryArtifactEntry,
)
from scripts.function_tracer_pcode.equivalence.obligations.model import (
    ProofArtifact,
    UnaryArtifactDomain,
)
from scripts.function_tracer_pcode.equivalence.obligations.recurrence import (
    recurrence_proof_requirement,
)
from scripts.function_tracer_pcode.equivalence.obligations.snapshot import (
    SnapshotFingerprintCodec,
)
from scripts.function_tracer_pcode.equivalence.obligations.runtime import (
    ObligationRuntimeSession,
)
from scripts.function_tracer_pcode.equivalence.obligations.unary_premise import (
    build_function_unary_premise,
)
from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
from scripts.function_tracer_pcode.equivalence import recurrence_promotion
from scripts.function_tracer_pcode.equivalence.recurrence_promotion import (
    PairRecurrencePromotionAuthority,
)
from scripts.function_tracer_pcode.analysis.summary_returns import (
    SummaryReturnAcceptanceResult,
)
from scripts.function_tracer_pcode.equivalence.unknown_reason import make_unknown_reason
from scripts.function_tracer_pcode.model import (
    COUNTED_LOOP_SUM_OPCODE,
    CountedLoopSummaryRef,
    Condition,
    Expression,
    LoopSideEffectProfileRef,
    StateTransitionLoopSummaryRef,
)
from scripts.function_tracer_pcode.model.analysis import (
    ReturnInfo,
    SummaryReturnCandidate,
)
from scripts.function_tracer_pcode.model.recurrence_contracts import (
    ImmutableRecurrenceExpression,
    ImmutableRecurrenceCondition,
    QuarantinedRecurrenceReturn,
    QuarantinedRecurrenceProposal,
    RecurrenceDigestCodec,
    RecurrenceSeedCore,
    RecurrenceSubproofEvidence,
    RecurrenceSMTQueryReceipt,
    RecurrenceValidationEvidence,
    RetainedExactReturnRef,
    function_recurrence_binding_digest,
    semantic_recurrence_closure_digest,
)


def _validation_evidence(seed, proposal, binding):
    width_sort = ("width_sort_v1", 4, "bitvec", "signed")
    candidate_id = "test-candidate"
    condition_key = ImmutableRecurrenceCondition.from_condition(Condition(
        Expression.binary_op(
            "INT_SLESS", Expression.constant(0, size=4),
            Expression.parameter("n", index=0, size=4),
        )
    )).stable_key()
    value_key = ImmutableRecurrenceExpression.from_expression(
        Expression.parameter("n", index=0, size=4)
    ).stable_key()
    linear_evidence = (
        "linear_self_recursion_transition_evidence_v1",
        ("step", -1),
        ("effect_profile", "single_direct_self_call_no_store"),
        ("termination_measure", "signed_unit_decrement_to_bound"),
        ("width", 32),
    )
    candidate = (
        "candidate_v2", candidate_id, ("guard_conditions_v1", (condition_key,)),
        value_key,
        (
            "transition_evidence_digest_v1",
            "linear_self_recursion_transition_evidence_v1",
            RecurrenceDigestCodec.digest(
                "recurrence_transition_evidence_v1", linear_evidence
            ),
        ),
        width_sort, ("active_precondition_digest_v1", "2" * 64),
    )
    candidate_proof = RecurrenceSubproofEvidence(
        "candidate_validation",
        ("candidate_validation_v2", "unit_step_affine_recurrence", proposal.digest, (candidate,)),
        "summary_return_candidate_validator_v2",
    )
    transition_proof = RecurrenceSubproofEvidence(
        "transition_termination",
        (
            "transition_termination_v2", proposal.digest,
            ((
                "candidate_transition_v2", candidate_id,
                ("unit_step_affine_recursion_v1", linear_evidence),
            ),),
            (("candidate_surface_v1", candidate_id, width_sort),),
        ),
        "typed_recurrence_transition_termination_validator_v2",
        dependencies=(candidate_proof.digest,),
    )
    overlap_receipt = RecurrenceSMTQueryReceipt(
        "overlap_value_inequality", (condition_key,),
        ("overlap_query_surface_v1", "comparison", width_sort, width_sort, (condition_key,)),
        "z3", "unsat",
    )
    overlap_proof = RecurrenceSubproofEvidence(
        "overlap",
        ("overlap_unsat_v2", proposal.digest, (overlap_receipt.stable_key(),)),
        "condition_smt_overlap_validator_v2",
        dependencies=(candidate_proof.digest, transition_proof.digest),
    )
    coverage_receipt = RecurrenceSMTQueryReceipt(
        "partition_coverage_miss", (condition_key,),
        ("coverage_query_surface_v1", "active_partition", (width_sort,), (condition_key,)),
        "z3", "unsat",
    )
    coverage_proof = RecurrenceSubproofEvidence(
        "partition_coverage",
        ("partition_coverage_unsat_v2", proposal.digest, (coverage_receipt.stable_key(),)),
        "condition_smt_partition_totality_v2",
        dependencies=(overlap_proof.digest,),
    )
    effect_proof = RecurrenceSubproofEvidence(
        "effect_surface",
        (
            "effect_surface_v2", proposal.digest,
            ((
                "candidate_effect_v1", candidate_id, ("effect_region",),
                ("memory_reads",), ("memory_writes",), ("call_effect",),
                ("ub_assumptions",),
            ),),
        ),
        "recurrence_effect_surface_validator_v2",
        dependencies=(candidate_proof.digest,),
    )
    proofs = (candidate_proof, transition_proof, overlap_proof, coverage_proof, effect_proof)
    return RecurrenceValidationEvidence(
        seed.digest, proposal.digest, binding, proofs
    )


def _content_bound_artifact(seed, proposal, premise_digest, target, view_id):
    binding = function_recurrence_binding_digest(
        seed.digest, proposal.digest, premise_digest
    )
    requirement = recurrence_proof_requirement(
        seed.digest, proposal.digest, binding,
        "recurrence_validation_complete", target,
    )
    evidence = _validation_evidence(seed, proposal, binding)
    closure = semantic_recurrence_closure_digest(
        binding,
        (requirement.to_key(),),
        evidence.proof_result_digest,
        evidence.dependency_subproof_digests,
    )
    return ProofArtifact(
        ("validated_recurrence_artifact_v2", closure),
        requirement,
        view_id,
        premise_digest,
        producer_version="1",
        encoding_version="recurrence_digest_codec_v1",
        artifact_validation_status="validated",
        payload={
            "object_target_key": requirement.proof_target_key,
            "semantic_closure_digest": closure,
            "recurrence_validation_evidence": evidence.to_dict(),
        },
    )


def test_transition_termination_validator_accepts_only_complete_small_residues():
    valid = CountedLoopSummaryRef(
        induction_step=1,
        result_size=4,
        signed_loop=True,
        residue_cases=((2, 0, 1, 0), (2, 1, 1, 1)),
    )
    assert recurrence_promotion._validate_counted_summary(valid)[0] == (
        "affine_counted_loop_v1"
    )

    incomplete = CountedLoopSummaryRef(
        induction_step=1,
        result_size=4,
        signed_loop=True,
        residue_cases=((2, 0, 1, 0),),
    )
    with pytest.raises(ValueError, match="partition is incomplete"):
        recurrence_promotion._validate_counted_summary(incomplete)


def test_transition_termination_validator_rejects_non_affine_guarded_branch():
    state = Expression.variable("__loop_state", size=4)
    positive = Expression.binary_op(
        "INT_SLESS", Expression.constant(0, size=4), state
    )
    decrement = Expression.binary_op(
        "INT_SUB", state, Expression.constant(1, size=4)
    )
    valid = StateTransitionLoopSummaryRef(
        state_guard=positive,
        transition_expr=decrement,
        accumulator_init=Expression.constant(0, size=4),
        accumulator_delta=Expression.constant(1, size=4),
        transition_cases=(((), decrement),),
        side_effect_profile=LoopSideEffectProfileRef(),
        state_size=4,
        result_size=4,
    )
    assert recurrence_promotion._validate_state_transition_termination(valid)[0] == (
        "guarded_affine_decreasing_state_v1"
    )

    unsafe_decrement = Expression.binary_op(
        "INT_SUB", state, Expression.constant(2, size=4)
    )
    unsafe = StateTransitionLoopSummaryRef(
        state_guard=positive,
        transition_expr=unsafe_decrement,
        accumulator_init=Expression.constant(0, size=4),
        accumulator_delta=Expression.constant(1, size=4),
        transition_cases=(((), unsafe_decrement),),
        side_effect_profile=LoopSideEffectProfileRef(),
        state_size=4,
        result_size=4,
    )
    with pytest.raises(ValueError, match="can wrap before decreasing"):
        recurrence_promotion._validate_state_transition_termination(unsafe)

    shifted = Expression.binary_op(
        "INT_RIGHT", state, Expression.constant(1, size=4)
    )
    invalid = StateTransitionLoopSummaryRef(
        state_guard=positive,
        transition_expr=shifted,
        accumulator_init=Expression.constant(0, size=4),
        accumulator_delta=Expression.constant(1, size=4),
        transition_cases=(((), shifted),),
        side_effect_profile=LoopSideEffectProfileRef(),
        state_size=4,
        result_size=4,
    )
    with pytest.raises(ValueError, match="not a strict affine decrement"):
        recurrence_promotion._validate_state_transition_termination(invalid)


def test_subproof_semantic_allowlist_rejects_arbitrary_method_and_proposition():
    with pytest.raises(ValueError, match="method is not allowed"):
        RecurrenceSubproofEvidence(
            "candidate_validation",
            ("candidate_validation_v2", "pattern", "proposal", (("candidate_v2",),)),
            "candidate_validator",
        )
    with pytest.raises(ValueError, match="candidate proposition schema"):
        RecurrenceSubproofEvidence(
            "candidate_validation",
            ("test_proposition", "candidate_validation"),
            "summary_return_candidate_validator_v2",
        )


def test_smt_receipt_rejects_tampered_digest_status_and_surface():
    condition_key = ImmutableRecurrenceCondition.from_condition(Condition(
        Expression.binary_op(
            "INT_SLESS", Expression.constant(0, size=4),
            Expression.parameter("n", index=0, size=4),
        )
    )).stable_key()
    width_sort = ("width_sort_v1", 4, "bitvec", "signed")
    receipt = RecurrenceSMTQueryReceipt(
        "partition_coverage_miss", (condition_key,),
        ("coverage_query_surface_v1", "partition", (width_sort,), (condition_key,)),
        "z3", "unsat",
    )
    tampered = list(receipt.stable_key())
    tampered[-1] = "0" * 64
    with pytest.raises(ValueError, match="query digest mismatch"):
        RecurrenceSMTQueryReceipt.from_stable_key(tuple(tampered))
    with pytest.raises(ValueError, match="solver result is not allowed"):
        RecurrenceSMTQueryReceipt(
            "partition_coverage_miss", (condition_key,),
            ("coverage_query_surface_v1", "partition", (width_sort,), (condition_key,)),
            "z3", "unknown",
        )
    with pytest.raises(ValueError, match="width/sort identity"):
        RecurrenceSMTQueryReceipt(
            "partition_coverage_miss", (condition_key,),
            (
                "coverage_query_surface_v1", "partition",
                (("width_sort_v1", 0, "bitvec", "signed"),), (condition_key,),
            ),
            "z3", "unsat",
        )


def test_coverage_subproof_rejects_sat_query_receipt():
    condition_key = ImmutableRecurrenceCondition.from_condition(Condition(
        Expression.binary_op(
            "INT_SLESS", Expression.constant(0, size=4),
            Expression.parameter("n", index=0, size=4),
        )
    )).stable_key()
    width_sort = ("width_sort_v1", 4, "bitvec", "signed")
    receipt = RecurrenceSMTQueryReceipt(
        "partition_coverage_miss", (condition_key,),
        ("coverage_query_surface_v1", "partition", (width_sort,), (condition_key,)),
        "z3", "sat",
    )
    with pytest.raises(ValueError, match="requires one UNSAT"):
        RecurrenceSubproofEvidence(
            "partition_coverage",
            ("partition_coverage_unsat_v2", "proposal", (receipt.stable_key(),)),
            "condition_smt_partition_totality_v2",
        )


def test_recurrence_codec_distinguishes_sequence_kinds_and_rejects_opaque_values():
    assert RecurrenceDigestCodec.digest("test", (1, 2)) != RecurrenceDigestCodec.digest(
        "test", [1, 2]
    )
    with pytest.raises(TypeError):
        RecurrenceDigestCodec.digest("test", {1.0})
    with pytest.raises(TypeError):
        RecurrenceDigestCodec.digest("test", object())


def test_recurrence_expression_dto_fails_closed_on_unknown_expression():
    with pytest.raises(ValueError, match="unsupported recurrence expression"):
        ImmutableRecurrenceExpression.from_expression(Expression.unknown("pending"))


def test_recurrence_expression_dto_is_typed_and_json_round_trips():
    parameter = Expression.parameter("n", index=0, size=4)
    expression = Expression.binary_op(
        "INT_SLESS", parameter, Expression.constant(-1, size=4)
    )
    dto = ImmutableRecurrenceExpression.from_expression(expression)
    assert dto.sort == "bool"
    assert dto.signedness == "signed"
    assert dto.operands[1].value == 0xFFFFFFFF
    restored = ImmutableRecurrenceExpression.from_dict(
        json.loads(json.dumps(dto.to_dict()))
    )
    assert restored.stable_key() == dto.stable_key()
    assert restored.materialize().semantic_key() == dto.stable_key()
    bool_dto = ImmutableRecurrenceExpression.from_expression(
        Expression.constant(True, size=1)
    )
    bv1_dto = ImmutableRecurrenceExpression.from_expression(
        Expression.constant(1, size=1)
    )
    assert bool_dto.sort == "bool"
    assert bv1_dto.sort == "bitvector"
    assert bool_dto.stable_key() != bv1_dto.stable_key()


def test_recurrence_expression_dto_requires_known_operator_and_typed_intrinsic():
    with pytest.raises(ValueError, match="unsupported recurrence binary operator"):
        ImmutableRecurrenceExpression.from_expression(
            Expression.binary_op(
                "INT_DIV", Expression.constant(4), Expression.constant(2)
            )
        )
    with pytest.raises(ValueError, match="typed runtime reference"):
        ImmutableRecurrenceExpression.from_expression(
            Expression.intrinsic(
                "COUNTED_LOOP_SUM",
                [Expression.constant(0), Expression.constant(1)],
                size=4,
                opcode=COUNTED_LOOP_SUM_OPCODE,
            )
        )
    runtime_ref = CountedLoopSummaryRef(-1, 4, True, ())
    intrinsic = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [Expression.constant(0), Expression.constant(1)],
        size=4,
        runtime_ref=runtime_ref,
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    dto = ImmutableRecurrenceExpression.from_expression(intrinsic)
    restored = ImmutableRecurrenceExpression.from_dict(
        json.loads(json.dumps(dto.to_dict()))
    )
    assert restored.materialize().semantic_key() == dto.stable_key()


def test_recurrence_expression_deserialization_reapplies_complete_allowlist():
    dto = ImmutableRecurrenceExpression.from_expression(
        Expression.binary_op(
            "INT_ADD", Expression.constant(4), Expression.constant(2)
        )
    )
    payload = dict(dto.to_dict())
    payload["operator"] = "INT_DIV"
    with pytest.raises(ValueError, match="binary operator"):
        ImmutableRecurrenceExpression.from_dict(payload)
    payload = dict(dto.to_dict())
    payload["operands"] = payload["operands"][:1]
    with pytest.raises(ValueError, match="arity"):
        ImmutableRecurrenceExpression.from_dict(payload)
    payload = dict(dto.to_dict())
    payload["sort"] = "bool"
    with pytest.raises(ValueError, match="operator/sort"):
        ImmutableRecurrenceExpression.from_dict(payload)


def test_recurrence_proposal_canonicalizes_returns_and_rejects_identity_collisions():
    seed = RecurrenceSeedCore(("function", "f"), ("active",), (), ("pure",))
    first = QuarantinedRecurrenceReturn(
        (), ImmutableRecurrenceExpression.from_expression(Expression.constant(1)),
        ("summary", "one"), ("transition", "one"),
    )
    second = QuarantinedRecurrenceReturn(
        (), ImmutableRecurrenceExpression.from_expression(Expression.constant(2)),
        ("summary", "two"), ("transition", "two"),
    )
    forward = QuarantinedRecurrenceProposal(
        seed.digest, "affine", (first, second), ()
    )
    reverse = QuarantinedRecurrenceProposal(
        seed.digest, "affine", (second, first), ()
    )
    assert forward.digest == reverse.digest
    with pytest.raises(ValueError, match="duplicate candidate"):
        QuarantinedRecurrenceProposal(seed.digest, "affine", (first, first), ())
    with pytest.raises(ValueError, match="exact/summary identity collision"):
        QuarantinedRecurrenceProposal(
            seed.digest,
            "affine",
            (first,),
            (RetainedExactReturnRef(first.candidate_id, "payload"),),
        )
def test_legacy_unary_premise_digest_is_bit_for_bit_unchanged():
    seed = ("seed", 1)
    contract = ("contract", "v1")
    snapshot = "snapshot"
    policy = "policy"
    premise = build_function_unary_premise(
        UnaryArtifactDomain.RETURN_OUTCOME_V1.value,
        snapshot,
        seed,
        contract,
        policy,
    )
    seed_digest = SnapshotFingerprintCodec.digest(seed)
    expected = SnapshotFingerprintCodec.digest(
        (
            "function_unary_premise_v2",
            "return_outcome_v1",
            snapshot,
            SnapshotFingerprintCodec.freeze(contract),
            policy,
            seed_digest,
        )
    )
    assert premise.semantic_seed_digest == seed_digest
    assert premise.function_premise_digest == expected


def _cache_entry(seed, proposal, premise_digest, target):
    artifact = _content_bound_artifact(
        seed, proposal, premise_digest, target, ("view", proposal.digest)
    )
    binding = function_recurrence_binding_digest(seed.digest, proposal.digest, premise_digest)
    return ValidatedUnaryArtifactEntry(
        artifact,
        UnaryArtifactDomain.RECURRENCE_SUMMARY_V1.value,
        premise_digest,
        "snapshot",
        seed.digest,
        "policy",
        True,
        True,
        premise_schema_id="function_unary_premise_v2",
        premise_codec_id="recurrence_digest_codec_v1",
        proposal_digest=proposal.digest,
        function_recurrence_binding_digest=binding,
    )


def test_recurrence_cache_keeps_two_proposals_and_requires_exact_binding():
    seed = RecurrenceSeedCore(("function", "f"), ("active",), (), ("pure",))
    proposal_a = QuarantinedRecurrenceProposal(seed.digest, "unit-step-a", (), ())
    proposal_b = QuarantinedRecurrenceProposal(seed.digest, "unit-step-b", (), ())
    assert proposal_a.digest != proposal_b.digest
    premise_digest = "a" * 64
    entry_a = _cache_entry(seed, proposal_a, premise_digest, ("target", "f"))
    entry_b = _cache_entry(seed, proposal_b, premise_digest, ("target", "f"))
    cache = ValidatedUnaryArtifactCache()
    cache.put_recurrence(entry_a)
    cache.put_recurrence(entry_b)

    def lookup(entry):
        return cache.get_recurrence(
            entry.artifact.requirement_id.to_key(),
            premise_digest,
            function_snapshot_fingerprint="snapshot",
            semantic_seed_digest=seed.digest,
            normalization_policy_digest="policy",
            producer_version="1",
            encoding_version="recurrence_digest_codec_v1",
            premise_schema_id="function_unary_premise_v2",
            premise_codec_id="recurrence_digest_codec_v1",
            proposal_digest=entry.proposal_digest,
            function_recurrence_binding_digest=entry.function_recurrence_binding_digest,
        )

    assert lookup(entry_a) is entry_a
    assert lookup(entry_b) is entry_b
    assert cache.get_recurrence(
        entry_a.artifact.requirement_id.to_key(),
        premise_digest,
        function_snapshot_fingerprint="snapshot",
        semantic_seed_digest=seed.digest,
        normalization_policy_digest="policy",
        producer_version="1",
        encoding_version="recurrence_digest_codec_v1",
        proposal_digest=entry_b.proposal_digest,
        function_recurrence_binding_digest=entry_b.function_recurrence_binding_digest,
    ) is None


def test_cache_rejects_proposal_fields_on_legacy_domain():
    seed = RecurrenceSeedCore(("function", "f"), ("active",), (), ("pure",))
    proposal = QuarantinedRecurrenceProposal(seed.digest, "unit-step", (), ())
    entry = _cache_entry(seed, proposal, "b" * 64, ("target", "f"))
    invalid = ValidatedUnaryArtifactEntry(
        entry.artifact,
        UnaryArtifactDomain.RETURN_WIDTH_V1.value,
        entry.function_premise_digest,
        entry.function_snapshot_fingerprint,
        entry.semantic_seed_digest,
        entry.normalization_policy_digest,
        True,
        True,
        proposal_digest=entry.proposal_digest,
        function_recurrence_binding_digest=entry.function_recurrence_binding_digest,
    )
    with pytest.raises(ValueError, match="proposal binding"):
        ValidatedUnaryArtifactCache().put(invalid)


def test_production_publish_cache_lookup_and_import_recompute_selected_proposal():
    analysis = SimpleNamespace(binary_id="left", function_name="f", entry_point=1)
    peer = SimpleNamespace(binary_id="right", function_name="f", entry_point=2)
    seed = RecurrenceSeedCore(("function", "f"), ("active",), (), ("pure",))
    proposal = QuarantinedRecurrenceProposal(seed.digest, "unit-step", (), ())
    contract = ("recurrence_domain_contract_v1", "integer_bitvector")
    policy = "recurrence-summary-normalization-v1"
    unary = ObligationRuntimeSession.create_unary(
        analysis,
        domain=UnaryArtifactDomain.RECURRENCE_SUMMARY_V1.value,
        semantic_seed=seed,
        domain_contract=contract,
        normalization_policy_digest=policy,
    )
    binding = function_recurrence_binding_digest(
        seed.digest, proposal.digest, unary.premise_digest
    )
    requirement = recurrence_proof_requirement(
        seed.digest, proposal.digest, binding,
        "recurrence_validation_complete", ("target", "f"),
    )
    artifact = _content_bound_artifact(
        seed, proposal, unary.premise_digest, ("target", "f"),
        unary.current_view.view_id,
    )
    unary.artifacts.append(artifact)
    entry = unary.publish_recurrence_artifact(artifact, seed, proposal)
    pair = ObligationRuntimeSession.create(analysis, peer)
    pair.unary_artifact_cache = unary.unary_artifact_cache
    pair.import_unary_artifact_for_analysis(
        entry,
        analysis=analysis,
        domain=UnaryArtifactDomain.RECURRENCE_SUMMARY_V1.value,
        semantic_seed=seed,
        selected_recurrence_proposal=proposal,
        pair_side="left",
        domain_contract=contract,
        normalization_policy_digest=policy,
    )
    other = QuarantinedRecurrenceProposal(seed.digest, "other", (), ())
    with pytest.raises(ValueError, match="recurrence import"):
        pair.import_unary_artifact_for_analysis(
            entry,
            analysis=analysis,
            domain=UnaryArtifactDomain.RECURRENCE_SUMMARY_V1.value,
            semantic_seed=seed,
            selected_recurrence_proposal=other,
            pair_side="left",
            domain_contract=contract,
            normalization_policy_digest=policy,
        )


def test_recurrence_publication_rejects_empty_validated_payload():
    analysis = SimpleNamespace(binary_id="left", function_name="f", entry_point=1)
    seed = RecurrenceSeedCore(("function", "f"), ("active",), (), ("pure",))
    proposal = QuarantinedRecurrenceProposal(seed.digest, "unit-step", (), ())
    unary = ObligationRuntimeSession.create_unary(
        analysis,
        domain=UnaryArtifactDomain.RECURRENCE_SUMMARY_V1.value,
        semantic_seed=seed,
        domain_contract=("recurrence_domain_contract_v1",),
        normalization_policy_digest="policy",
    )
    binding = function_recurrence_binding_digest(
        seed.digest, proposal.digest, unary.premise_digest
    )
    requirement = recurrence_proof_requirement(
        seed.digest, proposal.digest, binding,
        "recurrence_validation_complete", ("target", "f"),
    )
    artifact = ProofArtifact(
        ("validated_recurrence_artifact_v2", "unbound"),
        requirement,
        unary.current_view.view_id,
        unary.premise_digest,
        artifact_validation_status="validated",
    )
    unary.artifacts.append(artifact)
    with pytest.raises(ValueError, match="payload"):
        unary.publish_recurrence_artifact(artifact, seed, proposal)


def test_recurrence_promotion_authority_is_branch_local_and_post_inconclusive():
    recurrence_reason = make_unknown_reason(
        "loop_summary_proof_missing",
        recovery_proof_kind="loop_recurrence_proof",
        proof_stage="recurrence_validation_complete",
        evidence_kind="quarantined_recurrence_proposal",
        object_target_key=("proposal", "digest"),
    )
    unknown = SimpleNamespace(
        is_equivalent=None,
        unknown_reasons=[recurrence_reason],
        sat_pairs=0,
        counterexample_raw=None,
    )
    authority = EquivalenceChecker._recurrence_promotion_authority(
        unknown,
        comparison_session_id="session",
        branch_id="S_PAIRWISE",
    )
    assert authority is not None
    assert authority.branch_id == "S_PAIRWISE"
    assert authority.targeted_blocker_keys
    terminal = SimpleNamespace(
        is_equivalent=False,
        unknown_reasons=[recurrence_reason],
        sat_pairs=0,
        counterexample_raw=None,
    )
    assert EquivalenceChecker._recurrence_promotion_authority(
        terminal,
        comparison_session_id="session",
        branch_id="S_PAIRWISE",
    ) is None
    pending_safety = SimpleNamespace(
        is_equivalent=None,
        unknown_reasons=[recurrence_reason],
        sat_pairs=1,
        counterexample_raw={"model": 1},
    )
    assert EquivalenceChecker._recurrence_promotion_authority(
        pending_safety,
        comparison_session_id="session",
        branch_id="S_PAIRWISE",
    ) is None
    with pytest.raises(ValueError, match="counterexample-safety"):
        PairRecurrencePromotionAuthority(
            "session", "S_PAIRWISE", (("blocker",),),
            counterexample_safety_pending=True,
        )


def _recurrence_candidate_fixture(candidate_id, constant):
    condition = Condition(Expression.binary_op(
        "INT_SLESS",
        Expression.constant(constant, size=4),
        Expression.parameter("n", index=0, size=4),
    ))
    value = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("n", index=0, size=4),
        Expression.constant(constant, size=4),
    )
    transition = ("transition", constant)
    quarantined = QuarantinedRecurrenceReturn(
        (ImmutableRecurrenceCondition.from_condition(condition),),
        ImmutableRecurrenceExpression.from_expression(value),
        tuple(candidate_id),
        transition,
    )
    return_info = ReturnInfo(
        hex(constant),
        value,
        [condition],
        return_kind="summary_derived",
        acceptance_status="accepted",
        summary_candidate_id=tuple(candidate_id),
    )
    candidate = SummaryReturnCandidate(
        tuple(candidate_id),
        return_info,
        condition.structural_key(),
        value.structural_key(),
        transition_evidence_key=transition,
        active_precondition_key=("active", constant),
        acceptance_status="accepted",
    )
    return quarantined, candidate


def test_recurrence_acceptance_rebinds_rebuilt_and_reordered_candidates():
    proposal_first, accepted_first = _recurrence_candidate_fixture(
        ("proposal", "first"), 1
    )
    proposal_second, accepted_second = _recurrence_candidate_fixture(
        ("proposal", "second"), 2
    )
    accepted_first = replace(
        accepted_first,
        candidate_id=("rebuilt", "one"),
        return_info=replace(
            accepted_first.return_info,
            summary_candidate_id=("rebuilt", "one"),
        ),
    )
    accepted_second = replace(
        accepted_second,
        candidate_id=("rebuilt", "two"),
        return_info=replace(
            accepted_second.return_info,
            summary_candidate_id=("rebuilt", "two"),
        ),
    )
    proposal = QuarantinedRecurrenceProposal(
        "seed", "unit-test", (proposal_first, proposal_second), ()
    )
    acceptance = SummaryReturnAcceptanceResult(
        (accepted_second.return_info, accepted_first.return_info),
        (accepted_second, accepted_first),
        (),
        True,
    )

    rebound = recurrence_promotion._bind_accepted_candidates_to_proposal(
        acceptance, proposal
    )

    assert {item.candidate_id for item in rebound.candidates} == {
        ("proposal", "first"),
        ("proposal", "second"),
    }
    assert {item.summary_candidate_id for item in rebound.accepted_returns} == {
        ("proposal", "first"),
        ("proposal", "second"),
    }


def test_recurrence_acceptance_rejects_candidate_subset_without_index_error():
    proposal_first, accepted_first = _recurrence_candidate_fixture(
        ("proposal", "first"), 1
    )
    proposal_second, _ = _recurrence_candidate_fixture(
        ("proposal", "second"), 2
    )
    proposal = QuarantinedRecurrenceProposal(
        "seed", "unit-test", (proposal_first, proposal_second), ()
    )
    acceptance = SummaryReturnAcceptanceResult(
        (accepted_first.return_info,), (accepted_first,), (), True
    )

    with pytest.raises(ValueError, match="candidate set is incomplete"):
        recurrence_promotion._bind_accepted_candidates_to_proposal(
            acceptance, proposal
        )


def test_recurrence_acceptance_rejects_matching_id_with_changed_content():
    proposal_return, _ = _recurrence_candidate_fixture(
        ("proposal", "only"), 1
    )
    _, changed_candidate = _recurrence_candidate_fixture(
        ("proposal", "only"), 2
    )
    proposal = QuarantinedRecurrenceProposal(
        "seed", "unit-test", (proposal_return,), ()
    )
    acceptance = SummaryReturnAcceptanceResult(
        (changed_candidate.return_info,), (changed_candidate,), (), True
    )

    with pytest.raises(ValueError, match="content differs"):
        recurrence_promotion._bind_accepted_candidates_to_proposal(
            acceptance, proposal
        )


def test_recurrence_seed_rejects_empty_proposal_binding_as_typed_failure():
    proposal_return, _ = _recurrence_candidate_fixture(
        ("proposal", "only"), 1
    )
    proposal = QuarantinedRecurrenceProposal(
        "seed", "unit-test", (proposal_return,), ()
    )
    analysis = SimpleNamespace(
        outcome_function_identity=lambda: ("function", "f"),
    )

    with pytest.raises(ValueError, match="no accepted candidate binding"):
        recurrence_promotion._seed_core(analysis, proposal, ())

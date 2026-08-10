# -*- coding: utf-8 -*-

from dataclasses import FrozenInstanceError, replace

import pytest

from scripts.function_tracer_pcode.equivalence.v2.census_contract import (
    ActiveOccurrenceMaterialization,
    CoverageInputs,
    CensusEntry,
    CensusManifest,
    CensusStatus,
    compute_canonical_census,
    coverage_ratio,
    join_outcome_relations,
    materialization_metrics,
)
from scripts.function_tracer_pcode.equivalence.v2.contracts import (
    BoundSatisfactionContract,
    BlockerEligibilityBaseRow,
    CActiveBaseRow,
    CauseIdV2,
    CauseOccurrence,
    CauseTransformationEvent,
    CauseTransformationProofReceipt,
    CensusMode,
    ExpressionKind,
    IdentityScope,
    Outcome,
    ProofRequirement,
    QOpenBaseRow,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementCompletionReceipt,
    RequirementSlotDefinition,
    ResultKind,
    SatisfactionContractDefinition,
    SatisfactionExpression,
    TransformationKind,
    VerifiedLifecycleProjection,
    all_of,
    any_of,
    authority_digest,
    requirement_slot,
)
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.v2.registry import (
    SatisfactionBindingFactory,
    SealedReasonRegistry,
    SealedRecoveryRegistry,
    SemanticCauseIdentityFactory,
)
from scripts.function_tracer_pcode.equivalence.v2.decision import (
    DecisiveProofKind,
    DecisiveProofReceipt,
    ErrorReceipt,
    FinalizationAuthority,
    TerminalTimeoutReceipt,
    DecisionReceipt,
    finalize_decision,
)
from scripts.function_tracer_pcode.equivalence.v2.frontier import (
    FrontierBudgetExceeded,
    FrontierEvaluationBudget,
    evaluate_live_frontier,
)
from scripts.function_tracer_pcode.equivalence.v2.stream import (
    ErrorEventAuthority,
    EventIntent,
    EventRecorder,
    EventType,
    SolverExecutionEventAuthority,
    StageObservationEventAuthority,
    SealedEventStream,
)


def _reason(**overrides):
    values = {
        "reason_id": "return_width_bridge_missing",
        "domain": "return_observation",
        "reason_class": "proof_obligation",
        "decision_effect": "blocks_equivalence",
        "allowed_target_kinds": frozenset(("relational_return",)),
        "required_evidence_contract": ("left_width", "right_width"),
        "allowed_proof_kinds": frozenset(("bridge", "canonical_observation")),
        "terminal_eligibility": False,
        "canonicalization_policy_id": "return-width-v1",
        "recovery_addressability": RecoveryAddressability.REQUIREMENT_REQUIRED,
    }
    values.update(overrides)
    return ReasonDefinition(**values)


def _cause(**overrides):
    values = {
        "identity_scope": IdentityScope.RELATIONAL,
        "reason_id": "return_width_bridge_missing",
        "canonical_target_key": ("pair", "left", "right"),
        "missing_semantic_fact": "canonical return observations are equal",
        "semantic_proposition": ("eq", "left-return", "right-return"),
        "observation_surface": ("return", 64),
        "active_semantic_precondition": ("reachable", True),
        "correspondence_contract": ("ordered", "left-to-right"),
    }
    values.update(overrides)
    return SemanticCauseIdentityFactory(
        SealedReasonRegistry.build((_reason(),))
    ).create(target_kind="relational_return", **values)


def _contract():
    expression = all_of(any_of(requirement_slot("A"), requirement_slot("B")), requirement_slot("C"))
    definition = SatisfactionContractDefinition(
        "return-width-recovery",
        1,
        (
            RequirementSlotDefinition("A", frozenset(("bridge",))),
            RequirementSlotDefinition("B", frozenset(("canonical",))),
            RequirementSlotDefinition("C", frozenset(("safety",))),
        ),
        expression,
    )
    requirements = {
        "A": ProofRequirement("req-A", "bridge", ("target", "A")),
        "B": ProofRequirement("req-B", "canonical", ("target", "B")),
        "C": ProofRequirement("req-C", "safety", ("target", "C")),
    }
    return definition, SatisfactionBindingFactory(
        SealedRecoveryRegistry.build((definition,))
    ).bind(
        contract_definition_id=definition.contract_definition_id,
        contract_version=definition.contract_version,
        bindings=requirements,
    )


def _active(result_id="result-1", occurrence="occ-1", cause="cause-1"):
    return CActiveBaseRow(
        result_id, occurrence, cause, "return_width_bridge_missing",
        "return_observation", "blocks_equivalence", "relational_return",
    )


def _open(result_id="result-1", occurrence="occ-1", cause="cause-1", requirement="req-A"):
    return QOpenBaseRow(
        result_id, occurrence, cause, requirement, "bridge", "target-digest"
    )


def _eligible(result_id="result-1", occurrence="occ-1", cause="cause-1"):
    return BlockerEligibilityBaseRow(result_id, occurrence, cause)


def test_reason_definition_is_immutable_and_no_proof_contract_is_strict():
    definition = _reason()
    with pytest.raises(FrozenInstanceError):
        definition.domain = "tampered"
    with pytest.raises(ValueError, match="cannot allow proof kinds"):
        _reason(recovery_addressability=RecoveryAddressability.NO_PROOF_RECOVERY)
    source_targets = {"relational_return"}
    copied = _reason(allowed_target_kinds=source_targets)
    source_targets.add("mutated")
    assert copied.allowed_target_kinds == frozenset(("relational_return",))


def test_cause_identity_excludes_recovery_strategy_and_changes_for_semantics():
    base = _cause()
    # Recovery alternatives and satisfaction expressions are deliberately not
    # CauseIdV2 inputs, so adding one cannot alter this identity.
    with_one_alternative = _cause()
    assert with_one_alternative.value == base.value
    for field, value in (
        ("semantic_proposition", ("eq", "different", "right-return")),
        ("canonical_target_key", ("pair", "other-left", "right")),
        ("active_semantic_precondition", ("reachable", False)),
        ("identity_scope", IdentityScope.UNARY),
        ("correspondence_contract", ("unordered", "bijection")),
    ):
        assert _cause(**{field: value}).value != base.value
    with pytest.raises(ValueError, match="registry-factory"):
        replace(base, value="fabricated")


def test_expression_normalization_is_structural_and_registry_owned():
    a, b, c = requirement_slot("A"), requirement_slot("B"), requirement_slot("C")
    left = all_of(c, all_of(a, b), a)
    right = all_of(b, c, a)
    assert left.digest == right.digest
    # Absorption is intentionally not claimed by structural normalization.
    assert all_of(a, any_of(a, b)).digest != a.digest
    with pytest.raises(ValueError, match="slots differ"):
        SatisfactionContractDefinition(
            "bad", 1,
            (RequirementSlotDefinition("A", frozenset(("proof",))),),
            any_of(a, b),
        )


def test_typed_binding_rejects_missing_extra_duplicate_and_incompatible_slots():
    definition, bound = _contract()
    bindings = dict(bound.slot_bindings)
    with pytest.raises(ValueError, match="missing or extra"):
        SatisfactionBindingFactory(SealedRecoveryRegistry.build((definition,))).bind(
            contract_definition_id=definition.contract_definition_id,
            contract_version=definition.contract_version,
            bindings={"A": bindings["A"], "B": bindings["B"]},
        )
    with pytest.raises(ValueError, match="missing or extra"):
        SatisfactionBindingFactory(SealedRecoveryRegistry.build((definition,))).bind(
            contract_definition_id=definition.contract_definition_id,
            contract_version=definition.contract_version,
            bindings={**bindings, "D": bindings["A"]},
        )
    with pytest.raises(ValueError, match="duplicate proof"):
        SatisfactionBindingFactory(SealedRecoveryRegistry.build((definition,))).bind(
            contract_definition_id=definition.contract_definition_id,
            contract_version=definition.contract_version,
            bindings={**bindings, "B": bindings["A"]},
        )
    with pytest.raises(ValueError, match="incompatible proof"):
        SatisfactionBindingFactory(SealedRecoveryRegistry.build((definition,))).bind(
            contract_definition_id=definition.contract_definition_id,
            contract_version=definition.contract_version,
            bindings={**bindings, "A": ProofRequirement("different", "wrong", "target")},
        )


@pytest.mark.parametrize(
    ("completed", "live", "satisfied"),
    (
        ((), {"req-A", "req-B", "req-C"}, False),
        (("req-A",), {"req-C"}, False),
        (("req-B",), {"req-C"}, False),
        (("req-C",), {"req-A", "req-B"}, False),
        (("req-A", "req-C"), set(), True),
        (("req-B", "req-C"), set(), True),
    ),
)
def test_live_frontier_is_union_of_minimal_satisfying_extensions(completed, live, satisfied):
    definition, bound = _contract()
    result = evaluate_live_frontier(definition, bound, completed)
    assert result.live_open_requirements == frozenset(live)
    assert result.satisfied is satisfied


def test_frontier_budget_exhaustion_has_no_partial_authority():
    definition, bound = _contract()
    with pytest.raises(FrontierBudgetExceeded):
        evaluate_live_frontier(
            definition,
            bound,
            (),
            FrontierEvaluationBudget(
                max_expression_nodes=2,
                max_antichain_sets=100,
                max_requirement_ids=10,
                max_union_operations=100,
            ),
        )
    with pytest.raises(ValueError, match="undeclared"):
        evaluate_live_frontier(definition, bound, ("not-declared",))


def test_occurrence_and_completion_receipt_are_immutable_and_consistent():
    cause = _cause()
    definition, bound = _contract()
    occurrence = CauseOccurrence(
        "occ-1", cause, cause.reason_id, "target-1",
        "relational_return", IdentityScope.RELATIONAL,
        bound.contract_definition_id, bound.contract_version,
        bound.normalized_expression_digest, bound.bound_expression_digest,
        tuple(sorted(bound.requirement_ids())), ("evidence",), "typed",
        "snapshot", "producer", "attempt",
    )
    with pytest.raises(FrozenInstanceError):
        occurrence.reason_id = "tampered"
    with pytest.raises(ValueError, match="differs"):
        replace(occurrence, reason_id="other")
    occurrence.validate_against(_reason(), bound)
    with pytest.raises(ValueError, match="target kind"):
        replace(occurrence, target_kind="wrong").validate_against(_reason(), bound)
    receipt = RequirementCompletionReceipt(
        cause.value, occurrence.occurrence_id, "req-A",
        bound.contract_definition_id, bound.contract_version,
        bound.bound_expression_digest, "proof-artifact", "applicability",
    )
    with pytest.raises(FrozenInstanceError):
        receipt.proof_artifact_digest = "tampered"
    receipt.validate_against(occurrence, bound, {"req-A", "req-B", "req-C"})
    with pytest.raises(ValueError, match="not live"):
        receipt.validate_against(occurrence, bound, {"req-B", "req-C"})


def test_transformation_sets_are_atomic_nonempty_disjoint_and_duplicate_free():
    event = CauseTransformationEvent(
        TransformationKind.REFINEMENT,
        ("old-1", "old-2"),
        ("new-1", "new-2", "new-3"),
        "proof", "stage", "snapshot",
    )
    assert len(event.replaced_occurrence_ids) == 2
    for old, new in (((), ("new",)), (("same",), ("same",)), (("old", "old"), ("new",))):
        with pytest.raises(ValueError):
            CauseTransformationEvent(
                TransformationKind.REPLACEMENT, old, new, "proof", "stage", "snapshot"
            )
    receipt = CauseTransformationProofReceipt(
        "proof",
        (("old-1", "cause-old-1"), ("old-2", "cause-old-2")),
        (("new-1", "cause-new-1"), ("new-2", "cause-new-2"), ("new-3", "cause-new-3")),
        (("old-req-1", "new-req-1"),),
        "snapshot",
        True,
    )
    receipt.validate_event(event)
    with pytest.raises(ValueError, match="every replacement"):
        replace(receipt, replacement_occurrence_bindings=(("new-1", "cause"),)).validate_event(event)
    with pytest.raises(ValueError, match="one-to-one"):
        replace(
            receipt,
            requirement_mapping=(("old-req", "new-req-1"), ("old-req", "new-req-2")),
        ).validate_event(event)


def test_event_stream_is_ordered_hash_chained_and_excludes_diagnostics():
    def build(detail):
        recorder = EventRecorder(
            stream_id="stream", result_occurrence_id="result", source_snapshot_fingerprint="snapshot"
        )
        recorder.append(EventIntent(
            EventType.NORMALIZATION_NO_CHANGE,
            StageObservationEventAuthority("normalization", "observation"), detail,
        ))
        recorder.append(EventIntent(
            EventType.SOLVER_UNKNOWN,
            SolverExecutionEventAuthority("req-A", "solver-1", "UNKNOWN"),
            {"elapsed": 1.2},
        ))
        return recorder.seal()

    first = build({"path": "/tmp/a", "timestamp": "one"})
    second = build({"path": "/different", "timestamp": "two"})
    assert first.envelope.authority_chain_digest == second.envelope.authority_chain_digest
    tampered_event = replace(
        first.events[1],
        authority_payload=SolverExecutionEventAuthority("other", "solver-1", "UNKNOWN"),
    )
    with pytest.raises(ValueError, match="payload digest"):
        SealedEventStream(first.envelope, (first.events[0], tampered_event)).validate()
    with pytest.raises(ValueError, match="result occurrence"):
        SealedEventStream(
            replace(first.envelope, result_occurrence_id="transplanted"), first.events
        ).validate()
    with pytest.raises(ValueError, match="source snapshot"):
        SealedEventStream(
            replace(first.envelope, source_snapshot_fingerprint="transplanted"), first.events
        ).validate()
    recorder = EventRecorder(
        stream_id="sealed", result_occurrence_id="result", source_snapshot_fingerprint="snapshot"
    )
    recorder.append(EventIntent(EventType.ERROR, ErrorEventAuthority("error", "x")))
    recorder.seal()
    with pytest.raises(ValueError, match="immutable"):
        recorder.append(EventIntent(EventType.ERROR, ErrorEventAuthority("error", "y")))


def test_verified_lifecycle_projection_enforces_foreign_keys_and_order_independent_digests():
    left = _active(occurrence="occ-2", cause="cause-2")
    right = _active()
    q_left = _open(occurrence="occ-2", cause="cause-2", requirement="req-B")
    q_right = _open()
    first = VerifiedLifecycleProjection.seal(
        result_occurrence_id="result-1",
        snapshot_digest="snapshot",
        c_active_base=(left, right),
        q_open_base=(q_left, q_right),
        blocker_eligibility_base=(
            _eligible(occurrence="occ-2", cause="cause-2"), _eligible(),
        ),
        satisfaction_projection={"version": 1},
    )
    second = VerifiedLifecycleProjection.seal(
        result_occurrence_id="result-1",
        snapshot_digest="snapshot",
        c_active_base=(right, left),
        q_open_base=(q_right, q_left),
        blocker_eligibility_base=(
            _eligible(), _eligible(occurrence="occ-2", cause="cause-2"),
        ),
        satisfaction_projection={"version": 1},
    )
    assert first.lifecycle_projection_digest == second.lifecycle_projection_digest
    changed_proof = VerifiedLifecycleProjection.seal(
        result_occurrence_id="result-1",
        snapshot_digest="snapshot",
        c_active_base=(right, left),
        q_open_base=(q_right, q_left),
        blocker_eligibility_base=(
            _eligible(), _eligible(occurrence="occ-2", cause="cause-2"),
        ),
        satisfaction_projection={"version": 2, "alternative": "new"},
    )
    assert changed_proof.semantic_cause_projection_digest == first.semantic_cause_projection_digest
    assert changed_proof.satisfaction_projection_digest != first.satisfaction_projection_digest
    with pytest.raises(ValueError, match="foreign|matching active"):
        VerifiedLifecycleProjection.seal(
            result_occurrence_id="result-1", snapshot_digest="snapshot", c_active_base=(right,),
            q_open_base=(_open(occurrence="missing"),),
            blocker_eligibility_base=(_eligible(),), satisfaction_projection={},
        )


def _projection(result_id="result-1", *, active=True, open_requirement=True):
    causes = (_active(result_id=result_id),) if active else ()
    requirements = (_open(result_id=result_id),) if active and open_requirement else ()
    return VerifiedLifecycleProjection.seal(
        result_occurrence_id=result_id,
        snapshot_digest="snapshot",
        c_active_base=causes,
        q_open_base=requirements,
        blocker_eligibility_base=(
            (_eligible(result_id=result_id),) if active else ()
        ),
        satisfaction_projection={"frontier": ("req-A",) if requirements else ()},
    )


def _decisive(projection, kind):
    return DecisiveProofReceipt.create(
        result_occurrence_id=projection.result_occurrence_id,
        lifecycle_projection_digest=projection.lifecycle_projection_digest,
        proof_kind=kind,
        proof_artifact_digest="proof-artifact",
    )


def _timeout(projection, requirement="req-A"):
    return TerminalTimeoutReceipt.create(
        result_occurrence_id=projection.result_occurrence_id,
        lifecycle_projection_digest=projection.lifecycle_projection_digest,
        proof_requirement_id=requirement,
        execution_event_digest="timeout-event",
    )


def _error(projection):
    return ErrorReceipt.create(
        result_occurrence_id=projection.result_occurrence_id,
        lifecycle_projection_digest=projection.lifecycle_projection_digest,
        error_kind="malformed_authority",
        error_artifact_digest="error-artifact",
    )


@pytest.mark.parametrize("expected", tuple(Outcome))
def test_five_value_decision_matrix_is_derived_from_bound_authority(expected):
    projection = _projection(
        "result", active=expected in {Outcome.UNKNOWN, Outcome.TIMEOUT}
    )
    kwargs = {}
    if expected == Outcome.EQUIVALENT:
        kwargs["decisive_proof_receipts"] = (
            _decisive(projection, DecisiveProofKind.EQ_CLOSURE),
        )
    elif expected == Outcome.NOT_EQ:
        kwargs["decisive_proof_receipts"] = (
            _decisive(projection, DecisiveProofKind.SAFE_COUNTEREXAMPLE),
        )
    elif expected == Outcome.TIMEOUT:
        kwargs["terminal_timeout_receipts"] = (_timeout(projection),)
    elif expected == Outcome.ERROR:
        kwargs["error_receipts"] = (_error(projection),)
    receipt = finalize_decision(FinalizationAuthority("result", projection, **kwargs))
    receipt.validate()
    assert receipt.outcome == expected
    with pytest.raises(ValueError, match="DecisionFinalizer"):
        DecisionReceipt("result", expected, "life", "input", "digest")


def test_decision_matrix_fails_closed_for_conflicts_and_forged_authority():
    empty = _projection("result", active=False)
    both = (
        _decisive(empty, DecisiveProofKind.EQ_CLOSURE),
        _decisive(empty, DecisiveProofKind.SAFE_COUNTEREXAMPLE),
    )
    assert finalize_decision(FinalizationAuthority(
        "result", empty, decisive_proof_receipts=both,
    )).outcome == Outcome.ERROR
    active = _projection("result")
    assert finalize_decision(FinalizationAuthority(
        "result", active, terminal_timeout_receipts=(_timeout(active, "other"),),
    )).outcome == Outcome.ERROR
    assert finalize_decision(FinalizationAuthority(
        "result", active,
        decisive_proof_receipts=(_decisive(active, DecisiveProofKind.EQ_CLOSURE),),
    )).outcome == Outcome.UNKNOWN
    assert finalize_decision(FinalizationAuthority(
        "result", active,
        decisive_proof_receipts=(
            _decisive(active, DecisiveProofKind.SAFE_COUNTEREXAMPLE),
        ),
    )).outcome == Outcome.NOT_EQ
    blocks_all = VerifiedLifecycleProjection.seal(
        result_occurrence_id="blocks-all",
        snapshot_digest="snapshot",
        c_active_base=(replace(
            _active(result_id="blocks-all"),
            decision_effect="blocks_decision",
        ),),
        q_open_base=(_open(result_id="blocks-all"),),
        blocker_eligibility_base=(_eligible(result_id="blocks-all"),),
        satisfaction_projection={},
    )
    assert finalize_decision(FinalizationAuthority(
        "blocks-all", blocks_all,
        decisive_proof_receipts=(
            _decisive(blocks_all, DecisiveProofKind.SAFE_COUNTEREXAMPLE),
        ),
    )).outcome == Outcome.UNKNOWN
    forged = replace(active, lifecycle_projection_digest="forged")
    assert finalize_decision(FinalizationAuthority("result", forged)).outcome == Outcome.ERROR


def _decision(result_id="result-1", outcome=Outcome.UNKNOWN):
    active = outcome in {Outcome.UNKNOWN, Outcome.TIMEOUT}
    projection = _projection(result_id, active=active)
    kwargs = {}
    if outcome == Outcome.EQUIVALENT:
        kwargs["decisive_proof_receipts"] = (
            _decisive(projection, DecisiveProofKind.EQ_CLOSURE),
        )
    elif outcome == Outcome.NOT_EQ:
        kwargs["decisive_proof_receipts"] = (
            _decisive(projection, DecisiveProofKind.SAFE_COUNTEREXAMPLE),
        )
    elif outcome == Outcome.TIMEOUT:
        kwargs["terminal_timeout_receipts"] = (_timeout(projection),)
    elif outcome == Outcome.ERROR:
        kwargs["error_receipts"] = (_error(projection),)
    receipt = finalize_decision(FinalizationAuthority(result_id, projection, **kwargs))
    return receipt, projection


def _entry(receipt, kind=ResultKind.V2_NATIVE):
    return CensusEntry(
        receipt.result_occurrence_id, kind, ("domain",), ("binaries",), ("functions",),
        "stream" if kind == ResultKind.V2_NATIVE else None,
        receipt.lifecycle_projection_digest if kind == ResultKind.V2_NATIVE else None,
        receipt.receipt_digest if kind == ResultKind.V2_NATIVE else None,
        "artifact",
    )


def _candidate_census_fixture(outcome=Outcome.UNKNOWN, *, nonterminal_timeout_count=0):
    from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase4 import (
        _candidate,
    )

    candidate, reduction, stream = _candidate(
        outcome,
        nonterminal_timeout_count=nonterminal_timeout_count,
        include_stream=True,
    )
    receipt = candidate.decision_receipt
    entry = CensusEntry(
        receipt.result_occurrence_id,
        ResultKind.V2_NATIVE,
        ("domain",),
        ("binaries",),
        ("functions",),
        reduction.snapshot.event_stream_authority_digest,
        reduction.projection.lifecycle_projection_digest,
        receipt.receipt_digest,
        "artifact",
    )
    return candidate, reduction, stream, entry


def test_manifest_modes_are_strict_and_generated_at_is_not_authority():
    receipt, _ = _decision()
    first = CensusManifest("manifest", CensusMode.V2_CANONICAL, "head", "config", (_entry(receipt),), generated_at="one")
    second = CensusManifest("manifest", CensusMode.V2_CANONICAL, "head", "config", (_entry(receipt),), generated_at="two")
    assert first.manifest_authority_digest == second.manifest_authority_digest
    with pytest.raises(ValueError, match="legacy"):
        CensusManifest(
            "bad", CensusMode.V2_CANONICAL, "head", "config",
            (_entry(receipt, ResultKind.LEGACY),),
        )
    with pytest.raises(ValueError, match="cannot claim"):
        CensusEntry(
            "legacy", ResultKind.LEGACY, (), (), (), "fake-stream", None, None, "artifact"
        )
    legacy = CensusEntry(
        "legacy", ResultKind.LEGACY, ("domain",), ("binaries",), ("functions",),
        None, None, None, "artifact", "pair"
    )
    native = replace(_entry(receipt), migration_pair_id="pair")
    CensusManifest(
        "comparison", CensusMode.MIGRATION_COMPARISON, "head", "config",
        (native, legacy),
    )
    with pytest.raises(ValueError, match="exact v1/v2"):
        CensusManifest(
            "bad-comparison", CensusMode.MIGRATION_COMPARISON, "head", "config",
            (native,),
        )
    with pytest.raises(ValueError, match="comparison identities"):
        CensusManifest(
            "bad-identity", CensusMode.MIGRATION_COMPARISON, "head", "config",
            (native, replace(legacy, function_identities=("different",))),
        )


def test_outcome_join_checks_key_sets_and_all_authority_digests():
    receipt, projection = _decision()
    manifest = CensusManifest(
        "manifest", CensusMode.V2_CANONICAL, "head", "config", (_entry(receipt),)
    )
    result = join_outcome_relations(manifest, (receipt,), (projection,))
    assert result["decision_counts"] == {
        "EQUIVALENT": 0, "NOT_EQ": 0, "UNKNOWN": 1, "TIMEOUT": 0, "ERROR": 0,
    }
    with pytest.raises(ValueError, match="key set"):
        join_outcome_relations(manifest, (), (projection,))
    forged_receipt = object.__new__(DecisionReceipt)
    for name, value in (
        ("result_occurrence_id", receipt.result_occurrence_id),
        ("outcome", receipt.outcome),
        ("lifecycle_projection_digest", receipt.lifecycle_projection_digest),
        ("authority_input_digest", receipt.authority_input_digest),
        ("receipt_digest", "bad"),
    ):
        object.__setattr__(forged_receipt, name, value)
    with pytest.raises(ValueError, match="digest"):
        join_outcome_relations(manifest, (forged_receipt,), (projection,))
    with pytest.raises(ValueError, match="key set"):
        join_outcome_relations(manifest, (receipt,), (_projection("other"),))
    with pytest.raises(ValueError, match="projection"):
        join_outcome_relations(
            manifest, (receipt,),
            (replace(projection, lifecycle_projection_digest="forged"),),
        )


def test_coverage_zero_denominator_is_na_and_materialization_categories_are_disjoint():
    assert coverage_ratio(0, 0) is None
    metrics = materialization_metrics(
        (
            ActiveOccurrenceMaterialization("r", "required-open", "c1", RecoveryAddressability.REQUIREMENT_REQUIRED),
            ActiveOccurrenceMaterialization("r", "required-missing", "c2", RecoveryAddressability.REQUIREMENT_REQUIRED),
            ActiveOccurrenceMaterialization("r", "optional", "c3", RecoveryAddressability.REQUIREMENT_OPTIONAL),
            ActiveOccurrenceMaterialization("r", "none", "c4", RecoveryAddressability.NO_PROOF_RECOVERY),
        ),
        (_open(result_id="r", occurrence="required-open", cause="c1"),),
    )
    assert metrics["required_requirement_materialization_coverage"] == 0.5
    assert metrics["optional_requirement_materialization_rate"] == 0.0
    assert metrics["active_causes_without_materialized_requirement"] == {
        "required_missing": 1,
        "optional_not_materialized": 1,
        "no_proof_recovery": 1,
    }
    with pytest.raises(ValueError, match="NO_PROOF_RECOVERY"):
        materialization_metrics(
            (ActiveOccurrenceMaterialization("r", "none", "c", RecoveryAddressability.NO_PROOF_RECOVERY),),
            (_open(result_id="r", occurrence="none", cause="c"),),
        )


def test_materialization_join_uses_full_result_occurrence_cause_key():
    metrics = materialization_metrics(
        (ActiveOccurrenceMaterialization(
            "result-1", "shared", "cause", RecoveryAddressability.REQUIREMENT_REQUIRED
        ),),
        (_open(result_id="result-2", occurrence="shared", cause="cause"),),
    )
    assert metrics["required_requirement_materialization_coverage"] == 0.0


def test_canonical_census_is_all_or_nothing_and_never_returns_partial_metrics():
    candidate, reduction, stream, entry = _candidate_census_fixture(
        nonterminal_timeout_count=2
    )
    receipt = candidate.decision_receipt
    projection = reduction.projection
    manifest = CensusManifest(
        "manifest", CensusMode.V2_CANONICAL, "head", "config", (entry,)
    )
    active_row = projection.c_active_base[0]
    active = ActiveOccurrenceMaterialization(
        active_row.result_occurrence_id,
        active_row.occurrence_id,
        active_row.cause_id,
        RecoveryAddressability.REQUIREMENT_REQUIRED,
    )
    valid = compute_canonical_census(
        manifest, (candidate,), (projection,), (stream,),
        coverage_inputs=CoverageInputs((active,)),
    )
    assert valid.status == CensusStatus.VALID
    assert valid.authoritative is True
    assert valid.canonical_metrics["active_blocker_occurrences"] == 1
    assert valid.canonical_metrics["final_unknown_results"] == 1
    assert valid.canonical_metrics["final_timeout_results"] == 0
    assert valid.canonical_metrics["terminal_timeout_events"] == 0
    assert valid.canonical_metrics["unique_open_requirements"] == 3
    assert valid.canonical_metrics["observed_nonterminal_timeout_events"] == 2
    assert valid.canonical_metrics["final_blocker_authority_coverage"] == 1.0
    invalid = compute_canonical_census(
        manifest, (candidate,), (), (stream,),
        coverage_inputs=CoverageInputs(()),
    )
    assert invalid.status == CensusStatus.INVALID
    assert invalid.authoritative is False
    assert invalid.canonical_metrics is None


def test_census_rejects_timeout_stream_mismatch_and_missing_required_materialization():
    candidate, reduction, stream, entry = _candidate_census_fixture()
    receipt = candidate.decision_receipt
    projection = reduction.projection
    manifest = CensusManifest(
        "manifest", CensusMode.V2_CANONICAL, "head", "config", (entry,)
    )
    active_row = projection.c_active_base[0]
    active = ActiveOccurrenceMaterialization(
        active_row.result_occurrence_id,
        active_row.occurrence_id,
        active_row.cause_id,
        RecoveryAddressability.REQUIREMENT_REQUIRED,
    )
    timeout_candidate, timeout_reduction, timeout_stream, _ = (
        _candidate_census_fixture(Outcome.TIMEOUT)
    )
    mismatched_stream = compute_canonical_census(
        manifest, (candidate,), (projection,), (timeout_stream,),
        coverage_inputs=CoverageInputs((active,)),
    )
    assert mismatched_stream.status == CensusStatus.INVALID
    missing_projection = VerifiedLifecycleProjection.seal(
        result_occurrence_id="result-1", snapshot_digest="snapshot",
        c_active_base=(_active(),), q_open_base=(),
        blocker_eligibility_base=(_eligible(),), satisfaction_projection={},
    )
    missing_receipt = finalize_decision(FinalizationAuthority("result-1", missing_projection))
    missing_manifest = CensusManifest(
        "missing", CensusMode.V2_CANONICAL, "head", "config",
        (_entry(missing_receipt),),
    )
    missing = compute_canonical_census(
        missing_manifest, (candidate,), (missing_projection,), (stream,),
        coverage_inputs=CoverageInputs((active,)),
    )
    assert missing.status == CensusStatus.INVALID


def test_factory_owned_expression_and_bound_contract_cannot_be_forged_directly():
    with pytest.raises(ValueError, match="typed factories"):
        SatisfactionExpression(ExpressionKind.REQUIREMENT_SLOT, slot_name="A")
    definition, bound = _contract()
    with pytest.raises(ValueError, match="registry-factory"):
        BoundSatisfactionContract(
            bound.contract_definition_id, bound.contract_version,
            bound.normalized_expression_digest, bound.slot_bindings,
            bound.bound_expression_digest,
        )
    bound.validate_against(definition)


def test_projection_rejects_duplicate_and_conflicting_relation_keys():
    with pytest.raises(ValueError, match="duplicate active-cause relation key"):
        VerifiedLifecycleProjection.seal(
            result_occurrence_id="result-1", snapshot_digest="snapshot",
            c_active_base=(
                _active(), replace(_active(), decision_effect="blocks_decision")
            ),
            q_open_base=(), blocker_eligibility_base=(_eligible(),),
            satisfaction_projection={},
        )
    with pytest.raises(ValueError, match="duplicate open-requirement relation key"):
        VerifiedLifecycleProjection.seal(
            result_occurrence_id="result-1", snapshot_digest="snapshot",
            c_active_base=(_active(),),
            q_open_base=(_open(), replace(_open(), proof_kind="other")),
            blocker_eligibility_base=(_eligible(),), satisfaction_projection={},
        )
    with pytest.raises(ValueError, match="duplicate blocker-eligibility relation key"):
        VerifiedLifecycleProjection.seal(
            result_occurrence_id="result-1", snapshot_digest="snapshot",
            c_active_base=(), q_open_base=(),
            blocker_eligibility_base=(
                BlockerEligibilityBaseRow("result-1", "same", None),
                BlockerEligibilityBaseRow("result-1", "same", "typed"),
            ),
            satisfaction_projection={},
        )


def test_typed_cause_coverage_zero_denominator_is_na_in_canonical_census():
    candidate, reduction, stream, entry = _candidate_census_fixture(Outcome.ERROR)
    manifest = CensusManifest(
        "coverage", CensusMode.V2_CANONICAL, "head", "config", (entry,)
    )
    result = compute_canonical_census(
        manifest, (candidate,), (reduction.projection,), (stream,),
        coverage_inputs=CoverageInputs(()),
    )
    assert result.status == CensusStatus.VALID
    assert result.canonical_metrics["v2_native_typed_cause_coverage"] is None


def test_function_identity_freeze_converts_boxed_integer_to_builtin_int():
    class BoxedInt(int):
        pass

    frozen = PairwiseStrategy._identity_freeze(BoxedInt(7))
    assert frozen == 7
    assert type(frozen) is int

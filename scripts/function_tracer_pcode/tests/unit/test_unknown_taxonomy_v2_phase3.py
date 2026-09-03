# -*- coding: utf-8 -*-

from dataclasses import replace
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.authority.contracts import (
    CauseOccurrence,
    CauseOccurrenceAuthority,
    CauseTransformationEvent,
    CauseTransformationProofReceipt,
    IdentityScope,
    ProofRequirement,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementCompletionReceipt,
    RequirementSlotDefinition,
    SatisfactionContractDefinition,
    TransformationKind,
    all_of,
    any_of,
    requirement_slot,
)
from scripts.function_tracer_pcode.authority.lifecycle.frontier import FrontierEvaluationBudget
from scripts.function_tracer_pcode.authority.lifecycle.reducer import (
    ShadowEvidenceIncomplete,
    ShadowLifecycleReducer,
)
from scripts.function_tracer_pcode.authority.registry import (
    SatisfactionBindingFactory,
    SealedReasonRegistry,
    SealedRecoveryRegistry,
    SemanticCauseIdentityFactory,
)
from scripts.function_tracer_pcode.authority.lifecycle.stream import (
    CauseObservedEventAuthority,
    CauseTransformedEventAuthority,
    EventIntent,
    EventRecorder,
    EventType,
    RequirementCompletedEventAuthority,
    ProcessExecutionEventAuthority,
    SealedEventStream,
    SolverExecutionEventAuthority,
)


def _required_reason():
    return ReasonDefinition(
        "return_width_bridge_missing", "return_observation", "proof_obligation",
        "blocks_equivalence", frozenset(("relational_return",)),
        ("left_width", "right_width"),
        frozenset(("bridge", "canonical", "safety")), False,
        "return-width-v1", RecoveryAddressability.REQUIREMENT_REQUIRED,
    )


def _no_proof_reason():
    return ReasonDefinition(
        "unsupported_semantics", "semantic_support", "coverage_gap",
        "blocks_equivalence", frozenset(("semantic_node",)),
        ("opcode",), frozenset(), False, "semantic-node-v1",
        RecoveryAddressability.NO_PROOF_RECOVERY,
    )


def _contract():
    return SatisfactionContractDefinition(
        "return-width-recovery", 1,
        (
            RequirementSlotDefinition("A", frozenset(("bridge",))),
            RequirementSlotDefinition("B", frozenset(("canonical",))),
            RequirementSlotDefinition("C", frozenset(("safety",))),
        ),
        all_of(
            any_of(requirement_slot("A"), requirement_slot("B")),
            requirement_slot("C"),
        ),
    )


def _environment(*, budget=None):
    reasons = SealedReasonRegistry.build((_required_reason(), _no_proof_reason()))
    recovery = SealedRecoveryRegistry.build((_contract(),))
    reducer = ShadowLifecycleReducer(
        reason_registry=reasons, recovery_registry=recovery,
        frontier_budget=budget or FrontierEvaluationBudget(),
    )
    return reasons, recovery, reducer


def _authority(
    occurrence_id="occ-1", *, no_proof=False, requirement_prefix="req",
):
    reasons, recovery, _ = _environment()
    definition = _no_proof_reason() if no_proof else _required_reason()
    reason_id = definition.reason_id
    target_kind = "semantic_node" if no_proof else "relational_return"
    cause = SemanticCauseIdentityFactory(reasons).create(
        reason_id=reason_id,
        identity_scope=IdentityScope.UNARY if no_proof else IdentityScope.RELATIONAL,
        target_kind=target_kind,
        canonical_target_key=("target", requirement_prefix),
        missing_semantic_fact=("missing", reason_id),
        semantic_proposition=("proposition", reason_id),
        observation_surface=(target_kind,),
        active_semantic_precondition=("reachable", True),
        correspondence_contract=("identity",),
    )
    if no_proof:
        occurrence = CauseOccurrence(
            occurrence_id, cause, reason_id, "target", target_kind,
            IdentityScope.UNARY, None, None, None, None, (), ("evidence",),
            "typed", "snapshot", "producer", "attempt",
        )
        return CauseOccurrenceAuthority(occurrence, None)
    contract = _contract()
    requirements = {
        "A": ProofRequirement(f"{requirement_prefix}-A", "bridge", ("A",)),
        "B": ProofRequirement(f"{requirement_prefix}-B", "canonical", ("B",)),
        "C": ProofRequirement(f"{requirement_prefix}-C", "safety", ("C",)),
    }
    bound = SatisfactionBindingFactory(recovery).bind(
        contract_definition_id=contract.contract_definition_id,
        contract_version=contract.contract_version,
        bindings=requirements,
    )
    occurrence = CauseOccurrence(
        occurrence_id, cause, reason_id, "target", target_kind,
        IdentityScope.RELATIONAL, contract.contract_definition_id,
        contract.contract_version, contract.normalized_expression_digest,
        bound.bound_expression_digest, tuple(sorted(bound.requirement_ids())),
        ("evidence",), "typed", "snapshot", "producer", "attempt",
    )
    return CauseOccurrenceAuthority(occurrence, bound)


def _completion(authority, requirement_id):
    bound = authority.bound_contract
    return RequirementCompletionReceipt(
        authority.occurrence.cause_id.value,
        authority.occurrence.occurrence_id,
        requirement_id,
        bound.contract_definition_id,
        bound.contract_version,
        bound.bound_expression_digest,
        f"proof-{requirement_id}",
        f"applicability-{requirement_id}",
    )


def _stream(*intents):
    recorder = EventRecorder(
        stream_id="stream", result_occurrence_id="result-1",
        source_snapshot_fingerprint="snapshot",
    )
    for intent in intents:
        recorder.append(intent)
    return recorder.seal()


def test_replay_partial_completion_uses_live_frontier_and_one_cause_row():
    _, _, reducer = _environment()
    authority = _authority()
    stream = _stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
        EventIntent(
            EventType.REQUIREMENT_COMPLETED,
            RequirementCompletedEventAuthority(_completion(authority, "req-A")),
        ),
    )
    result = reducer.replay(stream)
    assert len(result.projection.c_active_base) == 1
    assert {row.proof_requirement_id for row in result.projection.q_open_base} == {"req-C"}
    assert result.snapshot.active_occurrence_ids == ("occ-1",)
    shuffled = SealedEventStream(stream.envelope, tuple(reversed(stream.events)))
    replayed = reducer.replay(shuffled)
    assert replayed.projection == result.projection
    before = reducer.replay(_stream(EventIntent(
        EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)
    )))
    assert len(before.projection.c_active_base) == 1
    assert {row.proof_requirement_id for row in before.projection.q_open_base} == {
        "req-A", "req-B", "req-C",
    }


def test_satisfied_occurrence_leaves_no_active_cause_or_open_requirement():
    _, _, reducer = _environment()
    authority = _authority()
    result = reducer.replay(_stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
        EventIntent(EventType.REQUIREMENT_COMPLETED, RequirementCompletedEventAuthority(_completion(authority, "req-A"))),
        EventIntent(EventType.REQUIREMENT_COMPLETED, RequirementCompletedEventAuthority(_completion(authority, "req-C"))),
    ))
    assert result.projection.c_active_base == ()
    assert result.projection.q_open_base == ()
    assert result.snapshot.active_occurrence_ids == ()


def test_no_implicit_supersession_and_no_proof_causes_have_no_null_q_rows():
    _, _, reducer = _environment()
    first = _authority("unsupported-1", no_proof=True, requirement_prefix="same")
    second = _authority("unsupported-2", no_proof=True, requirement_prefix="same")
    result = reducer.replay(_stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(first)),
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(second)),
    ))
    assert len(result.projection.c_active_base) == 2
    assert len({row.cause_id for row in result.projection.c_active_base}) == 1
    assert result.projection.q_open_base == ()


def test_solver_timeout_requires_exactly_one_live_requirement():
    _, _, reducer = _environment()
    authority = _authority()
    valid = reducer.replay(_stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
        EventIntent(
            EventType.SOLVER_TIMEOUT,
            SolverExecutionEventAuthority("req-A", "solver", "TIMEOUT", 1000),
        ),
    ))
    assert len(valid.snapshot.execution_event_digests) == 1
    with pytest.raises(ShadowEvidenceIncomplete, match="not uniquely live"):
        reducer.replay(_stream(
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
            EventIntent(
                EventType.SOLVER_TIMEOUT,
                SolverExecutionEventAuthority("missing", "solver", "TIMEOUT", 1000),
            ),
        ))


def test_atomic_transformation_replaces_only_explicit_old_occurrence():
    _, _, reducer = _environment()
    old = _authority("old", requirement_prefix="old")
    new = _authority("new", requirement_prefix="new")
    event = CauseTransformationEvent(
        TransformationKind.REPLACEMENT, ("old",), ("new",),
        "transform", "stage", "snapshot",
    )
    proof = CauseTransformationProofReceipt(
        "transform", (("old", old.occurrence.cause_id.value),),
        (("new", new.occurrence.cause_id.value),), (), "snapshot", False,
    )
    result = reducer.replay(_stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(old)),
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(new)),
        EventIntent(EventType.CAUSE_TRANSFORMED, CauseTransformedEventAuthority(event, proof)),
    ))
    assert result.snapshot.active_occurrence_ids == ("new",)
    assert {row.occurrence_id for row in result.projection.c_active_base} == {"new"}


def test_n_to_m_transformation_checks_every_observed_cause_binding():
    _, _, reducer = _environment()
    olds = tuple(_authority(f"old-{index}", requirement_prefix=f"old-{index}") for index in range(2))
    news = tuple(_authority(f"new-{index}", requirement_prefix=f"new-{index}") for index in range(3))
    event = CauseTransformationEvent(
        TransformationKind.REFINEMENT,
        tuple(item.occurrence.occurrence_id for item in olds),
        tuple(item.occurrence.occurrence_id for item in news),
        "n-to-m", "stage", "snapshot",
    )
    proof = CauseTransformationProofReceipt(
        "n-to-m",
        tuple((item.occurrence.occurrence_id, item.occurrence.cause_id.value) for item in olds),
        tuple((item.occurrence.occurrence_id, item.occurrence.cause_id.value) for item in news),
        (), "snapshot", False,
    )
    intents = [
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(item))
        for item in (*olds, *news)
    ]
    intents.append(EventIntent(
        EventType.CAUSE_TRANSFORMED, CauseTransformedEventAuthority(event, proof)
    ))
    result = reducer.replay(_stream(*intents))
    assert set(result.snapshot.active_occurrence_ids) == {
        item.occurrence.occurrence_id for item in news
    }
    wrong = replace(
        proof,
        replaced_occurrence_bindings=(
            (olds[0].occurrence.occurrence_id, "WRONG-CAUSE"),
            proof.replaced_occurrence_bindings[1],
        ),
    )
    with pytest.raises(ShadowEvidenceIncomplete, match="old occurrence/cause"):
        reducer.replay(_stream(
            *intents[:-1],
            EventIntent(
                EventType.CAUSE_TRANSFORMED,
                CauseTransformedEventAuthority(event, wrong),
            ),
        ))


def test_exact_completion_transfer_success_and_fail_closed_variants():
    _, _, reducer = _environment()
    old = _authority("old", requirement_prefix="old")
    new = _authority("new", requirement_prefix="new")
    event = CauseTransformationEvent(
        TransformationKind.REPLACEMENT, ("old",), ("new",),
        "transfer", "stage", "snapshot",
    )

    def proof(mapping):
        return CauseTransformationProofReceipt(
            "transfer", (("old", old.occurrence.cause_id.value),),
            (("new", new.occurrence.cause_id.value),), mapping,
            "snapshot", True,
        )

    prefix = (
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(old)),
        EventIntent(
            EventType.REQUIREMENT_COMPLETED,
            RequirementCompletedEventAuthority(_completion(old, "old-A")),
        ),
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(new)),
    )
    success = reducer.replay(_stream(
        *prefix,
        EventIntent(
            EventType.CAUSE_TRANSFORMED,
            CauseTransformedEventAuthority(event, proof((("old-A", "new-A"),))),
        ),
    ))
    assert {row.proof_requirement_id for row in success.projection.q_open_base} == {"new-C"}
    with pytest.raises(ShadowEvidenceIncomplete, match="transfer is incomplete"):
        reducer.replay(_stream(
            *prefix,
            EventIntent(
                EventType.CAUSE_TRANSFORMED,
                CauseTransformedEventAuthority(event, proof((("old-B", "new-B"),))),
            ),
        ))
    with pytest.raises(ShadowEvidenceIncomplete, match="owner is not unique/declared"):
        reducer.replay(_stream(
            *prefix,
            EventIntent(
                EventType.CAUSE_TRANSFORMED,
                CauseTransformedEventAuthority(event, proof((("old-A", "missing"),))),
            ),
        ))
    with pytest.raises(ShadowEvidenceIncomplete, match="owner is not unique/declared"):
        reducer.replay(_stream(
            *prefix,
            EventIntent(
                EventType.CAUSE_TRANSFORMED,
                CauseTransformedEventAuthority(
                    event,
                    proof((
                        ("old-A", "new-A"),
                        ("UNDECLARED-OLD", "UNDECLARED-NEW"),
                    )),
                ),
            ),
        ))
    duplicate_target = _authority("new-2", requirement_prefix="new")
    ambiguous_event = CauseTransformationEvent(
        TransformationKind.REFINEMENT, ("old",), ("new", "new-2"),
        "transfer-ambiguous", "stage", "snapshot",
    )
    ambiguous_proof = CauseTransformationProofReceipt(
        "transfer-ambiguous", (("old", old.occurrence.cause_id.value),),
        (
            ("new", new.occurrence.cause_id.value),
            ("new-2", duplicate_target.occurrence.cause_id.value),
        ),
        (("old-A", "new-A"),), "snapshot", True,
    )
    with pytest.raises(ShadowEvidenceIncomplete, match="owner is not unique/declared"):
        reducer.replay(_stream(
            *prefix,
            EventIntent(
                EventType.CAUSE_OBSERVED,
                CauseObservedEventAuthority(duplicate_target),
            ),
            EventIntent(
                EventType.CAUSE_TRANSFORMED,
                CauseTransformedEventAuthority(ambiguous_event, ambiguous_proof),
            ),
        ))


def test_reducer_rejects_duplicate_observation_invalid_completion_and_stream_tamper():
    _, _, reducer = _environment()
    authority = _authority()
    with pytest.raises(ShadowEvidenceIncomplete, match="duplicate occurrence"):
        reducer.replay(_stream(
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
        ))
    with pytest.raises(ShadowEvidenceIncomplete, match="inactive/unknown"):
        reducer.replay(_stream(
            EventIntent(
                EventType.REQUIREMENT_COMPLETED,
                RequirementCompletedEventAuthority(_completion(authority, "req-A")),
            ),
        ))
    stream = _stream(EventIntent(
        EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)
    ))
    tampered = replace(
        stream,
        events=(replace(stream.events[0], authority_digest="forged"),),
    )
    with pytest.raises(ShadowEvidenceIncomplete, match="invalid sealed"):
        reducer.replay(tampered)
    mixed = replace(
        stream,
        events=(replace(
            stream.events[0],
            header=replace(stream.events[0].header, stream_id="other"),
        ),),
    )
    with pytest.raises(ShadowEvidenceIncomplete, match="invalid sealed"):
        reducer.replay(mixed)
    duplicated = replace(
        stream,
        events=(stream.events[0], stream.events[0]),
    )
    with pytest.raises(ShadowEvidenceIncomplete, match="invalid sealed"):
        reducer.replay(duplicated)
    two_event = _stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
        EventIntent(
            EventType.SOLVER_TIMEOUT,
            SolverExecutionEventAuthority("req-A", "solver", "TIMEOUT", 1000),
        ),
    )
    gap = replace(
        two_event,
        events=(
            two_event.events[0],
            replace(
                two_event.events[1],
                header=replace(two_event.events[1].header, sequence_number=3),
            ),
        ),
    )
    with pytest.raises(ShadowEvidenceIncomplete, match="invalid sealed"):
        reducer.replay(gap)


def test_transformation_rejects_unobserved_replacement_without_partial_result():
    _, _, reducer = _environment()
    old = _authority("old", requirement_prefix="old")
    new = _authority("new", requirement_prefix="new")
    event = CauseTransformationEvent(
        TransformationKind.REPLACEMENT, ("old",), ("new",),
        "transform", "stage", "snapshot",
    )
    proof = CauseTransformationProofReceipt(
        "transform", (("old", old.occurrence.cause_id.value),),
        (("new", new.occurrence.cause_id.value),), (), "snapshot", False,
    )
    with pytest.raises(ShadowEvidenceIncomplete, match="not observed first"):
        reducer.replay(_stream(
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(old)),
            EventIntent(
                EventType.CAUSE_TRANSFORMED,
                CauseTransformedEventAuthority(event, proof),
            ),
        ))


def test_frontier_budget_exhaustion_emits_no_partial_authority():
    _, _, reducer = _environment(budget=FrontierEvaluationBudget(
        max_expression_nodes=2, max_antichain_sets=100,
        max_requirement_ids=10, max_union_operations=100,
    ))
    authority = _authority()
    with pytest.raises(ShadowEvidenceIncomplete, match="budget exhausted"):
        reducer.replay(_stream(EventIntent(
            EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)
        )))


def test_process_event_also_requires_currently_live_requirement():
    _, _, reducer = _environment()
    authority = _authority()
    valid = reducer.replay(_stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
        EventIntent(
            EventType.PROCESS_TIMEOUT,
            ProcessExecutionEventAuthority("req-B", "process"),
        ),
    ))
    assert len(valid.snapshot.execution_event_digests) == 1
    with pytest.raises(ShadowEvidenceIncomplete, match="not uniquely live"):
        reducer.replay(_stream(
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
            EventIntent(
                EventType.PROCESS_TIMEOUT,
                ProcessExecutionEventAuthority("not-live", "process"),
            ),
        ))


def test_snapshot_and_projection_tamper_are_rejected_and_reducer_has_no_outcome_dependency():
    _, _, reducer = _environment()
    authority = _authority()
    result = reducer.replay(_stream(EventIntent(
        EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)
    )))
    with pytest.raises(ValueError, match="snapshot digest"):
        replace(result.snapshot, snapshot_digest="forged").validate()
    with pytest.raises(ValueError, match="projection"):
        replace(
            result.projection, lifecycle_projection_digest="forged"
        ).validate()
    source = Path(
        "scripts/function_tracer_pcode/authority/lifecycle/reducer.py"
    ).read_text(encoding="utf-8")
    for forbidden in (
        "from .decision", "from .census_contract", "from .legacy_codec",
        "DecisionReceipt", "C_active_by_outcome", "Q_open_by_outcome",
    ):
        assert forbidden not in source
    assert "final_outcome" not in result.projection.c_active_base[0].__dataclass_fields__
    assert "final_outcome" not in result.projection.q_open_base[0].__dataclass_fields__

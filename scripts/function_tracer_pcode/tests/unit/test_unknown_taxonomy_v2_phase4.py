# -*- coding: utf-8 -*-

from dataclasses import replace
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.v2.candidate import (
    CandidateDecisionProjection,
    build_candidate_projection,
)
from scripts.function_tracer_pcode.equivalence.v2.census_contract import (
    ActiveOccurrenceMaterialization,
    CensusEntry,
    CensusManifest,
    CensusMode,
    CensusStatus,
    CoverageInputs,
)
from scripts.function_tracer_pcode.equivalence.v2.contracts import (
    Outcome,
    RecoveryAddressability,
    ResultKind,
    authority_digest,
)
from scripts.function_tracer_pcode.equivalence.v2.decision import (
    DecisiveProofKind,
    DecisiveProofReceipt,
    ErrorReceipt,
    TerminalTimeoutReceipt,
)
from scripts.function_tracer_pcode.equivalence.v2.shadow_compare import (
    LegacyExpectedProjection,
    ShadowComparisonKind,
    build_shadow_census_preview,
    compare_shadow,
)
from scripts.function_tracer_pcode.equivalence.v2.stream import (
    CauseObservedEventAuthority,
    DecisiveProofEventAuthority,
    ErrorEventAuthority,
    EventIntent,
    EventType,
    SolverExecutionEventAuthority,
    EventRecorder,
)
from scripts.function_tracer_pcode.tests.unit.test_unknown_taxonomy_v2_phase3 import (
    _authority,
    _environment,
    _stream,
)


def _reducer():
    return _environment()[2]


def _stream_for(result_occurrence_id, *intents):
    recorder = EventRecorder(
        stream_id=f"stream-{result_occurrence_id}",
        result_occurrence_id=result_occurrence_id,
        source_snapshot_fingerprint="snapshot",
    )
    for intent in intents:
        recorder.append(intent)
    return recorder.seal()


def _candidate(outcome, *, nonterminal_timeout_count=0, include_stream=False):
    reducer = _reducer()
    def pack(candidate, reduction, stream):
        if include_stream:
            return candidate, reduction, stream
        return candidate, reduction

    if outcome == Outcome.EQUIVALENT:
        artifact = "eq-proof"
        stream = _stream(EventIntent(
            EventType.EQ_CLOSURE, DecisiveProofEventAuthority(artifact)
        ))
        reduction = reducer.replay(stream)
        receipt = DecisiveProofReceipt.create(
            result_occurrence_id="result-1",
            lifecycle_projection_digest=reduction.projection.lifecycle_projection_digest,
            proof_kind=DecisiveProofKind.EQ_CLOSURE,
            proof_artifact_digest=artifact,
        )
        return pack(build_candidate_projection(
            reduction, decisive_proof_receipts=(receipt,)
        ), reduction, stream)
    if outcome == Outcome.NOT_EQ:
        artifact = "counterexample"
        stream = _stream(EventIntent(
            EventType.COUNTEREXAMPLE, DecisiveProofEventAuthority(artifact)
        ))
        reduction = reducer.replay(stream)
        receipt = DecisiveProofReceipt.create(
            result_occurrence_id="result-1",
            lifecycle_projection_digest=reduction.projection.lifecycle_projection_digest,
            proof_kind=DecisiveProofKind.SAFE_COUNTEREXAMPLE,
            proof_artifact_digest=artifact,
        )
        return pack(build_candidate_projection(
            reduction, decisive_proof_receipts=(receipt,)
        ), reduction, stream)
    if outcome == Outcome.UNKNOWN:
        authority = _authority()
        intents = [EventIntent(
            EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)
        )]
        intents.extend(
            EventIntent(
                EventType.SOLVER_TIMEOUT,
                SolverExecutionEventAuthority(
                    "req-A", f"solver-{index}", "TIMEOUT", 1000
                ),
            )
            for index in range(nonterminal_timeout_count)
        )
        stream = _stream(*intents)
        reduction = reducer.replay(stream)
        return pack(build_candidate_projection(reduction), reduction, stream)
    if outcome == Outcome.TIMEOUT:
        authority = _authority()
        stream = _stream(
            EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
            EventIntent(
                EventType.SOLVER_TIMEOUT,
                SolverExecutionEventAuthority("req-A", "solver", "TIMEOUT", 1000),
            ),
        )
        reduction = reducer.replay(stream)
        receipt = TerminalTimeoutReceipt.create(
            result_occurrence_id="result-1",
            lifecycle_projection_digest=reduction.projection.lifecycle_projection_digest,
            proof_requirement_id="req-A",
            execution_event_digest=reduction.snapshot.terminal_timeout_event_digests[0],
        )
        return pack(build_candidate_projection(
            reduction, terminal_timeout_receipts=(receipt,)
        ), reduction, stream)
    artifact = "error-artifact"
    stream = _stream(EventIntent(
        EventType.ERROR, ErrorEventAuthority("internal", artifact)
    ))
    reduction = reducer.replay(stream)
    receipt = ErrorReceipt.create(
        result_occurrence_id="result-1",
        lifecycle_projection_digest=reduction.projection.lifecycle_projection_digest,
        error_kind="internal",
        error_artifact_digest=artifact,
    )
    return pack(
        build_candidate_projection(reduction, error_receipts=(receipt,)),
        reduction,
        stream,
    )


def _legacy(candidate, **changes):
    values = {
        "outcome": candidate.decision_receipt.outcome,
        "decisive_proof_receipt_digests": candidate.decisive_proof_receipt_digests,
        "decisive_proof_artifact_digests": candidate.decisive_proof_artifact_digests,
        "active_cause_ids": candidate.active_cause_ids,
        "proof_backlog_keys": candidate.proof_backlog_keys,
        "terminal_execution_event_digests": candidate.terminal_execution_event_digests,
        "retry_fallback_projection": candidate.retry_fallback_projection,
        "cli_batch_projection": candidate.cli_batch_projection,
    }
    values.update(changes)
    return LegacyExpectedProjection(**values)


def _forge_candidate_timeout_projection(candidate, *, observed, terminal):
    forged = object.__new__(CandidateDecisionProjection)
    for name in CandidateDecisionProjection.__dataclass_fields__:
        object.__setattr__(forged, name, getattr(candidate, name))
    object.__setattr__(forged, "observed_timeout_event_digests", tuple(observed))
    object.__setattr__(forged, "terminal_execution_event_digests", tuple(terminal))
    values = {
        "decision_receipt_digest": forged.decision_receipt.receipt_digest,
        "decisive_proof_receipt_digests": forged.decisive_proof_receipt_digests,
        "decisive_proof_artifact_digests": forged.decisive_proof_artifact_digests,
        "active_cause_ids": forged.active_cause_ids,
        "proof_backlog_keys": forged.proof_backlog_keys,
        "event_stream_authority_digest": forged.event_stream_authority_digest,
        "lifecycle_snapshot_digest": forged.lifecycle_snapshot_digest,
        "observed_timeout_event_digests": forged.observed_timeout_event_digests,
        "terminal_execution_event_digests": forged.terminal_execution_event_digests,
        "retry_fallback_projection": forged.retry_fallback_projection,
        "cli_batch_projection": forged.cli_batch_projection,
    }
    object.__setattr__(forged, "projection_digest", authority_digest(values))
    forged.validate()
    return forged


@pytest.mark.parametrize("outcome", tuple(Outcome))
def test_candidate_five_value_decision_is_derived_without_legacy(outcome):
    candidate, _ = _candidate(outcome)
    assert candidate.decision_receipt.outcome == outcome
    assert compare_shadow(_legacy(candidate), candidate) == ShadowComparisonKind.MATCH


def test_candidate_rejects_unrecorded_decisive_timeout_and_error_authority_as_error():
    candidate, reduction = _candidate(Outcome.UNKNOWN)
    forged = DecisiveProofReceipt.create(
        result_occurrence_id="result-1",
        lifecycle_projection_digest=reduction.projection.lifecycle_projection_digest,
        proof_kind=DecisiveProofKind.EQ_CLOSURE,
        proof_artifact_digest="not-in-stream",
    )
    result = build_candidate_projection(
        reduction, decisive_proof_receipts=(forged,)
    )
    assert result.decision_receipt.outcome == Outcome.ERROR
    assert result.decision_receipt.outcome != Outcome.UNKNOWN
    _, eq_reduction = _candidate(Outcome.EQUIVALENT)
    wrong_kind = DecisiveProofReceipt.create(
        result_occurrence_id="result-1",
        lifecycle_projection_digest=eq_reduction.projection.lifecycle_projection_digest,
        proof_kind=DecisiveProofKind.SAFE_COUNTEREXAMPLE,
        proof_artifact_digest="eq-proof",
    )
    assert build_candidate_projection(
        eq_reduction, decisive_proof_receipts=(wrong_kind,)
    ).decision_receipt.outcome == Outcome.ERROR
    _, timeout_reduction = _candidate(Outcome.TIMEOUT)
    wrong_requirement = TerminalTimeoutReceipt.create(
        result_occurrence_id="result-1",
        lifecycle_projection_digest=timeout_reduction.projection.lifecycle_projection_digest,
        proof_requirement_id="req-B",
        execution_event_digest=timeout_reduction.snapshot.terminal_timeout_event_digests[0],
    )
    assert build_candidate_projection(
        timeout_reduction, terminal_timeout_receipts=(wrong_requirement,)
    ).decision_receipt.outcome == Outcome.ERROR
    _, error_reduction = _candidate(Outcome.ERROR)
    wrong_error_kind = ErrorReceipt.create(
        result_occurrence_id="result-1",
        lifecycle_projection_digest=error_reduction.projection.lifecycle_projection_digest,
        error_kind="different",
        error_artifact_digest="error-artifact",
    )
    assert build_candidate_projection(
        error_reduction, error_receipts=(wrong_error_kind,)
    ).decision_receipt.outcome == Outcome.ERROR


def test_conflicting_recorded_decisive_authority_is_error_not_unknown():
    reducer = _reducer()
    reduction = reducer.replay(_stream(
        EventIntent(
            EventType.EQ_CLOSURE,
            DecisiveProofEventAuthority("eq-proof"),
        ),
        EventIntent(
            EventType.COUNTEREXAMPLE,
            DecisiveProofEventAuthority("counterexample"),
        ),
    ))
    receipts = (
        DecisiveProofReceipt.create(
            result_occurrence_id="result-1",
            lifecycle_projection_digest=reduction.projection.lifecycle_projection_digest,
            proof_kind=DecisiveProofKind.EQ_CLOSURE,
            proof_artifact_digest="eq-proof",
        ),
        DecisiveProofReceipt.create(
            result_occurrence_id="result-1",
            lifecycle_projection_digest=reduction.projection.lifecycle_projection_digest,
            proof_kind=DecisiveProofKind.SAFE_COUNTEREXAMPLE,
            proof_artifact_digest="counterexample",
        ),
    )
    candidate = build_candidate_projection(
        reduction, decisive_proof_receipts=receipts
    )
    assert candidate.decision_receipt.outcome == Outcome.ERROR
    assert candidate.decision_receipt.outcome != Outcome.UNKNOWN


def test_stream_decisive_and_error_authority_cannot_be_hidden_by_omitting_receipts():
    reducer = _reducer()
    authority = _authority()
    conflict_with_cause = reducer.replay(_stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
        EventIntent(EventType.EQ_CLOSURE, DecisiveProofEventAuthority("eq-proof")),
        EventIntent(
            EventType.COUNTEREXAMPLE,
            DecisiveProofEventAuthority("counterexample"),
        ),
    ))
    no_receipts = build_candidate_projection(conflict_with_cause)
    assert no_receipts.decision_receipt.outcome == Outcome.ERROR
    assert no_receipts.decision_receipt.outcome != Outcome.UNKNOWN

    conflict = reducer.replay(_stream(
        EventIntent(EventType.EQ_CLOSURE, DecisiveProofEventAuthority("eq-proof")),
        EventIntent(
            EventType.COUNTEREXAMPLE,
            DecisiveProofEventAuthority("counterexample"),
        ),
    ))
    eq_only = DecisiveProofReceipt.create(
        result_occurrence_id="result-1",
        lifecycle_projection_digest=conflict.projection.lifecycle_projection_digest,
        proof_kind=DecisiveProofKind.EQ_CLOSURE,
        proof_artifact_digest="eq-proof",
    )
    partial_receipts = build_candidate_projection(
        conflict, decisive_proof_receipts=(eq_only,)
    )
    assert partial_receipts.decision_receipt.outcome == Outcome.ERROR
    assert partial_receipts.decision_receipt.outcome != Outcome.EQUIVALENT

    error_with_cause = reducer.replay(_stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(authority)),
        EventIntent(
            EventType.ERROR,
            ErrorEventAuthority("internal", "error-artifact"),
        ),
    ))
    hidden_error = build_candidate_projection(error_with_cause)
    assert hidden_error.decision_receipt.outcome == Outcome.ERROR
    assert hidden_error.decision_receipt.outcome != Outcome.UNKNOWN


def test_active_semantic_cause_projection_is_a_set_not_occurrence_multiset():
    first = _authority("unsupported-1", no_proof=True, requirement_prefix="same")
    second = _authority("unsupported-2", no_proof=True, requirement_prefix="same")
    reduction = _reducer().replay(_stream(
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(first)),
        EventIntent(EventType.CAUSE_OBSERVED, CauseObservedEventAuthority(second)),
    ))
    assert len(reduction.projection.c_active_base) == 2
    candidate = build_candidate_projection(reduction)
    assert candidate.active_cause_ids == (
        first.occurrence.cause_id.value,
    )


def test_candidate_projection_cannot_be_forged_outside_builder():
    candidate, _ = _candidate(Outcome.UNKNOWN)
    with pytest.raises(ValueError, match="issued only"):
        CandidateDecisionProjection(
            candidate.decision_receipt,
            candidate.decisive_proof_receipt_digests,
            candidate.decisive_proof_artifact_digests,
            candidate.active_cause_ids,
            candidate.proof_backlog_keys,
            candidate.event_stream_authority_digest,
            candidate.lifecycle_snapshot_digest,
            candidate.observed_timeout_event_digests,
            candidate.terminal_execution_event_digests,
            candidate.retry_fallback_projection,
            candidate.cli_batch_projection,
            candidate.projection_digest,
        )


@pytest.mark.parametrize(
    ("changes", "expected"),
    (
        ({"outcome": Outcome.ERROR}, ShadowComparisonKind.MISMATCH_DECISION_AUTHORITY),
        ({"decisive_proof_receipt_digests": ("different",)}, ShadowComparisonKind.MISMATCH_DECISION_AUTHORITY),
        ({"active_cause_ids": ("different",)}, ShadowComparisonKind.MISMATCH_LIFECYCLE),
        ({"proof_backlog_keys": (("contract", 2, "req"),)}, ShadowComparisonKind.MISMATCH_LIFECYCLE),
        ({"terminal_execution_event_digests": ("different",)}, ShadowComparisonKind.MISMATCH_EXECUTION_EVENT),
        ({"retry_fallback_projection": ("different",)}, ShadowComparisonKind.MISMATCH_FALLBACK_POLICY),
        ({"cli_batch_projection": ("different",)}, ShadowComparisonKind.MISMATCH_DECISION_AUTHORITY),
        ({"ambiguity": True}, ShadowComparisonKind.MISMATCH_LEGACY_AMBIGUITY),
    ),
)
def test_shadow_comparison_classifies_every_authority_difference(changes, expected):
    candidate, _ = _candidate(Outcome.UNKNOWN)
    assert compare_shadow(_legacy(candidate, **changes), candidate) == expected
    assert compare_shadow(_legacy(candidate), None) == ShadowComparisonKind.SHADOW_EVIDENCE_INCOMPLETE
    assert compare_shadow(
        _legacy(candidate), candidate, evidence_incomplete=True
    ) == ShadowComparisonKind.SHADOW_EVIDENCE_INCOMPLETE


def test_shadow_census_join_is_post_receipt_and_all_or_nothing():
    candidate, reduction, stream = _candidate(
        Outcome.UNKNOWN, include_stream=True
    )
    entry = CensusEntry(
        "result-1", ResultKind.V2_NATIVE, ("domain",), ("left", "right"),
        ("f", "f"), reduction.snapshot.event_stream_authority_digest,
        reduction.projection.lifecycle_projection_digest,
        candidate.decision_receipt.receipt_digest, "artifact",
    )
    manifest = CensusManifest(
        "manifest", CensusMode.V2_CANONICAL, "head", "config", (entry,)
    )
    row = reduction.projection.c_active_base[0]
    coverage = CoverageInputs((ActiveOccurrenceMaterialization(
        row.result_occurrence_id, row.occurrence_id, row.cause_id,
        RecoveryAddressability.REQUIREMENT_REQUIRED,
    ),))
    valid = build_shadow_census_preview(
        manifest, (candidate,), (reduction.projection,), (stream,),
        coverage_inputs=coverage,
    )
    assert valid.status == CensusStatus.VALID
    assert valid.canonical_metrics["affected_unknown_results_by_reason"] == {
        "return_width_bridge_missing": 1
    }
    forged_nonterminal = _forge_candidate_timeout_projection(
        candidate,
        observed=("caller-supplied-timeout",),
        terminal=(),
    )
    forged_nonterminal_result = build_shadow_census_preview(
        manifest,
        (forged_nonterminal,),
        (reduction.projection,),
        (stream,),
        coverage_inputs=coverage,
    )
    assert forged_nonterminal_result.status == CensusStatus.INVALID
    assert forged_nonterminal_result.canonical_metrics is None

    timeout_candidate, timeout_reduction, timeout_stream = _candidate(
        Outcome.TIMEOUT, include_stream=True
    )
    timeout_entry = replace(
        entry,
        event_stream_authority_digest=(
            timeout_reduction.snapshot.event_stream_authority_digest
        ),
        lifecycle_projection_digest=(
            timeout_reduction.projection.lifecycle_projection_digest
        ),
        decision_receipt_digest=(
            timeout_candidate.decision_receipt.receipt_digest
        ),
    )
    timeout_manifest = CensusManifest(
        "timeout-manifest", CensusMode.V2_CANONICAL, "head", "config",
        (timeout_entry,),
    )
    timeout_row = timeout_reduction.projection.c_active_base[0]
    timeout_coverage = CoverageInputs((ActiveOccurrenceMaterialization(
        timeout_row.result_occurrence_id,
        timeout_row.occurrence_id,
        timeout_row.cause_id,
        RecoveryAddressability.REQUIREMENT_REQUIRED,
    ),))
    forged_terminal = _forge_candidate_timeout_projection(
        timeout_candidate,
        observed=("caller-supplied-terminal",),
        terminal=("caller-supplied-terminal",),
    )
    forged_terminal_result = build_shadow_census_preview(
        timeout_manifest,
        (forged_terminal,),
        (timeout_reduction.projection,),
        (timeout_stream,),
        coverage_inputs=timeout_coverage,
    )
    assert forged_terminal_result.status == CensusStatus.INVALID
    assert forged_terminal_result.canonical_metrics is None
    missing = build_shadow_census_preview(
        manifest, (), (reduction.projection,), (stream,),
        coverage_inputs=coverage,
    )
    assert missing.status == CensusStatus.INVALID
    wrong_manifest = CensusManifest(
        "wrong", CensusMode.V2_CANONICAL, "head", "config",
        (replace(entry, decision_receipt_digest="wrong"),),
    )
    mismatched = build_shadow_census_preview(
        wrong_manifest, (candidate,), (reduction.projection,), (stream,),
        coverage_inputs=coverage,
    )
    assert mismatched.status == CensusStatus.INVALID

    duplicate_decision = build_shadow_census_preview(
        manifest, (candidate, candidate), (reduction.projection,), (stream,),
        coverage_inputs=coverage,
    )
    assert duplicate_decision.status == CensusStatus.INVALID
    assert duplicate_decision.canonical_metrics is None

    duplicate_projection = build_shadow_census_preview(
        manifest, (candidate,), (reduction.projection, reduction.projection), (stream,),
        coverage_inputs=coverage,
    )
    assert duplicate_projection.status == CensusStatus.INVALID
    assert duplicate_projection.canonical_metrics is None

    orphan_reduction = _reducer().replay(_stream_for(
        "result-2",
        EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(_authority()),
        ),
    ))
    orphan_candidate = build_candidate_projection(orphan_reduction)
    orphan_stream = _stream_for(
        "result-2",
        EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(_authority()),
        ),
    )
    orphan_decision = build_shadow_census_preview(
        manifest, (candidate, orphan_candidate), (reduction.projection,),
        (stream, orphan_stream),
        coverage_inputs=coverage,
    )
    assert orphan_decision.status == CensusStatus.INVALID
    assert orphan_decision.canonical_metrics is None
    orphan_projection = build_shadow_census_preview(
        manifest, (candidate,), (reduction.projection, orphan_reduction.projection),
        (stream, orphan_stream),
        coverage_inputs=coverage,
    )
    assert orphan_projection.status == CensusStatus.INVALID
    assert orphan_projection.canonical_metrics is None


def test_candidate_module_has_no_legacy_or_census_dependency():
    source = Path(
        "scripts/function_tracer_pcode/equivalence/v2/candidate.py"
    ).read_text(encoding="utf-8")
    for forbidden in (
        "LegacyExpectedProjection", "from .shadow_compare",
        "from .legacy_codec", "from .census_contract", "C_active_by_outcome",
    ):
        assert forbidden not in source

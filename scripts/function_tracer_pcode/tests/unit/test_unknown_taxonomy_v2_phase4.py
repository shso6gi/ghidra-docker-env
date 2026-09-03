# -*- coding: utf-8 -*-

from dataclasses import replace
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.authority.decision.candidate import (
    CandidateDecisionProjection,
    build_candidate_projection,
)
from scripts.function_tracer_pcode.authority.census_contract import (
    ActiveOccurrenceMaterialization,
    CensusEntry,
    CensusManifest,
    CensusMode,
    CensusStatus,
    CoverageInputs,
)
from scripts.function_tracer_pcode.authority.contracts import (
    Outcome,
    RecoveryAddressability,
    ResultKind,
    authority_digest,
)
from scripts.function_tracer_pcode.authority.decision.decision import (
    DecisiveProofKind,
    DecisiveProofReceipt,
    ErrorReceipt,
    TerminalTimeoutReceipt,
)
from scripts.function_tracer_pcode.authority.decision.shadow_compare import (
    LegacyExpectedProjection,
    ShadowComparisonKind,
)
from scripts.function_tracer_pcode.authority.lifecycle.stream import (
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


def test_candidate_module_has_no_legacy_or_census_dependency():
    source = Path(
        "scripts/function_tracer_pcode/authority/decision/candidate.py"
    ).read_text(encoding="utf-8")
    for forbidden in (
        "LegacyExpectedProjection", "from .shadow_compare",
        "from .legacy_codec", "from .census_contract", "C_active_by_outcome",
    ):
        assert forbidden not in source

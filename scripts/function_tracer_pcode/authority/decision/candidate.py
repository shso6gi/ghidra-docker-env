"""Legacy-blind candidate decision projection over verified v2 authority."""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from typing import Any, Sequence, Tuple

from scripts.function_tracer_pcode.authority.contracts import authority_digest, canonical_value
from scripts.function_tracer_pcode.authority.decision.decision import (
    DecisiveProofKind,
    DecisiveProofReceipt,
    DecisionReceipt,
    ErrorReceipt,
    FinalizationAuthority,
    TerminalTimeoutReceipt,
    finalize_decision,
)
from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowReductionResult


_CANDIDATE_PROJECTION_FACTORY_TOKEN = object()


@dataclass(frozen=True, init=False)
class CandidateDecisionProjection:
    decision_receipt: DecisionReceipt
    decisive_proof_receipt_digests: Tuple[str, ...]
    decisive_proof_artifact_digests: Tuple[str, ...]
    active_cause_ids: Tuple[str, ...]
    proof_backlog_keys: Tuple[Tuple[str, int, str], ...]
    event_stream_authority_digest: str
    lifecycle_snapshot_digest: str
    observed_timeout_event_digests: Tuple[str, ...]
    terminal_execution_event_digests: Tuple[str, ...]
    retry_fallback_projection: Any
    cli_batch_projection: Any
    projection_digest: str

    def __init__(
        self,
        decision_receipt,
        decisive_proof_receipt_digests,
        decisive_proof_artifact_digests,
        active_cause_ids,
        proof_backlog_keys,
        event_stream_authority_digest,
        lifecycle_snapshot_digest,
        observed_timeout_event_digests,
        terminal_execution_event_digests,
        retry_fallback_projection,
        cli_batch_projection,
        projection_digest,
        *,
        _factory_token=None,
    ):
        if _factory_token is not _CANDIDATE_PROJECTION_FACTORY_TOKEN:
            raise ValueError("candidate projections are issued only by the legacy-blind builder")
        object.__setattr__(self, "decision_receipt", decision_receipt)
        object.__setattr__(self, "decisive_proof_receipt_digests", tuple(decisive_proof_receipt_digests))
        object.__setattr__(self, "decisive_proof_artifact_digests", tuple(decisive_proof_artifact_digests))
        object.__setattr__(self, "active_cause_ids", tuple(active_cause_ids))
        object.__setattr__(self, "proof_backlog_keys", tuple(proof_backlog_keys))
        object.__setattr__(self, "event_stream_authority_digest", event_stream_authority_digest)
        object.__setattr__(self, "lifecycle_snapshot_digest", lifecycle_snapshot_digest)
        object.__setattr__(self, "observed_timeout_event_digests", tuple(observed_timeout_event_digests))
        object.__setattr__(self, "terminal_execution_event_digests", tuple(terminal_execution_event_digests))
        object.__setattr__(self, "retry_fallback_projection", canonical_value(retry_fallback_projection))
        object.__setattr__(self, "cli_batch_projection", canonical_value(cli_batch_projection))
        object.__setattr__(self, "projection_digest", projection_digest)

    def validate(self) -> None:
        self.decision_receipt.validate()
        if not all(type(value) is str and value for value in (
            self.event_stream_authority_digest, self.lifecycle_snapshot_digest,
        )):
            raise TypeError("candidate stream/snapshot authority digests must be exact strings")
        if any(
            type(value) is not str or not value
            for value in (
                *self.observed_timeout_event_digests,
                *self.terminal_execution_event_digests,
            )
        ):
            raise TypeError("candidate timeout event digests must be exact strings")
        if len(self.observed_timeout_event_digests) != len(
            set(self.observed_timeout_event_digests)
        ) or len(self.terminal_execution_event_digests) != len(
            set(self.terminal_execution_event_digests)
        ):
            raise ValueError("candidate timeout event digests must be duplicate-free")
        if not set(self.terminal_execution_event_digests).issubset(
            self.observed_timeout_event_digests
        ):
            raise ValueError("candidate terminal timeout is not an observed timeout event")
        terminal_count = len(self.terminal_execution_event_digests)
        if self.decision_receipt.outcome.value == "TIMEOUT":
            if terminal_count != 1:
                raise ValueError("TIMEOUT candidate requires exactly one terminal timeout event")
        elif terminal_count:
            raise ValueError("non-TIMEOUT candidate cannot retain terminal timeout authority")
        expected = authority_digest({
            "decision_receipt_digest": self.decision_receipt.receipt_digest,
            "decisive_proof_receipt_digests": self.decisive_proof_receipt_digests,
            "decisive_proof_artifact_digests": self.decisive_proof_artifact_digests,
            "active_cause_ids": self.active_cause_ids,
            "proof_backlog_keys": self.proof_backlog_keys,
            "event_stream_authority_digest": self.event_stream_authority_digest,
            "lifecycle_snapshot_digest": self.lifecycle_snapshot_digest,
            "observed_timeout_event_digests": self.observed_timeout_event_digests,
            "terminal_execution_event_digests": self.terminal_execution_event_digests,
            "retry_fallback_projection": self.retry_fallback_projection,
            "cli_batch_projection": self.cli_batch_projection,
        })
        if expected != self.projection_digest:
            raise ValueError("candidate decision projection digest mismatch")


def build_candidate_projection(
    reduction: ShadowReductionResult,
    *,
    decisive_proof_receipts: Sequence[DecisiveProofReceipt] = (),
    terminal_timeout_receipts: Sequence[TerminalTimeoutReceipt] = (),
    error_receipts: Sequence[ErrorReceipt] = (),
    retry_fallback_projection: Any = (),
    cli_batch_projection: Any = (),
) -> CandidateDecisionProjection:
    reduction.snapshot.validate()
    reduction.projection.validate()
    if reduction.projection.snapshot_digest != reduction.snapshot.snapshot_digest:
        raise ValueError("candidate lifecycle projection is not bound to its snapshot")
    decisive = tuple(decisive_proof_receipts)
    timeouts = tuple(terminal_timeout_receipts)
    errors = tuple(error_receipts)
    malformed = False
    allowed_timeouts = set(reduction.snapshot.terminal_timeout_event_bindings)
    event_type_for_kind = {
        DecisiveProofKind.EQ_CLOSURE: "EQ_CLOSURE",
        DecisiveProofKind.SAFE_COUNTEREXAMPLE: "COUNTEREXAMPLE",
    }
    receipt_proof_bindings = tuple(
        (event_type_for_kind[receipt.proof_kind], receipt.proof_artifact_digest)
        for receipt in decisive
    )
    # Decisive stream authority is not optional evidence: it must be transferred
    # losslessly to receipts.  Counter retains duplicate events so callers cannot
    # hide either a conflict or a repeated authority event by omission/dedup.
    if Counter(receipt_proof_bindings) != Counter(
        reduction.snapshot.decisive_proof_event_bindings
    ):
        malformed = True
    if any(
        (receipt.execution_event_digest, receipt.proof_requirement_id)
        not in allowed_timeouts
        for receipt in timeouts
    ):
        malformed = True
    receipt_error_bindings = tuple(
        (receipt.error_kind, receipt.error_artifact_digest) for receipt in errors
    )
    if Counter(receipt_error_bindings) != Counter(
        reduction.snapshot.error_event_bindings
    ):
        malformed = True
    decision = finalize_decision(FinalizationAuthority(
        reduction.snapshot.result_occurrence_id,
        reduction.projection,
        decisive_proof_receipts=decisive,
        terminal_timeout_receipts=timeouts,
        error_receipts=errors,
        malformed_authority=malformed,
    ))
    occurrence_by_id = {
        item.occurrence.occurrence_id: item
        for item in reduction.snapshot.occurrence_authorities
    }
    proof_keys = []
    for row in reduction.projection.q_open_base:
        authority = occurrence_by_id[row.occurrence_id]
        bound = authority.bound_contract
        if bound is None:
            raise ValueError("candidate open requirement lacks bound contract")
        proof_keys.append((
            bound.contract_definition_id,
            bound.contract_version,
            row.proof_requirement_id,
        ))
    fallback = canonical_value(retry_fallback_projection)
    cli = canonical_value(cli_batch_projection)
    values = {
        "decision_receipt_digest": decision.receipt_digest,
        "decisive_proof_receipt_digests": tuple(sorted(
            receipt.receipt_digest for receipt in decisive
        )),
        "decisive_proof_artifact_digests": tuple(sorted(
            receipt.proof_artifact_digest for receipt in decisive
        )),
        "active_cause_ids": tuple(sorted({
            row.cause_id for row in reduction.projection.c_active_base
        })),
        "proof_backlog_keys": tuple(sorted(proof_keys)),
        "event_stream_authority_digest": (
            reduction.snapshot.event_stream_authority_digest
        ),
        "lifecycle_snapshot_digest": reduction.snapshot.snapshot_digest,
        "observed_timeout_event_digests": tuple(sorted(
            reduction.snapshot.terminal_timeout_event_digests
        )),
        "terminal_execution_event_digests": tuple(sorted(
            receipt.execution_event_digest for receipt in timeouts
        )) if decision.outcome.value == "TIMEOUT" else (),
        "retry_fallback_projection": fallback,
        "cli_batch_projection": cli,
    }
    candidate = CandidateDecisionProjection(
        decision,
        values["decisive_proof_receipt_digests"],
        values["decisive_proof_artifact_digests"],
        values["active_cause_ids"],
        values["proof_backlog_keys"],
        values["event_stream_authority_digest"],
        values["lifecycle_snapshot_digest"],
        values["observed_timeout_event_digests"],
        values["terminal_execution_event_digests"],
        fallback,
        cli,
        authority_digest(values),
        _factory_token=_CANDIDATE_PROJECTION_FACTORY_TOKEN,
    )
    candidate.validate()
    return candidate

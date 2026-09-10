"""Five-value decision authority over one verified lifecycle bundle."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Tuple

from scripts.function_tracer_pcode.authority.contracts import (
    Outcome,
    VerifiedLifecycleProjection,
    authority_digest,
)


class DecisiveProofKind(str, Enum):
    EQ_CLOSURE = "EQ_CLOSURE"
    SAFE_COUNTEREXAMPLE = "SAFE_COUNTEREXAMPLE"


@dataclass(frozen=True)
class DecisiveProofReceipt:
    result_occurrence_id: str
    lifecycle_projection_digest: str
    proof_kind: DecisiveProofKind
    proof_artifact_digest: str
    receipt_digest: str

    @classmethod
    def create(
        cls,
        *,
        result_occurrence_id: str,
        lifecycle_projection_digest: str,
        proof_kind: DecisiveProofKind,
        proof_artifact_digest: str,
    ) -> "DecisiveProofReceipt":
        payload = {
            "result_occurrence_id": result_occurrence_id,
            "lifecycle_projection_digest": lifecycle_projection_digest,
            "proof_kind": proof_kind.value,
            "proof_artifact_digest": proof_artifact_digest,
        }
        return cls(
            result_occurrence_id,
            lifecycle_projection_digest,
            proof_kind,
            proof_artifact_digest,
            authority_digest(payload),
        )

    def validate(self) -> None:
        expected = DecisiveProofReceipt.create(
            result_occurrence_id=self.result_occurrence_id,
            lifecycle_projection_digest=self.lifecycle_projection_digest,
            proof_kind=self.proof_kind,
            proof_artifact_digest=self.proof_artifact_digest,
        )
        if expected != self or not self.proof_artifact_digest:
            raise ValueError("invalid decisive proof receipt")


@dataclass(frozen=True)
class TerminalTimeoutReceipt:
    result_occurrence_id: str
    lifecycle_projection_digest: str
    proof_requirement_id: str
    execution_event_digest: str
    receipt_digest: str

    @classmethod
    def create(
        cls,
        *,
        result_occurrence_id: str,
        lifecycle_projection_digest: str,
        proof_requirement_id: str,
        execution_event_digest: str,
    ) -> "TerminalTimeoutReceipt":
        payload = {
            "result_occurrence_id": result_occurrence_id,
            "lifecycle_projection_digest": lifecycle_projection_digest,
            "proof_requirement_id": proof_requirement_id,
            "execution_event_digest": execution_event_digest,
        }
        return cls(
            result_occurrence_id,
            lifecycle_projection_digest,
            proof_requirement_id,
            execution_event_digest,
            authority_digest(payload),
        )

    def validate(self) -> None:
        expected = TerminalTimeoutReceipt.create(
            result_occurrence_id=self.result_occurrence_id,
            lifecycle_projection_digest=self.lifecycle_projection_digest,
            proof_requirement_id=self.proof_requirement_id,
            execution_event_digest=self.execution_event_digest,
        )
        if expected != self or not self.proof_requirement_id or not self.execution_event_digest:
            raise ValueError("invalid terminal timeout receipt")


@dataclass(frozen=True)
class ErrorReceipt:
    result_occurrence_id: str
    lifecycle_projection_digest: str
    error_kind: str
    error_artifact_digest: str
    receipt_digest: str

    @classmethod
    def create(
        cls,
        *,
        result_occurrence_id: str,
        lifecycle_projection_digest: str,
        error_kind: str,
        error_artifact_digest: str,
    ) -> "ErrorReceipt":
        payload = {
            "result_occurrence_id": result_occurrence_id,
            "lifecycle_projection_digest": lifecycle_projection_digest,
            "error_kind": error_kind,
            "error_artifact_digest": error_artifact_digest,
        }
        return cls(
            result_occurrence_id,
            lifecycle_projection_digest,
            error_kind,
            error_artifact_digest,
            authority_digest(payload),
        )

    def validate(self) -> None:
        expected = ErrorReceipt.create(
            result_occurrence_id=self.result_occurrence_id,
            lifecycle_projection_digest=self.lifecycle_projection_digest,
            error_kind=self.error_kind,
            error_artifact_digest=self.error_artifact_digest,
        )
        if expected != self or not self.error_kind or not self.error_artifact_digest:
            raise ValueError("invalid error receipt")


@dataclass(frozen=True)
class FinalizationAuthority:
    result_occurrence_id: str
    lifecycle_projection: VerifiedLifecycleProjection
    decisive_proof_receipts: Tuple[DecisiveProofReceipt, ...] = ()
    terminal_timeout_receipts: Tuple[TerminalTimeoutReceipt, ...] = ()
    error_receipts: Tuple[ErrorReceipt, ...] = ()
    malformed_authority: bool = False

    def __post_init__(self) -> None:
        if type(self.lifecycle_projection) is not VerifiedLifecycleProjection:
            raise TypeError("decision finalization requires FINAL lifecycle authority")
        # The unconditional lane accepts exactly these receipt types.  A
        # conditional (assumption-dependent) proof carries a different type and
        # is rejected here rather than falling through as a receipt whose kind
        # the outcome derivation happens not to recognise.
        for receipts, expected in (
            (self.decisive_proof_receipts, DecisiveProofReceipt),
            (self.terminal_timeout_receipts, TerminalTimeoutReceipt),
            (self.error_receipts, ErrorReceipt),
        ):
            for receipt in receipts:
                if type(receipt) is not expected:
                    raise TypeError(
                        "the unconditional decision accepts "
                        f"{expected.__name__} only: {type(receipt).__name__}"
                    )
        object.__setattr__(self, "decisive_proof_receipts", tuple(self.decisive_proof_receipts))
        object.__setattr__(self, "terminal_timeout_receipts", tuple(self.terminal_timeout_receipts))
        object.__setattr__(self, "error_receipts", tuple(self.error_receipts))


_DECISION_RECEIPT_FACTORY_TOKEN = object()
_DECISION_RECEIPT_CODEC_TOKEN = object()


@dataclass(frozen=True, init=False)
class DecisionReceipt:
    result_occurrence_id: str
    outcome: Outcome
    lifecycle_projection_digest: str
    authority_input_digest: str
    receipt_digest: str

    def __init__(
        self,
        result_occurrence_id: str,
        outcome: Outcome,
        lifecycle_projection_digest: str,
        authority_input_digest: str,
        receipt_digest: str,
        *,
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _DECISION_RECEIPT_FACTORY_TOKEN:
            raise ValueError("decision receipts are issued only by DecisionFinalizer")
        object.__setattr__(self, "result_occurrence_id", result_occurrence_id)
        object.__setattr__(self, "outcome", Outcome(outcome))
        object.__setattr__(self, "lifecycle_projection_digest", lifecycle_projection_digest)
        object.__setattr__(self, "authority_input_digest", authority_input_digest)
        object.__setattr__(self, "receipt_digest", receipt_digest)

    def validate(self) -> None:
        expected = authority_digest(
            {
                "result_occurrence_id": self.result_occurrence_id,
                "outcome": self.outcome.value,
                "lifecycle_projection_digest": self.lifecycle_projection_digest,
                "authority_input_digest": self.authority_input_digest,
            }
        )
        if expected != self.receipt_digest:
            raise ValueError("decision receipt digest mismatch")

    @classmethod
    def from_persisted(
        cls,
        *,
        result_occurrence_id: str,
        outcome: Outcome,
        lifecycle_projection_digest: str,
        authority_input_digest: str,
        receipt_digest: str,
        _codec_token: object = None,
    ) -> "DecisionReceipt":
        if _codec_token is not _DECISION_RECEIPT_CODEC_TOKEN:
            raise ValueError("persisted decision receipts require the strict codec")
        receipt = cls(
            result_occurrence_id,
            outcome,
            lifecycle_projection_digest,
            authority_input_digest,
            receipt_digest,
            _factory_token=_DECISION_RECEIPT_FACTORY_TOKEN,
        )
        receipt.validate()
        return receipt


def finalize_decision(authority: FinalizationAuthority) -> DecisionReceipt:
    projection = authority.lifecycle_projection
    malformed = authority.malformed_authority
    try:
        projection.validate()
    except (TypeError, ValueError):
        malformed = True
    if (
        projection.result_occurrence_id != authority.result_occurrence_id
        or any(
            row.result_occurrence_id != authority.result_occurrence_id
            for row in (*projection.c_active_base, *projection.q_open_base)
        )
    ):
        malformed = True
    for receipt in (
        *authority.decisive_proof_receipts,
        *authority.terminal_timeout_receipts,
        *authority.error_receipts,
    ):
        try:
            receipt.validate()
        except (TypeError, ValueError):
            malformed = True
        if (
            receipt.result_occurrence_id != authority.result_occurrence_id
            or receipt.lifecycle_projection_digest != projection.lifecycle_projection_digest
        ):
            malformed = True
    decisive_kinds = [receipt.proof_kind for receipt in authority.decisive_proof_receipts]
    if len(decisive_kinds) != len(set(decisive_kinds)):
        malformed = True
    if len(authority.terminal_timeout_receipts) > 1:
        malformed = True
    active = projection.c_active_base
    open_requirement_ids = {row.proof_requirement_id for row in projection.q_open_base}
    if authority.terminal_timeout_receipts and (
        authority.terminal_timeout_receipts[0].proof_requirement_id
        not in open_requirement_ids
    ):
        malformed = True
    has_eq = DecisiveProofKind.EQ_CLOSURE in decisive_kinds
    has_not_eq = DecisiveProofKind.SAFE_COUNTEREXAMPLE in decisive_kinds
    conflict = (has_eq and has_not_eq) or (
        (has_eq or has_not_eq) and bool(authority.terminal_timeout_receipts)
    )
    blocks_eq = any(
        row.decision_effect in {"blocks_equivalence", "blocks_decision"} for row in active
    )
    blocks_not_eq = any(
        row.decision_effect in {"blocks_disequivalence", "blocks_decision"}
        for row in active
    )
    if malformed or authority.error_receipts or conflict:
        outcome = Outcome.ERROR
    elif has_eq:
        outcome = Outcome.EQUIVALENT if not blocks_eq else Outcome.UNKNOWN
    elif has_not_eq:
        outcome = Outcome.NOT_EQ if not blocks_not_eq else Outcome.UNKNOWN
    elif authority.terminal_timeout_receipts:
        outcome = Outcome.TIMEOUT if active and projection.q_open_base else Outcome.ERROR
    elif active:
        outcome = Outcome.UNKNOWN
    else:
        outcome = Outcome.ERROR
    input_digest = authority_digest(
        {
            "result_occurrence_id": authority.result_occurrence_id,
            "lifecycle_projection_digest": projection.lifecycle_projection_digest,
            "decisive_receipt_digests": tuple(
                receipt.receipt_digest for receipt in authority.decisive_proof_receipts
            ),
            "terminal_timeout_receipt_digests": tuple(
                receipt.receipt_digest for receipt in authority.terminal_timeout_receipts
            ),
            "error_receipt_digests": tuple(
                receipt.receipt_digest for receipt in authority.error_receipts
            ),
            "malformed_authority": malformed,
        }
    )
    receipt_digest = authority_digest(
        {
            "result_occurrence_id": authority.result_occurrence_id,
            "outcome": outcome.value,
            "lifecycle_projection_digest": projection.lifecycle_projection_digest,
            "authority_input_digest": input_digest,
        }
    )
    receipt = DecisionReceipt(
        authority.result_occurrence_id,
        outcome,
        projection.lifecycle_projection_digest,
        input_digest,
        receipt_digest,
        _factory_token=_DECISION_RECEIPT_FACTORY_TOKEN,
    )
    receipt.validate()
    return receipt

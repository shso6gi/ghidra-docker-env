"""Conditional (assumption-dependent) decision authority.

A conditional proof is never authority over the pair's outcome.  The five-value
``Outcome`` and the CLI exit code are read from the unconditional
``DecisionReceipt`` alone; the receipts issued here live in their own column and
carry the whole assumption set the conditional proof depended on.

Ownership follows the layering: the premise contract belongs to the proof layer
(``proof.assumptions``) and is imported downward here, so no new
``proof -> authority`` edge is created.  Nothing in this module can turn a
conditional proof into an unconditional one -- the unconditional finalizer
accepts exactly ``DecisiveProofReceipt`` and rejects every conditional receipt
by type.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Iterable, Mapping, Tuple

from scripts.function_tracer_pcode.authority.contracts import (
    Outcome,
    VerifiedLifecycleProjection,
    assert_deep_immutable,
    authority_digest,
    freeze_authority_value,
)
from scripts.function_tracer_pcode.authority.decision.decision import DecisionReceipt
from scripts.function_tracer_pcode.proof.assumptions import AssumptionPremise


class ConditionalDecisiveProofKind(str, Enum):
    CONDITIONAL_EQ_CLOSURE = "CONDITIONAL_EQ_CLOSURE"
    CONDITIONAL_SAFE_COUNTEREXAMPLE = "CONDITIONAL_SAFE_COUNTEREXAMPLE"


def canonical_assumption_dependencies(
    premises: Iterable[AssumptionPremise],
) -> Tuple[AssumptionPremise, ...]:
    """Return the assumption set in a deterministic, digest-ordered form.

    The premises are frozen and checked with the existing authority
    immutability contract, de-duplicated, and ordered by their own digest, so
    the receipt digest does not depend on the order the proof happened to
    collect them in.
    """
    frozen = freeze_authority_value(tuple(premises))
    ordered = []
    seen = set()
    for premise in frozen:
        if type(premise) is not AssumptionPremise:
            raise TypeError(
                "conditional receipts carry proof-owned AssumptionPremise only: "
                f"{type(premise).__name__}"
            )
        assert_deep_immutable(premise)
        digest = authority_digest(premise)
        if digest in seen:
            continue
        seen.add(digest)
        ordered.append((digest, premise))
    return tuple(premise for _digest, premise in sorted(ordered, key=lambda item: item[0]))


def assumption_dependencies_digest(premises: Iterable[AssumptionPremise]) -> str:
    """Digest one canonical assumption set."""
    return authority_digest(canonical_assumption_dependencies(premises))


@dataclass(frozen=True)
class ConditionalDecisiveProofReceipt:
    """One decisive proof that holds only under its assumption dependencies."""

    result_occurrence_id: str
    lifecycle_projection_digest: str
    proof_kind: ConditionalDecisiveProofKind
    proof_artifact_digest: str
    assumption_dependencies: Tuple[AssumptionPremise, ...]
    assumption_set_digest: str
    receipt_digest: str

    @classmethod
    def create(
        cls,
        *,
        result_occurrence_id: str,
        lifecycle_projection_digest: str,
        proof_kind: ConditionalDecisiveProofKind,
        proof_artifact_digest: str,
        assumption_dependencies: Iterable[AssumptionPremise],
    ) -> "ConditionalDecisiveProofReceipt":
        dependencies = canonical_assumption_dependencies(assumption_dependencies)
        if not dependencies:
            raise ValueError("a conditional proof receipt requires assumption dependencies")
        kind = ConditionalDecisiveProofKind(proof_kind)
        digest = authority_digest(dependencies)
        payload = {
            "result_occurrence_id": result_occurrence_id,
            "lifecycle_projection_digest": lifecycle_projection_digest,
            "proof_kind": kind.value,
            "proof_artifact_digest": proof_artifact_digest,
            "assumption_set_digest": digest,
        }
        return cls(
            result_occurrence_id,
            lifecycle_projection_digest,
            kind,
            proof_artifact_digest,
            dependencies,
            digest,
            authority_digest(payload),
        )

    def validate(self) -> None:
        if not self.assumption_dependencies:
            raise ValueError("conditional proof receipt lost its assumption dependencies")
        expected = ConditionalDecisiveProofReceipt.create(
            result_occurrence_id=self.result_occurrence_id,
            lifecycle_projection_digest=self.lifecycle_projection_digest,
            proof_kind=self.proof_kind,
            proof_artifact_digest=self.proof_artifact_digest,
            assumption_dependencies=self.assumption_dependencies,
        )
        if expected != self or not self.proof_artifact_digest:
            raise ValueError("invalid conditional decisive proof receipt")
        assert_deep_immutable(self)


@dataclass(frozen=True)
class ConditionalFinalizationAuthority:
    """The inputs of one conditional lane run.

    ``assumption_set`` is the conditional view's whole assumption set.  Issue
    #20 does not minimize dependencies, so every decisive receipt must depend
    on exactly this set; a receipt that carries a smaller set is malformed.
    """

    result_occurrence_id: str
    unconditional_decision: DecisionReceipt
    lifecycle_projection: VerifiedLifecycleProjection
    assumption_set: Tuple[AssumptionPremise, ...]
    conditional_decisive_proof_receipts: Tuple[ConditionalDecisiveProofReceipt, ...] = ()
    malformed_authority: bool = False

    def __post_init__(self) -> None:
        if type(self.unconditional_decision) is not DecisionReceipt:
            raise TypeError("the conditional lane requires the unconditional DecisionReceipt")
        if type(self.lifecycle_projection) is not VerifiedLifecycleProjection:
            raise TypeError("conditional finalization requires FINAL lifecycle authority")
        for receipt in self.conditional_decisive_proof_receipts:
            if type(receipt) is not ConditionalDecisiveProofReceipt:
                raise TypeError(
                    "the conditional lane collects ConditionalDecisiveProofReceipt only: "
                    f"{type(receipt).__name__}"
                )
        assumption_set = canonical_assumption_dependencies(self.assumption_set)
        if not assumption_set:
            raise ValueError("a conditional lane requires a non-empty assumption set")
        object.__setattr__(self, "assumption_set", assumption_set)
        object.__setattr__(
            self,
            "conditional_decisive_proof_receipts",
            tuple(self.conditional_decisive_proof_receipts),
        )


_CONDITIONAL_DECISION_FACTORY_TOKEN = object()
_CONDITIONAL_DECISION_CODEC_TOKEN = object()


@dataclass(frozen=True, init=False)
class ConditionalDecisionReceipt:
    """The conditional column of one pair, bound to its unconditional decision."""

    result_occurrence_id: str
    conditional_outcome: Outcome
    unconditional_outcome: Outcome
    unconditional_receipt_digest: str
    lifecycle_projection_digest: str
    assumption_set_digest: str
    authority_input_digest: str
    receipt_digest: str

    def __init__(
        self,
        result_occurrence_id: str,
        conditional_outcome: Outcome,
        unconditional_outcome: Outcome,
        unconditional_receipt_digest: str,
        lifecycle_projection_digest: str,
        assumption_set_digest: str,
        authority_input_digest: str,
        receipt_digest: str,
        *,
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _CONDITIONAL_DECISION_FACTORY_TOKEN:
            raise ValueError(
                "conditional decision receipts are issued only by finalize_conditional_decision"
            )
        object.__setattr__(self, "result_occurrence_id", result_occurrence_id)
        object.__setattr__(self, "conditional_outcome", Outcome(conditional_outcome))
        object.__setattr__(self, "unconditional_outcome", Outcome(unconditional_outcome))
        object.__setattr__(self, "unconditional_receipt_digest", unconditional_receipt_digest)
        object.__setattr__(self, "lifecycle_projection_digest", lifecycle_projection_digest)
        object.__setattr__(self, "assumption_set_digest", assumption_set_digest)
        object.__setattr__(self, "authority_input_digest", authority_input_digest)
        object.__setattr__(self, "receipt_digest", receipt_digest)

    def is_decisive(self) -> bool:
        return self.conditional_outcome in (Outcome.EQUIVALENT, Outcome.NOT_EQ)

    def validate(self) -> None:
        expected = authority_digest(
            {
                "result_occurrence_id": self.result_occurrence_id,
                "conditional_outcome": self.conditional_outcome.value,
                "unconditional_outcome": self.unconditional_outcome.value,
                "unconditional_receipt_digest": self.unconditional_receipt_digest,
                "lifecycle_projection_digest": self.lifecycle_projection_digest,
                "assumption_set_digest": self.assumption_set_digest,
                "authority_input_digest": self.authority_input_digest,
            }
        )
        if expected != self.receipt_digest:
            raise ValueError("conditional decision receipt digest mismatch")
        if self.unconditional_outcome is not Outcome.UNKNOWN and self.is_decisive():
            raise ValueError("a conditional decision cannot follow an unconditional decision")
        if self.is_decisive() and not self.assumption_set_digest:
            raise ValueError("a decisive conditional receipt requires its assumption set")

    @classmethod
    def from_persisted(
        cls,
        *,
        result_occurrence_id: str,
        conditional_outcome: Outcome,
        unconditional_outcome: Outcome,
        unconditional_receipt_digest: str,
        lifecycle_projection_digest: str,
        assumption_set_digest: str,
        authority_input_digest: str,
        receipt_digest: str,
        _codec_token: object = None,
    ) -> "ConditionalDecisionReceipt":
        if _codec_token is not _CONDITIONAL_DECISION_CODEC_TOKEN:
            raise ValueError("persisted conditional decision receipts require the strict codec")
        receipt = cls(
            result_occurrence_id,
            conditional_outcome,
            unconditional_outcome,
            unconditional_receipt_digest,
            lifecycle_projection_digest,
            assumption_set_digest,
            authority_input_digest,
            receipt_digest,
            _factory_token=_CONDITIONAL_DECISION_FACTORY_TOKEN,
        )
        receipt.validate()
        return receipt


CONDITIONAL_DECISION_RECEIPT_FIELDS = frozenset({
    "result_occurrence_id", "conditional_outcome", "unconditional_outcome",
    "unconditional_receipt_digest", "lifecycle_projection_digest",
    "assumption_set_digest", "authority_input_digest", "receipt_digest",
})


def conditional_decision_receipt_payload(receipt: Any) -> dict:
    """Return the strict public representation of one conditional receipt.

    The payload repeats the unconditional outcome and the receipt digest the
    conditional decision was issued against, so every consumer can re-check the
    join instead of trusting the column it is printed next to.
    """
    if type(receipt) is not ConditionalDecisionReceipt:
        raise TypeError("the conditional column requires an exact ConditionalDecisionReceipt")
    receipt.validate()
    return {
        "result_occurrence_id": receipt.result_occurrence_id,
        "conditional_outcome": receipt.conditional_outcome.value,
        "unconditional_outcome": receipt.unconditional_outcome.value,
        "unconditional_receipt_digest": receipt.unconditional_receipt_digest,
        "lifecycle_projection_digest": receipt.lifecycle_projection_digest,
        "assumption_set_digest": receipt.assumption_set_digest,
        "authority_input_digest": receipt.authority_input_digest,
        "receipt_digest": receipt.receipt_digest,
    }


def conditional_decision_receipt_from_payload(payload: Any) -> ConditionalDecisionReceipt:
    """Rebuild one persisted conditional receipt through its own validation.

    Every consumer of a serialized conditional column goes through here, so the
    digest check is the receipt's own ``validate()`` and no second, weaker
    verification exists anywhere.
    """
    if not isinstance(payload, Mapping) or set(payload) != set(
        CONDITIONAL_DECISION_RECEIPT_FIELDS
    ):
        raise ValueError("serialized conditional decision receipt shape is invalid")
    for name in CONDITIONAL_DECISION_RECEIPT_FIELDS - {
        "conditional_outcome", "unconditional_outcome",
    }:
        if type(payload[name]) is not str or not payload[name]:
            raise TypeError(
                f"conditional decision receipt field {name} must be a non-empty exact string"
            )
    return ConditionalDecisionReceipt.from_persisted(
        **{
            **payload,
            "conditional_outcome": Outcome(payload["conditional_outcome"]),
            "unconditional_outcome": Outcome(payload["unconditional_outcome"]),
        },
        _codec_token=_CONDITIONAL_DECISION_CODEC_TOKEN,
    )


def validate_conditional_decision_join(
    receipt: ConditionalDecisionReceipt,
    *,
    result_occurrence_id: str,
    unconditional_outcome: Outcome,
    unconditional_receipt_digest: str,
) -> None:
    """Bind one conditional receipt to the exact unconditional decision it followed.

    A conditional receipt is only ever meaningful next to its own pair's
    unconditional decision: a receipt from another pair, or one issued against
    a different ``DecisionReceipt`` of the same pair, is rejected rather than
    reported in the conditional column of whatever it was pasted into.
    """
    if type(receipt) is not ConditionalDecisionReceipt:
        raise TypeError("the conditional join requires an exact ConditionalDecisionReceipt")
    receipt.validate()
    if receipt.result_occurrence_id != result_occurrence_id:
        raise ValueError("conditional receipt belongs to a different pair")
    if receipt.unconditional_receipt_digest != unconditional_receipt_digest:
        raise ValueError("conditional receipt joins a different DecisionReceipt")
    if receipt.unconditional_outcome is not Outcome(unconditional_outcome):
        raise ValueError("conditional receipt contradicts the unconditional outcome")


def finalize_conditional_decision(
    authority: ConditionalFinalizationAuthority,
) -> ConditionalDecisionReceipt:
    """Derive the conditional column from one conditional lane bundle.

    The lane runs only after an unconditional ``UNKNOWN``; every other
    unconditional outcome, a broken join, or a receipt that depends on less
    than the whole assumption set is malformed and yields ``ERROR`` in the
    conditional column.  The unconditional decision is never touched.
    """
    projection = authority.lifecycle_projection
    unconditional = authority.unconditional_decision
    malformed = authority.malformed_authority
    try:
        projection.validate()
        unconditional.validate()
    except (TypeError, ValueError):
        malformed = True
    if (
        projection.result_occurrence_id != authority.result_occurrence_id
        or unconditional.result_occurrence_id != authority.result_occurrence_id
        or any(
            row.result_occurrence_id != authority.result_occurrence_id
            for row in (*projection.c_active_base, *projection.q_open_base)
        )
    ):
        malformed = True
    if unconditional.outcome is not Outcome.UNKNOWN:
        # The lane must not start after a decided pair; refuse to claim anything.
        malformed = True
    set_digest = authority_digest(authority.assumption_set)
    for receipt in authority.conditional_decisive_proof_receipts:
        try:
            receipt.validate()
        except (TypeError, ValueError):
            malformed = True
            continue
        if (
            receipt.result_occurrence_id != authority.result_occurrence_id
            or receipt.lifecycle_projection_digest != projection.lifecycle_projection_digest
            or receipt.assumption_set_digest != set_digest
            or receipt.assumption_dependencies != authority.assumption_set
        ):
            malformed = True
    kinds = [receipt.proof_kind for receipt in authority.conditional_decisive_proof_receipts]
    if len(kinds) != len(set(kinds)):
        malformed = True
    has_eq = ConditionalDecisiveProofKind.CONDITIONAL_EQ_CLOSURE in kinds
    has_not_eq = ConditionalDecisiveProofKind.CONDITIONAL_SAFE_COUNTEREXAMPLE in kinds
    active = projection.c_active_base
    blocks_eq = any(
        row.decision_effect in {"blocks_equivalence", "blocks_decision"} for row in active
    )
    blocks_not_eq = any(
        row.decision_effect in {"blocks_disequivalence", "blocks_decision"} for row in active
    )
    if malformed or (has_eq and has_not_eq):
        conditional_outcome = Outcome.ERROR
    elif has_eq:
        conditional_outcome = Outcome.EQUIVALENT if not blocks_eq else Outcome.UNKNOWN
    elif has_not_eq:
        conditional_outcome = Outcome.NOT_EQ if not blocks_not_eq else Outcome.UNKNOWN
    else:
        conditional_outcome = Outcome.UNKNOWN
    input_digest = authority_digest(
        {
            "result_occurrence_id": authority.result_occurrence_id,
            "lifecycle_projection_digest": projection.lifecycle_projection_digest,
            "unconditional_receipt_digest": unconditional.receipt_digest,
            "assumption_set_digest": set_digest,
            "conditional_receipt_digests": tuple(
                receipt.receipt_digest
                for receipt in authority.conditional_decisive_proof_receipts
            ),
            "malformed_authority": malformed,
        }
    )
    receipt_digest = authority_digest(
        {
            "result_occurrence_id": authority.result_occurrence_id,
            "conditional_outcome": conditional_outcome.value,
            "unconditional_outcome": unconditional.outcome.value,
            "unconditional_receipt_digest": unconditional.receipt_digest,
            "lifecycle_projection_digest": projection.lifecycle_projection_digest,
            "assumption_set_digest": set_digest,
            "authority_input_digest": input_digest,
        }
    )
    receipt = ConditionalDecisionReceipt(
        authority.result_occurrence_id,
        conditional_outcome,
        unconditional.outcome,
        unconditional.receipt_digest,
        projection.lifecycle_projection_digest,
        set_digest,
        input_digest,
        receipt_digest,
        _factory_token=_CONDITIONAL_DECISION_FACTORY_TOKEN,
    )
    receipt.validate()
    return receipt

"""Explicit bridge from production proof producers to canonical v2 sessions."""

from __future__ import annotations

from dataclasses import dataclass, field, replace
import secrets
from typing import Any, Callable, Iterator, Mapping, Optional

from scripts.function_tracer_pcode.authority.contracts import (
    CauseOccurrence,
    CauseOccurrenceAuthority,
    IdentityScope,
    ProofRequirement,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementSlotDefinition,
    SatisfactionContractDefinition,
    authority_digest,
    canonical_value,
    requirement_slot,
)
from scripts.function_tracer_pcode.authority.lifecycle.production_context import (
    active_production_pilot_session,
    comparison_receipt_authority,
    production_pilot_session_scope,
)
from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
    AnalysisLimitationBlockerSignal,
)
from scripts.function_tracer_pcode.authority.domains.comparison_closure import (
    ComparisonClosureProductionSignal,
)
from scripts.function_tracer_pcode.authority.domains.identical_function_identity import (
    IdenticalFunctionIdentitySignal,
)
from scripts.function_tracer_pcode.authority.domains.call_effect_sites import (
    CALL_EFFECT_PROOF_BATCH_SITE,
)
from scripts.function_tracer_pcode.authority.registry import (
    SatisfactionBindingFactory,
    SealedReasonRegistry,
    SealedRecoveryRegistry,
    SemanticCauseIdentityFactory,
)
from scripts.function_tracer_pcode.authority.lifecycle.stream import (
    CauseObservedEventAuthority,
    DecisiveProofEventAuthority,
    EventIntent,
    EventType,
)


COMPARISON_CLOSURE_REASON_ID = "comparison_equivalence_closure_unproven"
COMPARISON_CLOSURE_PROOF_KIND = "comparison_equivalence_closure"
COMPARISON_CLOSURE_CONTRACT_ID = "comparison-equivalence-closure-recovery"
COMPARISON_CLOSURE_REASON_REGISTRY = SealedReasonRegistry.build((
    ReasonDefinition(
        COMPARISON_CLOSURE_REASON_ID, "comparison_closure", "proof_obligation",
        "blocks_decision", frozenset(("comparison_execution_receipt",)),
        ("comparison_receipt", "terminal_receipt", "query_receipts"),
        frozenset((COMPARISON_CLOSURE_PROOF_KIND,)), True,
        "comparison_closure_v1", RecoveryAddressability.REQUIREMENT_REQUIRED,
    ),
))
COMPARISON_CLOSURE_RECOVERY_REGISTRY = SealedRecoveryRegistry.build((
    SatisfactionContractDefinition(
        COMPARISON_CLOSURE_CONTRACT_ID, 1,
        (RequirementSlotDefinition(
            "closure", frozenset((COMPARISON_CLOSURE_PROOF_KIND,))
        ),),
        requirement_slot("closure"),
    ),
))


class ComparisonClosurePilotEncoder:
    def __init__(self) -> None:
        self._cause_factory = SemanticCauseIdentityFactory(
            COMPARISON_CLOSURE_REASON_REGISTRY
        )
        self._binding_factory = SatisfactionBindingFactory(
            COMPARISON_CLOSURE_RECOVERY_REGISTRY
        )

    def __call__(
        self, session: Any, signal: ComparisonClosureProductionSignal,
    ) -> tuple[EventIntent, ...]:
        if type(signal) is not ComparisonClosureProductionSignal:
            raise TypeError("comparison closure encoder requires an exact signal")
        target = (
            "comparison_execution_receipt_v1", signal.comparison_receipt_id,
            signal.terminal_receipt_digest, signal.branch_id,
            signal.runtime_premise_digest, signal.runtime_view_id,
            signal.query_receipt_digests,
        )
        cause = self._cause_factory.create(
            reason_id=COMPARISON_CLOSURE_REASON_ID,
            identity_scope=IdentityScope.RELATIONAL,
            target_kind="comparison_execution_receipt",
            canonical_target_key=target,
            missing_semantic_fact=("decisive_comparison_closure", signal.branch_id),
            semantic_proposition=("comparison_is_decisive", signal.comparison_receipt_id),
            observation_surface=(
                signal.runtime_view_id, signal.runtime_premise_digest,
                signal.query_receipt_digests,
            ),
            active_semantic_precondition=(
                "inconclusive_terminal_receipt", signal.terminal_receipt_digest,
            ),
            correspondence_contract=None,
        )
        requirement = ProofRequirement(
            "comparison-closure-q-" + authority_digest(target)[:32],
            COMPARISON_CLOSURE_PROOF_KIND, target,
        )
        bound = self._binding_factory.bind(
            contract_definition_id=COMPARISON_CLOSURE_CONTRACT_ID,
            contract_version=1, bindings={"closure": requirement},
        )
        occurrence = CauseOccurrence(
            "comparison-closure-occ-" + authority_digest({
                "result_occurrence_id": session.identity.result_occurrence_id,
                "target": target,
            })[:32],
            cause, COMPARISON_CLOSURE_REASON_ID, authority_digest(target),
            "comparison_execution_receipt", IdentityScope.RELATIONAL,
            bound.contract_definition_id, bound.contract_version,
            bound.normalized_expression_digest, bound.bound_expression_digest,
            (requirement.requirement_id,),
            (signal.terminal_receipt_digest, *signal.query_receipt_digests),
            "comparison_closure_producer_signal",
            session.identity.source_snapshot_fingerprint, signal.producer_id,
            session.identity.execution_identity_digest,
        )
        return (EventIntent(
            EventType.CAUSE_OBSERVED,
            CauseObservedEventAuthority(CauseOccurrenceAuthority(occurrence, bound)),
        ),)


@dataclass(frozen=True)
class OutcomePartitionProductionSignal:
    stage: str
    producer_status: str
    proof_requirement_identity: Mapping[str, Any]
    function_identity: Any
    outcome_seed_digest: str
    producer_evidence: Mapping[str, Any]
    outcome_seed_revision: Optional[int] = None
    function_snapshot_fingerprint: Optional[str] = None
    premise_digest: Optional[str] = None
    producer_attempt_identity: Optional[str] = None
    producer_attempt_ordinal: Optional[int] = None
    execution_identity_digest: Optional[str] = None
    execution_receipts: tuple[Any, ...] = ()
    witness_artifact: Optional[Any] = None
    validated_artifact_authority: Optional[Mapping[str, Any]] = None

    def _phase7_signal_authority(self) -> Mapping[str, Any]:
        """Project only semantic signal data into Phase 7 authority."""

        from scripts.function_tracer_pcode.authority.domains.return_outcome import (
            OutcomeStageExecutionReceipt,
            UnaryOutcomeWitnessArtifact,
        )

        receipt_authority = []
        for receipt in self.execution_receipts:
            if type(receipt) is not OutcomeStageExecutionReceipt:
                raise TypeError(
                    "outcome partition signal contains a non-receipt authority"
                )
            receipt_authority.append(receipt.to_authority_dict())
        witness_authority = None
        if self.witness_artifact is not None:
            if type(self.witness_artifact) is not UnaryOutcomeWitnessArtifact:
                raise TypeError(
                    "outcome partition signal contains a non-witness authority"
                )
            witness_authority = self.witness_artifact.to_authority_dict()
        return {
            "stage": self.stage,
            "producer_status": self.producer_status,
            "proof_requirement_identity": self.proof_requirement_identity,
            "function_identity": self.function_identity,
            "outcome_seed_digest": self.outcome_seed_digest,
            "producer_evidence": self.producer_evidence,
            "outcome_seed_revision": self.outcome_seed_revision,
            "function_snapshot_fingerprint": self.function_snapshot_fingerprint,
            "premise_digest": self.premise_digest,
            "producer_attempt_identity": self.producer_attempt_identity,
            "producer_attempt_ordinal": self.producer_attempt_ordinal,
            "execution_identity_digest": self.execution_identity_digest,
            "execution_receipts": tuple(receipt_authority),
            "witness_artifact": witness_authority,
            "validated_artifact_authority": self.validated_artifact_authority,
        }

    def __post_init__(self) -> None:
        if type(self.stage) is not str or not self.stage:
            raise TypeError("outcome partition signal stage must be a non-empty string")
        if type(self.producer_status) is not str or not self.producer_status:
            raise TypeError("outcome partition signal status must be a non-empty string")
        canonical_value(self.proof_requirement_identity)
        canonical_value(self.function_identity)
        canonical_value(self.producer_evidence)
        object.__setattr__(self, "execution_receipts", tuple(self.execution_receipts))
        if self.validated_artifact_authority is not None:
            canonical_value(self.validated_artifact_authority)
        if self.outcome_seed_revision is not None and (
            type(self.outcome_seed_revision) is not int
            or self.outcome_seed_revision < 0
        ):
            raise TypeError("outcome partition signal seed revision is invalid")
        for value in (self.function_snapshot_fingerprint, self.premise_digest):
            if value is not None and (type(value) is not str or not value):
                raise TypeError("outcome partition signal authority is incomplete")
        if self.producer_attempt_identity is not None and (
            type(self.producer_attempt_identity) is not str
            or not self.producer_attempt_identity
        ):
            raise TypeError("outcome producer attempt identity is invalid")
        if self.execution_identity_digest is not None and (
            type(self.execution_identity_digest) is not str
            or not self.execution_identity_digest
        ):
            raise TypeError("outcome producer execution identity is invalid")
        if self.producer_attempt_ordinal is not None and (
            type(self.producer_attempt_ordinal) is not int
            or self.producer_attempt_ordinal <= 0
        ):
            raise TypeError("outcome producer attempt ordinal is invalid")
        if type(self.outcome_seed_digest) is not str or not self.outcome_seed_digest:
            raise TypeError("outcome partition signal seed digest must be non-empty")
        # Validate the complete public projection at construction time.  Private
        # factory tokens never enter this projection or its digest.
        authority_digest(self._phase7_signal_authority())


SAT_SAFETY_TYPED_REASON_IDS = frozenset({
    "counterexample_analysis_safety_unproven",
    "counterexample_partition_replay_ambiguous",
    "counterexample_replay_unproven",
})


_SAFE_COUNTEREXAMPLE_SIGNAL_TOKEN = object()


@dataclass(frozen=True)
class SatCounterexampleEvidenceBinding:
    formula_digest: str
    model_digest: str
    premise_digest: str
    pair_key: tuple[Any, Any]

    def __post_init__(self) -> None:
        for value in (
            self.formula_digest,
            self.model_digest,
            self.premise_digest,
        ):
            if type(value) is not str or not value:
                raise TypeError("SAT counterexample binding authority is incomplete")
        if type(self.pair_key) is not tuple or len(self.pair_key) != 2:
            raise TypeError("SAT counterexample binding pair key is invalid")
        try:
            object.__setattr__(self, "pair_key", canonical_value(self.pair_key))
        except (TypeError, ValueError) as exc:
            raise TypeError("SAT counterexample binding pair key is invalid") from exc


@dataclass(frozen=True)
class SatSafetyBlockerProductionSignal:
    action: str
    reason_id: str
    canonical_target_key: Any
    missing_semantic_fact: Any
    evidence_refs: tuple[str, ...]
    producer_id: str
    proof_artifact_digest: Optional[str] = None
    counterexample_binding: Optional[SatCounterexampleEvidenceBinding] = None
    defer_until_terminal: bool = False

    def __post_init__(self) -> None:
        if self.action not in {"OBSERVED", "COMPLETED"}:
            raise ValueError("SAT safety blocker signal action is invalid")
        if self.reason_id not in SAT_SAFETY_TYPED_REASON_IDS:
            raise ValueError("SAT safety blocker signal reason is not sealed")
        if type(self.producer_id) is not str or not self.producer_id:
            raise TypeError("SAT safety blocker producer identity is incomplete")
        object.__setattr__(self, "canonical_target_key", canonical_value(self.canonical_target_key))
        object.__setattr__(self, "missing_semantic_fact", canonical_value(self.missing_semantic_fact))
        object.__setattr__(self, "evidence_refs", tuple(self.evidence_refs))
        if any(type(item) is not str or not item for item in self.evidence_refs):
            raise TypeError("SAT safety evidence references must be exact strings")
        if self.action == "COMPLETED" and not self.proof_artifact_digest:
            raise ValueError("SAT safety completion lacks proof artifact authority")
        if (
            self.counterexample_binding is not None
            and type(self.counterexample_binding) is not SatCounterexampleEvidenceBinding
        ):
            raise TypeError("SAT safety counterexample binding is invalid")
        if type(self.defer_until_terminal) is not bool:
            raise TypeError("SAT safety deferral marker is invalid")
        if self.defer_until_terminal and self.action != "OBSERVED":
            raise ValueError("only SAT safety observations may be deferred")


@dataclass(frozen=True, init=False)
class SafeCounterexampleProductionSignal:
    proof_artifact_digest: str
    formula_digest: str
    model_digest: str
    premise_digest: str
    pair_key: tuple[Any, Any]
    receipt_kind: str
    safety_receipt: Any = field(repr=False, compare=False)
    verification_context: tuple[Any, ...] = field(repr=False, compare=False)

    def __init__(self, **values: Any) -> None:
        if values.pop("_factory_token", None) is not _SAFE_COUNTEREXAMPLE_SIGNAL_TOKEN:
            raise TypeError(
                "safe counterexample signal must be issued from a typed safety receipt"
            )
        for name in (
            "proof_artifact_digest", "formula_digest", "model_digest",
            "premise_digest", "pair_key", "receipt_kind", "safety_receipt",
            "verification_context",
        ):
            object.__setattr__(self, name, values.pop(name))
        if values:
            raise TypeError("safe counterexample signal fields are not sealed")
        object.__setattr__(self, "pair_key", canonical_value(self.pair_key))
        object.__setattr__(
            self, "verification_context", tuple(self.verification_context)
        )
        if not self.validates():
            raise ValueError("safe counterexample typed receipt validation failed")

    @classmethod
    def from_pairwise_receipt(cls, receipt: Any):
        from scripts.function_tracer_pcode.proof.obligations.pair_disposition import (
            CounterexampleSafetyReceipt,
        )

        if (
            type(receipt) is not CounterexampleSafetyReceipt
            or not receipt.validates_authority()
        ):
            raise ValueError("pairwise counterexample safety receipt is invalid")
        return cls(
            proof_artifact_digest=receipt.authority_digest,
            formula_digest=receipt.formula_digest,
            model_digest=receipt.model_digest,
            premise_digest=receipt.premise_digest,
            pair_key=receipt.pair_key,
            receipt_kind="pairwise_counterexample_safety_receipt_v1",
            safety_receipt=receipt,
            verification_context=(),
            _factory_token=_SAFE_COUNTEREXAMPLE_SIGNAL_TOKEN,
        )

    @classmethod
    def from_monolithic_receipt(cls, terminal_receipt: Any):
        from scripts.function_tracer_pcode.proof.monolithic_authority import (
            CounterexampleSafetyDecisionReceipt,
            MonolithicTerminalDecisionReceipt,
        )

        if (
            type(terminal_receipt) is not MonolithicTerminalDecisionReceipt
            or terminal_receipt.outcome_kind != "decisive_counterexample"
            or not terminal_receipt.validates()
        ):
            raise ValueError("monolithic terminal counterexample receipt is invalid")
        receipt = terminal_receipt.counterexample_safety_receipt
        if type(receipt) is not CounterexampleSafetyDecisionReceipt:
            raise ValueError("monolithic terminal safety receipt is invalid")
        replay_contract = receipt.legacy_replay_receipt.contract
        return cls(
            proof_artifact_digest=terminal_receipt.receipt_digest,
            formula_digest=replay_contract.formula_digest,
            model_digest=receipt.model_digest,
            premise_digest=replay_contract.contract_digest,
            pair_key=("monolithic", terminal_receipt.sat_region_id),
            receipt_kind="monolithic_terminal_counterexample_receipt_v1",
            safety_receipt=receipt,
            verification_context=(terminal_receipt,),
            _factory_token=_SAFE_COUNTEREXAMPLE_SIGNAL_TOKEN,
        )

    def validates(self) -> bool:
        if type(self.pair_key) is not tuple or len(self.pair_key) != 2:
            return False
        if any(
            type(value) is not str or not value
            for value in (
                self.proof_artifact_digest, self.formula_digest,
                self.model_digest, self.premise_digest,
            )
        ):
            return False
        if self.receipt_kind == "pairwise_counterexample_safety_receipt_v1":
            from scripts.function_tracer_pcode.proof.obligations.pair_disposition import (
                CounterexampleSafetyReceipt,
            )

            receipt = self.safety_receipt
            return bool(
                type(receipt) is CounterexampleSafetyReceipt
                and self.verification_context == ()
                and receipt.validates_authority()
                and self.proof_artifact_digest == receipt.authority_digest
                and self.formula_digest == receipt.formula_digest
                and self.model_digest == receipt.model_digest
                and self.premise_digest == receipt.premise_digest
                and self.pair_key == canonical_value(receipt.pair_key)
            )
        if self.receipt_kind == "monolithic_terminal_counterexample_receipt_v1":
            from scripts.function_tracer_pcode.proof.monolithic_authority import (
                CounterexampleSafetyDecisionReceipt,
                MonolithicTerminalDecisionReceipt,
            )

            if len(self.verification_context) != 1:
                return False
            receipt = self.safety_receipt
            terminal_receipt = self.verification_context[0]
            if (
                type(receipt) is not CounterexampleSafetyDecisionReceipt
                or type(terminal_receipt) is not MonolithicTerminalDecisionReceipt
                or terminal_receipt.outcome_kind != "decisive_counterexample"
                or not terminal_receipt.validates()
                or terminal_receipt.counterexample_safety_receipt is not receipt
            ):
                return False
            replay_contract = receipt.legacy_replay_receipt.contract
            return bool(
                self.proof_artifact_digest == terminal_receipt.receipt_digest
                and self.formula_digest == replay_contract.formula_digest
                and self.model_digest == receipt.model_digest
                and self.premise_digest == replay_contract.contract_digest
                and self.pair_key == canonical_value(
                    ("monolithic", terminal_receipt.sat_region_id)
                )
            )
        return False

    @property
    def counterexample_binding(self) -> SatCounterexampleEvidenceBinding:
        return SatCounterexampleEvidenceBinding(
            self.formula_digest,
            self.model_digest,
            self.premise_digest,
            self.pair_key,
        )

    def _phase7_signal_authority(self) -> Mapping[str, Any]:
        """Project only receipt-verified identities into the runtime digest."""
        if not self.validates():
            raise ValueError("safe counterexample signal authority is invalid")
        return {
            "proof_artifact_digest": self.proof_artifact_digest,
            "formula_digest": self.formula_digest,
            "model_digest": self.model_digest,
            "premise_digest": self.premise_digest,
            "pair_key": self.pair_key,
            "receipt_kind": self.receipt_kind,
        }


_PENDING_EQ_CLOSURE_TOKEN = object()
_POST_CLEANUP_EQ_RECEIPT_TOKEN = object()


@dataclass(frozen=True, init=False)
class PostCleanupEqClosureReceipt:
    """Immutable factory receipt replacing a live dispatch-frame reference."""

    result_occurrence_id: str
    execution_identity_digest: str
    comparison_receipt_id: str
    comparison_receipt_authority_digest: str
    comparison_session_id: str
    branch_id: str
    generation: int
    runtime_view_id: str
    runtime_premise_digest: str
    post_cleanup_binding_digest: str
    receipt_digest: str

    def __init__(self, *, _token: object, **values: Any) -> None:
        if _token is not _POST_CLEANUP_EQ_RECEIPT_TOKEN:
            raise TypeError("post-cleanup EQ receipt requires its factory")
        supplied = values.pop("receipt_digest", None)
        for name, value in values.items():
            object.__setattr__(self, name, value)
        digest = authority_digest(values)
        if supplied is not None and supplied != digest:
            raise ValueError("post-cleanup EQ receipt digest mismatch")
        object.__setattr__(self, "receipt_digest", digest)
        self.validate()

    def validate(self) -> None:
        values = {
            name: getattr(self, name) for name in self.__dataclass_fields__
            if name != "receipt_digest"
        }
        if (
            authority_digest(values) != self.receipt_digest
            or self.generation < 0
            or any(
                type(value) is not str or not value
                for name, value in values.items() if name != "generation"
            )
        ):
            raise ValueError("post-cleanup EQ receipt is invalid")


@dataclass(frozen=True, init=False)
class PendingEqClosureAuthority:
    result_occurrence_id: str
    execution_identity_digest: str
    comparison_receipt_id: str
    comparison_receipt_authority_digest: str
    comparison_session_id: str
    branch_id: str
    generation: int
    dispatch_frame_authority_digest: str
    runtime_view_id: str
    runtime_premise_digest: str
    post_cleanup_binding_digest: str
    post_cleanup_receipt_digest: str
    proof_artifact_digest: str
    authority_nonce: str
    receipt_digest: str

    def __init__(self, *, _token: object, **values: Any) -> None:
        if _token is not _PENDING_EQ_CLOSURE_TOKEN:
            raise TypeError("pending EQ authority requires its verifier-owned issuer")
        supplied = values.pop("receipt_digest", None)
        for name, value in values.items():
            object.__setattr__(self, name, value)
        digest = authority_digest(values)
        if supplied is not None and supplied != digest:
            raise ValueError("pending EQ authority digest mismatch")
        object.__setattr__(self, "receipt_digest", digest)

    def validate(self) -> None:
        values = {
            name: getattr(self, name)
            for name in self.__dataclass_fields__
            if name != "receipt_digest"
        }
        if (
            authority_digest(values) != self.receipt_digest
            or self.generation < 0
            or any(
                type(value) is not str or not value
                for name, value in values.items()
                if name != "generation"
            )
        ):
            raise ValueError("pending EQ authority is invalid")


@dataclass(frozen=True)
class PendingEqTransitionReceipt:
    pending_receipt_digest: str
    action: str
    lifecycle_projection_digest: str
    terminal_candidate_view_digest: str
    receipt_digest: str

    @classmethod
    def create(
        cls, pending: PendingEqClosureAuthority, *, action: str,
        lifecycle_projection_digest: str, terminal_candidate_view_digest: str,
    ) -> "PendingEqTransitionReceipt":
        if action not in {"CONSUMED", "DISCARDED"}:
            raise ValueError("pending EQ transition action is invalid")
        payload = {
            "pending_receipt_digest": pending.receipt_digest,
            "action": action,
            "lifecycle_projection_digest": lifecycle_projection_digest,
            "terminal_candidate_view_digest": terminal_candidate_view_digest,
        }
        return cls(*payload.values(), authority_digest(payload))


def _pending_eq_post_cleanup_binding(dispatch_frame: Any) -> dict[str, Any]:
    """Freeze the exact mutable authority surface consumed by EQ closure."""

    runtime = getattr(dispatch_frame, "obligation_runtime", None)
    view_id = str(getattr(getattr(runtime, "current_view", None), "view_id", ""))
    premise_digest = str(getattr(runtime, "premise_digest", ""))
    successor_plan = getattr(dispatch_frame, "replan_successor_plan", None)
    successor_ledger = getattr(dispatch_frame, "replan_successor_ledger", None)
    pair_ledger = getattr(dispatch_frame, "pair_disposition_ledger", None)
    return {
        "comparison_session_id": dispatch_frame.comparison_session_id,
        "branch_id": dispatch_frame.branch_id,
        "generation": dispatch_frame.generation,
        "dispatch_nonce": dispatch_frame.dispatch_nonce,
        "prepared_surface_digest": dispatch_frame.prepared.surface_digest,
        "projection_id": dispatch_frame.projection.projection_id,
        "cleanup_complete": bool(dispatch_frame.cleanup_complete),
        "lifecycle_state": str(dispatch_frame.lifecycle_state),
        "runtime_view_id": view_id,
        "runtime_premise_digest": premise_digest,
        "successor_ledger_reused": bool(dispatch_frame.successor_ledger_reused),
        "successor_plan_key": (
            successor_plan.stable_key() if successor_plan is not None else None
        ),
        "successor_ledger_is_pair_ledger": (
            successor_ledger is pair_ledger if successor_plan is not None else True
        ),
        "pair_ledger_binding_key": (
            pair_ledger.binding.stable_key() if pair_ledger is not None else None
        ),
        "pair_ledger_expected_pairs": (
            int(pair_ledger.expected_pairs) if pair_ledger is not None else None
        ),
    }


def issue_pending_eq_closure_authority(
    session: Any, comparison_receipt: Any, dispatch_frame: Any,
) -> PendingEqClosureAuthority:
    """Seal immutable comparison authority for post-proof-DAG EQ promotion."""

    if getattr(dispatch_frame, "receipt", None) is not comparison_receipt:
        raise ValueError("pending EQ receipt is not the dispatch-frame receipt")
    authority = comparison_receipt_authority(comparison_receipt, dispatch_frame)
    if authority is None or not comparison_receipt.is_trusted_for(dispatch_frame):
        raise ValueError("pending EQ comparison receipt is not trusted")
    if authority[2] is not session:
        raise ValueError("pending EQ receipt belongs to another production session")
    if not bool(getattr(dispatch_frame, "cleanup_complete", False)):
        raise ValueError("pending EQ requires a post-cleanup dispatch frame")
    runtime = getattr(dispatch_frame, "obligation_runtime", None)
    runtime_view_id = str(getattr(getattr(runtime, "current_view", None), "view_id", ""))
    runtime_premise_digest = str(getattr(runtime, "premise_digest", ""))
    if not runtime_view_id or not runtime_premise_digest:
        raise ValueError("pending EQ lacks terminal runtime authority")
    receipt_authority_digest = authority_digest(comparison_receipt)
    post_cleanup_binding = _pending_eq_post_cleanup_binding(dispatch_frame)
    frame_digest = authority_digest(post_cleanup_binding)
    post_cleanup_receipt = PostCleanupEqClosureReceipt(
        result_occurrence_id=session.identity.result_occurrence_id,
        execution_identity_digest=session.identity.execution_identity_digest,
        comparison_receipt_id=comparison_receipt.receipt_id,
        comparison_receipt_authority_digest=receipt_authority_digest,
        comparison_session_id=dispatch_frame.comparison_session_id,
        branch_id=dispatch_frame.branch_id,
        generation=dispatch_frame.generation,
        runtime_view_id=runtime_view_id,
        runtime_premise_digest=runtime_premise_digest,
        post_cleanup_binding_digest=frame_digest,
        _token=_POST_CLEANUP_EQ_RECEIPT_TOKEN,
    )
    proof_digest = authority_digest({
        "comparison_receipt_authority_digest": receipt_authority_digest,
        "post_cleanup_receipt_digest": post_cleanup_receipt.receipt_digest,
        "result_occurrence_id": session.identity.result_occurrence_id,
        "execution_identity_digest": session.identity.execution_identity_digest,
    })
    pending = PendingEqClosureAuthority(
        result_occurrence_id=session.identity.result_occurrence_id,
        execution_identity_digest=session.identity.execution_identity_digest,
        comparison_receipt_id=comparison_receipt.receipt_id,
        comparison_receipt_authority_digest=receipt_authority_digest,
        comparison_session_id=dispatch_frame.comparison_session_id,
        branch_id=dispatch_frame.branch_id,
        generation=dispatch_frame.generation,
        dispatch_frame_authority_digest=frame_digest,
        runtime_view_id=runtime_view_id,
        runtime_premise_digest=runtime_premise_digest,
        post_cleanup_binding_digest=frame_digest,
        post_cleanup_receipt_digest=post_cleanup_receipt.receipt_digest,
        proof_artifact_digest=proof_digest,
        authority_nonce=secrets.token_hex(24),
        _token=_PENDING_EQ_CLOSURE_TOKEN,
    )
    pending.validate()
    ledger = session.domain_signal_state.setdefault("pending_eq_authorities", {})
    if ledger:
        raise ValueError("production result already owns a pending EQ authority")
    ledger[pending.authority_nonce] = {
        "authority": pending,
        "post_cleanup_receipt": post_cleanup_receipt,
        "state": "PENDING",
    }
    return pending


def finalize_pending_eq_authorities(
    session: Any, lifecycle_projection: Any, terminal_candidate_view: Any,
) -> tuple[EventIntent, ...]:
    """Consume or neutrally discard every one-shot pending EQ capability."""

    ledger = session.domain_signal_state.setdefault("pending_eq_authorities", {})
    intents = []
    transitions = session.domain_signal_state.setdefault(
        "pending_eq_transition_receipts", []
    )
    for nonce, entry in tuple(sorted(ledger.items())):
        pending = entry.get("authority")
        if (
            entry.get("state") != "PENDING"
            or type(pending) is not PendingEqClosureAuthority
            or pending.authority_nonce != nonce
        ):
            raise ValueError("pending EQ ledger contains invalid authority state")
        pending.validate()
        if (
            pending.result_occurrence_id != session.identity.result_occurrence_id
            or pending.execution_identity_digest
            != session.identity.execution_identity_digest
        ):
            raise ValueError("pending EQ execution identity changed")
        post_cleanup_receipt = entry.get("post_cleanup_receipt")
        if (
            type(post_cleanup_receipt) is not PostCleanupEqClosureReceipt
            or post_cleanup_receipt.receipt_digest
            != pending.post_cleanup_receipt_digest
            or post_cleanup_receipt.result_occurrence_id
            != pending.result_occurrence_id
            or post_cleanup_receipt.execution_identity_digest
            != pending.execution_identity_digest
            or post_cleanup_receipt.comparison_receipt_id
            != pending.comparison_receipt_id
            or post_cleanup_receipt.comparison_receipt_authority_digest
            != pending.comparison_receipt_authority_digest
            or post_cleanup_receipt.comparison_session_id
            != pending.comparison_session_id
            or post_cleanup_receipt.branch_id != pending.branch_id
            or post_cleanup_receipt.generation != pending.generation
            or post_cleanup_receipt.runtime_view_id != pending.runtime_view_id
            or post_cleanup_receipt.runtime_premise_digest
            != pending.runtime_premise_digest
            or post_cleanup_receipt.post_cleanup_binding_digest
            != pending.post_cleanup_binding_digest
        ):
            raise ValueError("pending EQ post-cleanup authority no longer validates")
        post_cleanup_receipt.validate()
        blocks_eq = any(
            row.decision_effect in {"blocks_equivalence", "blocks_decision"}
            for row in lifecycle_projection.c_active_base
        )
        competing = bool(
            terminal_candidate_view.timeout_candidates
            or terminal_candidate_view.counterexample_event_digests
            or terminal_candidate_view.error_event_digests
            or terminal_candidate_view.competing_decisive_event_digests
        )
        action = "DISCARDED" if blocks_eq or competing else "CONSUMED"
        transitions.append(PendingEqTransitionReceipt.create(
            pending,
            action=action,
            lifecycle_projection_digest=(
                getattr(lifecycle_projection, "lifecycle_projection_digest", None)
                or lifecycle_projection.prefix_projection_digest
            ),
            terminal_candidate_view_digest=terminal_candidate_view.view_digest,
        ))
        entry["state"] = action
        if action == "CONSUMED":
            intents.append(EventIntent(
                EventType.EQ_CLOSURE,
                DecisiveProofEventAuthority(pending.proof_artifact_digest),
            ))
    return tuple(intents)


_CALL_EFFECT_BLOCKER_SIGNAL_TOKEN = object()


@dataclass(frozen=True, init=False)
class CallEffectBlockerProductionSignal:
    """Object-derived relational blocker input; reason is registry-classified."""

    source_contract: str
    failure_code: str
    obligation_id: str
    observation_contract_id: str
    left_fact_id: Optional[str]
    right_fact_id: Optional[str]
    semantic_arm: str
    structural_certificate_id: str
    producer_id: str
    effect_stage_required: bool

    def __init__(
        self,
        source_contract: str,
        failure_code: str,
        obligation_id: str,
        observation_contract_id: str,
        left_fact_id: str,
        right_fact_id: str,
        semantic_arm: str,
        structural_certificate_id: str,
        producer_id: str,
        effect_stage_required: bool = False,
        *,
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _CALL_EFFECT_BLOCKER_SIGNAL_TOKEN:
            raise TypeError("call/effect blocker signal must be proof-input factory issued")
        for name, value in (
            ("source_contract", source_contract),
            ("failure_code", failure_code),
            ("obligation_id", obligation_id),
            ("observation_contract_id", observation_contract_id),
            ("left_fact_id", left_fact_id),
            ("right_fact_id", right_fact_id),
            ("semantic_arm", semantic_arm),
            ("structural_certificate_id", structural_certificate_id),
            ("producer_id", producer_id),
            ("effect_stage_required", effect_stage_required),
        ):
            object.__setattr__(self, name, value)
        for value in (
            self.source_contract, self.failure_code, self.obligation_id,
            self.observation_contract_id, self.left_fact_id, self.right_fact_id,
            self.semantic_arm, self.structural_certificate_id, self.producer_id,
        ):
            if type(value) is not str or not value:
                raise TypeError("call/effect blocker signal identity is incomplete")
        if self.semantic_arm not in {
            "inline_region_semantic_proof", "callee_summary_semantic_proof"
        }:
            raise ValueError("call/effect blocker semantic arm is not sealed")
        if type(self.effect_stage_required) is not bool:
            raise TypeError("call/effect effect-stage predicate must be exact bool")

    def _phase7_signal_authority(self) -> Mapping[str, Any]:
        return {
            name: getattr(self, name)
            for name in self.__dataclass_fields__
        }

    @classmethod
    def from_proof_input(cls, proof_input: Any) -> "CallEffectBlockerProductionSignal":
        from scripts.function_tracer_pcode.proof.call_effect.proof_input import (
            CALL_EFFECT_PRODUCER_KIND,
            PureCallRegionProofInput,
            PureDirectCallProofInput,
        )

        if type(proof_input) is PureCallRegionProofInput:
            semantic_arm = "inline_region_semantic_proof"
        elif type(proof_input) is PureDirectCallProofInput:
            semantic_arm = "callee_summary_semantic_proof"
        else:
            raise TypeError("call/effect blocker membership requires exact typed proof input")
        memory_stage_required = (
            bool(proof_input.region_effects or proof_input.call_effect.memory_effects)
            if type(proof_input) is PureCallRegionProofInput
            else bool(
                proof_input.left_effect.memory_effects
                or proof_input.right_effect.memory_effects
            )
        )
        caller_memory_stage_required = bool(
            proof_input.left_caller_effects
            or proof_input.right_caller_effects
            or int(getattr(proof_input.left_caller_profile, "store_count", 0) or 0)
            or int(getattr(proof_input.right_caller_profile, "store_count", 0) or 0)
            or any(
                int(getattr(evidence, "memory_effect_count", 0) or 0) > 0
                for evidence in (
                    *proof_input.left_caller_call_effects,
                    *proof_input.right_caller_call_effects,
                )
            )
        )
        return cls(
            "primary_proof_stage",
            "relational_call_effect_stage_proofs_missing",
            proof_input.obligation_id,
            proof_input.observation_contract_id,
            proof_input.left_fact_id,
            proof_input.right_fact_id,
            semantic_arm,
            proof_input.structural_certificate_id,
            CALL_EFFECT_PRODUCER_KIND,
            memory_stage_required or caller_memory_stage_required,
            _factory_token=_CALL_EFFECT_BLOCKER_SIGNAL_TOKEN,
        )


@dataclass(frozen=True)
class CallEffectProofBatchProductionSignal:
    blocker: CallEffectBlockerProductionSignal
    artifacts: tuple[Any, ...]
    producer_id: str = CALL_EFFECT_PROOF_BATCH_SITE.producer_id

    def __post_init__(self) -> None:
        if type(self.blocker) is not CallEffectBlockerProductionSignal:
            raise TypeError("call/effect proof batch lacks exact blocker signal")
        object.__setattr__(self, "artifacts", tuple(self.artifacts))
        if not self.artifacts:
            raise ValueError("call/effect proof batch cannot be empty")
        if self.producer_id != CALL_EFFECT_PROOF_BATCH_SITE.producer_id:
            raise ValueError("call/effect proof batch producer is not sealed")

    def _phase7_signal_authority(self) -> Mapping[str, Any]:
        return {
            "blocker": self.blocker._phase7_signal_authority(),
            "proof_records": tuple(
                artifact.record.to_dict() for artifact in self.artifacts
            ),
            "producer_id": self.producer_id,
        }


@dataclass(frozen=True)
class CallEffectPrerequisiteProductionSignal:
    """Object-derived blocker for an ineligible relational call obligation."""

    obligation_id: str
    observation_contract_id: str
    left_fact_id: str
    right_fact_id: str
    structural_certificate_id: str
    eligibility_blockers: tuple[str, ...]
    reason_id: str = "callsite_correspondence_unproven"
    producer_id: str = "internal_typed_pure_direct_call_stage_producer"

    def __post_init__(self) -> None:
        object.__setattr__(
            self, "eligibility_blockers", tuple(self.eligibility_blockers)
        )
        for value in (
            self.obligation_id,
            self.observation_contract_id,
            self.structural_certificate_id,
            self.reason_id,
            self.producer_id,
        ):
            if type(value) is not str or not value:
                raise TypeError("call/effect prerequisite identity is incomplete")
        if (
            self.left_fact_id is not None
            and (type(self.left_fact_id) is not str or not self.left_fact_id)
        ) or (
            self.right_fact_id is not None
            and (type(self.right_fact_id) is not str or not self.right_fact_id)
        ) or (self.left_fact_id is None and self.right_fact_id is None):
            raise TypeError("call/effect prerequisite endpoints are incomplete")
        if not self.eligibility_blockers:
            raise ValueError("call/effect prerequisite blocker set is empty")
        if any(type(blocker) is not str or not blocker
               for blocker in self.eligibility_blockers):
            raise TypeError("call/effect prerequisite blocker is invalid")

    def _phase7_signal_authority(self) -> Mapping[str, Any]:
        return {
            name: getattr(self, name)
            for name in self.__dataclass_fields__
        }


class CompositeProductionSignalEncoder:
    """Exact-type router; an unregistered producer signal fails closed."""

    def __init__(self, routes: Mapping[type, Callable[[Any, Any], Any]]) -> None:
        if not routes or any(type(key) is not type or not callable(value) for key, value in routes.items()):
            raise TypeError("production signal routes must map exact types to encoders")
        self._routes = dict(routes)

    def __call__(self, session: Any, signal: Any) -> Any:
        encoder = self._routes.get(type(signal))
        if encoder is None:
            raise TypeError("production signal type has no registered encoder")
        return encoder(session, signal)

    def commit_emitted_signal(
        self, session: Any, signal: Any, intents: tuple[EventIntent, ...]
    ) -> None:
        encoder = self._routes.get(type(signal))
        committer = getattr(encoder, "commit_emitted_signal", None)
        if callable(committer):
            committer(session, signal, intents)

    def rollback_emitted_signal(self, session: Any, signal: Any) -> None:
        encoder = self._routes.get(type(signal))
        rollback = getattr(encoder, "rollback_emitted_signal", None)
        if callable(rollback):
            rollback(session, signal)

    def is_committed_signal_replay(
        self, session: Any, signal: Any, intents: tuple[EventIntent, ...] = ()
    ) -> bool:
        """Delegate transaction replay probes to the exact signal owner."""

        encoder = self._routes.get(type(signal))
        if encoder is None:
            raise TypeError("production signal type has no registered encoder")
        probe = getattr(encoder, "is_committed_signal_replay", None)
        return bool(probe(session, signal, intents)) if callable(probe) else False

    def supports_signal_replay(self, session: Any, signal: Any) -> bool:
        """Report whether the exact routed producer validates replay intents."""

        del session
        encoder = self._routes.get(type(signal))
        return callable(getattr(encoder, "is_committed_signal_replay", None))

    def accepts_signal_type(self, signal_type: type) -> bool:
        return type(signal_type) is type and signal_type in self._routes

    def operational_authority_factory_for_session(self, session: Any) -> Any:
        factories = []
        for encoder in {id(value): value for value in self._routes.values()}.values():
            resolver = getattr(encoder, "authority_factory_for_session", None)
            if callable(resolver):
                factories.append(resolver(session))
        if not factories:
            return None
        if len(factories) != 1:
            raise ValueError("operational authority factory route is not unique")
        return factories[0]

    def has_observed(self, session: Any, signal: Any) -> bool:
        """Delegate conditional completion checks to the exact routed encoder."""

        encoder = self._routes.get(type(signal))
        if encoder is None:
            raise TypeError("production signal type has no registered encoder")
        predicate = getattr(encoder, "has_observed", None)
        if not callable(predicate):
            return False
        return bool(predicate(session, signal))

    def authority_for_signal(self, session: Any, signal: Any) -> Any:
        """Resolve exact routed occurrence authority without emitting an event."""

        encoder = self._routes.get(type(signal))
        resolver = getattr(encoder, "authority_for_signal", None)
        if not callable(resolver):
            raise TypeError("production signal route lacks occurrence authority")
        return resolver(session, signal)

    def finalize_terminal_timeout_bindings(
        self, session: Any, stream: Any
    ) -> tuple[tuple[int, str], ...]:
        bindings = []
        encoders = tuple({id(value): value for value in self._routes.values()}.values())
        for encoder in encoders:
            resolver = getattr(encoder, "finalize_terminal_timeout_bindings", None)
            if callable(resolver):
                bindings.extend(resolver(session, stream))
        if len({sequence for sequence, _ in bindings}) != len(bindings):
            raise ValueError("duplicate production terminal timeout selection")
        ordered = tuple(sorted(bindings))
        session.domain_signal_state[
            "terminal_timeout_domain_candidate_bindings"
        ] = ordered
        if len(ordered) <= 1:
            return ordered
        events = {
            event.header.sequence_number: event for event in stream.events
        }
        candidates = []
        for sequence_number, requirement_id in ordered:
            event = events.get(sequence_number)
            if (
                event is None
                or event.authority_payload.proof_requirement_id != requirement_id
            ):
                raise ValueError(
                    "production terminal timeout selection is outside the source stream"
                )
            candidates.append((
                sequence_number,
                event.authority_digest,
                requirement_id,
            ))
        winner = max(candidates)
        return ((winner[0], winner[2]),)

    def finalize_open_execution_history(self, session: Any) -> None:
        encoders = tuple({id(value): value for value in self._routes.values()}.values())
        for encoder in encoders:
            finalizer = getattr(encoder, "finalize_open_execution_history", None)
            if callable(finalizer):
                finalizer(session)

    def validate_startup(self) -> tuple[Any, ...]:
        encoders = tuple({id(value): value for value in self._routes.values()}.values())
        receipts = {}
        for encoder in encoders:
            validator = getattr(encoder, "validate_startup", None)
            if callable(validator):
                receipt = validator()
                if receipt is not None:
                    digest = getattr(receipt, "receipt_digest", None)
                    if type(digest) is not str or not digest:
                        raise TypeError("production startup receipt lacks exact digest")
                    prior = receipts.setdefault(digest, receipt)
                    if prior != receipt:
                        raise ValueError("production startup receipt digest collided")
        return tuple(receipts[digest] for digest in sorted(receipts))

    def build_call_effect_execution_context(
        self, session: Any, signals: tuple[Any, ...], registry: Any
    ) -> Any:
        encoders = {
            self._routes.get(type(signal)) for signal in signals
        }
        encoders.discard(None)
        if len(encoders) != 1:
            raise ValueError("call/effect signals do not have one exact encoder")
        encoder = next(iter(encoders))
        builder = getattr(encoder, "build_execution_context", None)
        if not callable(builder):
            raise TypeError("call/effect encoder lacks execution-context authority")
        return builder(session, signals, registry)

    def loop_requirement_for_signal(
        self, session: Any, blocker: Any, proof_kind: str
    ) -> Any:
        encoder = self._routes.get(type(blocker))
        resolver = getattr(encoder, "requirement_for_signal", None)
        if not callable(resolver):
            raise TypeError("loop blocker route lacks requirement authority")
        return resolver(session, blocker, proof_kind)

    def build_loop_execution_context(
        self, session: Any, blocker: Any, queries: tuple[Any, ...]
    ) -> Any:
        encoder = self._routes.get(type(blocker))
        builder = getattr(encoder, "build_execution_context", None)
        if not callable(builder):
            raise TypeError("loop blocker route lacks execution-context authority")
        return builder(session, blocker, queries)

    def register_readonly_promotion(self, session: Any, seed: Any) -> None:
        from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
            AbiWidthReadonlyBlockerSignal,
        )

        encoder = self._routes.get(AbiWidthReadonlyBlockerSignal)
        registrar = getattr(encoder, "register_readonly_promotion", None)
        if not callable(registrar):
            raise TypeError("ABI/width route lacks readonly promotion authority")
        registrar(session, seed)

    def register_abi_width_solver_candidate(
        self, session: Any, blocker: Any, seed: Any
    ) -> None:
        from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
            AbiWidthReadonlyBlockerSignal,
        )

        encoder = self._routes.get(AbiWidthReadonlyBlockerSignal)
        registrar = getattr(encoder, "register_solver_candidate", None)
        if not callable(registrar):
            raise TypeError("ABI/width route lacks solver scheduler authority")
        registrar(session, blocker, seed)

    def register_void_effect_only_return_abi_seed(self, session: Any, seed: Any) -> None:
        from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
            AbiWidthReadonlyBlockerSignal,
        )

        encoder = self._routes.get(AbiWidthReadonlyBlockerSignal)
        registrar = getattr(encoder, "register_void_effect_only_return_abi_seed", None)
        if not callable(registrar):
            raise TypeError("ABI/width route lacks void effect-only ABI planning")
        registrar(session, seed)

    def register_return_observation_proof_plan(
        self, session: Any, projection_seed: Any, assessment: Any
    ) -> None:
        from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
            AbiWidthReadonlyBlockerSignal,
        )

        encoder = self._routes.get(AbiWidthReadonlyBlockerSignal)
        registrar = getattr(encoder, "register_return_observation_proof_plan", None)
        if not callable(registrar):
            raise TypeError("ABI/width route lacks return-observation proof planning")
        registrar(session, projection_seed, assessment)

    def prepare_sat_safety_transformation(
        self, session: Any, signal: Any,
    ) -> Any:
        encoder = self._routes.get(SatSafetyBlockerProductionSignal)
        resolver = getattr(encoder, "authority_for_signal", None)
        if not callable(resolver):
            raise TypeError("SAT safety route lacks occurrence authority")
        return resolver(session, signal)

    def commit_sat_safety_transformed_observation(
        self, session: Any, signal: Any,
    ) -> None:
        encoder = self._routes.get(SatSafetyBlockerProductionSignal)
        committer = getattr(encoder, "commit_transformed_observation", None)
        if not callable(committer):
            raise TypeError("SAT safety route lacks transformation registration")
        committer(session, signal)


def active_operational_authority_factory() -> Optional[Any]:
    session = active_production_pilot_session()
    if session is None:
        return None
    resolver = getattr(
        session.domain_signal_encoder,
        "operational_authority_factory_for_session",
        None,
    )
    if not callable(resolver):
        return None
    return resolver(session)


def record_production_pilot_shadow_error(exc: Exception) -> None:
    import traceback

    session = active_production_pilot_session()
    if session is not None:
        error_kinds = getattr(session, "domain_signal_error_kinds", None)
        if isinstance(error_kinds, list):
            error_kinds.append(type(exc).__name__)
        details = getattr(session, "domain_signal_error_details", None)
        if isinstance(details, list):
            frames = traceback.extract_tb(exc.__traceback__)
            selected_frames = (
                frames
                if len(frames) <= 8
                else frames[:6] + frames[-2:]
            )
            location = " <- ".join(
                f"{frame.filename}:{frame.lineno}:{frame.name}"
                for frame in selected_frames
            ) or "unknown-catch-site"
            details.append(f"{location}: {exc}")


def production_signal_scope(session: Any) -> Iterator[None]:
    return production_pilot_session_scope(session)


def emit_outcome_partition_signal(
    signal: OutcomePartitionProductionSignal,
    *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    """Return emitted event count; remain a strict no-op when pilot is disabled."""

    session = active_production_pilot_session()
    if session is None:
        return 0
    if getattr(session, "phase7_runtime", None) is not None:
        session.record_phase7_pre_emission_activation(
            producer_site_manifest_id, signal
        )
    emit = getattr(session, "emit_domain_signal", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks signal authority")
    return int(emit(signal))


def emit_comparison_closure_signal(
    signal: ComparisonClosureProductionSignal,
    *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    session = active_production_pilot_session()
    if session is None:
        return 0
    if getattr(session, "phase7_runtime", None) is not None:
        session.record_phase7_pre_emission_activation(
            producer_site_manifest_id, signal
        )
    emit = getattr(session, "emit_domain_signal", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks signal authority")
    return int(emit(signal))


def emit_identical_function_identity_signal(
    signal: IdenticalFunctionIdentitySignal,
    *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    """Issue #15: 同一バイナリ・同一関数の decisive proof を 1 回だけ出す。

    pilot が無効なら厳密に no-op（0）。`emit_comparison_closure_signal` と同型で、
    ここには判定も正規化も置かない（artifact の検証は encoder が行う）。
    """

    session = active_production_pilot_session()
    if session is None:
        return 0
    if getattr(session, "phase7_runtime", None) is not None:
        session.record_phase7_pre_emission_activation(
            producer_site_manifest_id, signal
        )
    emit = getattr(session, "emit_domain_signal", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks signal authority")
    return int(emit(signal))


def emit_analysis_limitation_signal(
    signal: AnalysisLimitationBlockerSignal,
    *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    """Return emitted event count; remain a strict no-op when pilot is disabled."""

    session = active_production_pilot_session()
    if session is None:
        return 0
    already_observed = getattr(session.domain_signal_encoder, "has_observed", None)
    if callable(already_observed) and already_observed(session, signal):
        # Re-observing the same limitation is not a new producer activation.  In
        # particular, do not open a Phase-7 discovery record which would
        # otherwise materialize the encoder's empty deduplication result.
        return 0
    if getattr(session, "phase7_runtime", None) is not None:
        session.record_phase7_pre_emission_activation(
            producer_site_manifest_id, signal
        )
    emit = getattr(session, "emit_domain_signal", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks signal authority")
    return int(emit(signal))


def emit_sat_safety_signal(
    signal: (
        SatSafetyBlockerProductionSignal
        | SafeCounterexampleProductionSignal
    ),
    *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    session = active_production_pilot_session()
    if session is None:
        return 0
    if type(signal) is SafeCounterexampleProductionSignal:
        if not signal.validates():
            raise ValueError("safe counterexample signal authority is invalid")
        if session.domain_signal_state.get(
            "sat_safety_safe_counterexample_committed"
        ):
            # A prior validated receipt already made NOT_EQ decisive.  Retry
            # phases may independently rediscover a counterexample, but must
            # not open a second Phase 7 activation for the encoder's no-op.
            return 0
    if (
        type(signal) is SatSafetyBlockerProductionSignal
        and signal.action == "OBSERVED"
    ):
        if signal.defer_until_terminal:
            pending = session.domain_signal_state.setdefault(
                "sat_safety_deferred_observations", {}
            )
            if type(pending) is not dict:
                raise TypeError("deferred SAT safety ledger is not exact")
            authority_for_signal = getattr(
                session.domain_signal_encoder, "authority_for_signal", None
            )
            if not callable(authority_for_signal):
                raise TypeError("SAT safety encoder lacks occurrence authority")
            occurrence_id = authority_for_signal(
                session, signal
            ).occurrence.occurrence_id
            prior = pending.setdefault(
                occurrence_id, (signal, producer_site_manifest_id)
            )
            if prior != (signal, producer_site_manifest_id):
                raise ValueError("deferred SAT safety authority collided")
            return 0
        already_observed = getattr(
            session.domain_signal_encoder, "has_observed", None
        )
        if callable(already_observed) and already_observed(session, signal):
            # Repeated legacy diagnostics are not new producer activations.  In
            # particular, do not open a Phase-7 discovery record which would
            # otherwise materialize the encoder's empty deduplication result as
            # a DECISIVE activation at this ELIGIBLE-only site.
            return 0
    if getattr(session, "phase7_runtime", None) is not None:
        session.record_phase7_pre_emission_activation(
            producer_site_manifest_id, signal
        )
    emit = getattr(session, "emit_domain_signal", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks signal authority")
    return int(emit(signal))


def emit_sat_safety_completion_if_observed(
    signal: SatSafetyBlockerProductionSignal,
    *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    if signal.action != "COMPLETED":
        raise ValueError("conditional SAT safety emission requires completion")
    session = active_production_pilot_session()
    if session is None:
        return 0
    pending = session.domain_signal_state.get(
        "sat_safety_deferred_observations", {}
    )
    if type(pending) is not dict:
        raise TypeError("deferred SAT safety ledger is not exact")
    authority_for_signal = getattr(
        session.domain_signal_encoder, "authority_for_signal", None
    )
    if callable(authority_for_signal):
        occurrence_id = authority_for_signal(
            session, signal
        ).occurrence.occurrence_id
        if occurrence_id in pending:
            pending.pop(occurrence_id)
            if not pending:
                session.domain_signal_state.pop(
                    "sat_safety_deferred_observations", None
                )
            return 0
    emit = getattr(session, "emit_domain_signal_if_observed", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks conditional signal authority")
    return int(emit(signal, producer_site_manifest_id))


def complete_observed_sat_safety_for_counterexample(
    signal: SafeCounterexampleProductionSignal,
) -> int:
    """Complete only blockers bound to this exact validated SAT witness."""

    if type(signal) is not SafeCounterexampleProductionSignal:
        raise TypeError("SAT safety completion requires a safe counterexample signal")
    if not signal.validates():
        raise ValueError("SAT safety completion receipt validation failed")
    session = active_production_pilot_session()
    if session is None:
        return 0
    observed = session.domain_signal_state.get("sat_safety_observed_signals", {})
    if type(observed) is not dict:
        raise TypeError("SAT safety observed signal ledger is not exact")

    from scripts.function_tracer_pcode.authority.domains.sat_safety_sites import (
        SAT_SAFETY_COUNTEREXAMPLE_BOUND_COMPLETED_SITE,
    )

    expected_binding = signal.counterexample_binding
    emitted = 0
    for occurrence_key in sorted(observed):
        observed_signal = observed[occurrence_key]
        if type(observed_signal) is not SatSafetyBlockerProductionSignal:
            raise TypeError("SAT safety observed signal has an invalid type")
        if observed_signal.counterexample_binding != expected_binding:
            continue
        emitted += emit_sat_safety_completion_if_observed(
            SatSafetyBlockerProductionSignal(
                action="COMPLETED",
                reason_id=observed_signal.reason_id,
                canonical_target_key=observed_signal.canonical_target_key,
                missing_semantic_fact=observed_signal.missing_semantic_fact,
                evidence_refs=observed_signal.evidence_refs,
                producer_id=(
                    SAT_SAFETY_COUNTEREXAMPLE_BOUND_COMPLETED_SITE.producer_id
                ),
                proof_artifact_digest=signal.proof_artifact_digest,
                counterexample_binding=expected_binding,
            ),
            producer_site_manifest_id=(
                "sat-safety-counterexample-bound-completed"
            ),
        )
    return emitted


def finalize_deferred_sat_safety_observations(session: Any) -> None:
    """Emit every pairwise SAT-safety blocker that is still deferred.

    Deferred observations describe analysis-level unsafety (incomplete control
    flow, unproven outcome partition, ...) of the very analyses every later
    strategy reuses.  A safe counterexample committed afterwards by the
    monolithic fallback therefore does not make them moot: only a completion
    bound to the exact witness (``complete_observed_sat_safety_for_counterexample``)
    may retire one.  Dropping them here turned the blockers into a fail-open
    NOT_EQ on Eq benchmarks (Issue #25), so they are always emitted and the
    decision authority decides whether they block the counterexample.
    """
    pending = session.domain_signal_state.pop(
        "sat_safety_deferred_observations", {}
    )
    if type(pending) is not dict:
        raise TypeError("deferred SAT safety ledger is not exact")
    if not pending:
        return
    for occurrence_id in sorted(pending):
        signal, manifest_id = pending[occurrence_id]
        terminal_signal = replace(signal, defer_until_terminal=False)
        if getattr(session, "phase7_runtime", None) is not None:
            session.record_phase7_pre_emission_activation(
                manifest_id, terminal_signal
            )
        session.emit_domain_signal(terminal_signal)


def emit_call_effect_signal(
    signal: Any, *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    session = active_production_pilot_session()
    if session is None:
        return 0
    accepts = getattr(session.domain_signal_encoder, "accepts_signal_type", None)
    if callable(accepts) and not accepts(type(signal)):
        return 0
    from scripts.function_tracer_pcode.authority.sites.runtime import Phase7ProductionRuntime

    signal_digest = Phase7ProductionRuntime.signal_digest(
        producer_site_manifest_id, signal
    )
    emitted = session.domain_signal_state.setdefault(
        "call_effect_production_signal_digests", set()
    )
    if signal_digest in emitted:
        return 0
    if getattr(session, "phase7_runtime", None) is not None:
        session.record_phase7_pre_emission_activation(
            producer_site_manifest_id, signal
        )
    emit = getattr(session, "emit_domain_signal", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks signal authority")
    count = int(emit(signal))
    emitted.add(signal_digest)
    return count


def emit_loop_recurrence_signal(
    signal: Any, *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    """Emit an exact slice4 signal; remain inert for pilots without its route."""

    from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
        LoopBlockerProductionSignal,
        LoopExactGuardPartitionCompletionSignal,
        LoopExactTermRelationCompletionSignal,
        LoopSolverExecutionBatchSignal,
        RecurrenceValidationCompletionSignal,
    )

    if type(signal) not in {
        LoopBlockerProductionSignal,
        LoopExactGuardPartitionCompletionSignal,
        LoopExactTermRelationCompletionSignal,
        LoopSolverExecutionBatchSignal,
        RecurrenceValidationCompletionSignal,
    }:
        raise TypeError("loop/recurrence emission requires an exact typed signal")
    session = active_production_pilot_session()
    if session is None:
        return 0
    accepts = getattr(session.domain_signal_encoder, "accepts_signal_type", None)
    if callable(accepts) and not accepts(type(signal)):
        return 0
    if type(signal) is LoopBlockerProductionSignal:
        already_observed = getattr(
            session.domain_signal_encoder, "has_observed", None
        )
        if callable(already_observed) and already_observed(session, signal):
            # A repeated semantic occurrence is not a new producer activation.
            # Do not let its empty encoder plan materialize as DECISIVE at an
            # ELIGIBLE-only Phase 7 site.
            return 0
    if getattr(session, "phase7_runtime", None) is not None:
        session.record_phase7_pre_emission_activation(
            producer_site_manifest_id, signal
        )
    emit = getattr(session, "emit_domain_signal", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks signal authority")
    return int(emit(signal))


def emit_abi_width_readonly_signal(
    signal: Any, *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    """Emit one exact slice5 blocker; remain inert when its route is absent."""

    from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
        AbiWidthReadonlyBlockerSignal,
    )

    if type(signal) is not AbiWidthReadonlyBlockerSignal:
        raise TypeError("ABI/width/readonly emission requires an exact blocker signal")
    session = active_production_pilot_session()
    if session is None:
        return 0
    accepts = getattr(session.domain_signal_encoder, "accepts_signal_type", None)
    if callable(accepts) and not accepts(type(signal)):
        return 0

    def emit_once() -> int:
        already_observed = getattr(
            session.domain_signal_encoder, "has_observed", None
        )
        if callable(already_observed) and already_observed(session, signal):
            return 0
        if getattr(session, "phase7_runtime", None) is not None:
            session.record_phase7_pre_emission_activation(
                producer_site_manifest_id, signal
            )
        emit = getattr(session, "emit_domain_signal", None)
        if not callable(emit):
            raise TypeError(
                "active production pilot session lacks signal authority"
            )
        return int(emit(signal))

    transaction = getattr(session, "domain_signal_transaction", None)
    if callable(transaction):
        with transaction():
            return emit_once()
    return emit_once()


def emit_operational_extraction_signal(
    signal: Any, *, producer_site_manifest_id: Optional[str] = None,
) -> int:
    """Emit only when the active composite explicitly registers the exact type."""

    session = active_production_pilot_session()
    if session is None:
        return 0
    accepts = getattr(session.domain_signal_encoder, "accepts_signal_type", None)
    if not callable(accepts) or not accepts(type(signal)):
        return 0
    if getattr(session, "phase7_runtime", None) is not None:
        session.record_phase7_pre_emission_activation(
            producer_site_manifest_id, signal
        )
    emit = getattr(session, "emit_domain_signal", None)
    if not callable(emit):
        raise TypeError("active production pilot session lacks signal authority")
    return int(emit(signal))


def register_readonly_promotion(seed: Any) -> None:
    """Register a typed readonly base seed for pre-seal relational promotion."""

    from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
        ReadonlyReductionObjectSetSeed,
    )

    if type(seed) is not ReadonlyReductionObjectSetSeed:
        raise TypeError("readonly promotion registration requires an exact base seed")
    session = active_production_pilot_session()
    if session is None:
        return
    registrar = getattr(session.domain_signal_encoder, "register_readonly_promotion", None)
    if not callable(registrar):
        return
    registrar(session, seed)


def register_abi_width_solver_candidate(blocker: Any, seed: Any) -> None:
    """Register one exact dependency-gated semantic solver candidate."""

    from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
        AbiWidthReadonlyBlockerSignal,
    )

    if type(blocker) is not AbiWidthReadonlyBlockerSignal:
        raise TypeError("ABI/width scheduler registration requires exact blocker")
    session = active_production_pilot_session()
    if session is None:
        return
    registrar = getattr(
        session.domain_signal_encoder,
        "register_abi_width_solver_candidate",
        None,
    )
    if not callable(registrar):
        return
    registrar(session, blocker, seed)


def register_void_effect_only_return_abi_seed(seed: Any) -> None:
    """Register one exact void effect-only ABI seed for structural closure (Issue #104)."""

    session = active_production_pilot_session()
    if session is None:
        return
    registrar = getattr(
        session.domain_signal_encoder,
        "register_void_effect_only_return_abi_seed",
        None,
    )
    if not callable(registrar):
        return
    registrar(session, seed)


def register_return_observation_proof_plan(
    projection_seed: Any, assessment: Any
) -> None:
    """Register one exact object-derived ABI relation for terminal proof closure."""

    session = active_production_pilot_session()
    if session is None:
        return
    registrar = getattr(
        session.domain_signal_encoder,
        "register_return_observation_proof_plan",
        None,
    )
    if not callable(registrar):
        return
    registrar(session, projection_seed, assessment)


def active_loop_requirement_for_signal(
    blocker: Any, proof_kind: str
) -> Any:
    """Resolve exact live-Q identity only while an opted-in pilot is active."""

    session = active_production_pilot_session()
    if session is None:
        return None
    resolver = getattr(
        session.domain_signal_encoder, "loop_requirement_for_signal", None
    )
    if not callable(resolver):
        return None
    return resolver(session, blocker, proof_kind)


def active_production_execution_identity_digest() -> Optional[str]:
    session = active_production_pilot_session()
    if session is None:
        return None
    return str(session.identity.execution_identity_digest)


def execute_loop_solver_rendered_query(
    blocker: Any,
    rendered: Any,
    *,
    configured_timeout_ms: int,
) -> int:
    """Execute a typed rendered loop query through the common signed issuer."""

    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        PINNED_SOLVER_EXECUTION_ISSUER,
    )
    from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
        LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        LoopSolverExecutionBatchSignal,
        _issue_loop_solver_query_authority,
    )

    session = active_production_pilot_session()
    if session is None:
        return 0
    query = _issue_loop_solver_query_authority(rendered)
    builder = getattr(
        session.domain_signal_encoder, "build_loop_execution_context", None
    )
    if not callable(builder):
        return 0
    context = builder(session, blocker, (query,))
    membership = context.membership_for(query)
    receipts = PINNED_SOLVER_EXECUTION_ISSUER.execute(
        registry=LOOP_COMMON_EXECUTION_STAGE_REGISTRY,
        result_occurrence_id=session.identity.result_occurrence_id,
        membership=membership,
        invocation_identity=(
            session.identity.result_occurrence_id
            + ":"
            + query.obligation_id
            + ":"
            + query.stage
        ),
        first_invocation_ordinal=1,
        query=query.query_text,
        configured_timeout_ms=configured_timeout_ms,
        query_authority=query,
        lifecycle_projection=context.lifecycle_projection,
    )
    batch = LoopSolverExecutionBatchSignal.from_issuer_results(
        blocker, query, membership, receipts, context.lifecycle_projection
    )
    commit = getattr(session.domain_signal_encoder, "commit_emitted_signal", None)
    rollback = getattr(session.domain_signal_encoder, "rollback_emitted_signal", None)
    try:
        intents = tuple(session.domain_signal_encoder(session, batch))
        session.emit_many(
            intents,
            (lambda: commit(session, batch, intents)) if callable(commit) else None,
        )
    except Exception:
        if callable(rollback):
            rollback(session, batch)
        raise
    emitted = len(intents)
    emitted += _consume_loop_sat_safety_handoffs(session)
    return emitted


def _consume_loop_sat_safety_handoffs(session: Any) -> int:
    """Consume each handoff only after an event or typed duplicate is proven."""

    state = session.domain_signal_state
    key = "loop_sat_safety_handoffs"
    pending = state.get(key)
    if pending is None:
        return 0
    if type(pending) is not list:
        raise TypeError("loop SAT safety handoff ledger is not an exact list")
    accepts = getattr(session.domain_signal_encoder, "accepts_signal_type", None)
    if not callable(accepts) or not accepts(SatSafetyBlockerProductionSignal):
        raise ValueError(
            "loop SAT refutation lacks Phase 6.1 counterexample-safety route"
        )
    has_observed = getattr(session.domain_signal_encoder, "has_observed", None)
    if not callable(has_observed):
        raise ValueError("loop SAT safety route lacks typed duplicate authority")
    emitted = 0
    while pending:
        handoff = pending[0]
        if type(handoff) is not SatSafetyBlockerProductionSignal:
            raise TypeError("loop SAT handoff signal is not exact")
        if has_observed(session, handoff):
            del pending[0]
            continue
        count = emit_sat_safety_signal(
            handoff,
            producer_site_manifest_id="pairwise-loop-sat-safety-observed",
        )
        if count <= 0 and not has_observed(session, handoff):
            raise ValueError(
                "loop SAT safety handoff was neither emitted nor deduplicated"
            )
        del pending[0]
        emitted += count
    state.pop(key, None)
    return emitted


def build_active_call_effect_execution_context(
    signals: tuple[CallEffectBlockerProductionSignal, ...], registry: Any
) -> Any:
    session = active_production_pilot_session()
    if session is None:
        return None
    accepts = getattr(session.domain_signal_encoder, "accepts_signal_type", None)
    if callable(accepts) and (
        not signals or not all(accepts(type(signal)) for signal in signals)
    ):
        return None
    builder = getattr(session.domain_signal_encoder, "build_call_effect_execution_context", None)
    if not callable(builder):
        return None
    return builder(session, tuple(signals), registry)

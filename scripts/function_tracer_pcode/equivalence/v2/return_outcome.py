"""Phase 6.2 return/outcome authority contracts.

This module deliberately contains no legacy-status finalization.  It seals the
producer matrix and preserves solver/witness authority before legacy producers
reduce their results to strings.
"""

from __future__ import annotations

from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from types import MappingProxyType
from typing import Any, Callable, Mapping, Optional

from .contracts import authority_digest, canonical_value
from ..cause_identity import ProofRequirementContract, ProofRequirementId


_EXECUTION_RECEIPT_FACTORY_TOKEN = object()
_WITNESS_ARTIFACT_FACTORY_TOKEN = object()
_ACTIVE_STAGE_CAPTURE: ContextVar[Optional["OutcomeStageCapture"]] = ContextVar(
    "unknown_taxonomy_v2_outcome_stage_capture", default=None
)


OUTCOME_STAGE_REASON_MATRIX = MappingProxyType({
    ("termination_classification", "proved"): None,
    ("termination_classification", "unclassified"): "outcome_termination_classification_unproven",
    ("cfg_reachability", "proved"): None,
    ("cfg_reachability", "incomplete"): "outcome_cfg_reachability_unproven",
    ("path_region_completeness", "proved"): None,
    ("path_region_completeness", "incomplete"): "outcome_path_region_completeness_unproven",
    ("member_classification", "proved"): None,
    ("member_classification", "unclassified"): "outcome_member_classification_unproven",
    ("same_kind_consistency", "proved"): None,
    ("same_kind_consistency", "comparison_surface_missing"): "outcome_same_kind_comparison_surface_missing",
    ("same_kind_consistency", "unknown"): "outcome_same_kind_consistency_unproven",
    ("same_kind_consistency", "timeout"): "outcome_same_kind_consistency_unproven",
    ("same_kind_consistency", "conflict"): "outcome_return_value_conflict_witnessed",
    ("cross_kind_disjointness", "proved"): None,
    ("cross_kind_disjointness", "unknown"): "outcome_cross_kind_disjointness_unproven",
    ("cross_kind_disjointness", "timeout"): "outcome_cross_kind_disjointness_unproven",
    ("cross_kind_disjointness", "overlap"): "outcome_cross_kind_overlap_witnessed",
    ("residual_totality", "proved"): None,
    ("residual_totality", "incomplete"): "outcome_partition_guard_union_incomplete",
    ("residual_totality", "unknown"): "outcome_partition_totality_unproven",
    ("residual_totality", "timeout"): "outcome_partition_totality_unproven",
    ("residual_totality", "residual_sat"): "outcome_partition_residual_sat_witnessed",
    ("partition_complete", "proved"): None,
    ("partition_complete", "unclassified"): "outcome_partition_completion_unproven",
})

WITNESSED_REASON_PROPOSITIONS = MappingProxyType({
    "outcome_return_value_conflict_witnessed": "reachable_return_values_conflict",
    "outcome_cross_kind_overlap_witnessed": "reachable_outcome_kinds_overlap",
    "outcome_partition_residual_sat_witnessed": "unclassified_input_region_is_satisfiable",
})

RETURN_OUTCOME_TYPED_REASON_IDS = frozenset(
    reason_id for reason_id in OUTCOME_STAGE_REASON_MATRIX.values() if reason_id
) | frozenset({
    "return_coverage_gap",
    "return_coverage_inconclusive",
    "outcome_partition_semantics_unresolved",
    "outcome_seed_missing",
    "outcome_stage_producer_missing",
    "outcome_partition_relation_unproven",
})


def reason_for_stage_status(stage: str, status: str) -> Optional[str]:
    if type(stage) is not str or type(status) is not str:
        raise TypeError("outcome stage and status must be exact strings")
    try:
        return OUTCOME_STAGE_REASON_MATRIX[(stage, status)]
    except KeyError as exc:
        raise ValueError("outcome stage/status pair is not sealed") from exc


@dataclass(frozen=True)
class OutcomeStageExecutionReceipt:
    stage: str
    proof_requirement_identity: ProofRequirementId
    premise_digest: str
    function_snapshot_fingerprint: str
    outcome_seed_digest: str
    outcome_seed_revision: int
    function_identity: tuple[Any, ...]
    input_domain_contract: tuple[Any, ...]
    extraction_schema_version: int
    outcome_encoding_version: str
    query_digest: str
    model_digest: Optional[str]
    solver_output_digest: str
    solver_identity: str
    execution_identity_digest: str
    producer_attempt_identity: str
    producer_attempt_ordinal: int
    invocation_identity: str
    invocation_ordinal: int
    configured_timeout_ms: Optional[int]
    elapsed_ms: int
    observed_status: str
    receipt_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _EXECUTION_RECEIPT_FACTORY_TOKEN:
            raise TypeError("outcome execution receipt must be factory-issued")

    @classmethod
    def create(
        cls,
        *,
        stage: str,
        seed: Any,
        premise_digest: str,
        function_snapshot_fingerprint: str,
        outcome_seed_digest: str,
        outcome_seed_revision: int,
        query: str,
        model: Optional[Mapping[str, Any]],
        solver_output: Any,
        solver_identity: str,
        execution_identity_digest: str,
        producer_attempt_identity: str,
        producer_attempt_ordinal: int,
        invocation_identity: str,
        invocation_ordinal: int,
        configured_timeout_ms: Optional[int],
        elapsed_ms: int,
        observed_status: str,
    ) -> "OutcomeStageExecutionReceipt":
        if not isinstance(solver_output, Mapping):
            raise TypeError("solver output authority must be a typed mapping")
        if solver_output.get("status") != observed_status:
            raise ValueError("solver output status differs from observed status")
        if canonical_value(solver_output.get("model")) != canonical_value(model):
            raise ValueError("solver output model differs from captured model")
        query_digest = authority_digest({"normalized_solver_query": query})
        model_digest = (
            authority_digest({"solver_model": canonical_value(model)})
            if model
            else None
        )
        solver_output_digest = authority_digest({
            "solver_output": canonical_value(solver_output)
        })
        from ..obligations.outcome_partition import (
            OUTCOME_ENCODING_VERSION,
            outcome_seed_digest as derive_seed_digest,
            requirement_for_stage,
        )
        requirement = requirement_for_stage(seed, stage)
        derived_seed_digest = derive_seed_digest(seed)
        seed_revision = int(getattr(seed, "partition_revision", 0) or 0)
        function_identity = tuple(getattr(seed, "function_identity", ()) or ())
        input_domain_contract = tuple(
            getattr(seed, "input_domain_contract", ()) or ()
        )
        extraction_schema_version = int(
            getattr(seed, "extraction_schema_version", 0) or 0
        )
        if outcome_seed_digest != derived_seed_digest:
            raise ValueError("caller outcome seed digest differs from seed authority")
        if outcome_seed_revision != seed_revision:
            raise ValueError("caller outcome seed revision differs from seed authority")
        payload = {
            "stage": stage,
            "proof_requirement_identity": requirement,
            "premise_digest": premise_digest,
            "function_snapshot_fingerprint": function_snapshot_fingerprint,
            "outcome_seed_digest": outcome_seed_digest,
            "outcome_seed_revision": outcome_seed_revision,
            "function_identity": function_identity,
            "input_domain_contract": input_domain_contract,
            "extraction_schema_version": extraction_schema_version,
            "outcome_encoding_version": OUTCOME_ENCODING_VERSION,
            "query_digest": query_digest,
            "model_digest": model_digest,
            "solver_output_digest": solver_output_digest,
            "solver_identity": solver_identity,
            "execution_identity_digest": execution_identity_digest,
            "producer_attempt_identity": producer_attempt_identity,
            "producer_attempt_ordinal": producer_attempt_ordinal,
            "invocation_identity": invocation_identity,
            "invocation_ordinal": invocation_ordinal,
            "configured_timeout_ms": configured_timeout_ms,
            "elapsed_ms": elapsed_ms,
            "observed_status": observed_status,
        }
        digest_payload = {
            **payload,
            "proof_requirement_identity": requirement.to_dict(),
        }
        receipt = cls(
            **payload,
            receipt_digest=authority_digest(digest_payload),
            _factory_token=_EXECUTION_RECEIPT_FACTORY_TOKEN,
        )
        receipt.validate()
        return receipt

    def validate(self) -> None:
        if self.stage not in {stage for stage, _ in OUTCOME_STAGE_REASON_MATRIX}:
            raise ValueError("solver receipt stage is not sealed")
        for value in (
            self.premise_digest,
            self.function_snapshot_fingerprint,
            self.outcome_seed_digest,
            self.outcome_encoding_version,
            self.query_digest,
            self.solver_output_digest,
            self.solver_identity,
            self.execution_identity_digest,
            self.producer_attempt_identity,
            self.invocation_identity,
            self.observed_status,
            self.receipt_digest,
        ):
            if type(value) is not str or not value:
                raise TypeError("outcome execution receipt identity is incomplete")
        if type(self.proof_requirement_identity) is not ProofRequirementId:
            raise TypeError("outcome execution receipt requirement is not typed")
        if type(self.outcome_seed_revision) is not int or self.outcome_seed_revision < 0:
            raise TypeError("outcome seed revision is invalid")
        if not self.function_identity or not self.input_domain_contract:
            raise ValueError("outcome seed function/domain authority is incomplete")
        if type(self.extraction_schema_version) is not int or self.extraction_schema_version <= 0:
            raise TypeError("outcome extraction schema version is invalid")
        if type(self.invocation_ordinal) is not int or self.invocation_ordinal <= 0:
            raise TypeError("solver invocation ordinal is invalid")
        if type(self.producer_attempt_ordinal) is not int or self.producer_attempt_ordinal <= 0:
            raise TypeError("outcome producer attempt ordinal is invalid")
        if type(self.elapsed_ms) is not int or self.elapsed_ms < 0:
            raise TypeError("solver elapsed time is invalid")
        if self.configured_timeout_ms is not None and (
            type(self.configured_timeout_ms) is not int or self.configured_timeout_ms <= 0
        ):
            raise TypeError("solver timeout budget is invalid")
        if self.observed_status not in {"sat", "unsat", "unknown", "timeout", "error"}:
            raise ValueError("solver receipt status is not sealed")
        if self.observed_status == "sat" and not self.model_digest:
            raise ValueError("SAT execution receipt lacks a captured model")
        if self.observed_status != "sat" and self.model_digest is not None:
            raise ValueError("non-SAT execution receipt cannot bind a model")
        expected_requirement = ProofRequirementId.create(
            f"unary_outcome_{self.stage}",
            (
                "function_outcome_seed",
                self.function_identity,
                self.outcome_seed_digest,
                self.outcome_seed_revision,
            ),
            ProofRequirementContract(
                proposition=f"reachable outcome {self.stage}",
                relation_direction="unary",
                observation_surface=(
                    self.input_domain_contract,
                    self.extraction_schema_version,
                    self.outcome_encoding_version,
                ),
                active_precondition=("function_input_domain",),
            ),
        )
        if self.proof_requirement_identity.to_key() != expected_requirement.to_key():
            raise ValueError("outcome execution requirement is not the exact stage authority")
        payload = {
            "stage": self.stage,
            "proof_requirement_identity": self.proof_requirement_identity,
            "premise_digest": self.premise_digest,
            "function_snapshot_fingerprint": self.function_snapshot_fingerprint,
            "outcome_seed_digest": self.outcome_seed_digest,
            "outcome_seed_revision": self.outcome_seed_revision,
            "function_identity": self.function_identity,
            "input_domain_contract": self.input_domain_contract,
            "extraction_schema_version": self.extraction_schema_version,
            "outcome_encoding_version": self.outcome_encoding_version,
            "query_digest": self.query_digest,
            "model_digest": self.model_digest,
            "solver_output_digest": self.solver_output_digest,
            "solver_identity": self.solver_identity,
            "execution_identity_digest": self.execution_identity_digest,
            "producer_attempt_identity": self.producer_attempt_identity,
            "producer_attempt_ordinal": self.producer_attempt_ordinal,
            "invocation_identity": self.invocation_identity,
            "invocation_ordinal": self.invocation_ordinal,
            "configured_timeout_ms": self.configured_timeout_ms,
            "elapsed_ms": self.elapsed_ms,
            "observed_status": self.observed_status,
        }
        digest_payload = {
            **payload,
            "proof_requirement_identity": self.proof_requirement_identity.to_dict(),
        }
        if authority_digest(digest_payload) != self.receipt_digest:
            raise ValueError("outcome execution receipt digest mismatch")
        from .stream import validate_outcome_execution_receipt_authority

        validate_outcome_execution_receipt_authority(
            self._authority_dict_unchecked()
        )

    def _authority_dict_unchecked(self) -> Mapping[str, Any]:
        return {
            "stage": self.stage,
            "proof_requirement_identity": self.proof_requirement_identity.to_dict(),
            "premise_digest": self.premise_digest,
            "function_snapshot_fingerprint": self.function_snapshot_fingerprint,
            "outcome_seed_digest": self.outcome_seed_digest,
            "outcome_seed_revision": self.outcome_seed_revision,
            "function_identity": self.function_identity,
            "input_domain_contract": self.input_domain_contract,
            "extraction_schema_version": self.extraction_schema_version,
            "outcome_encoding_version": self.outcome_encoding_version,
            "query_digest": self.query_digest,
            "model_digest": self.model_digest,
            "solver_output_digest": self.solver_output_digest,
            "solver_identity": self.solver_identity,
            "execution_identity_digest": self.execution_identity_digest,
            "producer_attempt_identity": self.producer_attempt_identity,
            "producer_attempt_ordinal": self.producer_attempt_ordinal,
            "invocation_identity": self.invocation_identity,
            "invocation_ordinal": self.invocation_ordinal,
            "configured_timeout_ms": self.configured_timeout_ms,
            "elapsed_ms": self.elapsed_ms,
            "observed_status": self.observed_status,
            "receipt_digest": self.receipt_digest,
        }

    def to_authority_dict(self) -> Mapping[str, Any]:
        self.validate()
        return self._authority_dict_unchecked()

@dataclass(frozen=True)
class UnaryOutcomeWitnessArtifact:
    reason_id: str
    stage: str
    proof_requirement_identity: ProofRequirementId
    premise_digest: str
    function_snapshot_fingerprint: str
    outcome_seed_digest: str
    outcome_seed_revision: int
    query_digest: str
    model_digest: str
    solver_invocation_receipt_digest: str
    witnessed_proposition: str
    producer_version: str
    encoding_version: str
    artifact_digest: str
    _factory_token: object = field(default=None, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._factory_token is not _WITNESS_ARTIFACT_FACTORY_TOKEN:
            raise TypeError("unary witness artifact must be factory-issued")

    @classmethod
    def create(
        cls,
        receipt: OutcomeStageExecutionReceipt,
        *,
        reason_id: str,
        witnessed_proposition: str,
        producer_version: str,
        encoding_version: str,
    ) -> "UnaryOutcomeWitnessArtifact":
        receipt.validate()
        if receipt.observed_status != "sat":
            raise ValueError("unary witness requires an exact SAT receipt")
        if not receipt.model_digest:
            raise ValueError("unary witness requires a receipt-bound model")
        expected = WITNESSED_REASON_PROPOSITIONS.get(reason_id)
        if expected is None or witnessed_proposition != expected:
            raise ValueError("unary witnessed proposition does not match reason")
        producer_status = {
            "outcome_return_value_conflict_witnessed": "conflict",
            "outcome_cross_kind_overlap_witnessed": "overlap",
            "outcome_partition_residual_sat_witnessed": "residual_sat",
        }[reason_id]
        if OUTCOME_STAGE_REASON_MATRIX.get((receipt.stage, producer_status)) != reason_id:
            raise ValueError("unary witness stage does not match reason")
        payload = {
            "reason_id": reason_id,
            "stage": receipt.stage,
            "proof_requirement_identity": receipt.proof_requirement_identity,
            "premise_digest": receipt.premise_digest,
            "function_snapshot_fingerprint": receipt.function_snapshot_fingerprint,
            "outcome_seed_digest": receipt.outcome_seed_digest,
            "outcome_seed_revision": receipt.outcome_seed_revision,
            "query_digest": receipt.query_digest,
            "model_digest": receipt.model_digest,
            "solver_invocation_receipt_digest": receipt.receipt_digest,
            "witnessed_proposition": witnessed_proposition,
            "producer_version": producer_version,
            "encoding_version": encoding_version,
        }
        artifact = cls(
            **payload,
            artifact_digest=authority_digest(payload),
            _factory_token=_WITNESS_ARTIFACT_FACTORY_TOKEN,
        )
        artifact.validate_against(receipt)
        return artifact

    def validate_against(self, receipt: OutcomeStageExecutionReceipt) -> None:
        receipt.validate()
        expected = WITNESSED_REASON_PROPOSITIONS.get(self.reason_id)
        if expected is None or self.witnessed_proposition != expected:
            raise ValueError("unary witness proposition is invalid")
        if receipt.observed_status != "sat":
            raise ValueError("unary witness receipt is not SAT")
        producer_status = {
            "outcome_return_value_conflict_witnessed": "conflict",
            "outcome_cross_kind_overlap_witnessed": "overlap",
            "outcome_partition_residual_sat_witnessed": "residual_sat",
        }.get(self.reason_id)
        if (
            producer_status is None
            or OUTCOME_STAGE_REASON_MATRIX.get((receipt.stage, producer_status))
            != self.reason_id
        ):
            raise ValueError("unary witness stage/reason binding mismatch")
        exact = {
            "stage": receipt.stage,
            "proof_requirement_identity": receipt.proof_requirement_identity,
            "premise_digest": receipt.premise_digest,
            "function_snapshot_fingerprint": receipt.function_snapshot_fingerprint,
            "outcome_seed_digest": receipt.outcome_seed_digest,
            "outcome_seed_revision": receipt.outcome_seed_revision,
            "query_digest": receipt.query_digest,
            "solver_invocation_receipt_digest": receipt.receipt_digest,
            "model_digest": receipt.model_digest,
        }
        for field_name, expected_value in exact.items():
            if getattr(self, field_name) != expected_value:
                raise ValueError(f"unary witness {field_name} binding mismatch")
        for value in (self.model_digest, self.producer_version, self.encoding_version):
            if type(value) is not str or not value:
                raise TypeError("unary witness artifact authority is incomplete")
        payload = {
            "reason_id": self.reason_id,
            "stage": self.stage,
            "proof_requirement_identity": self.proof_requirement_identity,
            "premise_digest": self.premise_digest,
            "function_snapshot_fingerprint": self.function_snapshot_fingerprint,
            "outcome_seed_digest": self.outcome_seed_digest,
            "outcome_seed_revision": self.outcome_seed_revision,
            "query_digest": self.query_digest,
            "model_digest": self.model_digest,
            "solver_invocation_receipt_digest": self.solver_invocation_receipt_digest,
            "witnessed_proposition": self.witnessed_proposition,
            "producer_version": self.producer_version,
            "encoding_version": self.encoding_version,
        }
        if authority_digest(payload) != self.artifact_digest:
            raise ValueError("unary witness artifact digest mismatch")


@dataclass
class OutcomeStageCapture:
    seed: Any
    stage: str
    premise_digest: str
    function_snapshot_fingerprint: str
    execution_identity_digest: str
    producer_attempt_identity: str
    producer_attempt_ordinal: int
    next_invocation_ordinal: Callable[[], int]
    receipts: list[OutcomeStageExecutionReceipt] = field(default_factory=list)

    def capture_parallel_result(
        self,
        *,
        query: str,
        parallel_result: Any,
        configured_timeout_ms: Optional[int],
    ) -> tuple[OutcomeStageExecutionReceipt, ...]:
        raw_results = tuple(getattr(parallel_result, "results", ()) or ())
        captured = []
        for raw in raw_results:
            status_value = getattr(getattr(raw, "status", None), "name", "")
            status = str(status_value).lower()
            model = getattr(raw, "model", None)
            ordinal = self.next_invocation_ordinal()
            solver_name = str(getattr(raw, "solver_name", "") or "unknown-solver")
            output = {
                "status": status,
                "model": model,
                "error_message": getattr(raw, "error_message", None),
                "raw_output": getattr(raw, "raw_output", None),
            }
            receipt = OutcomeStageExecutionReceipt.create(
                stage=self.stage,
                seed=self.seed,
                premise_digest=self.premise_digest,
                function_snapshot_fingerprint=self.function_snapshot_fingerprint,
                outcome_seed_digest=_seed_digest(self.seed),
                outcome_seed_revision=int(
                    getattr(self.seed, "partition_revision", 0) or 0
                ),
                query=query,
                model=model,
                solver_output=output,
                solver_identity=solver_name,
                execution_identity_digest=self.execution_identity_digest,
                producer_attempt_identity=self.producer_attempt_identity,
                producer_attempt_ordinal=self.producer_attempt_ordinal,
                invocation_identity=authority_digest({
                    "execution_identity_digest": self.execution_identity_digest,
                    "producer_attempt_identity": self.producer_attempt_identity,
                    "stage": self.stage,
                    "query": query,
                    "solver": solver_name,
                    "invocation_ordinal": ordinal,
                }),
                invocation_ordinal=ordinal,
                configured_timeout_ms=configured_timeout_ms,
                elapsed_ms=max(0, int(round(
                    float(getattr(raw, "elapsed_time", 0.0) or 0.0) * 1000
                ))),
                observed_status=status,
            )
            self.receipts.append(receipt)
            captured.append(receipt)
        return tuple(captured)


def _seed_digest(seed: Any) -> str:
    from ..obligations.outcome_partition import outcome_seed_digest

    return outcome_seed_digest(seed)


@contextmanager
def outcome_stage_capture_scope(
    *,
    seed: Any,
    stage: str,
    premise_digest: str,
    function_snapshot_fingerprint: str,
    execution_identity_digest: str = "isolated-test-execution",
    producer_attempt_identity: str = "isolated-test-producer-attempt",
    producer_attempt_ordinal: int = 1,
    next_invocation_ordinal: Optional[Callable[[], int]] = None,
):
    local_ordinal = {"value": 0}
    if next_invocation_ordinal is None:
        def next_invocation_ordinal() -> int:
            local_ordinal["value"] += 1
            return local_ordinal["value"]
    capture = OutcomeStageCapture(
        seed,
        stage,
        premise_digest,
        function_snapshot_fingerprint,
        execution_identity_digest,
        producer_attempt_identity,
        producer_attempt_ordinal,
        next_invocation_ordinal,
    )
    token = _ACTIVE_STAGE_CAPTURE.set(capture)
    try:
        yield capture
    finally:
        _ACTIVE_STAGE_CAPTURE.reset(token)


def capture_active_outcome_solver_result(
    *, query: str, parallel_result: Any, configured_timeout_ms: Optional[int]
) -> tuple[OutcomeStageExecutionReceipt, ...]:
    capture = _ACTIVE_STAGE_CAPTURE.get()
    if capture is None:
        return ()
    try:
        return capture.capture_parallel_result(
            query=query,
            parallel_result=parallel_result,
            configured_timeout_ms=configured_timeout_ms,
        )
    except Exception as exc:
        from .production_signals import record_production_pilot_shadow_error

        record_production_pilot_shadow_error(exc)
        return ()


# Registry-owned recovery expression for every unary outcome-stage blocker.
# Producers reference this contract; they cannot manufacture equivalent Boolean
# spellings that would fragment cause identity.
from .contracts import (  # noqa: E402  (kept below producer contracts to avoid cycles)
    CauseOccurrence,
    CauseOccurrenceAuthority,
    IdentityScope,
    ProofRequirement,
    ReasonDefinition,
    RecoveryAddressability,
    RequirementCompletionReceipt,
    RequirementSlotDefinition,
    SatisfactionContractDefinition,
    requirement_slot,
)
from .registry import (  # noqa: E402
    SatisfactionBindingFactory,
    SealedReasonRegistry,
    SealedRecoveryRegistry,
    SemanticCauseIdentityFactory,
)
from .stream import (  # noqa: E402
    CauseObservedEventAuthority,
    EventIntent,
    EventType,
    OutcomeProducerAttemptEventAuthority,
    RequirementCompletedEventAuthority,
    ReceiptBoundSolverExecutionEventAuthority,
)


RETURN_OUTCOME_STAGE_CONTRACT = SatisfactionContractDefinition(
    "return-outcome-stage-recovery",
    1,
    (RequirementSlotDefinition(
        "stage_proof",
        frozenset(f"unary_outcome_{stage}" for stage, _ in OUTCOME_STAGE_REASON_MATRIX),
    ),),
    requirement_slot("stage_proof"),
)


def _stage_reason_definition(reason_id: str) -> ReasonDefinition:
    return ReasonDefinition(
        reason_id,
        "return_outcome",
        "semantic_partition_blocker",
        "blocks_equivalence",
        frozenset(("function_outcome_stage",)),
        ("outcome_seed", "stage_producer_authority"),
        RETURN_OUTCOME_STAGE_CONTRACT.requirement_slots[0].allowed_proof_kinds,
        True,
        "return-outcome-stage-v2",
        RecoveryAddressability.REQUIREMENT_REQUIRED,
    )


RETURN_OUTCOME_REASON_REGISTRY = SealedReasonRegistry.build(
    _stage_reason_definition(reason_id)
    for reason_id in sorted({
        reason_id for reason_id in OUTCOME_STAGE_REASON_MATRIX.values() if reason_id
    })
)
RETURN_OUTCOME_RECOVERY_REGISTRY = SealedRecoveryRegistry.build(
    (RETURN_OUTCOME_STAGE_CONTRACT,)
)


class ReturnOutcomePilotEncoder:
    """Encode production stage signals without deriving authority from final outcomes."""

    def __init__(self) -> None:
        self._cause_factory = SemanticCauseIdentityFactory(
            RETURN_OUTCOME_REASON_REGISTRY
        )
        self._binding_factory = SatisfactionBindingFactory(
            RETURN_OUTCOME_RECOVERY_REGISTRY
        )

    @staticmethod
    def _state(session: Any) -> dict[str, Any]:
        return session.domain_signal_state.setdefault(
            "return_outcome_v2",
            {
                "authorities": {},
                "receipts": set(),
                "completed": set(),
                "attempts": set(),
            },
        )

    @staticmethod
    def _validate_signal(signal: Any) -> Optional[str]:
        from .production_signals import OutcomePartitionProductionSignal

        if type(signal) is not OutcomePartitionProductionSignal:
            raise TypeError("return/outcome encoder requires exact production signal")
        if (
            signal.outcome_seed_revision is None
            or signal.function_snapshot_fingerprint is None
            or signal.premise_digest is None
            or signal.producer_attempt_identity is None
            or signal.producer_attempt_ordinal is None
            or signal.execution_identity_digest is None
        ):
            raise ValueError("return/outcome production signal lacks exact authority")
        reason_id = reason_for_stage_status(signal.stage, signal.producer_status)
        receipts = tuple(signal.execution_receipts)
        if len({
            (receipt.producer_attempt_identity, receipt.producer_attempt_ordinal)
            for receipt in receipts
            if type(receipt) is OutcomeStageExecutionReceipt
        }) > 1:
            raise ValueError("one producer signal cannot mix producer attempts")
        for receipt in receipts:
            if type(receipt) is not OutcomeStageExecutionReceipt:
                raise TypeError("return/outcome signal contains non-receipt authority")
            receipt.validate()
            if (
                receipt.stage != signal.stage
                or receipt.outcome_seed_digest != signal.outcome_seed_digest
                or receipt.outcome_seed_revision != signal.outcome_seed_revision
                or receipt.function_snapshot_fingerprint
                != signal.function_snapshot_fingerprint
                or receipt.premise_digest != signal.premise_digest
                or canonical_value(receipt.function_identity)
                != canonical_value(signal.function_identity)
                or canonical_value(receipt.proof_requirement_identity.to_dict())
                != canonical_value(signal.proof_requirement_identity)
                or receipt.producer_attempt_identity
                != signal.producer_attempt_identity
                or receipt.producer_attempt_ordinal
                != signal.producer_attempt_ordinal
            ):
                raise ValueError("return/outcome receipt differs from producer authority")
        if signal.producer_status == "proved":
            if reason_id is not None or signal.validated_artifact_authority is None:
                raise ValueError("proved outcome signal lacks validated completion authority")
            artifact = signal.validated_artifact_authority
            artifact_payload = {
                key: value for key, value in artifact.items()
                if key != "artifact_authority_digest"
            }
            if artifact.get("artifact_authority_digest") != authority_digest(artifact_payload):
                raise ValueError("outcome completion artifact authority digest mismatch")
            if signal.witness_artifact is not None:
                raise ValueError("proved outcome signal cannot carry a witness blocker")
        elif signal.validated_artifact_authority is not None:
            raise ValueError("unproved outcome signal cannot complete a requirement")
        if reason_id in WITNESSED_REASON_PROPOSITIONS:
            sat_receipts = tuple(r for r in receipts if r.observed_status == "sat")
            if len(sat_receipts) != 1 or type(signal.witness_artifact) is not UnaryOutcomeWitnessArtifact:
                raise ValueError("witnessed outcome signal lacks exact SAT witness authority")
            signal.witness_artifact.validate_against(sat_receipts[0])
            if signal.witness_artifact.reason_id != reason_id:
                raise ValueError("outcome witness reason differs from sealed matrix")
        elif signal.witness_artifact is not None:
            raise ValueError("non-witness outcome signal carries witness authority")
        if signal.producer_status == "timeout" and not any(
            receipt.observed_status == "timeout" for receipt in receipts
        ):
            raise ValueError("timeout outcome signal lacks a TIMEOUT execution receipt")
        if signal.producer_status != "timeout" and any(
            receipt.observed_status == "timeout" for receipt in receipts
        ):
            raise ValueError("non-timeout outcome signal carries a TIMEOUT receipt")
        return reason_id

    def _authority(self, session: Any, signal: Any, reason_id: str):
        proof_kind = str(signal.proof_requirement_identity.get("proof_kind", ""))
        expected_kind = f"unary_outcome_{signal.stage}"
        if proof_kind != expected_kind:
            raise ValueError("outcome proof requirement kind differs from stage")
        cause = self._cause_factory.create(
            reason_id=reason_id,
            identity_scope=IdentityScope.UNARY,
            target_kind="function_outcome_stage",
            canonical_target_key=(
                "function_outcome_seed_stage",
                canonical_value(signal.function_identity),
                signal.function_snapshot_fingerprint,
                signal.outcome_seed_digest,
                signal.outcome_seed_revision,
                signal.stage,
            ),
            missing_semantic_fact=("reachable_outcome_stage_proof", signal.stage),
            semantic_proposition=("reachable_outcome_stage_is_proved", signal.stage),
            observation_surface=("outcome_partition", "smt", signal.premise_digest),
            active_semantic_precondition=("outcome_seed_available", True),
            correspondence_contract=("unary_function_identity",),
        )
        requirement_id = "outcome-stage-" + authority_digest({
            "typed_requirement": canonical_value(signal.proof_requirement_identity),
        })[:32]
        requirement = ProofRequirement(
            requirement_id,
            proof_kind,
            ("typed_requirement", canonical_value(signal.proof_requirement_identity)),
        )
        bound = self._binding_factory.bind(
            contract_definition_id=RETURN_OUTCOME_STAGE_CONTRACT.contract_definition_id,
            contract_version=RETURN_OUTCOME_STAGE_CONTRACT.contract_version,
            bindings={"stage_proof": requirement},
        )
        occurrence_id = "outcome-stage-occ-" + authority_digest({
            "cause_id": cause.value,
            "result_occurrence_id": session.identity.result_occurrence_id,
        })[:32]
        evidence_refs = [authority_digest({
            "producer_evidence": canonical_value(signal.producer_evidence)
        })]
        evidence_refs.extend(receipt.receipt_digest for receipt in signal.execution_receipts)
        if signal.witness_artifact is not None:
            evidence_refs.append(signal.witness_artifact.artifact_digest)
        occurrence = CauseOccurrence(
            occurrence_id,
            cause,
            reason_id,
            authority_digest((signal.function_identity, signal.outcome_seed_digest, signal.stage)),
            "function_outcome_stage",
            IdentityScope.UNARY,
            bound.contract_definition_id,
            bound.contract_version,
            bound.normalized_expression_digest,
            bound.bound_expression_digest,
            (requirement_id,),
            tuple(evidence_refs),
            "return_outcome_producer_signal",
            session.identity.source_snapshot_fingerprint,
            "reachable_outcome_producer_v1",
            session.identity.execution_identity_digest,
        )
        return CauseOccurrenceAuthority(occurrence, bound), requirement_id

    @staticmethod
    def _solver_event(
        requirement_id: str,
        receipt: OutcomeStageExecutionReceipt,
        *,
        terminal_candidate: bool,
    ):
        event_type = {
            "unknown": EventType.SOLVER_UNKNOWN,
            "timeout": EventType.SOLVER_TIMEOUT,
            "error": EventType.SOLVER_ERROR,
        }[receipt.observed_status]
        payload = ReceiptBoundSolverExecutionEventAuthority(
            requirement_id,
            receipt.to_authority_dict(),
            terminal_candidate,
        )
        return EventIntent(event_type, payload)

    @staticmethod
    def _attempt_event(requirement_id: str, signal: Any) -> EventIntent:
        return EventIntent(
            EventType.OUTCOME_PRODUCER_ATTEMPT,
            OutcomeProducerAttemptEventAuthority(
                requirement_id,
                signal.stage,
                signal.producer_status,
                signal.producer_attempt_identity,
                signal.producer_attempt_ordinal,
                signal.execution_identity_digest,
            ),
        )

    def __call__(self, session: Any, signal: Any) -> tuple[EventIntent, ...]:
        reason_id = self._validate_signal(signal)
        if any(
            receipt.execution_identity_digest != signal.execution_identity_digest
            for receipt in signal.execution_receipts
        ):
            raise ValueError("outcome receipt execution identity differs from session")
        if signal.execution_identity_digest != session.identity.execution_identity_digest:
            raise ValueError("outcome signal execution identity differs from session")
        state = self._state(session)
        if reason_id is None:
            artifact = signal.validated_artifact_authority
            requirement_id = "outcome-stage-" + authority_digest({
                "typed_requirement": canonical_value(signal.proof_requirement_identity),
            })[:32]
            authority = state["authorities"].get(requirement_id)
            if authority is None or requirement_id in state["completed"]:
                return ()
            if (
                artifact.get("artifact_validation_status") != "validated"
                or artifact.get("stage") != signal.stage
                or artifact.get("outcome_seed_digest") != signal.outcome_seed_digest
                or artifact.get("outcome_seed_revision") != signal.outcome_seed_revision
                or artifact.get("function_snapshot_fingerprint")
                != signal.function_snapshot_fingerprint
                or artifact.get("premise_digest") != signal.premise_digest
                or canonical_value(artifact.get("requirement_id"))
                != canonical_value(signal.proof_requirement_identity)
            ):
                raise ValueError("outcome completion artifact differs from observed authority")
            state["completed"].add(requirement_id)
            receipt = RequirementCompletionReceipt(
                authority.occurrence.cause_id.value,
                authority.occurrence.occurrence_id,
                requirement_id,
                authority.bound_contract.contract_definition_id,
                authority.bound_contract.contract_version,
                authority.bound_contract.bound_expression_digest,
                str(artifact["artifact_id"]),
                authority_digest({
                    "artifact_authority_digest": artifact["artifact_authority_digest"],
                    "cause_id": authority.occurrence.cause_id.value,
                    "requirement_id": requirement_id,
                }),
            )
            attempt_key = signal.producer_attempt_identity
            intents = []
            if attempt_key not in state["attempts"]:
                state["attempts"].add(attempt_key)
                intents.append(self._attempt_event(requirement_id, signal))
            intents.append(EventIntent(
                EventType.REQUIREMENT_COMPLETED,
                RequirementCompletedEventAuthority(receipt),
            ))
            return tuple(intents)

        authority, requirement_id = self._authority(session, signal, reason_id)
        intents = []
        if requirement_id not in state["authorities"]:
            state["authorities"][requirement_id] = authority
            intents.append(EventIntent(
                EventType.CAUSE_OBSERVED,
                CauseObservedEventAuthority(authority),
            ))
        elif state["authorities"][requirement_id].occurrence.cause_id != authority.occurrence.cause_id:
            raise ValueError("outcome requirement was rebound to a different semantic cause")
        attempt_key = signal.producer_attempt_identity
        if attempt_key not in state["attempts"]:
            state["attempts"].add(attempt_key)
            intents.append(self._attempt_event(requirement_id, signal))
        for receipt in signal.execution_receipts:
            if receipt.observed_status not in {"unknown", "timeout", "error"}:
                continue
            if receipt.receipt_digest in state["receipts"]:
                continue
            state["receipts"].add(receipt.receipt_digest)
            intents.append(self._solver_event(
                requirement_id,
                receipt,
                terminal_candidate=(
                    receipt.observed_status == "timeout"
                    and signal.producer_status == "timeout"
                ),
            ))
        return tuple(intents)

    def has_observed(self, session: Any, signal: Any) -> bool:
        requirement_id = "outcome-stage-" + authority_digest({
            "typed_requirement": canonical_value(signal.proof_requirement_identity),
        })[:32]
        return requirement_id in self._state(session)["authorities"]

    def finalize_terminal_timeout_bindings(
        self, session: Any, stream: Any
    ) -> tuple[tuple[int, str], ...]:
        reduction = session.reducer.replay(stream)
        live_requirements = {
            row.proof_requirement_id
            for row in reduction.projection.q_open_base
        }
        attempt_markers = tuple(
            event
            for event in stream.events
            if (
                event.header.event_type == EventType.OUTCOME_PRODUCER_ATTEMPT
                and type(event.authority_payload)
                is OutcomeProducerAttemptEventAuthority
                and event.authority_payload.proof_requirement_id
                in live_requirements
            )
        )
        if not attempt_markers:
            return ()
        latest_marker_by_requirement = {}
        for event in attempt_markers:
            requirement_id = event.authority_payload.proof_requirement_id
            current = latest_marker_by_requirement.get(requirement_id)
            if (
                current is None
                or event.authority_payload.producer_attempt_ordinal
                > current.authority_payload.producer_attempt_ordinal
            ):
                latest_marker_by_requirement[requirement_id] = event
        winning_marker = max(
            latest_marker_by_requirement.values(),
            key=lambda event: event.authority_payload.producer_attempt_ordinal,
        )
        marker = winning_marker.authority_payload
        if marker.producer_status != "timeout":
            return ()
        winning_events = tuple(
            event for event in stream.events
            if (
                type(event.authority_payload)
                is ReceiptBoundSolverExecutionEventAuthority
                and event.authority_payload.proof_requirement_id
                == marker.proof_requirement_id
                and event.authority_payload.execution_receipt_authority[
                    "producer_attempt_identity"
                ] == marker.producer_attempt_identity
                and event.authority_payload.execution_receipt_authority[
                    "producer_attempt_ordinal"
                ] == marker.producer_attempt_ordinal
                and event.authority_payload.execution_receipt_authority[
                    "execution_identity_digest"
                ] == marker.execution_identity_digest
            )
        )
        timeout_candidates = tuple(
            event for event in winning_events
            if (
                event.header.event_type == EventType.SOLVER_TIMEOUT
                and event.authority_payload.terminal_candidate
            )
        )
        if not timeout_candidates:
            return ()
        latest = max(
            timeout_candidates, key=lambda event: event.header.sequence_number
        )
        return ((
            latest.header.sequence_number,
            latest.authority_payload.proof_requirement_id,
        ),)

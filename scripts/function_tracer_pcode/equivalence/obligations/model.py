"""Typed identities and states for obligation execution."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Mapping, Optional, Tuple

from ..cause_identity import ProofRequirementId


class ActivationState(str, Enum):
    DORMANT = "dormant"
    ELIGIBLE = "eligible"
    ACTIVE = "active"
    SHORT_CIRCUITED = "short_circuited"
    INAPPLICABLE = "inapplicable"
    COMPLETED = "completed"


class ExecutionState(str, Enum):
    PLANNED = "planned"
    READY = "ready"
    RUNNING = "running"
    COMPLETED = "completed"
    BLOCKED = "blocked"
    CANCELLED = "cancelled"
    FAILED = "failed"
    SUPERSEDED = "superseded"


class FunctionProofOutcome(str, Enum):
    EQUIVALENT = "equivalent"
    NOT_EQUIVALENT = "not_equivalent"
    INCONCLUSIVE = "inconclusive"


class UnaryArtifactDomain(str, Enum):
    """Semantic domain of a function-scoped, pair-independent artifact."""

    RETURN_OUTCOME_V1 = "return_outcome_v1"
    RETURN_WIDTH_V1 = "return_width_v1"

    @classmethod
    def normalize(cls, value: object) -> str:
        if isinstance(value, cls):
            return value.value
        return cls(str(value)).value


@dataclass(frozen=True)
class ObligationInstanceId:
    requirement_id: ProofRequirementId
    derived_view_id: Tuple[Any, ...]
    premise_digest: str
    planner_schema_version: int = 1

    def to_key(self) -> Tuple[Any, ...]:
        return (
            self.planner_schema_version,
            self.requirement_id.to_key(),
            self.derived_view_id,
            self.premise_digest,
        )


@dataclass(frozen=True)
class AttemptKey:
    """Cache lookup identity.  It intentionally excludes attempt generation."""

    obligation_instance_id: Tuple[Any, ...]
    producer_id: str
    producer_version: str
    encoding_version: str
    solver_identity: Tuple[Any, ...]
    timeout_budget: float
    execution_policy: Tuple[Any, ...] = ()

    def to_key(self) -> Tuple[Any, ...]:
        return (
            self.obligation_instance_id,
            self.producer_id,
            self.producer_version,
            self.encoding_version,
            self.solver_identity,
            float(self.timeout_budget),
            self.execution_policy,
        )


@dataclass(frozen=True)
class AttemptRecordId:
    attempt_key: AttemptKey
    attempt_generation: int
    scheduler_run_id: str

    def to_key(self) -> Tuple[Any, ...]:
        return (self.attempt_key.to_key(), self.attempt_generation, self.scheduler_run_id)


@dataclass(frozen=True)
class SemanticFactProvenance:
    fact_id: Tuple[Any, ...]
    source_snapshot_fact_ids: Tuple[Tuple[Any, ...], ...] = ()
    source_artifact_ids: Tuple[Tuple[Any, ...], ...] = ()
    normalization_rule_ids: Tuple[Tuple[Any, ...], ...] = ()
    builder_version: str = "1"


@dataclass(frozen=True)
class ProofArtifact:
    artifact_id: Tuple[Any, ...]
    requirement_id: ProofRequirementId
    produced_from_view_id: Tuple[Any, ...]
    premise_digest: str
    dependency_artifact_ids: Tuple[Tuple[Any, ...], ...] = ()
    producer_id: str = ""
    producer_version: str = "1"
    encoding_version: str = "1"
    artifact_validation_status: str = "pending"
    payload: Mapping[str, Any] = field(default_factory=dict, compare=False, hash=False)

    @property
    def is_validated(self) -> bool:
        return self.artifact_validation_status == "validated"

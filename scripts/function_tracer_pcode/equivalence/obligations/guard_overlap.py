"""Typed, generation-bound guard-overlap execution and reuse.

Guard overlap is deliberately non-decisive for function equivalence.  An
UNSAT result may close one case pair; SAT and UNKNOWN only control whether the
value obligation remains scheduled.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from enum import Enum
import hashlib
import hmac
import inspect
from pathlib import Path
import secrets
from typing import Any, Dict, Mapping, Optional, Tuple


_GUARD_ARTIFACT_AUTHORITY_KEY = secrets.token_bytes(32)
_TRUSTED_GUARD_QUERY_EXECUTOR_CODE: Any = None


def _guard_artifact_seal(payload: Tuple[Any, ...]) -> str:
    return hmac.new(
        _GUARD_ARTIFACT_AUTHORITY_KEY,
        repr(payload).encode("utf-8"),
        hashlib.sha256,
    ).hexdigest()


class WorkResultRole(str, Enum):
    PROOF_DECISION = "proof_decision"
    NON_DECISIONAL_EXECUTION = "non_decisional_execution"


class GuardOverlapStatus(str, Enum):
    UNSAT = "unsat"
    SAT = "sat"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class GuardRegionSeed:
    side: str
    case_index: int
    structural_condition_key: Tuple[Any, ...]
    rendered_condition_digest: str

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "guard_region_seed_v1",
            self.side,
            self.structural_condition_key,
            self.rendered_condition_digest,
        )


@dataclass(frozen=True)
class GuardOverlapRequirement:
    left_seed_key: Tuple[Any, ...]
    right_seed_key: Tuple[Any, ...]
    canonical_query_digest: str
    derived_view_id: Tuple[Any, ...]
    premise_digest: str
    graph_generation: int

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "guard_overlap_requirement_v1",
            self.left_seed_key,
            self.right_seed_key,
            self.canonical_query_digest,
            self.derived_view_id,
            self.premise_digest,
            self.graph_generation,
        )


@dataclass(frozen=True)
class GuardOverlapAttempt:
    requirement_key: Tuple[Any, ...]
    status: GuardOverlapStatus
    solver_identity: Tuple[Any, ...]
    timeout_budget: float
    query_digest: str


def _solver_result_digest(result: Any) -> str:
    parallel = getattr(result, "solver_results", None)
    raw_results = getattr(parallel, "results", ())
    if not isinstance(raw_results, (tuple, list)):
        raw_results = ()
    payload = (
        getattr(result, "is_equivalent", None),
        tuple(
            (
                getattr(item, "solver_name", None),
                str(getattr(item, "status", None)),
                getattr(item, "error_message", None),
            )
            for item in raw_results
        ),
    )
    return hashlib.sha256(repr(payload).encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class GuardQueryExecutionArtifact:
    """Formula-bound receipt issued only by the canonical guard executor."""

    requirement_key: Tuple[Any, ...]
    canonical_query_digest: str
    solver_result_digest: str
    solver_status: GuardOverlapStatus
    solver_identity: Tuple[Any, ...]
    derived_view_id: Tuple[Any, ...]
    premise_digest: str
    graph_generation: int
    issuer_identity: Tuple[Any, ...]
    authority_digest: str = ""
    schema_version: str = "guard_query_execution_artifact_v1"

    def _payload(self) -> Tuple[Any, ...]:
        return (
            self.requirement_key,
            self.canonical_query_digest,
            self.solver_result_digest,
            self.solver_status.value,
            self.solver_identity,
            self.derived_view_id,
            self.premise_digest,
            self.graph_generation,
            self.issuer_identity,
            self.schema_version,
        )

    def validates(
        self,
        requirement: GuardOverlapRequirement,
        attempt: GuardOverlapAttempt,
        raw_result: Any,
    ) -> bool:
        return (
            self.requirement_key == requirement.stable_key()
            and self.canonical_query_digest
            == requirement.canonical_query_digest
            and self.canonical_query_digest == attempt.query_digest
            and self.solver_result_digest == _solver_result_digest(raw_result)
            and self.solver_status == attempt.status
            and self.solver_status == status_from_query_result(raw_result)
            and self.solver_identity == attempt.solver_identity
            and self.derived_view_id == requirement.derived_view_id
            and self.premise_digest == requirement.premise_digest
            and self.graph_generation == requirement.graph_generation
            and self.issuer_identity
            == ("pairwise.canonical_guard_query_executor", "v1")
            and hmac.compare_digest(
                self.authority_digest,
                _guard_artifact_seal(self._payload()),
            )
        )

    def stable_key(self) -> Tuple[Any, ...]:
        return self._payload() + (self.authority_digest,)

    def receipt_digest(self) -> str:
        return hashlib.sha256(
            repr(self.stable_key()).encode("utf-8")
        ).hexdigest()


def register_guard_query_executor(executor: Any) -> None:
    """One-time registration from the production query executor module."""

    global _TRUSTED_GUARD_QUERY_EXECUTOR_CODE
    frame = inspect.currentframe()
    caller = frame.f_back if frame is not None else None
    try:
        caller_path = Path(caller.f_code.co_filename) if caller is not None else None
        if (
            caller is None
            or caller.f_code.co_name != "<module>"
            or caller_path is None
            or caller_path.name != "pairwise_query_executor.py"
            or caller_path.parent.name != "strategies"
        ):
            raise RuntimeError("guard query executor registrar is not trusted")
    finally:
        del caller
        del frame
    if _TRUSTED_GUARD_QUERY_EXECUTOR_CODE is not None:
        raise RuntimeError("guard query executor already registered")
    _TRUSTED_GUARD_QUERY_EXECUTOR_CODE = executor.__code__


def issue_guard_query_execution_artifact(
    requirement: GuardOverlapRequirement,
    attempt: GuardOverlapAttempt,
    raw_result: Any,
) -> GuardQueryExecutionArtifact:
    """Issue a receipt only from the registered canonical executor."""

    frame = inspect.currentframe()
    caller = frame.f_back if frame is not None else None
    try:
        if (
            caller is None
            or caller.f_code is not _TRUSTED_GUARD_QUERY_EXECUTOR_CODE
        ):
            raise RuntimeError("guard query artifact issuer is not trusted")
    finally:
        del caller
        del frame
    if attempt.requirement_key != requirement.stable_key():
        raise ValueError("guard query artifact requirement mismatch")
    if attempt.query_digest != requirement.canonical_query_digest:
        raise ValueError("guard query artifact formula mismatch")
    status = status_from_query_result(raw_result)
    if status != attempt.status:
        raise ValueError("guard query artifact solver status mismatch")
    artifact = GuardQueryExecutionArtifact(
        requirement.stable_key(),
        requirement.canonical_query_digest,
        _solver_result_digest(raw_result),
        status,
        attempt.solver_identity,
        requirement.derived_view_id,
        requirement.premise_digest,
        requirement.graph_generation,
        ("pairwise.canonical_guard_query_executor", "v1"),
    )
    return replace(
        artifact, authority_digest=_guard_artifact_seal(artifact._payload())
    )


@dataclass(frozen=True)
class GuardOverlapExecutionResult:
    attempt: GuardOverlapAttempt
    raw_result: Any
    query_artifact: Optional[GuardQueryExecutionArtifact] = None
    result_role: WorkResultRole = WorkResultRole.NON_DECISIONAL_EXECUTION

    @property
    def status(self) -> GuardOverlapStatus:
        return self.attempt.status


@dataclass(frozen=True)
class GuardDisjointArtifact:
    requirement_key: Tuple[Any, ...]
    query_digest: str
    derived_view_id: Tuple[Any, ...]
    premise_digest: str
    graph_generation: int
    query_execution_digest: str = ""
    query_issuer_identity: Tuple[Any, ...] = ()
    authority_digest: str = ""

    @classmethod
    def issue(cls, requirement: GuardOverlapRequirement) -> "GuardDisjointArtifact":
        raise RuntimeError("guard disjoint artifact issuer is not trusted")

    @classmethod
    def _issue_from_validated_query(
        cls,
        requirement: GuardOverlapRequirement,
        query_artifact: GuardQueryExecutionArtifact,
    ) -> "GuardDisjointArtifact":
        frame = inspect.currentframe()
        caller = frame.f_back if frame is not None else None
        try:
            if (
                caller is None
                or caller.f_code is not GuardOverlapGraph.record.__code__
            ):
                raise RuntimeError("guard disjoint artifact issuer is not trusted")
        finally:
            del caller
            del frame
        if query_artifact.solver_status != GuardOverlapStatus.UNSAT:
            raise ValueError("guard disjoint artifact requires typed UNSAT")
        payload = (
            requirement.stable_key(), requirement.canonical_query_digest,
            requirement.derived_view_id, requirement.premise_digest,
            requirement.graph_generation,
            query_artifact.receipt_digest(),
            query_artifact.issuer_identity,
        )
        return cls(
            requirement.stable_key(), requirement.canonical_query_digest,
            requirement.derived_view_id, requirement.premise_digest,
            requirement.graph_generation,
            query_artifact.receipt_digest(),
            query_artifact.issuer_identity,
            _guard_artifact_seal(payload),
        )

    def validates(self) -> bool:
        payload = (
            self.requirement_key, self.query_digest, self.derived_view_id,
            self.premise_digest, self.graph_generation,
            self.query_execution_digest, self.query_issuer_identity,
        )
        return (
            self.requirement_key[:1] == ("guard_overlap_requirement_v1",)
            and self.query_digest == self.requirement_key[3]
            and self.derived_view_id == self.requirement_key[4]
            and self.premise_digest == self.requirement_key[5]
            and self.graph_generation == self.requirement_key[6]
            and len(self.query_execution_digest) == 64
            and self.query_issuer_identity
            == ("pairwise.canonical_guard_query_executor", "v1")
            and hmac.compare_digest(
                self.authority_digest, _guard_artifact_seal(payload)
            )
        )


@dataclass(frozen=True)
class GuardOverlapNode:
    requirement: GuardOverlapRequirement
    result: GuardOverlapExecutionResult
    disjoint_artifact: Optional[GuardDisjointArtifact]


@dataclass
class GuardOverlapGraph:
    """One generation of canonical guard-overlap nodes.

    A node is reusable only within its exact view, premise and graph
    generation.  This prevents results from a superseded prepared surface from
    being carried into the replacement graph.
    """

    derived_view_id: Tuple[Any, ...]
    premise_digest: str
    generation: int = 1
    nodes: Dict[Tuple[Any, ...], GuardOverlapNode] = field(default_factory=dict)

    def requirement(
        self,
        left_seed: GuardRegionSeed,
        right_seed: GuardRegionSeed,
        canonical_query: str,
    ) -> GuardOverlapRequirement:
        digest = canonical_guard_query_digest(canonical_query)
        return GuardOverlapRequirement(
            left_seed.stable_key(),
            right_seed.stable_key(),
            digest,
            self.derived_view_id,
            self.premise_digest,
            self.generation,
        )

    def lookup(self, requirement: GuardOverlapRequirement) -> Optional[GuardOverlapNode]:
        if (
            requirement.derived_view_id != self.derived_view_id
            or requirement.premise_digest != self.premise_digest
            or requirement.graph_generation != self.generation
        ):
            return None
        return self.nodes.get(requirement.stable_key())

    def record(self, result: GuardOverlapExecutionResult) -> GuardOverlapNode:
        key = result.attempt.requirement_key
        if key[:1] != ("guard_overlap_requirement_v1",):
            raise ValueError("guard attempt is not bound to a typed requirement")
        requirement = GuardOverlapRequirement(
            left_seed_key=key[1],
            right_seed_key=key[2],
            canonical_query_digest=key[3],
            derived_view_id=key[4],
            premise_digest=key[5],
            graph_generation=key[6],
        )
        if self.lookup(requirement) is not None:
            return self.nodes[key]
        if result.attempt.query_digest != requirement.canonical_query_digest:
            raise ValueError("guard attempt query digest mismatch")
        query_artifact = result.query_artifact
        if (
            query_artifact is None
            or not query_artifact.validates(
                requirement, result.attempt, result.raw_result
            )
        ):
            raise ValueError(
                "guard result requires a typed canonical query artifact"
            )
        artifact = None
        if result.status == GuardOverlapStatus.UNSAT:
            artifact = GuardDisjointArtifact._issue_from_validated_query(
                requirement, query_artifact
            )
        node = GuardOverlapNode(requirement, result, artifact)
        self.nodes[key] = node
        return node

    def supersede(self) -> "GuardOverlapGraph":
        return GuardOverlapGraph(
            self.derived_view_id,
            self.premise_digest,
            generation=self.generation + 1,
        )


def guard_seed(side: str, case: Any, renderer: Any) -> GuardRegionSeed:
    conditions = tuple(getattr(case, "conditions", ()) or ())
    structural = tuple(
        condition.structural_key(budget=256)
        if callable(getattr(condition, "structural_key", None))
        else repr(condition)
        for condition in conditions
    )
    render_conditions = getattr(case, "get_conditions_smt", None)
    rendered = (
        tuple(render_conditions(renderer))
        if callable(render_conditions)
        else tuple(repr(condition) for condition in conditions)
    )
    rendered_digest = hashlib.sha256(repr(rendered).encode("utf-8")).hexdigest()
    return GuardRegionSeed(side, int(getattr(case, "index", -1)), structural, rendered_digest)


def status_from_query_result(result: Any) -> GuardOverlapStatus:
    semantic = getattr(result, "is_equivalent", None)
    if semantic is True:
        return GuardOverlapStatus.UNSAT
    if semantic is False:
        return GuardOverlapStatus.SAT
    return GuardOverlapStatus.UNKNOWN


def canonical_guard_query_digest(query: str) -> str:
    """Hash SMT semantics while ignoring diagnostic comments and whitespace."""
    semantic_lines = (
        " ".join(line.split())
        for line in query.splitlines()
        if line.strip() and not line.lstrip().startswith(";")
    )
    return hashlib.sha256("\n".join(semantic_lines).encode("utf-8")).hexdigest()

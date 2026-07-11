"""Proof expressions, sequential branch activation, and provenance validation."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
import hashlib
from typing import Callable, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from .model import ActivationState, FunctionProofOutcome, ProofArtifact


class ProofNodeKind(str, Enum):
    ALL_OF = "all_of"
    ANY_OF = "any_of"
    GATE = "gate"
    DECISIVE = "decisive"
    LEAF_OBLIGATION = "leaf_obligation"


@dataclass(frozen=True)
class ProofExpression:
    node_id: str
    kind: ProofNodeKind
    children: Tuple["ProofExpression", ...] = ()
    leaf_outcome: FunctionProofOutcome = FunctionProofOutcome.INCONCLUSIVE


@dataclass(frozen=True)
class ProofEvaluation:
    outcome: FunctionProofOutcome
    conflict_detected: bool = False
    conflicting_node_ids: Tuple[str, ...] = ()


class ProofExpressionEvaluator:
    @classmethod
    def evaluate(cls, expression: ProofExpression) -> ProofEvaluation:
        if expression.kind in {ProofNodeKind.LEAF_OBLIGATION, ProofNodeKind.GATE, ProofNodeKind.DECISIVE}:
            return ProofEvaluation(expression.leaf_outcome)
        evaluations = tuple(cls.evaluate(child) for child in expression.children)
        outcomes = tuple(item.outcome for item in evaluations)
        inherited_conflicts = tuple(
            node_id for item in evaluations for node_id in item.conflicting_node_ids
        )
        if expression.kind == ProofNodeKind.ALL_OF:
            if any(value == FunctionProofOutcome.NOT_EQUIVALENT for value in outcomes):
                return ProofEvaluation(
                    FunctionProofOutcome.NOT_EQUIVALENT,
                    bool(inherited_conflicts),
                    inherited_conflicts,
                )
            if outcomes and all(value == FunctionProofOutcome.EQUIVALENT for value in outcomes):
                return ProofEvaluation(FunctionProofOutcome.EQUIVALENT, bool(inherited_conflicts), inherited_conflicts)
            return ProofEvaluation(FunctionProofOutcome.INCONCLUSIVE, bool(inherited_conflicts), inherited_conflicts)
        if expression.kind == ProofNodeKind.ANY_OF:
            has_eq = any(value == FunctionProofOutcome.EQUIVALENT for value in outcomes)
            has_not_eq = any(value == FunctionProofOutcome.NOT_EQUIVALENT for value in outcomes)
            if has_eq and has_not_eq:
                nodes = inherited_conflicts + (expression.node_id,)
                return ProofEvaluation(FunctionProofOutcome.NOT_EQUIVALENT, True, nodes)
            if any(value == FunctionProofOutcome.EQUIVALENT for value in outcomes):
                return ProofEvaluation(FunctionProofOutcome.EQUIVALENT, bool(inherited_conflicts), inherited_conflicts)
            if outcomes and all(value == FunctionProofOutcome.NOT_EQUIVALENT for value in outcomes):
                return ProofEvaluation(FunctionProofOutcome.NOT_EQUIVALENT, bool(inherited_conflicts), inherited_conflicts)
            return ProofEvaluation(FunctionProofOutcome.INCONCLUSIVE, bool(inherited_conflicts), inherited_conflicts)
        raise ValueError(f"unsupported proof node kind: {expression.kind}")


@dataclass(frozen=True)
class BranchSpec:
    branch_id: str
    enabled: bool = True
    eligibility: Optional[Callable[[Mapping[str, FunctionProofOutcome]], bool]] = None


class BranchActivationController:
    """Versioned sequential policy matching the legacy stage runner."""

    policy_version = "legacy-sequential-v1"

    def __init__(self, branches: Sequence[BranchSpec]) -> None:
        self._branches = tuple(branches)
        self.states: Dict[str, ActivationState] = {
            branch.branch_id: ActivationState.DORMANT for branch in self._branches
        }
        self.outcomes: Dict[str, FunctionProofOutcome] = {}

    def next_branch(self, _untrusted_outcomes: Optional[Mapping[str, FunctionProofOutcome]] = None) -> Optional[str]:
        terminal_seen = any(
            value in {FunctionProofOutcome.EQUIVALENT, FunctionProofOutcome.NOT_EQUIVALENT}
            for branch_id, value in self.outcomes.items()
            if self.states.get(branch_id) == ActivationState.COMPLETED
        )
        if terminal_seen:
            for branch in self._branches:
                if self.states[branch.branch_id] in {ActivationState.DORMANT, ActivationState.ELIGIBLE}:
                    self.states[branch.branch_id] = ActivationState.SHORT_CIRCUITED
            return None
        for branch in self._branches:
            state = self.states[branch.branch_id]
            if state in {ActivationState.ACTIVE, ActivationState.COMPLETED, ActivationState.INAPPLICABLE, ActivationState.SHORT_CIRCUITED}:
                continue
            if not branch.enabled:
                self.states[branch.branch_id] = ActivationState.INAPPLICABLE
                continue
            if branch.eligibility is not None and not branch.eligibility(self.outcomes):
                self.states[branch.branch_id] = ActivationState.INAPPLICABLE
                continue
            self.states[branch.branch_id] = ActivationState.ACTIVE
            return branch.branch_id
        return None

    def record(self, branch_id: str, outcome: FunctionProofOutcome) -> None:
        if self.states.get(branch_id) != ActivationState.ACTIVE:
            raise ValueError(f"branch is not active: {branch_id}")
        self.outcomes[branch_id] = outcome
        self.states[branch_id] = ActivationState.COMPLETED
        if outcome in {FunctionProofOutcome.EQUIVALENT, FunctionProofOutcome.NOT_EQUIVALENT}:
            for branch in self._branches:
                if self.states[branch.branch_id] == ActivationState.DORMANT:
                    self.states[branch.branch_id] = ActivationState.SHORT_CIRCUITED


@dataclass(frozen=True)
class ValidatedProofClosure:
    closure_id: Tuple[object, ...]
    root_artifact_ids: Tuple[Tuple[object, ...], ...]
    transitive_dependency_ids: Tuple[Tuple[object, ...], ...]
    topological_order: Tuple[Tuple[object, ...], ...]
    validation_digest: str

    @property
    def is_internally_consistent(self) -> bool:
        return self.validation_digest == _closure_validation_digest(
            self.closure_id,
            self.root_artifact_ids,
            self.transitive_dependency_ids,
            self.topological_order,
        )


def _closure_validation_digest(
    closure_id: Tuple[object, ...],
    roots: Tuple[Tuple[object, ...], ...],
    transitive: Tuple[Tuple[object, ...], ...],
    order: Tuple[Tuple[object, ...], ...],
) -> str:
    return hashlib.sha256(
        repr(
            (
                "validated-proof-closure-v2",
                closure_id,
                roots,
                transitive,
                order,
            )
        ).encode("utf-8")
    ).hexdigest()


@dataclass(frozen=True)
class ViewPremiseRecord:
    view_id: Tuple[object, ...]
    premise_digest: str
    available_artifact_ids: Tuple[Tuple[object, ...], ...] = ()
    parent_view_id: Optional[Tuple[object, ...]] = None


@dataclass(frozen=True)
class ArtifactApplicabilityRecord:
    artifact_id: Tuple[object, ...]
    source_view_id: Tuple[object, ...]
    target_view_id: Tuple[object, ...]
    premise_digest: str
    candidate_independent: bool
    status: str
    validated_closure_id: Tuple[object, ...]


def validate_proof_closure(
    artifacts: Iterable[ProofArtifact],
    root_artifact_ids: Iterable[Tuple[object, ...]],
    view_records: Mapping[Tuple[object, ...], ViewPremiseRecord],
) -> ValidatedProofClosure:
    materialized_artifacts = tuple(artifacts)
    artifact_ids = tuple(artifact.artifact_id for artifact in materialized_artifacts)
    duplicate_ids = tuple(
        sorted(
            {artifact_id for artifact_id in artifact_ids if artifact_ids.count(artifact_id) > 1},
            key=repr,
        )
    )
    if duplicate_ids:
        raise ValueError(f"duplicate proof artifact ids: {duplicate_ids!r}")
    by_id = {artifact.artifact_id: artifact for artifact in materialized_artifacts}
    roots = tuple(root_artifact_ids)
    order = []
    visiting = set()
    visited = set()

    def visit(artifact_id: Tuple[object, ...]) -> None:
        if artifact_id in visiting:
            raise ValueError("cyclic proof provenance")
        if artifact_id in visited:
            return
        artifact = by_id.get(artifact_id)
        if artifact is None:
            raise ValueError(f"missing proof dependency: {artifact_id!r}")
        if not artifact.is_validated:
            raise ValueError(f"unvalidated proof artifact: {artifact_id!r}")
        if artifact_id in artifact.dependency_artifact_ids:
            raise ValueError("self-justifying proof artifact")
        source_view = view_records.get(artifact.produced_from_view_id)
        if source_view is None:
            raise ValueError(f"unknown proof source view: {artifact.produced_from_view_id!r}")
        if source_view.premise_digest != artifact.premise_digest:
            raise ValueError(f"proof premise mismatch: {artifact_id!r}")
        unavailable = set(artifact.dependency_artifact_ids) - set(source_view.available_artifact_ids)
        if unavailable:
            raise ValueError(f"proof dependency unavailable in source view: {sorted(unavailable, key=repr)!r}")
        visiting.add(artifact_id)
        for dependency_id in artifact.dependency_artifact_ids:
            visit(dependency_id)
        visiting.remove(artifact_id)
        visited.add(artifact_id)
        order.append(artifact_id)

    for root_id in roots:
        visit(root_id)
    transitive = tuple(item for item in order if item not in roots)
    closure_id = ("proof_closure", tuple(order))
    topological_order = tuple(order)
    return ValidatedProofClosure(
        closure_id,
        roots,
        transitive,
        topological_order,
        _closure_validation_digest(closure_id, roots, transitive, topological_order),
    )


def validate_artifact_applicability(
    artifact: ProofArtifact,
    *,
    source_view: ViewPremiseRecord,
    target_view: ViewPremiseRecord,
    candidate_independent_premise_digest: str,
    validated_closure_id: Tuple[object, ...],
) -> ArtifactApplicabilityRecord:
    if source_view.view_id != artifact.produced_from_view_id:
        raise ValueError("artifact source view mismatch")
    if source_view.premise_digest != artifact.premise_digest:
        raise ValueError("artifact source premise mismatch")
    candidate_independent = candidate_independent_premise_digest == target_view.premise_digest
    return ArtifactApplicabilityRecord(
        artifact_id=artifact.artifact_id,
        source_view_id=source_view.view_id,
        target_view_id=target_view.view_id,
        premise_digest=target_view.premise_digest,
        candidate_independent=candidate_independent,
        status="applicable" if candidate_independent else "requires_reproof",
        validated_closure_id=validated_closure_id,
    )

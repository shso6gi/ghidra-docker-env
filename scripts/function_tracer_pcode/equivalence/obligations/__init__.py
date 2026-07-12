"""Proof-obligation execution model used by equivalence strategies.

The package is deliberately independent from Ghidra and solver implementations.
It supplies stable identities, immutable view fingerprints, proof provenance,
branch activation, and process-local caches.  Existing strategy facades remain
the production dispatch surface while migration to obligation scheduling is in
progress.
"""

from .cache import AttemptCache, AttemptCacheEntry, ProofCache, ProofCacheEntry
from .decision import DecisionAggregation, DecisionAggregator
from .model import (
    ActivationState,
    AttemptKey,
    AttemptRecordId,
    ExecutionState,
    FunctionProofOutcome,
    ObligationInstanceId,
    ProofArtifact,
    SemanticFactProvenance,
)
from .proof import (
    ArtifactApplicabilityRecord,
    BranchActivationController,
    BranchSpec,
    ProofExpression,
    ProofExpressionEvaluator,
    ProofEvaluation,
    ProofNodeKind,
    ValidatedProofClosure,
    ViewPremiseRecord,
    validate_artifact_applicability,
    validate_proof_closure,
)
from .snapshot import AnalysisSnapshot, DerivedAnalysisView, SnapshotFingerprintCodec
from .shadow import (
    LegacyExecutionSnapshot,
    ProductionShadowValidation,
    ProductionShadowValidator,
    ShadowComparisonReport,
)
from .runtime import (
    ObligationExecutionEvent,
    ObligationRuntimeSession,
    PendingCounterexampleSafety,
)
from .stage_runner import (
    BranchExecutionRecord,
    InternalBranchTrace,
    ProofGateProjection,
    project_proof_gates,
    run_obligation_branch_plan,
)
from .worklist import ProofWorklist, WorkItem

__all__ = (
    "ActivationState", "AnalysisSnapshot", "ArtifactApplicabilityRecord", "AttemptCache", "AttemptCacheEntry",
    "AttemptKey", "AttemptRecordId", "BranchActivationController", "BranchSpec",
    "BranchExecutionRecord", "DecisionAggregation", "DecisionAggregator", "DerivedAnalysisView", "ExecutionState", "FunctionProofOutcome",
    "ObligationInstanceId", "ObligationExecutionEvent", "ObligationRuntimeSession", "PendingCounterexampleSafety", "ProofArtifact", "ProofCache", "ProofCacheEntry",
    "ProofExpression", "ProofExpressionEvaluator", "ProofEvaluation", "ProofNodeKind", "ProofWorklist",
    "InternalBranchTrace", "LegacyExecutionSnapshot", "ProductionShadowValidation", "ProductionShadowValidator", "ProofGateProjection", "SemanticFactProvenance", "ShadowComparisonReport", "SnapshotFingerprintCodec", "ValidatedProofClosure",
    "ViewPremiseRecord", "WorkItem", "project_proof_gates", "run_obligation_branch_plan", "validate_artifact_applicability", "validate_proof_closure",
)

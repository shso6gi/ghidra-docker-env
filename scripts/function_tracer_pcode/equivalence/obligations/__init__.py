"""Proof-obligation execution model used by equivalence strategies.

The package is deliberately independent from Ghidra and solver implementations.
It supplies stable identities, immutable view fingerprints, proof provenance,
branch activation, and process-local caches.  Existing strategy facades remain
the production dispatch surface while migration to obligation scheduling is in
progress.
"""

from .cache import AttemptCache, AttemptCacheEntry, ProofCache, ProofCacheEntry
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
from .worklist import ProofWorklist, WorkItem

__all__ = (
    "ActivationState", "AnalysisSnapshot", "ArtifactApplicabilityRecord", "AttemptCache", "AttemptCacheEntry",
    "AttemptKey", "AttemptRecordId", "BranchActivationController", "BranchSpec",
    "DerivedAnalysisView", "ExecutionState", "FunctionProofOutcome",
    "ObligationInstanceId", "ProofArtifact", "ProofCache", "ProofCacheEntry",
    "ProofExpression", "ProofExpressionEvaluator", "ProofEvaluation", "ProofNodeKind", "ProofWorklist",
    "SemanticFactProvenance", "SnapshotFingerprintCodec", "ValidatedProofClosure",
    "ViewPremiseRecord", "WorkItem", "validate_artifact_applicability", "validate_proof_closure",
)

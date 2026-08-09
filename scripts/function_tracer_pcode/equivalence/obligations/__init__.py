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
    DecisivenessSnapshot,
    LegacyExecutionSnapshot,
    ProductionShadowValidation,
    ProductionShadowValidator,
    ShadowComparisonReport,
    SolverOutcomeClass,
)
from .runtime import (
    ObligationExecutionEvent,
    ObligationRuntimeSession,
    PendingCounterexampleSafety,
)
from .return_width import (
    RETURN_WIDTH_ENCODING_VERSION,
    RETURN_WIDTH_PRODUCER_VERSION,
    UnaryWidthProofResult,
    prove_function_return_width,
    return_width_requirement,
)
from .outcome_partition import (
    UnaryPartitionProofResult,
    UnaryProducerResult,
    outcome_seed_digest,
    prove_unary_partition,
    requirement_for_stage,
)
from .stage_runner import (
    BranchExecutionRecord,
    InternalBranchTrace,
    ProofGateProjection,
    project_proof_gates,
    run_obligation_branch_plan,
)
from .worklist import ProofWorklist, WorkItem
from .guard_overlap import (
    GuardDisjointArtifact,
    GuardOverlapAttempt,
    GuardOverlapExecutionResult,
    GuardOverlapGraph,
    GuardQueryExecutionArtifact,
    GuardOverlapRequirement,
    GuardOverlapStatus,
    GuardRegionSeed,
    WorkResultRole,
    canonical_guard_query_digest,
    guard_seed,
    status_from_query_result,
)
from .pair_disposition import (
    LedgerLifecycle,
    PairClosureEvidence,
    PairClosureKind,
    PairDisposition,
    PairDispositionLedger,
    PairLedgerBinding,
    PairLedgerPromotionState,
    PairLedgerSuccessorIntent,
    PairLedgerSuccessorPlan,
    CounterexampleSafetyReceipt,
    SolverQueryExecutionReceipt,
    StructuralEqualityReceipt,
    issue_structural_equality_receipt,
    register_structural_equality_producer,
    RuntimeQuiescenceCertificate,
    GuardUnsatClosureArtifact,
    SolverUnsatClosureArtifact,
    StructuralEqualityClosureArtifact,
    TerminalPairArtifact,
    PairLedgerManager,
)

__all__ = (
    "ActivationState", "AnalysisSnapshot", "ArtifactApplicabilityRecord", "AttemptCache", "AttemptCacheEntry",
    "AttemptKey", "AttemptRecordId", "BranchActivationController", "BranchSpec",
    "BranchExecutionRecord", "DecisionAggregation", "DecisionAggregator", "DerivedAnalysisView", "ExecutionState", "FunctionProofOutcome",
    "ObligationInstanceId", "ObligationExecutionEvent", "ObligationRuntimeSession", "PendingCounterexampleSafety", "ProofArtifact", "ProofCache", "ProofCacheEntry",
    "ProofExpression", "ProofExpressionEvaluator", "ProofEvaluation", "ProofNodeKind", "ProofWorklist",
    "InternalBranchTrace", "LegacyExecutionSnapshot", "ProductionShadowValidation", "ProductionShadowValidator", "ProofGateProjection", "SemanticFactProvenance", "ShadowComparisonReport", "SnapshotFingerprintCodec", "ValidatedProofClosure", "DecisivenessSnapshot", "SolverOutcomeClass",
    "ViewPremiseRecord", "WorkItem", "project_proof_gates", "run_obligation_branch_plan", "validate_artifact_applicability", "validate_proof_closure",
    "UnaryPartitionProofResult", "UnaryProducerResult", "outcome_seed_digest", "prove_unary_partition", "requirement_for_stage",
    "UnaryWidthProofResult", "prove_function_return_width", "return_width_requirement",
    "RETURN_WIDTH_PRODUCER_VERSION", "RETURN_WIDTH_ENCODING_VERSION",
    "GuardDisjointArtifact", "GuardOverlapAttempt", "GuardOverlapExecutionResult",
    "GuardOverlapGraph", "GuardOverlapRequirement", "GuardOverlapStatus", "GuardQueryExecutionArtifact",
    "GuardRegionSeed", "WorkResultRole", "canonical_guard_query_digest", "guard_seed", "status_from_query_result",
    "LedgerLifecycle", "PairClosureEvidence", "PairClosureKind", "PairDisposition",
    "PairDispositionLedger", "PairLedgerBinding", "PairLedgerPromotionState", "PairLedgerSuccessorIntent", "PairLedgerSuccessorPlan", "RuntimeQuiescenceCertificate",
    "GuardUnsatClosureArtifact", "CounterexampleSafetyReceipt",
    "SolverQueryExecutionReceipt", "StructuralEqualityReceipt",
    "issue_structural_equality_receipt", "register_structural_equality_producer",
    "SolverUnsatClosureArtifact", "StructuralEqualityClosureArtifact",
    "TerminalPairArtifact", "PairLedgerManager",
)

"""Proof-obligation execution model used by equivalence strategies.

The package is deliberately independent from Ghidra and solver implementations.
It supplies stable identities, immutable view fingerprints, proof provenance,
branch activation, and process-local caches.  Existing strategy facades remain
the production dispatch surface while migration to obligation scheduling is in
progress.

Names are resolved lazily on first access so importing a submodule never
pulls in the whole layer (and cannot create import cycles)."""

from importlib import import_module

_LAZY = {
    "ActivationState": ("scripts.function_tracer_pcode.proof.obligations.model", "ActivationState"),
    "AnalysisSnapshot": ("scripts.function_tracer_pcode.proof.obligations.snapshot", "AnalysisSnapshot"),
    "ArtifactApplicabilityRecord": ("scripts.function_tracer_pcode.proof.obligations.proof", "ArtifactApplicabilityRecord"),
    "AttemptCache": ("scripts.function_tracer_pcode.proof.obligations.cache", "AttemptCache"),
    "AttemptCacheEntry": ("scripts.function_tracer_pcode.proof.obligations.cache", "AttemptCacheEntry"),
    "AttemptKey": ("scripts.function_tracer_pcode.proof.obligations.model", "AttemptKey"),
    "AttemptRecordId": ("scripts.function_tracer_pcode.proof.obligations.model", "AttemptRecordId"),
    "BranchActivationController": ("scripts.function_tracer_pcode.proof.obligations.proof", "BranchActivationController"),
    "BranchExecutionRecord": ("scripts.function_tracer_pcode.proof.obligations.stage_runner", "BranchExecutionRecord"),
    "BranchSpec": ("scripts.function_tracer_pcode.proof.obligations.proof", "BranchSpec"),
    "CounterexampleSafetyReceipt": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "CounterexampleSafetyReceipt"),
    "CrossSideIdentification": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "CrossSideIdentification"),
    "DecisionAggregation": ("scripts.function_tracer_pcode.proof.obligations.decision", "DecisionAggregation"),
    "DecisionAggregator": ("scripts.function_tracer_pcode.proof.obligations.decision", "DecisionAggregator"),
    "DecisivenessSnapshot": ("scripts.function_tracer_pcode.proof.obligations.shadow", "DecisivenessSnapshot"),
    "DerivedAnalysisView": ("scripts.function_tracer_pcode.proof.obligations.snapshot", "DerivedAnalysisView"),
    "ExecutionState": ("scripts.function_tracer_pcode.proof.obligations.model", "ExecutionState"),
    "FunctionProofOutcome": ("scripts.function_tracer_pcode.proof.obligations.model", "FunctionProofOutcome"),
    "GuardDisjointArtifact": ("scripts.function_tracer_pcode.proof.obligations.guard_overlap", "GuardDisjointArtifact"),
    "GuardOverlapAttempt": ("scripts.function_tracer_pcode.proof.obligations.guard_overlap", "GuardOverlapAttempt"),
    "GuardOverlapExecutionResult": ("scripts.function_tracer_pcode.proof.obligations.guard_overlap", "GuardOverlapExecutionResult"),
    "GuardOverlapGraph": ("scripts.function_tracer_pcode.proof.obligations.guard_overlap", "GuardOverlapGraph"),
    "GuardOverlapRequirement": ("scripts.function_tracer_pcode.proof.obligations.guard_overlap", "GuardOverlapRequirement"),
    "GuardOverlapStatus": ("scripts.function_tracer_pcode.proof.obligations.guard_overlap", "GuardOverlapStatus"),
    "GuardQueryExecutionArtifact": ("scripts.function_tracer_pcode.proof.obligations.guard_overlap", "GuardQueryExecutionArtifact"),
    "GuardRegionSeed": ("scripts.function_tracer_pcode.proof.obligations.guard_overlap", "GuardRegionSeed"),
    "GuardUnsatClosureArtifact": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "GuardUnsatClosureArtifact"),
    "InternalBranchTrace": ("scripts.function_tracer_pcode.proof.obligations.stage_runner", "InternalBranchTrace"),
    "LedgerLifecycle": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "LedgerLifecycle"),
    "LegacyExecutionSnapshot": ("scripts.function_tracer_pcode.proof.obligations.shadow", "LegacyExecutionSnapshot"),
    "ObligationExecutionEvent": ("scripts.function_tracer_pcode.proof.obligations.runtime", "ObligationExecutionEvent"),
    "ObligationInstanceId": ("scripts.function_tracer_pcode.proof.obligations.model", "ObligationInstanceId"),
    "ObligationRuntimeSession": ("scripts.function_tracer_pcode.proof.obligations.runtime", "ObligationRuntimeSession"),
    "PairClosureEvidence": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "PairClosureEvidence"),
    "PairClosureKind": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "PairClosureKind"),
    "PairDisposition": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "PairDisposition"),
    "PairDispositionLedger": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "PairDispositionLedger"),
    "PairLedgerBinding": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "PairLedgerBinding"),
    "PairLedgerManager": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "PairLedgerManager"),
    "PairLedgerPromotionState": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "PairLedgerPromotionState"),
    "PairLedgerSuccessorIntent": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "PairLedgerSuccessorIntent"),
    "PairLedgerSuccessorPlan": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "PairLedgerSuccessorPlan"),
    "PendingCounterexampleSafety": ("scripts.function_tracer_pcode.proof.obligations.runtime", "PendingCounterexampleSafety"),
    "ProductionShadowValidation": ("scripts.function_tracer_pcode.proof.obligations.shadow", "ProductionShadowValidation"),
    "ProductionShadowValidator": ("scripts.function_tracer_pcode.proof.obligations.shadow", "ProductionShadowValidator"),
    "ProofArtifact": ("scripts.function_tracer_pcode.proof.obligations.model", "ProofArtifact"),
    "ProofCache": ("scripts.function_tracer_pcode.proof.obligations.cache", "ProofCache"),
    "ProofCacheEntry": ("scripts.function_tracer_pcode.proof.obligations.cache", "ProofCacheEntry"),
    "ProofEvaluation": ("scripts.function_tracer_pcode.proof.obligations.proof", "ProofEvaluation"),
    "ProofExpression": ("scripts.function_tracer_pcode.proof.obligations.proof", "ProofExpression"),
    "ProofExpressionEvaluator": ("scripts.function_tracer_pcode.proof.obligations.proof", "ProofExpressionEvaluator"),
    "ProofGateProjection": ("scripts.function_tracer_pcode.proof.obligations.stage_runner", "ProofGateProjection"),
    "ProofNodeKind": ("scripts.function_tracer_pcode.proof.obligations.proof", "ProofNodeKind"),
    "ProofWorklist": ("scripts.function_tracer_pcode.proof.obligations.worklist", "ProofWorklist"),
    "RETURN_WIDTH_ENCODING_VERSION": ("scripts.function_tracer_pcode.proof.obligations.return_width", "RETURN_WIDTH_ENCODING_VERSION"),
    "RETURN_WIDTH_PRODUCER_VERSION": ("scripts.function_tracer_pcode.proof.obligations.return_width", "RETURN_WIDTH_PRODUCER_VERSION"),
    "RuntimeQuiescenceCertificate": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "RuntimeQuiescenceCertificate"),
    "SemanticFactProvenance": ("scripts.function_tracer_pcode.proof.obligations.model", "SemanticFactProvenance"),
    "ShadowComparisonReport": ("scripts.function_tracer_pcode.proof.obligations.shadow", "ShadowComparisonReport"),
    "SnapshotFingerprintCodec": ("scripts.function_tracer_pcode.proof.obligations.snapshot", "SnapshotFingerprintCodec"),
    "SolverOutcomeClass": ("scripts.function_tracer_pcode.proof.obligations.shadow", "SolverOutcomeClass"),
    "SolverQueryExecutionReceipt": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "SolverQueryExecutionReceipt"),
    "SolverUnsatClosureArtifact": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "SolverUnsatClosureArtifact"),
    "StructuralEqualityClosureArtifact": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "StructuralEqualityClosureArtifact"),
    "StructuralEqualityReceipt": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "StructuralEqualityReceipt"),
    "TerminalPairArtifact": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "TerminalPairArtifact"),
    "UnaryPartitionProofResult": ("scripts.function_tracer_pcode.proof.obligations.outcome_partition", "UnaryPartitionProofResult"),
    "UnaryProducerResult": ("scripts.function_tracer_pcode.proof.obligations.outcome_partition", "UnaryProducerResult"),
    "UnaryWidthProofResult": ("scripts.function_tracer_pcode.proof.obligations.return_width", "UnaryWidthProofResult"),
    "ValidatedProofClosure": ("scripts.function_tracer_pcode.proof.obligations.proof", "ValidatedProofClosure"),
    "ViewPremiseRecord": ("scripts.function_tracer_pcode.proof.obligations.proof", "ViewPremiseRecord"),
    "WorkItem": ("scripts.function_tracer_pcode.proof.obligations.worklist", "WorkItem"),
    "WorkResultRole": ("scripts.function_tracer_pcode.proof.obligations.guard_overlap", "WorkResultRole"),
    "canonical_guard_query_digest": ("scripts.function_tracer_pcode.proof.obligations.guard_overlap", "canonical_guard_query_digest"),
    "closure_identification_floor": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "closure_identification_floor"),
    "guard_seed": ("scripts.function_tracer_pcode.proof.obligations.guard_overlap", "guard_seed"),
    "issue_structural_equality_receipt": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "issue_structural_equality_receipt"),
    "outcome_seed_digest": ("scripts.function_tracer_pcode.proof.obligations.outcome_partition", "outcome_seed_digest"),
    "project_proof_gates": ("scripts.function_tracer_pcode.proof.obligations.stage_runner", "project_proof_gates"),
    "prove_function_return_width": ("scripts.function_tracer_pcode.proof.obligations.return_width", "prove_function_return_width"),
    "prove_unary_partition": ("scripts.function_tracer_pcode.proof.obligations.outcome_partition", "prove_unary_partition"),
    "register_structural_equality_producer": ("scripts.function_tracer_pcode.proof.obligations.pair_disposition", "register_structural_equality_producer"),
    "requirement_for_stage": ("scripts.function_tracer_pcode.proof.obligations.outcome_partition", "requirement_for_stage"),
    "return_width_requirement": ("scripts.function_tracer_pcode.proof.obligations.return_width", "return_width_requirement"),
    "run_obligation_branch_plan": ("scripts.function_tracer_pcode.proof.obligations.stage_runner", "run_obligation_branch_plan"),
    "status_from_query_result": ("scripts.function_tracer_pcode.proof.obligations.guard_overlap", "status_from_query_result"),
    "validate_artifact_applicability": ("scripts.function_tracer_pcode.proof.obligations.proof", "validate_artifact_applicability"),
    "validate_proof_closure": ("scripts.function_tracer_pcode.proof.obligations.proof", "validate_proof_closure"),
}

__all__ = sorted(_LAZY)


def __getattr__(name):
    try:
        module_name, attribute = _LAZY[name]
    except KeyError:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}") from None
    value = getattr(import_module(module_name), attribute)
    globals()[name] = value
    return value


def __dir__():
    return sorted(set(globals()) | set(_LAZY))

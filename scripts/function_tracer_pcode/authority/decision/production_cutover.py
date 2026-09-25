"""Atomic five-value production decision cutover.

This module owns the one-way projection from a verified ``DecisionReceipt`` to
legacy compatibility fields.  Consumers must read ``final_outcome`` (or the
receipt itself); solver rows and ``is_equivalent`` are never final authority.
"""

from __future__ import annotations

import json
import argparse
from pathlib import Path
from typing import Any, Mapping

from scripts.function_tracer_pcode.authority.contracts import (
    BATCH_RESUME_DISPOSITION_BY_OUTCOME,
    CLI_EXIT_CODE_BY_OUTCOME,
    Outcome,
)
from scripts.function_tracer_pcode.authority.decision.conditional import (
    conditional_decision_receipt_from_payload,
    conditional_decision_receipt_payload,
    validate_conditional_decision_join,
)
from scripts.function_tracer_pcode.authority.decision.decision import DecisionReceipt
from scripts.function_tracer_pcode.authority.process.process_identity import (
    process_is_alive,
)
from scripts.function_tracer_pcode.authority.process.terminal_driver import (
    inspect as inspect_terminal,
)
from scripts.function_tracer_pcode.authority.process.terminal_recovery import StepKind


RETRY_FALLBACK_MATRIX: Mapping[Outcome, tuple[str, ...]] = {
    Outcome.EQUIVALENT: ("STOP",),
    Outcome.NOT_EQ: ("STOP",),
    Outcome.UNKNOWN: ("RETRY_TYPED_PROOF", "FALLBACK_NEXT_STRATEGY", "STOP"),
    Outcome.TIMEOUT: ("RETRY_WITH_LARGER_BUDGET", "FALLBACK_NEXT_STRATEGY", "STOP"),
    Outcome.ERROR: ("STOP",),
}

BATCH_RESUME_MATRIX = BATCH_RESUME_DISPOSITION_BY_OUTCOME

# Compatibility name retained for callers; the mapping has one authority.
CLI_EXIT_MATRIX = CLI_EXIT_CODE_BY_OUTCOME


def decision_receipt_payload(receipt: DecisionReceipt) -> dict[str, str]:
    """Return the strict public representation of one validated receipt."""

    if type(receipt) is not DecisionReceipt:
        raise TypeError("canonical result requires an exact DecisionReceipt")
    receipt.validate()
    return {
        "result_occurrence_id": receipt.result_occurrence_id,
        "outcome": receipt.outcome.value,
        "lifecycle_projection_digest": receipt.lifecycle_projection_digest,
        "authority_input_digest": receipt.authority_input_digest,
        "receipt_digest": receipt.receipt_digest,
    }


def attach_conditional_decision(result: Any, receipt: Any) -> Any:
    """Install the conditional column without touching the unconditional one.

    ``is_equivalent``, ``final_outcome`` and ``decision_receipt`` keep the
    values the unconditional lane gave them; a conditional proof can only ever
    add a separate column.
    """
    payload = conditional_decision_receipt_payload(receipt)
    unconditional = outcome_from_result(result)
    if unconditional is not Outcome.UNKNOWN:
        raise ValueError("the conditional lane runs only after an unconditional UNKNOWN")
    validate_conditional_decision_join(
        receipt,
        result_occurrence_id=result.decision_receipt.result_occurrence_id,
        unconditional_outcome=unconditional,
        unconditional_receipt_digest=result.decision_receipt.receipt_digest,
    )
    result.conditional_decision_receipt = receipt
    result.conditional_outcome = payload["conditional_outcome"]
    return result


def conditional_outcome_from_payload(payload: Mapping[str, Any]) -> Outcome | None:
    """Validate a serialized conditional column; ``None`` when there is none.

    The column is only accepted when it joins the unconditional decision of the
    same payload: same pair, same ``DecisionReceipt`` digest, same unconditional
    outcome.  ``outcome_from_payload`` validates that outer receipt first, so a
    conditional result can never be read next to a decision it did not follow.
    """

    receipt_payload = payload.get("conditional_decision_receipt")
    declared = payload.get("conditional_outcome")
    if receipt_payload is None:
        if declared is not None:
            raise ValueError("conditional outcome without its conditional receipt")
        return None
    receipt = conditional_decision_receipt_from_payload(receipt_payload)
    if declared != receipt.conditional_outcome.value:
        raise ValueError("payload conditional_outcome contradicts its receipt")
    outer = payload.get("decision_receipt")
    if not isinstance(outer, Mapping):
        raise ValueError("conditional column without its unconditional decision receipt")
    unconditional = outcome_from_payload(payload)
    validate_conditional_decision_join(
        receipt,
        result_occurrence_id=outer["result_occurrence_id"],
        unconditional_outcome=unconditional,
        unconditional_receipt_digest=outer["receipt_digest"],
    )
    return receipt.conditional_outcome


def _relation_payload(row: Any) -> dict[str, Any]:
    if not hasattr(row, "__dataclass_fields__"):
        raise TypeError("canonical relation row must be a sealed dataclass")
    return {
        name: getattr(row, name)
        for name in row.__dataclass_fields__
        if not name.startswith("_")
    }


def attach_canonical_relations(result: Any, projection: Any) -> Any:
    projection.validate()
    receipt = getattr(result, "decision_receipt", None)
    if (
        type(receipt) is not DecisionReceipt
        or receipt.result_occurrence_id != projection.result_occurrence_id
        or receipt.lifecycle_projection_digest
        != projection.lifecycle_projection_digest
    ):
        raise ValueError("canonical relations do not join DecisionReceipt")
    result.canonical_c_active_base = tuple(
        _relation_payload(row) for row in projection.c_active_base
    )
    result.canonical_q_open_base = tuple(
        _relation_payload(row) for row in projection.q_open_base
    )
    return result


def attach_canonical_decision(result: Any, receipt: DecisionReceipt) -> Any:
    """Install the receipt and derive compatibility fields in one operation."""

    decision_receipt_payload(receipt)
    result.decision_receipt = receipt
    result.final_outcome = receipt.outcome.value
    result.is_equivalent = {
        Outcome.EQUIVALENT: True,
        Outcome.NOT_EQ: False,
        Outcome.UNKNOWN: None,
        Outcome.TIMEOUT: None,
        Outcome.ERROR: None,
    }[receipt.outcome]
    result.canonical_decision_required = True
    return result


def issue_infrastructure_error_decision(
    *, result_occurrence_id: str, error_kind: str, error_artifact_digest: str,
) -> DecisionReceipt:
    """Fail closed with typed ERROR authority when canonical finalization fails."""

    from scripts.function_tracer_pcode.authority.contracts import (
        VerifiedLifecycleProjection,
        authority_digest,
    )
    from scripts.function_tracer_pcode.authority.decision.decision import (
        ErrorReceipt,
        FinalizationAuthority,
        finalize_decision,
    )

    snapshot_digest = authority_digest({
        "result_occurrence_id": result_occurrence_id,
        "error_kind": error_kind,
        "error_artifact_digest": error_artifact_digest,
    })
    projection = VerifiedLifecycleProjection.seal(
        result_occurrence_id=result_occurrence_id,
        snapshot_digest=snapshot_digest,
        c_active_base=(),
        q_open_base=(),
        blocker_eligibility_base=(),
        satisfaction_projection=(),
    )
    error = ErrorReceipt.create(
        result_occurrence_id=result_occurrence_id,
        lifecycle_projection_digest=projection.lifecycle_projection_digest,
        error_kind=error_kind,
        error_artifact_digest=error_artifact_digest,
    )
    return finalize_decision(FinalizationAuthority(
        result_occurrence_id,
        projection,
        error_receipts=(error,),
    ))


def rematerialize_process_timeout_decision(
    *, checkpoint_root: Path, execution_nonce: str,
    supervisor_signing_key_id: str, supervisor_signing_key_file: Path,
    worker_signing_key_id: str, worker_signing_key_file: Path,
) -> DecisionReceipt:
    """Derive TIMEOUT only from the durable terminal supervisor bundle.

    Issue #165: the store must adopt TIMEOUT under the same decision the
    supervisor uses (deadline and observed exit evidence, no conflicting
    authority); a timeout bundle alone is not TIMEOUT authority.
    """

    from scripts.function_tracer_pcode.authority.codecs import StrictV2JsonCodec
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        DurableCheckpointStore,
        PROCESS_DURABLE_REASON_REGISTRY,
        PROCESS_DURABLE_RECOVERY_REGISTRY,
        ProcessSupervisorAuthorityFactory,
    )

    factory = ProcessSupervisorAuthorityFactory(
        supervisor_signing_key_id=supervisor_signing_key_id,
        supervisor_signing_key=supervisor_signing_key_file.read_bytes(),
        worker_signing_key_id=worker_signing_key_id,
        worker_signing_key=worker_signing_key_file.read_bytes(),
    )
    store = DurableCheckpointStore(checkpoint_root, factory, execution_nonce)
    inspection = inspect_terminal(store, mode=None, process_alive=process_is_alive)
    step = inspection.step
    if step.kind is not StepKind.ADOPT_TIMEOUT or inspection.authority is None:
        raise ValueError(
            "durable store is not a TIMEOUT terminal authority: "
            f"{step.kind.value} {getattr(step.invalid_code, 'value', None)}"
        )
    bundle = inspection.authority.bundle
    factory.validate_timeout_bundle_membership(bundle)
    codec = StrictV2JsonCodec(
        reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
        recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
    )
    receipt = codec.loads(json.dumps(
        bundle.canonical_result_bundle["decision_receipt"]
    ))
    if type(receipt) is not DecisionReceipt:
        raise ValueError("supervisor canonical bundle lacks DecisionReceipt")
    receipt.validate()
    if (
        receipt.result_occurrence_id != bundle.result_occurrence_id
        or receipt.outcome is not Outcome.TIMEOUT
    ):
        raise ValueError("supervisor canonical DecisionReceipt join differs")
    return receipt


def outcome_from_result(result: Any) -> Outcome:
    """Read final status only from the sealed receipt."""

    return outcome_from_projection(
        getattr(result, "decision_receipt", None),
        final_outcome=getattr(result, "final_outcome", None),
        is_equivalent=getattr(result, "is_equivalent", None),
    )


def outcome_from_projection(receipt: Any, *, final_outcome: Any, is_equivalent: Any) -> Outcome:
    """`outcome_from_result` の本体（結果の object を受けず、読んだ値だけを受ける）。

    Issue #22 PR-22-D: 出力の bounded path は結果の live な値を `core.live_values` で読んで
    渡す（`final_outcome` は基底型の文字列、`is_equivalent` は `True` / `False` / `None` の
    identity で比べる値）。receipt は exact な `DecisionReceipt` だけを受ける。
    """

    if type(receipt) is not DecisionReceipt:
        raise ValueError("canonical result lacks its DecisionReceipt authority")
    receipt.validate()
    declared = final_outcome
    if declared is not None and declared != receipt.outcome.value:
        raise ValueError("serialized final outcome contradicts DecisionReceipt")
    projected = {
        Outcome.EQUIVALENT: True,
        Outcome.NOT_EQ: False,
        Outcome.UNKNOWN: None,
        Outcome.TIMEOUT: None,
        Outcome.ERROR: None,
    }[receipt.outcome]
    if is_equivalent is not projected:
        raise ValueError("legacy is_equivalent projection contradicts DecisionReceipt")
    return receipt.outcome


def outcome_from_payload(payload: Mapping[str, Any]) -> Outcome:
    """Validate a serialized result-entry decision binding."""

    receipt = payload.get("decision_receipt")
    if not isinstance(receipt, Mapping):
        raise ValueError("canonical payload lacks decision_receipt")
    required = {
        "result_occurrence_id", "outcome", "lifecycle_projection_digest",
        "authority_input_digest", "receipt_digest",
    }
    if set(receipt) != required:
        raise ValueError("serialized decision receipt shape is invalid")
    outcome = Outcome(receipt["outcome"])
    from scripts.function_tracer_pcode.authority.contracts import authority_digest

    expected_digest = authority_digest({
        "result_occurrence_id": receipt["result_occurrence_id"],
        "outcome": outcome.value,
        "lifecycle_projection_digest": receipt["lifecycle_projection_digest"],
        "authority_input_digest": receipt["authority_input_digest"],
    })
    if receipt["receipt_digest"] != expected_digest:
        raise ValueError("serialized decision receipt digest is invalid")
    if payload.get("final_outcome") != outcome.value:
        raise ValueError("payload final_outcome contradicts decision receipt")
    projected = {
        Outcome.EQUIVALENT: True,
        Outcome.NOT_EQ: False,
        Outcome.UNKNOWN: None,
        Outcome.TIMEOUT: None,
        Outcome.ERROR: None,
    }[outcome]
    if payload.get("is_equivalent") is not projected:
        raise ValueError("payload compatibility projection contradicts receipt")
    return outcome


def build_default_cutover_connector() -> Any:
    """Build the repository-sealed production connector for all Phase 7 sites."""

    import os
    from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
        AbiWidthReadonlyBlockerSignal,
        AbiWidthReadonlyPilotEncoder,
        AbiWidthReadonlySolverExecutionBatchSignal,
    )
    from scripts.function_tracer_pcode.authority.domains.call_effect import (
        CallEffectPilotEncoder,
        SummaryEffectPrerequisiteProductionSignal,
    )
    from scripts.function_tracer_pcode.authority.domains.loop_recurrence import (
        LoopBlockerProductionSignal,
        LoopExactGuardPartitionCompletionSignal,
        LoopExactTermRelationCompletionSignal,
        LoopRecurrencePilotEncoder,
        LoopSolverExecutionBatchSignal,
        RecurrenceValidationCompletionSignal,
    )
    from scripts.function_tracer_pcode.authority.process.operational_extraction import (
        OperationalBlockerSignal,
        OperationalCompletionSignal,
        OperationalExtractionPilotEncoder,
    )
    from scripts.function_tracer_pcode.authority.sites.runtime import runtime_from_audited_manifest
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        PROCESS_DURABLE_REASON_REGISTRY,
        PROCESS_DURABLE_RECOVERY_REGISTRY,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        CallEffectBlockerProductionSignal,
        CallEffectPrerequisiteProductionSignal,
        CallEffectProofBatchProductionSignal,
        ComparisonClosureProductionSignal,
        CompositeProductionSignalEncoder,
        OutcomePartitionProductionSignal,
        SafeCounterexampleProductionSignal,
        SatSafetyBlockerProductionSignal,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowLifecycleReducer
    from scripts.function_tracer_pcode.authority.domains.return_outcome import (
        ReturnOutcomePilotEncoder,
    )
    from scripts.function_tracer_pcode.authority.domains.sat_safety import SatSafetyPilotEncoder
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        ComparisonClosurePilotEncoder,
    )
    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        AnalysisLimitationBlockerSignal,
        AnalysisLimitationPilotEncoder,
    )
    from scripts.function_tracer_pcode.authority.domains.identical_function_identity import (
        IdenticalFunctionIdentityPilotEncoder,
        IdenticalFunctionIdentitySignal,
    )

    worker_key_id = os.environ.get("UNKNOWN_TAXONOMY_V2_WORKER_KEY_ID")
    worker_key_file = os.environ.get("UNKNOWN_TAXONOMY_V2_WORKER_KEY_FILE")
    if worker_key_id and worker_key_file:
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            activate_process_worker_execution_authority_deployment,
        )

        activate_process_worker_execution_authority_deployment(
            key_id=worker_key_id,
            key=Path(worker_key_file).read_bytes(),
            key_source_id=str(Path(worker_key_file).resolve()),
        )

    repo_root = Path(__file__).resolve().parents[4]
    manifest_path = repo_root / (
        "artifacts/unknown_taxonomy_v2/phase7/producer-sites.json"
    )
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    outcome = ReturnOutcomePilotEncoder()
    sat = SatSafetyPilotEncoder()
    call = CallEffectPilotEncoder()
    loop = LoopRecurrencePilotEncoder()
    abi = AbiWidthReadonlyPilotEncoder(enable_solver_execution=True)
    operational = OperationalExtractionPilotEncoder()
    comparison = ComparisonClosurePilotEncoder()
    analysis_limitation = AnalysisLimitationPilotEncoder()
    identical_function_identity = IdenticalFunctionIdentityPilotEncoder()
    routes = {
        OutcomePartitionProductionSignal: outcome,
        SatSafetyBlockerProductionSignal: sat,
        SafeCounterexampleProductionSignal: sat,
        CallEffectBlockerProductionSignal: call,
        CallEffectPrerequisiteProductionSignal: call,
        CallEffectProofBatchProductionSignal: call,
        SummaryEffectPrerequisiteProductionSignal: call,
        LoopBlockerProductionSignal: loop,
        LoopExactGuardPartitionCompletionSignal: loop,
        LoopExactTermRelationCompletionSignal: loop,
        LoopSolverExecutionBatchSignal: loop,
        RecurrenceValidationCompletionSignal: loop,
        AbiWidthReadonlyBlockerSignal: abi,
        AbiWidthReadonlySolverExecutionBatchSignal: abi,
        OperationalBlockerSignal: operational,
        OperationalCompletionSignal: operational,
        ComparisonClosureProductionSignal: comparison,
        AnalysisLimitationBlockerSignal: analysis_limitation,
        IdenticalFunctionIdentitySignal: identical_function_identity,
    }
    return ProductionDualWritePilotConnector(
        ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        ),
        domain_signal_encoder=CompositeProductionSignalEncoder(routes),
        phase7_runtime_factory=lambda identity: runtime_from_audited_manifest(
            manifest, identity
        ),
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit-infrastructure-error-json", action="store_true")
    parser.add_argument("--emit-process-timeout-json", action="store_true")
    parser.add_argument("--print-production-execution-identity", action="store_true")
    parser.add_argument("--print-batch-resume-policy", action="store_true")
    parser.add_argument("--outcome")
    parser.add_argument("--result-occurrence-id")
    parser.add_argument("--error-kind")
    parser.add_argument("--error-detail", default="")
    parser.add_argument("--checkpoint-root")
    parser.add_argument("--execution-nonce")
    parser.add_argument("--supervisor-signing-key-id")
    parser.add_argument("--supervisor-signing-key-file")
    parser.add_argument("--worker-signing-key-id")
    parser.add_argument("--worker-signing-key-file")
    parser.add_argument("--binary1-path")
    parser.add_argument("--binary2-path")
    parser.add_argument("--binary1-id")
    parser.add_argument("--binary2-id")
    parser.add_argument("--function-name1")
    parser.add_argument("--function-name2")
    parser.add_argument("--result-entry-occurrence-nonce")
    args = parser.parse_args(argv)
    if args.print_batch_resume_policy:
        raw = "EQUIVALENT" if args.outcome == "EQ" else args.outcome
        try:
            outcome = Outcome(raw)
        except (TypeError, ValueError):
            parser.error("batch resume policy requires a canonical five-value outcome")
        print(BATCH_RESUME_MATRIX[outcome])
        return 0
    if args.print_production_execution_identity:
        required = (
            args.binary1_path, args.binary2_path,
            args.function_name1, args.function_name2,
            args.result_entry_occurrence_nonce,
        )
        if not all(required):
            parser.error("production identity requires binary paths and functions")
        import hashlib
        from scripts.function_tracer_pcode.proof.call_effect.obligations import (
            EquivalenceObservationContract,
        )
        from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
            ProductionPilotExecutionIdentity,
        )

        def content_identity(path: str) -> tuple[str, str]:
            digest = hashlib.sha256(Path(path).read_bytes()).hexdigest()
            return ("sha256", digest)

        identity = ProductionPilotExecutionIdentity.create({
            "binary1_id": args.binary1_id,
            "binary2_id": args.binary2_id,
            "binary1_content_identity": content_identity(args.binary1_path),
            "binary2_content_identity": content_identity(args.binary2_path),
            "function_name1": args.function_name1,
            "function_name2": args.function_name2,
            "observation_contract_id": EquivalenceObservationContract().contract_id,
            "result_entry_occurrence_nonce": (
                args.result_entry_occurrence_nonce
            ),
        })
        print("\t".join((
            identity.result_occurrence_id,
            identity.source_snapshot_fingerprint,
            "stream-" + identity.result_occurrence_id,
        )))
        return 0
    if args.emit_process_timeout_json:
        required = (
            args.checkpoint_root, args.execution_nonce,
            args.supervisor_signing_key_id, args.supervisor_signing_key_file,
            args.worker_signing_key_id, args.worker_signing_key_file,
        )
        if not all(required):
            parser.error("process TIMEOUT output requires durable authority inputs")
        receipt = rematerialize_process_timeout_decision(
            checkpoint_root=Path(args.checkpoint_root),
            execution_nonce=args.execution_nonce,
            supervisor_signing_key_id=args.supervisor_signing_key_id,
            supervisor_signing_key_file=Path(args.supervisor_signing_key_file),
            worker_signing_key_id=args.worker_signing_key_id,
            worker_signing_key_file=Path(args.worker_signing_key_file),
        )
        if receipt.outcome is not Outcome.TIMEOUT:
            raise ValueError("durable process projection did not finalize TIMEOUT")
        print("=== EQUIVALENCE_RESULT_JSON_BEGIN ===")
        print(json.dumps({
            "is_equivalent": None,
            "is_timeout": True,
            "final_outcome": Outcome.TIMEOUT.value,
            "decision_receipt": decision_receipt_payload(receipt),
            "error_message": None,
            "timeout_class": "pair_process_timeout",
        }, sort_keys=True, separators=(",", ":")))
        print("=== EQUIVALENCE_RESULT_JSON_END ===")
        return 0
    if not args.emit_infrastructure_error_json:
        parser.error("one output mode is required")
    if not args.result_occurrence_id or not args.error_kind:
        parser.error("error output requires result occurrence ID and kind")
    from scripts.function_tracer_pcode.authority.contracts import authority_digest

    receipt = issue_infrastructure_error_decision(
        result_occurrence_id=args.result_occurrence_id,
        error_kind=args.error_kind,
        error_artifact_digest=authority_digest({
            "result_occurrence_id": args.result_occurrence_id,
            "error_kind": args.error_kind,
            "error_detail": args.error_detail,
        }),
    )
    print("=== EQUIVALENCE_RESULT_JSON_BEGIN ===")
    print(json.dumps({
        "is_equivalent": None,
        "is_timeout": False,
        "final_outcome": Outcome.ERROR.value,
        "decision_receipt": decision_receipt_payload(receipt),
        "error_message": args.error_kind,
        "failure_message": args.error_detail,
    }, sort_keys=True, separators=(",", ":")))
    print("=== EQUIVALENCE_RESULT_JSON_END ===")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

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

from .contracts import Outcome
from .decision import DecisionReceipt


RETRY_FALLBACK_MATRIX: Mapping[Outcome, tuple[str, ...]] = {
    Outcome.EQUIVALENT: ("STOP",),
    Outcome.NOT_EQ: ("STOP",),
    Outcome.UNKNOWN: ("RETRY_TYPED_PROOF", "FALLBACK_NEXT_STRATEGY", "STOP"),
    Outcome.TIMEOUT: ("RETRY_WITH_LARGER_BUDGET", "FALLBACK_NEXT_STRATEGY", "STOP"),
    Outcome.ERROR: ("STOP",),
}

BATCH_RESUME_MATRIX: Mapping[Outcome, str] = {
    Outcome.EQUIVALENT: "COMPLETE_EQ",
    Outcome.NOT_EQ: "COMPLETE_NOT_EQ",
    Outcome.UNKNOWN: "RESUMABLE_SEMANTIC_BACKLOG",
    Outcome.TIMEOUT: "RESUMABLE_DEADLINE_BACKLOG",
    Outcome.ERROR: "FAILED_INFRASTRUCTURE",
}

CLI_EXIT_MATRIX: Mapping[Outcome, int] = {
    Outcome.EQUIVALENT: 0,
    Outcome.NOT_EQ: 1,
    Outcome.UNKNOWN: 2,
    Outcome.TIMEOUT: 3,
    Outcome.ERROR: 4,
}


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

    from .contracts import VerifiedLifecycleProjection, authority_digest
    from .decision import ErrorReceipt, FinalizationAuthority, finalize_decision

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
    """Derive TIMEOUT only from the durable terminal supervisor bundle."""

    from .decision import (
        FinalizationAuthority,
        TerminalTimeoutReceipt,
        finalize_decision,
    )
    from .process_supervisor import (
        DurableCheckpointStore,
        PROCESS_DURABLE_REASON_REGISTRY,
        PROCESS_DURABLE_RECOVERY_REGISTRY,
        ProcessSupervisorAuthorityFactory,
    )
    from .reducer import ShadowLifecycleReducer

    factory = ProcessSupervisorAuthorityFactory(
        supervisor_signing_key_id=supervisor_signing_key_id,
        supervisor_signing_key=supervisor_signing_key_file.read_bytes(),
        worker_signing_key_id=worker_signing_key_id,
        worker_signing_key=worker_signing_key_file.read_bytes(),
    )
    store = DurableCheckpointStore(checkpoint_root, factory, execution_nonce)
    prefix = store.rematerialize_active_prefix()
    bundle = store.rematerialize_timeout_bundle(prefix=prefix)
    reduction = ShadowLifecycleReducer(
        reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
        recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
    ).replay(bundle.terminal_segment.composite_stream)
    terminal_event = bundle.terminal_segment.composite_stream.events[-1]
    timeout = TerminalTimeoutReceipt.create(
        result_occurrence_id=bundle.result_occurrence_id,
        lifecycle_projection_digest=reduction.projection.lifecycle_projection_digest,
        proof_requirement_id=bundle.proof_requirement_id,
        execution_event_digest=terminal_event.authority_digest,
    )
    return finalize_decision(FinalizationAuthority(
        bundle.result_occurrence_id,
        reduction.projection,
        terminal_timeout_receipts=(timeout,),
    ))


def outcome_from_result(result: Any) -> Outcome:
    """Read final status only from the sealed receipt."""

    receipt = getattr(result, "decision_receipt", None)
    if type(receipt) is not DecisionReceipt:
        raise ValueError("canonical result lacks its DecisionReceipt authority")
    receipt.validate()
    declared = getattr(result, "final_outcome", None)
    if declared is not None and declared != receipt.outcome.value:
        raise ValueError("serialized final outcome contradicts DecisionReceipt")
    projected = {
        Outcome.EQUIVALENT: True,
        Outcome.NOT_EQ: False,
        Outcome.UNKNOWN: None,
        Outcome.TIMEOUT: None,
        Outcome.ERROR: None,
    }[receipt.outcome]
    if getattr(result, "is_equivalent", None) is not projected:
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
    from .contracts import authority_digest

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
    from .abi_width_readonly import (
        AbiWidthReadonlyBlockerSignal,
        AbiWidthReadonlyPilotEncoder,
        AbiWidthReadonlySolverExecutionBatchSignal,
    )
    from .call_effect import (
        CallEffectPilotEncoder,
        SummaryEffectPrerequisiteProductionSignal,
    )
    from .loop_recurrence import (
        LoopBlockerProductionSignal,
        LoopExactGuardPartitionCompletionSignal,
        LoopExactTermRelationCompletionSignal,
        LoopRecurrencePilotEncoder,
        LoopSolverExecutionBatchSignal,
        RecurrenceValidationCompletionSignal,
    )
    from .operational_extraction import (
        OperationalBlockerSignal,
        OperationalCompletionSignal,
        OperationalExtractionPilotEncoder,
    )
    from .phase7_runtime import runtime_from_audited_manifest
    from .pilot import ProductionDualWritePilotConnector
    from .process_supervisor import (
        PROCESS_DURABLE_REASON_REGISTRY,
        PROCESS_DURABLE_RECOVERY_REGISTRY,
    )
    from .production_signals import (
        CallEffectBlockerProductionSignal,
        CallEffectProofBatchProductionSignal,
        CompositeProductionSignalEncoder,
        EqClosureProductionSignal,
        OutcomePartitionProductionSignal,
        SafeCounterexampleProductionSignal,
        SatSafetyBlockerProductionSignal,
    )
    from .reducer import ShadowLifecycleReducer
    from .return_outcome import ReturnOutcomePilotEncoder
    from .sat_safety import SatSafetyPilotEncoder

    worker_key_id = os.environ.get("UNKNOWN_TAXONOMY_V2_WORKER_KEY_ID")
    worker_key_file = os.environ.get("UNKNOWN_TAXONOMY_V2_WORKER_KEY_FILE")
    if worker_key_id and worker_key_file:
        from .execution_authority import (
            ExecutionAuthorityDeploymentPolicy,
            activate_execution_authority_deployment,
            install_execution_authority_signing_key,
        )

        install_execution_authority_signing_key(
            worker_key_id, Path(worker_key_file).read_bytes()
        )
        activate_execution_authority_deployment(ExecutionAuthorityDeploymentPolicy(
            "phase8-process-worker-execution-authority",
            1,
            "eqbench-process-supervisor",
            str(Path(worker_key_file).resolve()),
            worker_key_id,
            (),
            86400,
            "phase8-process-worker-revocation",
        ))

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
    routes = {
        OutcomePartitionProductionSignal: outcome,
        SatSafetyBlockerProductionSignal: sat,
        SafeCounterexampleProductionSignal: sat,
        EqClosureProductionSignal: sat,
        CallEffectBlockerProductionSignal: call,
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
        from ..call_effect_obligations import EquivalenceObservationContract
        from ..source_declarations import infer_adjacent_c_return_type
        from .pilot import ProductionPilotExecutionIdentity

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
            "declared_return_type1": infer_adjacent_c_return_type(
                args.binary1_path, args.function_name1
            ),
            "declared_return_type2": infer_adjacent_c_return_type(
                args.binary2_path, args.function_name2
            ),
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
    from .contracts import authority_digest

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

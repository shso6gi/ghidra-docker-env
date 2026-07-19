"""Production boundary for the Phase 8 canonical five-value decision path."""

from __future__ import annotations

from typing import Any

from ..workflow import run_check_from_binaries as _run_legacy_check_from_binaries
from .production_signals import production_signal_scope
from .contracts import authority_digest
from .phase8_cutover import (
    attach_canonical_decision,
    attach_canonical_relations,
    issue_infrastructure_error_decision,
)


def _operational_binary_content_identity(value: Any) -> str:
    """Project the CLI content tuple into the operational authority contract."""

    if type(value) is str and value:
        return value
    if (
        type(value) is tuple
        and len(value) == 2
        and value[0] == "sha256"
        and type(value[1]) is str
        and len(value[1]) == 64
        and all(character in "0123456789abcdef" for character in value[1])
    ):
        return f"sha256:{value[1]}"
    raise ValueError("binary content identity is not canonical")


def run_check_from_binaries_with_v2_pilot(
    checker: Any,
    program1: Any,
    program2: Any,
    function_name1: str,
    function_name2: str,
    **kwargs: Any,
) -> Any:
    connector = getattr(checker, "v2_dual_write_pilot_connector", None)
    if connector is None:
        return _run_legacy_check_from_binaries(
            checker,
            program1,
            program2,
            function_name1,
            function_name2,
            **kwargs,
        )
    execution_payload = {
        "binary1_id": kwargs.get("binary1_id"),
        "binary2_id": kwargs.get("binary2_id"),
        "binary1_content_identity": getattr(
            checker, "_active_binary_content_identities", (None, None)
        )[0],
        "binary2_content_identity": getattr(
            checker, "_active_binary_content_identities", (None, None)
        )[1],
        "function_name1": function_name1,
        "function_name2": function_name2,
        "declared_return_type1": kwargs.get("declared_return_type1"),
        "declared_return_type2": kwargs.get("declared_return_type2"),
        "observation_contract_id": checker.observation_contract.contract_id,
    }
    try:
        session = connector.begin(execution_payload)
    except Exception as exc:
        from ...smt import ParallelResult
        from ..result import EquivalenceResult

        result_occurrence_id = "startup-error-" + authority_digest(
            execution_payload
        )[:32]
        result = EquivalenceResult(
            is_equivalent=None,
            function1_name=function_name1,
            function2_name=function_name2,
            binary1_name=(
                program1.getName() if hasattr(program1, "getName") else "binary1"
            ),
            binary2_name=(
                program2.getName() if hasattr(program2, "getName") else "binary2"
            ),
            solver_results=ParallelResult(results=[]),
            error_message="V2_EXECUTION_AUTHORITY_STARTUP_INVALID",
            failure_status="strategy_exception",
            failure_message=str(exc),
        )
        attach_canonical_decision(
            result,
            issue_infrastructure_error_decision(
                result_occurrence_id=result_occurrence_id,
                error_kind="V2_EXECUTION_AUTHORITY_STARTUP_INVALID",
                error_artifact_digest=authority_digest({
                    "result_occurrence_id": result_occurrence_id,
                    "exception_type": type(exc).__name__,
                    "message": str(exc),
                }),
            ),
        )
        return result
    operational_factory_resolver = getattr(
        session.domain_signal_encoder,
        "operational_authority_factory_for_session",
        None,
    )
    if callable(operational_factory_resolver):
        operational_factory = operational_factory_resolver(session)
        if operational_factory is not None:
            content_identities = getattr(
                checker, "_active_binary_content_identities", (None, None)
            )
            session.domain_signal_state[
                "operational_program_binary_identities"
            ] = {
                id(program1): _operational_binary_content_identity(
                    content_identities[0]
                ),
                id(program2): _operational_binary_content_identity(
                    content_identities[1]
                ),
            }
    previous_session = getattr(checker, "_active_v2_dual_write_pilot_session", None)
    previous_emit = getattr(checker, "emit_v2_dual_write_pilot_event", None)
    previous_terminalize = getattr(
        checker, "terminalize_v2_dual_write_pilot_timeout", None
    )
    checker._active_v2_dual_write_pilot_session = session
    checker.emit_v2_dual_write_pilot_event = session.emit
    checker.terminalize_v2_dual_write_pilot_timeout = session.terminalize
    try:
        with production_signal_scope(session):
            result = _run_legacy_check_from_binaries(
                checker,
                program1,
                program2,
                function_name1,
                function_name2,
                **kwargs,
            )
        if getattr(result, "error_message", None):
            session.closed = True
            attach_canonical_decision(
                result,
                issue_infrastructure_error_decision(
                    result_occurrence_id=session.identity.result_occurrence_id,
                    error_kind=str(
                        getattr(result, "failure_status", None)
                        or "strategy_exception"
                    ),
                    error_artifact_digest=authority_digest({
                        "result_occurrence_id": session.identity.result_occurrence_id,
                        "error_message": result.error_message,
                        "failure_status": getattr(result, "failure_status", None),
                        "failure_message": getattr(result, "failure_message", None),
                    }),
                ),
            )
            result.v2_dual_write_pilot = {
                "status": "CANONICAL_ERROR",
                "non_authoritative_shadow": False,
            }
            return result
        try:
            evidence = connector.finish(
                session,
                result,
                case_id=session.identity.result_occurrence_id,
            )
        except Exception as exc:
            if session.phase7_runtime is not None:
                result.legacy_unknown_reasons = list(
                    getattr(result, "unknown_reasons", ()) or ()
                )
                result.unknown_reasons = []
                result.unknown_recovery_actions = []
                result.error_message = "V2_PROJECTION_AUTHORITY_INVALID"
                result.failure_status = "canonical_projection_exception"
                result.failure_message = f"{type(exc).__name__}: {exc}"
            result_occurrence_id = session.identity.result_occurrence_id
            error_artifact_digest = authority_digest({
                "result_occurrence_id": result_occurrence_id,
                "error_kind": type(exc).__name__,
                "error_message": str(exc),
            })
            attach_canonical_decision(
                result,
                issue_infrastructure_error_decision(
                    result_occurrence_id=result_occurrence_id,
                    error_kind="V2_PROJECTION_AUTHORITY_INVALID",
                    error_artifact_digest=error_artifact_digest,
                ),
            )
            result.v2_dual_write_pilot = {
                "non_authoritative_shadow": True,
                "status": "SHADOW_EVIDENCE_INCOMPLETE",
                "error_kind": type(exc).__name__,
            }
        else:
            result._v2_dual_write_evidence = evidence
            result.v2_dual_write_pilot = dict(evidence.to_dict())
            candidate_receipt = evidence.pilot_result.candidate.decision_receipt
            if evidence.pilot_result.decision_delta:
                result.error_message = "V2_LEGACY_DECISION_CONTRADICTION"
                candidate_receipt = issue_infrastructure_error_decision(
                    result_occurrence_id=session.identity.result_occurrence_id,
                    error_kind="V2_LEGACY_DECISION_CONTRADICTION",
                    error_artifact_digest=authority_digest({
                        "legacy_outcome": evidence.pilot_result.legacy_outcome_after.value,
                        "candidate_outcome": candidate_receipt.outcome.value,
                        "candidate_receipt_digest": candidate_receipt.receipt_digest,
                    }),
                )
            attach_canonical_decision(result, candidate_receipt)
            if candidate_receipt is evidence.pilot_result.candidate.decision_receipt:
                attach_canonical_relations(
                    result, evidence.pilot_result.reduction.projection
                )
        return result
    finally:
        if previous_session is None:
            del checker._active_v2_dual_write_pilot_session
        else:
            checker._active_v2_dual_write_pilot_session = previous_session
        if previous_emit is None:
            del checker.emit_v2_dual_write_pilot_event
        else:
            checker.emit_v2_dual_write_pilot_event = previous_emit
        if previous_terminalize is None:
            del checker.terminalize_v2_dual_write_pilot_timeout
        else:
            checker.terminalize_v2_dual_write_pilot_timeout = previous_terminalize

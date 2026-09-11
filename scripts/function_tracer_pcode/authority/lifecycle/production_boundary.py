"""Production boundary for the Phase 8 canonical five-value decision path."""

from __future__ import annotations

import time
from dataclasses import dataclass
from enum import Enum
from typing import Any, Dict

from scripts.function_tracer_pcode.checker.workflow import (
    run_check_from_binaries as _run_legacy_check_from_binaries,
)
from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    production_signal_scope,
)
from scripts.function_tracer_pcode.authority.contracts import authority_digest
from scripts.function_tracer_pcode.authority.decision.production_cutover import (
    attach_canonical_decision,
    attach_canonical_relations,
    issue_infrastructure_error_decision,
)


class LegacyBoundaryErrorKind(str, Enum):
    FUNCTION_LOOKUP_MISS = "function_lookup_miss"
    STRATEGY_EXCEPTION = "strategy_exception"
    UNEXPECTED_PAIRWISE_STATE = "unexpected_pairwise_state"
    COMPATIBILITY_ERROR = "legacy_compatibility_error"
    RETURN_ABI_AUTHORITY_INVALID = "return_abi_authority_invalid"


@dataclass(frozen=True)
class LegacyBoundaryErrorArtifact:
    """Typed authority issued where a legacy ERROR crosses the v2 boundary."""

    error_kind: LegacyBoundaryErrorKind
    result_occurrence_id: str
    source_snapshot_fingerprint: str
    legacy_failure_status: str | None
    diagnostic_digest: str
    artifact_digest: str

    def validate(self) -> None:
        payload = {
            "authority_kind": "LegacyBoundaryErrorArtifact",
            "error_kind": self.error_kind.value,
            "result_occurrence_id": self.result_occurrence_id,
            "source_snapshot_fingerprint": self.source_snapshot_fingerprint,
            "diagnostic_digest": self.diagnostic_digest,
            "issuer_contract_id": "production-boundary-legacy-error-v1",
        }
        if (
            type(self.error_kind) is not LegacyBoundaryErrorKind
            or not self.result_occurrence_id
            or not self.source_snapshot_fingerprint
            or authority_digest(payload) != self.artifact_digest
        ):
            raise ValueError("legacy boundary error artifact is invalid")


def _issue_legacy_boundary_error(
    session: Any, result: Any,
) -> LegacyBoundaryErrorArtifact:
    raw_status = getattr(result, "failure_status", None)
    sealed = {
        "function_lookup_miss": LegacyBoundaryErrorKind.FUNCTION_LOOKUP_MISS,
        "strategy_exception": LegacyBoundaryErrorKind.STRATEGY_EXCEPTION,
        "unexpected_pairwise_state": (
            LegacyBoundaryErrorKind.UNEXPECTED_PAIRWISE_STATE
        ),
        "return_abi_authority_invalid": (
            LegacyBoundaryErrorKind.RETURN_ABI_AUTHORITY_INVALID
        ),
    }.get(raw_status, LegacyBoundaryErrorKind.COMPATIBILITY_ERROR)
    diagnostic_digest = authority_digest({
        "legacy_failure_status": raw_status,
        "error_message": getattr(result, "error_message", None),
        "failure_message": getattr(result, "failure_message", None),
    })
    payload = {
        "authority_kind": "LegacyBoundaryErrorArtifact",
        "error_kind": sealed.value,
        "result_occurrence_id": session.identity.result_occurrence_id,
        "source_snapshot_fingerprint": (
            session.identity.source_snapshot_fingerprint
        ),
        "diagnostic_digest": diagnostic_digest,
        "issuer_contract_id": "production-boundary-legacy-error-v1",
    }
    artifact = LegacyBoundaryErrorArtifact(
        sealed,
        session.identity.result_occurrence_id,
        session.identity.source_snapshot_fingerprint,
        raw_status if type(raw_status) is str else None,
        diagnostic_digest,
        authority_digest(payload),
    )
    artifact.validate()
    return artifact


def _reconcile_legacy_and_canonical_candidate(
    *, session: Any, legacy_outcome: Any, candidate_receipt: Any
) -> tuple[Any, str | None]:
    """Apply the exhaustive Phase-10 non-legacy-ERROR reconciliation table."""

    from scripts.function_tracer_pcode.authority.contracts import Outcome
    from scripts.function_tracer_pcode.authority.decision.decision import DecisionReceipt

    if type(candidate_receipt) is not DecisionReceipt:
        raise TypeError("canonical candidate is not an exact DecisionReceipt")
    candidate_receipt.validate()
    legacy = Outcome(legacy_outcome)
    candidate = candidate_receipt.outcome
    decisive = {Outcome.EQUIVALENT, Outcome.NOT_EQ}
    if legacy in decisive and candidate in decisive and legacy is not candidate:
        error_kind = "DECISIVE_OUTCOME_DISAGREEMENT"
        return issue_infrastructure_error_decision(
            result_occurrence_id=session.identity.result_occurrence_id,
            error_kind=error_kind,
            error_artifact_digest=authority_digest({
                "legacy_outcome": legacy.value,
                "candidate_outcome": candidate.value,
                "candidate_receipt_digest": candidate_receipt.receipt_digest,
            }),
        ), error_kind
    return candidate_receipt, None


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


def _profiled_finish(connector: Any, session: Any, result: Any) -> Any:
    """``connector.finish`` を呼ぶ。環境変数
    ``UNKNOWN_TAXONOMY_V2_PROFILE_FINISH_DIR`` が設定されていれば cProfile の
    統計をそのディレクトリへ書く（診断専用、判定には影響しない）。"""
    import os

    profile_dir = os.environ.get("UNKNOWN_TAXONOMY_V2_PROFILE_FINISH_DIR")
    if not profile_dir:
        return connector.finish(
            session, result, case_id=session.identity.result_occurrence_id
        )
    import cProfile

    profiler = cProfile.Profile()
    profiler.enable()
    try:
        return connector.finish(
            session, result, case_id=session.identity.result_occurrence_id
        )
    finally:
        profiler.disable()
        try:
            os.makedirs(profile_dir, exist_ok=True)
            profiler.dump_stats(
                os.path.join(
                    profile_dir,
                    f"finish-{session.identity.result_occurrence_id}.pstats",
                )
            )
        except Exception:
            pass


def _attach_boundary_seconds(result: Any, seconds: Dict[str, float]) -> None:
    """authority 境界（session begin / 判定本体 / finish）の所要秒を診断ブロックへ
    残す（Issue #14、署名対象外・fail-open）。"""
    try:
        diagnostics = dict(getattr(result, "diagnostics", None) or {})
        diagnostics["boundary_seconds"] = {
            key: round(float(value), 6) for key, value in seconds.items()
        }
        from scripts.function_tracer_pcode.authority.contracts import VALIDATED_ONCE

        # 0 なら validate-once キャッシュが一度も効いていない（深く不変でない
        # オブジェクトしか無かった）ことを意味する。
        diagnostics["validated_once_entries"] = len(VALIDATED_ONCE)
        result.diagnostics = diagnostics
    except Exception:
        return


def _run_conditional_lane(checker: Any, result: Any, *, projection: Any) -> None:
    """conditional lane を起動し、診断だけ結果へ残す（判定は変えない）。

    lane 自身が fail closed（例外を投げず、条件を満たさなければ列を作らない）
    なので、ここでは呼び出し口を用意して診断を書くだけにする。
    """

    from scripts.function_tracer_pcode.authority.decision.conditional_lane import (
        run_production_conditional_lane,
    )

    diagnostics = run_production_conditional_lane(
        result,
        projection=projection,
        analyses=getattr(result, "_conditional_lane_analyses", None),
        observation_policy=getattr(checker, "external_call_effect_policy", None),
        solver_runner=getattr(checker, "solver_runner", None),
        timeout=getattr(checker, "timeout", None),
        debug=bool(getattr(checker, "debug", False)),
    )
    if diagnostics is None:
        return
    try:
        current = dict(getattr(result, "diagnostics", None) or {})
        current["conditional_lane"] = diagnostics
        result.diagnostics = current
    except Exception:
        return


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
        "observation_contract_id": checker.observation_contract.contract_id,
    }
    boundary_seconds: Dict[str, float] = {}
    begin_started = time.monotonic()
    try:
        session = connector.begin(execution_payload)
    except Exception as exc:
        from scripts.function_tracer_pcode.smt import ParallelResult
        from scripts.function_tracer_pcode.checker.result import EquivalenceResult

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
        from scripts.function_tracer_pcode.authority.decision.canonical_result import (
            attach_durable_error_finalization,
        )
        attach_durable_error_finalization(
            result,
            execution_payload=execution_payload,
            error_kind="V2_EXECUTION_AUTHORITY_STARTUP_INVALID",
            error_artifact_digest=authority_digest({
                "result_occurrence_id": result_occurrence_id,
                "exception_type": type(exc).__name__,
                "message": str(exc),
            }),
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
    boundary_seconds["session_begin"] = time.monotonic() - begin_started
    try:
        check_started = time.monotonic()
        with production_signal_scope(session):
            result = _run_legacy_check_from_binaries(
                checker,
                program1,
                program2,
                function_name1,
                function_name2,
                **kwargs,
            )
        boundary_seconds["check_body"] = time.monotonic() - check_started
        _attach_boundary_seconds(result, boundary_seconds)
        if getattr(result, "error_message", None):
            session.closed = True
            error_artifact = _issue_legacy_boundary_error(session, result)
            error_kind = error_artifact.error_kind.value
            error_artifact_digest = error_artifact.artifact_digest
            result.v2_legacy_error_authority = error_artifact
            attach_canonical_decision(
                result,
                issue_infrastructure_error_decision(
                    result_occurrence_id=session.identity.result_occurrence_id,
                    error_kind=error_kind,
                    error_artifact_digest=error_artifact_digest,
                ),
            )
            from scripts.function_tracer_pcode.authority.decision.canonical_result import (
                attach_durable_error_finalization,
            )
            attach_durable_error_finalization(
                result,
                execution_payload=execution_payload,
                error_kind=error_kind,
                error_artifact_digest=error_artifact_digest,
            )
            result.v2_dual_write_pilot = {
                "status": "CANONICAL_ERROR",
                "non_authoritative_shadow": False,
            }
            return result
        finish_started = time.monotonic()
        try:
            evidence = _profiled_finish(connector, session, result)
        except Exception as exc:
            # 判定は ERROR へ落ちるが、原因はログ（stderr）に残す。
            import sys
            import traceback

            print(
                "[ProductionBoundary] connector.finish raised "
                f"{type(exc).__name__}: {exc}",
                file=sys.stderr,
            )
            traceback.print_exc(file=sys.stderr)
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
            from scripts.function_tracer_pcode.authority.decision.canonical_result import (
                attach_durable_error_finalization,
            )
            attach_durable_error_finalization(
                result,
                execution_payload=execution_payload,
                error_kind="V2_PROJECTION_AUTHORITY_INVALID",
                error_artifact_digest=error_artifact_digest,
            )
            result.v2_dual_write_pilot = {
                "non_authoritative_shadow": True,
                "status": "SHADOW_EVIDENCE_INCOMPLETE",
                "error_kind": type(exc).__name__,
            }
        else:
            result._v2_dual_write_evidence = evidence
            result.v2_dual_write_pilot = dict(evidence.to_dict())
            candidate_receipt, reconciliation_error = (
                _reconcile_legacy_and_canonical_candidate(
                    session=session,
                    legacy_outcome=(
                        evidence.pilot_result.legacy_outcome_after
                    ),
                    candidate_receipt=(
                        evidence.pilot_result.candidate.decision_receipt
                    ),
                )
            )
            if reconciliation_error is not None:
                result.error_message = reconciliation_error
                result.failure_status = "canonical_decisive_disagreement"
            attach_canonical_decision(result, candidate_receipt)
            result.v2_dual_write_pilot["non_authoritative_shadow"] = False
            result.v2_dual_write_pilot["status"] = "CANONICAL_AUTHORITY"
            if reconciliation_error is not None:
                from scripts.function_tracer_pcode.authority.decision.canonical_result import (
                    attach_durable_error_finalization,
                )
                attach_durable_error_finalization(
                    result,
                    execution_payload=execution_payload,
                    error_kind="canonical_decisive_disagreement",
                    error_artifact_digest=authority_digest({
                        "result_occurrence_id": session.identity.result_occurrence_id,
                        "reconciliation_error": reconciliation_error,
                    }),
                )
            else:
                attach_canonical_relations(
                    result, evidence.pilot_result.reduction.projection
                )
                # Issue #20 PR-20-B3: 無条件 DecisionReceipt が確定したあと、
                # UNKNOWN のときだけ conditional lane を回す。conditional 列は
                # 別列で、is_equivalent / final_outcome / exit code は動かない。
                _run_conditional_lane(
                    checker,
                    result,
                    projection=evidence.pilot_result.reduction.projection,
                )
                # The CLI owns the final serialized payload (including binary
                # content identities and timing).  Preserve exact issuer-owned
                # objects here and seal the bundle only after that payload is
                # complete; sealing this earlier produced durable null
                # identities that no later digest rebound could repair.
                result._canonical_finalization_context = (evidence, session)
        boundary_seconds["finish"] = time.monotonic() - finish_started
        _attach_boundary_seconds(result, boundary_seconds)
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

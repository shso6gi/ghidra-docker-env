"""Issue #165: 採用した終端（``TerminalAuthority``）から projection の field を作る。

supervisor はこの field を projection として公開し、分類器は同じ store から
同じ判断（``terminal_driver.inspect``）で採用した終端についてこの関数を
呼び直し、公開された projection と比べる。projection の条件（どの authority
と何が join するか）はここだけで決め、supervisor と分類器に写さない。

INVALID の projection は終端ではないので、ここでは作らない（supervisor の
``_invalid_projection``）。
"""

from __future__ import annotations

from typing import Any

from scripts.function_tracer_pcode.authority.contracts import Outcome
from scripts.function_tracer_pcode.authority.process.canonical_envelope import (
    resolved_projection,
)
from scripts.function_tracer_pcode.authority.process.child_exit import (
    validate_durable_child_returncode_observation,
)
from scripts.function_tracer_pcode.authority.process.terminal_transaction import (
    TerminalAuthority,
)

#: TIMEOUT の supervisor exit code（runner の ``timeout`` と同じ値）。
TIMEOUT_EXIT_CODE = 124
#: rc 0 で終わった child の supervisor ERROR（成功と区別する）。
ERROR_FALLBACK_EXIT_CODE = 2


def terminal_projection(authority: TerminalAuthority, factory: Any) -> dict[str, Any]:
    """採用した終端の projection の field（``projection_schema`` / digest は除く）。"""

    if authority.status == "RESOLVED":
        return resolved_projection(
            authority.envelope, authority.canonical_receipt, launch=authority.launch,
        )
    if authority.status not in {"TIMEOUT", "ERROR"}:
        raise ValueError(f"{authority.status!r} is not an adopted terminal")
    return _durable_projection(authority, factory)


def terminal_exit_code(authority: TerminalAuthority) -> int:
    """supervisor の exit code（runner が読む）。"""

    if authority.status == "RESOLVED":
        return 0
    if authority.status == "TIMEOUT":
        return TIMEOUT_EXIT_CODE
    returncode = authority.child_exit.payload["child_returncode"]
    return returncode if returncode else ERROR_FALLBACK_EXIT_CODE


def _durable_projection(authority: TerminalAuthority, factory: Any) -> dict[str, Any]:
    status, launch, bundle = authority.status, authority.launch, authority.bundle
    outcome = Outcome.TIMEOUT if status == "TIMEOUT" else Outcome.ERROR
    error_kind = bundle.error_kind if outcome is Outcome.ERROR else None
    validated = factory._validate_supervisor_canonical_bundle(
        bundle.canonical_result_bundle, launch=launch, outcome=outcome,
        error_kind=error_kind,
    )
    canonical = bundle.canonical_result_bundle
    occurrence = canonical["result_entry_occurrence_receipt"]
    identity = validated["execution_identity"]
    exit_payload = authority.child_exit.payload
    child_returncode = exit_payload["child_returncode"]
    observation_kind = exit_payload["returncode_observation_kind"]
    if (
        validated["outcome"] != outcome.value
        or bundle.canonical_result_bundle_digest != validated["bundle_digest"]
        or occurrence["launch_receipt_digest"] != launch.receipt_digest
        or occurrence["result_entry_occurrence_id"]
        != launch.payload["result_occurrence_id"]
        or bundle.child_exit_disposition != exit_payload["child_exit_disposition"]
    ):
        raise ValueError(
            f"{status} durable authority does not join the launch and the "
            "observed child exit"
        )
    validate_durable_child_returncode_observation(
        child_exit_disposition=bundle.child_exit_disposition,
        child_returncode=child_returncode,
        observation_kind=observation_kind,
    )
    kind = type(bundle).__name__
    return {
        "status": status,
        "authority_kind": kind,
        "supervisor_authority_kind": kind,
        "supervisor_final_authority_digest": bundle.bundle_digest,
        "launch_receipt_digest": launch.receipt_digest,
        "finalization_bundle_digest": bundle.bundle_digest,
        "event_stream_authority_digest": bundle.composite_stream_authority_digest,
        "canonical_outcome": validated["outcome"],
        "decision_receipt_digest": validated["decision_receipt_digest"],
        "result_occurrence_id": identity["result_occurrence_id"],
        "result_entry_occurrence_receipt_digest": occurrence["receipt_digest"],
        "execution_identity_digest": identity["execution_identity_digest"],
        "stream_id": identity["stream_id"],
        "source_snapshot_fingerprint": identity["source_snapshot_fingerprint"],
        "canonical_result_bundle_digest": validated["bundle_digest"],
        "canonical_result_bundle_kind": canonical["authority_kind"],
        "canonical_result_payload_preimage_digest": validated["payload_preimage_digest"],
        "semantic_projection_digest": validated["semantic_projection_digest"],
        "error_kind": error_kind,
        "child_exit_disposition": bundle.child_exit_disposition,
        "child_returncode_observation_kind": observation_kind,
        "child_returncode": child_returncode,
        "classification_valid": True,
    }

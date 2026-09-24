"""Issue #165: 採用した終端（``TerminalAuthority``）から projection の field を作る。

projection の field の唯一の owner。supervisor はこの field を projection として
公開し、分類器は同じ store から同じ判断（``terminal_driver.inspect``）で採用した
終端についてこの関数を呼び直し、公開された projection と比べる。

field は 3 つの部分から成り、それぞれ 1 箇所で作る。

* 終端の共通部（``_terminal_fields``）: status、authority の種類と digest、
  launch、error_kind、E の実測 rc。
* canonical 結果の identity（``_canonical_identity``）: 検証済み bundle の
  outcome・decision・execution identity・digest。RESOLVED（child の envelope）
  でも TIMEOUT / ERROR（supervisor の bundle）でも同じ規則。
* 終端の種類に固有の部分: RESOLVED は採用 receipt、TIMEOUT / ERROR は durable
  bundle と E の disposition / observation。

INVALID の projection は終端ではないので、ここでは作らない（supervisor の
``_invalid_projection``）。
"""

from __future__ import annotations

from typing import Any, Mapping, Optional

from scripts.function_tracer_pcode.authority.contracts import Outcome
from scripts.function_tracer_pcode.authority.process.child_exit import (
    validate_durable_child_returncode_observation,
)
from scripts.function_tracer_pcode.authority.process.terminal_transaction import (
    TerminalAuthority,
)

#: 採用できる終端の status（INVALID は終端ではない）。
TERMINAL_STATUSES = frozenset({"RESOLVED", "TIMEOUT", "ERROR"})
#: TIMEOUT の supervisor exit code（runner の ``timeout`` と同じ値）。
TIMEOUT_EXIT_CODE = 124
#: rc 0 で終わった child の supervisor ERROR（成功と区別する）。
ERROR_FALLBACK_EXIT_CODE = 2


def terminal_projection(authority: TerminalAuthority, factory: Any) -> dict[str, Any]:
    """採用した終端の projection の field（``projection_schema`` / digest は除く）。"""

    if authority.status not in TERMINAL_STATUSES:
        raise ValueError(f"{authority.status!r} is not an adopted terminal")
    if authority.status == "RESOLVED":
        return _resolved_projection(authority)
    return _durable_projection(authority, factory)


def terminal_exit_code(authority: TerminalAuthority) -> int:
    """supervisor の exit code（runner が読む）。"""

    if authority.status == "RESOLVED":
        return 0
    if authority.status == "TIMEOUT":
        return TIMEOUT_EXIT_CODE
    returncode = authority.child_exit.payload["child_returncode"]
    return returncode if returncode else ERROR_FALLBACK_EXIT_CODE


def _terminal_fields(
    status: str, *, authority_kind: str, final_authority_digest: str, launch: Any,
    error_kind: Optional[str], child_returncode: int,
) -> dict[str, Any]:
    return {
        "status": status,
        "authority_kind": authority_kind,
        "supervisor_authority_kind": authority_kind,
        "supervisor_final_authority_digest": final_authority_digest,
        "launch_receipt_digest": launch.receipt_digest,
        "error_kind": error_kind,
        "child_returncode": child_returncode,
        "classification_valid": True,
    }


def _canonical_identity(
    validated: Mapping[str, Any], bundle: Mapping[str, Any],
) -> dict[str, Any]:
    identity = validated["execution_identity"]
    return {
        "canonical_outcome": validated["outcome"],
        "decision_receipt_digest": validated["decision_receipt_digest"],
        "result_occurrence_id": identity["result_occurrence_id"],
        "result_entry_occurrence_receipt_digest": bundle[
            "result_entry_occurrence_receipt"
        ]["receipt_digest"],
        "execution_identity_digest": identity["execution_identity_digest"],
        "stream_id": identity["stream_id"],
        "source_snapshot_fingerprint": identity["source_snapshot_fingerprint"],
        "canonical_result_bundle_digest": validated["bundle_digest"],
        "canonical_result_bundle_kind": bundle["authority_kind"],
        "canonical_result_payload_preimage_digest": validated["payload_preimage_digest"],
        "semantic_projection_digest": validated["semantic_projection_digest"],
    }


def _resolved_projection(authority: TerminalAuthority) -> dict[str, Any]:
    """canonical RESOLVED: 検証済み envelope と、E の rc で作った採用 receipt。"""

    envelope, receipt = authority.envelope, authority.canonical_receipt
    semantic = envelope.bundle["canonical_semantic_result_projection"]
    return {
        **_terminal_fields(
            "RESOLVED", authority_kind=type(receipt).__name__,
            final_authority_digest=receipt.receipt_digest, launch=authority.launch,
            error_kind=semantic["payload"].get("error_kind"),
            child_returncode=receipt.child_returncode,
        ),
        **_canonical_identity(envelope.validated, envelope.bundle),
    }


def _durable_projection(authority: TerminalAuthority, factory: Any) -> dict[str, Any]:
    """TIMEOUT / ERROR: supervisor の durable bundle と、E の実測 rc / disposition。"""

    status, launch, bundle = authority.status, authority.launch, authority.bundle
    outcome = Outcome.TIMEOUT if status == "TIMEOUT" else Outcome.ERROR
    error_kind = bundle.error_kind if outcome is Outcome.ERROR else None
    canonical = bundle.canonical_result_bundle
    validated = factory.validate_supervisor_canonical_bundle(
        canonical, launch=launch, outcome=outcome, error_kind=error_kind,
    )
    occurrence = canonical["result_entry_occurrence_receipt"]
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
    return {
        **_terminal_fields(
            status, authority_kind=type(bundle).__name__,
            final_authority_digest=bundle.bundle_digest, launch=launch,
            error_kind=error_kind, child_returncode=child_returncode,
        ),
        **_canonical_identity(validated, canonical),
        "finalization_bundle_digest": bundle.bundle_digest,
        "event_stream_authority_digest": bundle.composite_stream_authority_digest,
        "child_exit_disposition": bundle.child_exit_disposition,
        "child_returncode_observation_kind": observation_kind,
    }

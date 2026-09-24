"""worker child が store に残す canonical 結果の envelope（Issue #165）。

envelope の規則の唯一の owner。書く側（worker の
``canonical_result.persist_canonical_result_envelope``）も、読む側（終端の
snapshot と分類器）も、ここの関数だけで envelope を作り・検証する。

検証するもの（``validate_canonical_envelope``）:

1. schema（key 集合と ``schema`` の値）
2. envelope digest（``envelope_digest`` が本体の digest）
3. bundle digest（envelope が名指す bundle と payload 中の bundle が同じ）
4. bundle の検証（封の署名を含む。鍵を持つ factory の検証を呼び出し側が渡す）
5. launch join（occurrence・source snapshot・stream が durable launch と同じ）
6. outcome が ERROR のときだけ ``error_kind`` がある

採用した canonical 結果（``SupervisorCanonicalResultResolvedReceipt``）も、
ここで envelope と E の rc から決定的に作る。projection の field は持たない
（``terminal_projection`` が終端の種類を横断して 1 つの owner として作る）。

この module は ``contracts`` しか import しない（store・分類器・process の
起動に依存しない）。bundle の中身の検証は ``validate_bundle`` として受け取る。
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from typing import Any, Callable, Mapping

from scripts.function_tracer_pcode.authority.contracts import (
    CLI_EXIT_CODE_BY_OUTCOME,
    Outcome,
    authority_digest,
)

ENVELOPE_SCHEMA = "canonical-result-envelope-v1"
_BODY_KEYS = frozenset({
    "schema", "canonical_result_payload", "canonical_result_bundle_digest",
})
_BUNDLE_FIELD = "canonical_result_finalization_bundle"

#: ``validate_bundle(bundle, result_payload_preimage=...)`` -> validated fields。
BundleValidator = Callable[..., Mapping[str, Any]]


def payload_preimage(payload: Mapping[str, Any]) -> dict[str, Any]:
    """canonical 結果の payload から bundle を除いたもの（bundle が封をする対象）。"""

    return {key: value for key, value in payload.items() if key != _BUNDLE_FIELD}


def seal_envelope(payload: Mapping[str, Any]) -> dict[str, Any]:
    """JSON に写した canonical 結果の payload を envelope にする（書く側）。"""

    body = {
        "schema": ENVELOPE_SCHEMA,
        "canonical_result_payload": dict(payload),
        "canonical_result_bundle_digest": payload[_BUNDLE_FIELD]["bundle_digest"],
    }
    return {**body, "envelope_digest": authority_digest(body)}


@dataclass(frozen=True)
class CanonicalEnvelope:
    """検証済みの child の canonical 結果。"""

    outcome: Outcome
    #: outcome に対応する CLI の exit code（E の実測 rc と join する値）。
    cli_returncode: int
    validated: Mapping[str, Any]
    bundle: Mapping[str, Any]
    payload: Mapping[str, Any]
    #: envelope file の bytes の sha256（E が観測した envelope との照合に使う）。
    sha256: str


def validate_canonical_envelope(
    raw: bytes, *, launch: Any, validate_bundle: BundleValidator,
) -> CanonicalEnvelope:
    """envelope file の bytes を検証する（rc は見ない。E との join は呼び出し側）。"""

    envelope = json.loads(raw.decode("utf-8"))
    if type(envelope) is not dict or set(envelope) != _BODY_KEYS | {"envelope_digest"}:
        raise ValueError("canonical result envelope fields differ")
    body = {key: envelope[key] for key in _BODY_KEYS}
    if (
        envelope["schema"] != ENVELOPE_SCHEMA
        or authority_digest(body) != envelope["envelope_digest"]
    ):
        raise ValueError("canonical result envelope seal is invalid")
    payload = envelope["canonical_result_payload"]
    if type(payload) is not dict or type(payload.get(_BUNDLE_FIELD)) is not dict:
        raise ValueError("canonical result envelope carries no finalization bundle")
    bundle = payload[_BUNDLE_FIELD]
    if bundle.get("bundle_digest") != envelope["canonical_result_bundle_digest"]:
        raise ValueError("canonical result envelope bundle differs")
    validated = validate_bundle(bundle, result_payload_preimage=payload_preimage(payload))
    identity = validated["execution_identity"]
    if (
        identity["result_occurrence_id"] != launch.payload["result_occurrence_id"]
        or identity["source_snapshot_fingerprint"]
        != launch.payload["source_snapshot_fingerprint"]
        or identity["stream_id"] != launch.payload["stream_id"]
    ):
        raise ValueError("canonical child result does not join the launch")
    outcome = Outcome(validated["outcome"])
    error_kind = bundle["canonical_semantic_result_projection"]["payload"].get("error_kind")
    if (outcome is Outcome.ERROR) != (type(error_kind) is str and bool(error_kind)):
        raise ValueError("canonical ERROR/error_kind join is invalid")
    return CanonicalEnvelope(
        outcome, CLI_EXIT_CODE_BY_OUTCOME[outcome], validated, bundle, payload,
        hashlib.sha256(raw).hexdigest(),
    )


@dataclass(frozen=True)
class SupervisorCanonicalResultResolvedReceipt:
    """supervisor が採用した canonical 結果（envelope と E の実測 rc の join）。"""

    launch_receipt_digest: str
    result_occurrence_id: str
    execution_identity_digest: str
    child_returncode: int
    canonical_result_bundle_digest: str
    payload_preimage_digest: str
    decision_receipt_digest: str
    receipt_digest: str

    @classmethod
    def create(cls, **values: Any) -> "SupervisorCanonicalResultResolvedReceipt":
        payload = dict(values)
        return cls(**payload, receipt_digest=authority_digest(payload))

    def validate(self) -> None:
        payload = {
            key: getattr(self, key) for key in self.__dataclass_fields__
            if key != "receipt_digest"
        }
        if authority_digest(payload) != self.receipt_digest:
            raise ValueError("supervisor canonical result receipt drifted")


def canonical_resolved_receipt(
    envelope: CanonicalEnvelope, *, launch: Any, child_returncode: int,
) -> SupervisorCanonicalResultResolvedReceipt:
    """envelope と E の実測 rc から canonical resolved receipt を決定的に作る。"""

    identity = envelope.validated["execution_identity"]
    receipt = SupervisorCanonicalResultResolvedReceipt.create(
        launch_receipt_digest=launch.receipt_digest,
        result_occurrence_id=identity["result_occurrence_id"],
        execution_identity_digest=identity["execution_identity_digest"],
        child_returncode=child_returncode,
        canonical_result_bundle_digest=envelope.validated["bundle_digest"],
        payload_preimage_digest=envelope.validated["payload_preimage_digest"],
        decision_receipt_digest=envelope.validated["decision_receipt_digest"],
    )
    receipt.validate()
    return receipt

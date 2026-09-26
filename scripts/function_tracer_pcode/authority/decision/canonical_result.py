"""Durable, independently replayable canonical result finalization authority."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import hmac
import json
import os
from pathlib import Path
import sys
import tempfile
from typing import Any, Mapping

from scripts.function_tracer_pcode.authority.process import checkpoint_vocabulary as vocabulary
from scripts.function_tracer_pcode.authority.process import store_layout as layout
from scripts.function_tracer_pcode.authority.codecs import StrictV2JsonCodec
from scripts.function_tracer_pcode.authority.contracts import (
    Outcome,
    authority_digest,
    canonical_value,
)
from scripts.function_tracer_pcode.authority.decision.decision import DecisiveProofKind
from scripts.function_tracer_pcode.authority.decision.pair_status_authority import seal_pair_status
from scripts.function_tracer_pcode.authority.process.canonical_envelope import (
    CanonicalEnvelope,
    seal_envelope,
)
from scripts.function_tracer_pcode.authority.process.process_identity import (
    process_is_alive,
)
from scripts.function_tracer_pcode.authority.process.supervisor import (
    PROCESS_DURABLE_REASON_REGISTRY,
    PROCESS_DURABLE_RECOVERY_REGISTRY,
)
from scripts.function_tracer_pcode.authority.lifecycle.reducer import ShadowLifecycleReducer
from scripts.function_tracer_pcode.authority.seal_work import (
    BundleWorkExceeded,
    SealPlan,
    persisted_envelope_byte_limit,
)
from scripts.function_tracer_pcode.authority.process.terminal_driver import (
    inspect as inspect_terminal,
)
from scripts.function_tracer_pcode.authority.process.terminal_projection import (
    TERMINAL_STATUSES,
    terminal_projection,
)
from scripts.function_tracer_pcode.authority.process.terminal_transaction import (
    TerminalAuthority,
)


BUNDLE_SCHEMA = "canonical-result-finalization-bundle-v1"
BUNDLE_KIND = "CanonicalResultFinalizationBundle"
SEMANTIC_SCHEMA = "canonical-semantic-result-projection-v1"
_EARLY_ERROR_OCCURRENCE_TOKEN = object()


@dataclass(frozen=True, init=False)
class EarlyErrorResultEntryOccurrenceReceipt:
    authority_kind: str
    result_entry_occurrence_id: str
    execution_payload_digest: str
    error_kind: str
    error_artifact_digest: str
    occurrence_nonce: str
    receipt_digest: str
    _factory_token: object

    def __init__(self, *, _factory_token: object = None, **values: Any) -> None:
        if _factory_token is not _EARLY_ERROR_OCCURRENCE_TOKEN:
            raise TypeError("early ERROR occurrence requires factory authority")
        for name, value in values.items():
            object.__setattr__(self, name, value)
        object.__setattr__(self, "_factory_token", _factory_token)

    @classmethod
    def issue(
        cls, *, result_entry_occurrence_id: str,
        execution_payload_digest: str, error_kind: str,
        error_artifact_digest: str,
    ) -> "EarlyErrorResultEntryOccurrenceReceipt":
        body = {
            "authority_kind": "EarlyErrorResultEntryOccurrenceReceipt",
            "result_entry_occurrence_id": result_entry_occurrence_id,
            "execution_payload_digest": execution_payload_digest,
            "error_kind": error_kind,
            "error_artifact_digest": error_artifact_digest,
            "occurrence_nonce": authority_digest({
                "early_error_result_occurrence": result_entry_occurrence_id,
                "execution_payload_digest": execution_payload_digest,
                "error_kind": error_kind,
                "error_artifact_digest": error_artifact_digest,
            }),
        }
        receipt = cls(
            **body, receipt_digest=authority_digest(body),
            _factory_token=_EARLY_ERROR_OCCURRENCE_TOKEN,
        )
        receipt.validate()
        return receipt

    def validate(self) -> None:
        body = {
            name: getattr(self, name) for name in (
                "authority_kind", "result_entry_occurrence_id",
                "execution_payload_digest", "error_kind",
                "error_artifact_digest", "occurrence_nonce",
            )
        }
        if (
            self._factory_token is not _EARLY_ERROR_OCCURRENCE_TOKEN
            or self.authority_kind
            != "EarlyErrorResultEntryOccurrenceReceipt"
            or any(type(value) is not str or not value for value in body.values())
            or self.receipt_digest != authority_digest(body)
        ):
            raise ValueError("early ERROR result-entry occurrence is invalid")

    def to_authority_dict(self) -> Mapping[str, Any]:
        self.validate()
        return {
            name: getattr(self, name) for name in self.__dataclass_fields__
            if name != "_factory_token"
        }


def attach_durable_error_finalization(
    result: Any, *, execution_payload: Mapping[str, Any], error_kind: str,
    error_artifact_digest: str,
) -> Any:
    """Create the same replayable canonical bundle context for early errors."""

    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        attach_canonical_decision,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
        ProductionDualWritePilotConnector,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        ErrorEventAuthority,
        EventIntent,
        EventType,
    )

    connector = ProductionDualWritePilotConnector(ShadowLifecycleReducer(
        reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
        recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
    ))
    session = connector.begin(execution_payload)
    session.result_entry_occurrence_receipt = (
        EarlyErrorResultEntryOccurrenceReceipt.issue(
            result_entry_occurrence_id=session.identity.result_occurrence_id,
            execution_payload_digest=authority_digest(
                session.execution_payload
            ),
            error_kind=error_kind,
            error_artifact_digest=error_artifact_digest,
        )
    )
    session.emit(EventIntent(
        EventType.ERROR,
        ErrorEventAuthority(error_kind, error_artifact_digest),
    ))
    evidence = connector.finish(
        session, result, case_id=session.identity.result_occurrence_id
    )
    attach_canonical_decision(
        result, evidence.pilot_result.candidate.decision_receipt
    )
    result._v2_dual_write_evidence = evidence
    result._canonical_finalization_context = (evidence, session)
    return result


def _codec() -> StrictV2JsonCodec:
    return StrictV2JsonCodec(
        reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
        recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
    )


def _encoded(codec: StrictV2JsonCodec, value: Any) -> Mapping[str, Any]:
    return json.loads(codec.dumps(value))


def _semantic_projection(
    result_payload: Mapping[str, Any], pilot: Any,
    execution_payload: Any = None,
) -> Mapping[str, Any]:
    projection = pilot.reduction.projection
    semantic_execution_payload = dict(execution_payload or ())
    semantic_execution_payload.pop("result_entry_occurrence_nonce", None)
    source_semantic_fingerprint = (
        authority_digest(canonical_value(semantic_execution_payload))
        if semantic_execution_payload
        else pilot.sealed_event_stream.envelope.source_snapshot_fingerprint
    )
    payload = json.loads(json.dumps({
        "schema": SEMANTIC_SCHEMA,
        "source_snapshot_fingerprint": source_semantic_fingerprint,
        "binary1_content_identity": result_payload.get("binary1_content_identity"),
        "binary2_content_identity": result_payload.get("binary2_content_identity"),
        "function1_name": result_payload.get("function1_name"),
        "function2_name": result_payload.get("function2_name"),
        "canonical_outcome": pilot.candidate.decision_receipt.outcome.value,
        "c_active_semantics": tuple(sorted((
            row.reason_id,
            row.cause_id,
            row.domain,
            row.decision_effect,
            row.target_kind,
        ) for row in projection.c_active_base)),
        "q_open_semantics": tuple(sorted((
            row.cause_id,
            row.proof_kind,
            row.semantic_target_digest,
        ) for row in projection.q_open_base)),
        "decisive_proof_kinds": tuple(sorted(
            receipt.proof_kind.value for receipt in pilot.decisive_proof_receipts
        )),
        "terminal_timeout_semantics": tuple(sorted(
            receipt.proof_requirement_id
            for receipt in pilot.terminal_timeout_receipts
        )),
        "error_kind": (
            pilot.error_receipts[0].error_kind if pilot.error_receipts else None
        ),
    }, sort_keys=True))
    return {
        "payload": payload,
        "semantic_projection_digest": authority_digest(payload),
    }


def build_canonical_result_finalization_bundle(
    *, result_payload_preimage: Mapping[str, Any], evidence: Any, session: Any,
    work: Any,
) -> Mapping[str, Any]:
    """Seal all replay material for one normal production-pilot finalization.

    Issue #110: every step proportional to the stream / projection / receipts /
    preimage is charged to the finite ``work`` (``authority.seal_work.SealWork``)
    before it runs; exceeding it raises ``BundleWorkExceeded`` and no partial
    bundle, digest or replay is returned.
    """

    pilot = evidence.pilot_result
    occurrence = evidence.result_entry_occurrence_receipt
    selection = session.domain_signal_state.get(
        "terminal_timeout_candidate_selection"
    )
    plan = SealPlan.price(
        work,
        stream=pilot.sealed_event_stream,
        projection=pilot.reduction.projection,
        receipts=(
            *pilot.decisive_proof_receipts, *pilot.terminal_timeout_receipts,
            *pilot.error_receipts, pilot.candidate.decision_receipt,
            occurrence, selection, tuple(session.terminalizations),
        ),
        preimage=result_payload_preimage,
        execution=session.execution_payload,
    )
    plan.charge("pilot_validate")
    pilot.validate()
    codec = _codec()
    plan.charge("semantic_projection")
    semantic = _semantic_projection(
        result_payload_preimage, pilot, session.execution_payload
    )
    seal_key_id = os.environ.get("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID")
    seal_key_file = os.environ.get("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE")
    if bool(seal_key_id) != bool(seal_key_file):
        raise ValueError("canonical result bundle seal configuration is incomplete")
    plan.charge("execution_payload_digest")
    execution_payload_digest = authority_digest(session.execution_payload)
    plan.charge("encode_stream")
    encoded_stream = _encoded(codec, pilot.sealed_event_stream)
    plan.charge("encode_projection")
    encoded_projection = _encoded(codec, pilot.reduction.projection)
    plan.charge("encode_receipts")
    encoded_decisive = tuple(
        _encoded(codec, item) for item in pilot.decisive_proof_receipts
    )
    encoded_timeouts = tuple(
        _encoded(codec, item) for item in pilot.terminal_timeout_receipts
    )
    encoded_errors = tuple(
        _encoded(codec, item) for item in pilot.error_receipts
    )
    encoded_decision = _encoded(codec, pilot.candidate.decision_receipt)
    plan.charge("preimage_digest")
    preimage_digest = authority_digest(result_payload_preimage)
    body = {
        "schema": BUNDLE_SCHEMA,
        "authority_kind": BUNDLE_KIND,
        "execution_identity": {
            "execution_identity_authority_kind": "ProductionPilotExecutionIdentity",
            "result_occurrence_id": session.identity.result_occurrence_id,
            "source_snapshot_fingerprint": (
                session.identity.source_snapshot_fingerprint
            ),
            "execution_identity_digest": (
                session.identity.execution_identity_digest
            ),
            "stream_id": pilot.sealed_event_stream.envelope.stream_id,
        },
        "execution_payload": session.execution_payload,
        "execution_payload_digest": execution_payload_digest,
        "result_entry_occurrence_receipt": (
            occurrence.to_authority_dict() if occurrence is not None else None
        ),
        "sealed_event_stream": encoded_stream,
        "terminalizations": tuple(
            {
                "event_sequence_number": item.event_sequence_number,
                "proof_requirement_id": item.proof_requirement_id,
            }
            for item in session.terminalizations
        ),
        "final_lifecycle_projection": encoded_projection,
        "decisive_proof_receipts": encoded_decisive,
        "terminal_timeout_receipts": encoded_timeouts,
        "terminal_timeout_candidate_selection_receipt": (
            selection.to_authority_dict() if selection is not None else None
        ),
        "error_receipts": encoded_errors,
        "decision_receipt": encoded_decision,
        "canonical_result_payload_preimage_digest": preimage_digest,
        "canonical_semantic_result_projection": semantic,
        "bundle_seal_key_id": seal_key_id,
    }
    _check_sealed_form(plan, body, signed=seal_key_file is not None)
    plan.charge("bundle_digest")
    bundle_digest = authority_digest(body)
    signature = None
    if seal_key_file is not None:
        signature = hmac.new(
            Path(seal_key_file).read_bytes(), bundle_digest.encode("ascii"),
            hashlib.sha256,
        ).hexdigest()
    bundle = {
        **body,
        "bundle_digest": bundle_digest,
        "bundle_signature": signature,
    }
    _validate_bundle_with_plan(
        bundle, plan, result_payload_preimage=result_payload_preimage
    )
    return bundle


def supervisor_canonical_result_payload_preimage(
    launch: Any, *, outcome: Outcome, error_kind: str | None,
) -> Mapping[str, Any]:
    return {
        "schema": "supervisor-canonical-result-preimage-v1",
        "result_occurrence_id": launch.payload["result_occurrence_id"],
        "source_snapshot_fingerprint": launch.payload[
            "source_snapshot_fingerprint"
        ],
        "stream_id": launch.payload["stream_id"],
        "launch_receipt_digest": launch.receipt_digest,
        "canonical_outcome": outcome.value,
        "error_kind": error_kind,
    }


def build_supervisor_canonical_result_finalization_bundle(
    *, launch: Any, sealed_event_stream: Any,
    terminalizations: tuple[tuple[int, str], ...],
    expected_outcome: Outcome, error_kind: str | None,
    seal_key_id: str, seal_key: bytes, work: Any,
) -> Mapping[str, Any]:
    """Run the canonical reducer/finalizer for a supervisor terminal stream.

    Issue #110: metered like the production seal (``work`` is a finite
    ``SealWork``; ``BundleWorkExceeded`` returns no partial bundle).
    """

    from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
        TerminalizationIntent,
        run_dual_write_pilot,
    )

    preimage = supervisor_canonical_result_payload_preimage(
        launch, outcome=expected_outcome, error_kind=error_kind
    )
    plan = SealPlan.price(
        work, stream=sealed_event_stream, projection=None, receipts=(),
        preimage=preimage, execution=None,
    )
    plan.charge("supervisor_stream_validate")
    sealed_event_stream.validate()
    plan.charge("supervisor_replay")
    replayed = run_dual_write_pilot(
        legacy_outcome=Outcome.UNKNOWN,
        reducer=ShadowLifecycleReducer(
            reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
            recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
        ),
        stream=sealed_event_stream,
        terminalizations=tuple(
            TerminalizationIntent(sequence, requirement)
            for sequence, requirement in terminalizations
        ),
    )
    if replayed.candidate.decision_receipt.outcome is not expected_outcome:
        raise ValueError("supervisor stream did not finalize to expected outcome")
    actual_error_kind = (
        replayed.error_receipts[0].error_kind
        if replayed.error_receipts else None
    )
    if actual_error_kind != error_kind:
        raise ValueError("supervisor ERROR kind differs from canonical receipt")
    if type(seal_key_id) is not str or not seal_key_id or len(seal_key) < 32:
        raise ValueError("supervisor canonical seal authority is incomplete")

    stream_identity = sealed_event_stream.envelope
    occurrence_body = {
        "authority_kind": "SupervisorResultEntryOccurrenceReceipt",
        "result_entry_occurrence_id": stream_identity.result_occurrence_id,
        "execution_payload_digest": (
            stream_identity.source_snapshot_fingerprint
        ),
        "occurrence_nonce": launch.payload["execution_nonce"],
        "launch_receipt_digest": launch.receipt_digest,
    }
    occurrence = {
        **occurrence_body,
        "receipt_digest": authority_digest(occurrence_body),
    }
    execution_identity_payload = {
        "result_occurrence_id": stream_identity.result_occurrence_id,
        "source_snapshot_fingerprint": (
            stream_identity.source_snapshot_fingerprint
        ),
        "stream_id": stream_identity.stream_id,
        "launch_receipt_digest": launch.receipt_digest,
    }
    execution_identity = {
        "execution_identity_authority_kind": (
            "SupervisorCanonicalExecutionIdentity"
        ),
        "result_occurrence_id": stream_identity.result_occurrence_id,
        "source_snapshot_fingerprint": (
            stream_identity.source_snapshot_fingerprint
        ),
        "execution_identity_digest": authority_digest({
            "supervisor_canonical_execution_identity": (
                execution_identity_payload
            )
        }),
        "stream_id": stream_identity.stream_id,
    }
    plan.measure_more(
        projection=replayed.reduction.projection,
        receipts=(
            *replayed.decisive_proof_receipts,
            *replayed.terminal_timeout_receipts,
            *replayed.error_receipts,
            replayed.candidate.decision_receipt,
        ),
    )
    codec = _codec()
    plan.charge("semantic_projection")
    semantic = _semantic_projection(preimage, replayed)
    plan.charge("encode_stream")
    encoded_stream = _encoded(codec, sealed_event_stream)
    plan.charge("encode_projection")
    encoded_projection = _encoded(codec, replayed.reduction.projection)
    plan.charge("encode_receipts")
    encoded_decisive = tuple(
        _encoded(codec, item) for item in replayed.decisive_proof_receipts
    )
    encoded_timeouts = tuple(
        _encoded(codec, item) for item in replayed.terminal_timeout_receipts
    )
    encoded_errors = tuple(
        _encoded(codec, item) for item in replayed.error_receipts
    )
    encoded_decision = _encoded(codec, replayed.candidate.decision_receipt)
    plan.charge("preimage_digest")
    preimage_digest = authority_digest(preimage)
    body = {
        "schema": BUNDLE_SCHEMA,
        "authority_kind": BUNDLE_KIND,
        "execution_identity": execution_identity,
        "execution_payload": None,
        "execution_payload_digest": (
            stream_identity.source_snapshot_fingerprint
        ),
        "result_entry_occurrence_receipt": occurrence,
        "sealed_event_stream": encoded_stream,
        "terminalizations": tuple({
            "event_sequence_number": sequence,
            "proof_requirement_id": requirement,
        } for sequence, requirement in terminalizations),
        "final_lifecycle_projection": encoded_projection,
        "decisive_proof_receipts": encoded_decisive,
        "terminal_timeout_receipts": encoded_timeouts,
        "terminal_timeout_candidate_selection_receipt": None,
        "error_receipts": encoded_errors,
        "decision_receipt": encoded_decision,
        "canonical_result_payload_preimage_digest": preimage_digest,
        "canonical_semantic_result_projection": semantic,
        "bundle_seal_key_id": seal_key_id,
    }
    _check_sealed_form(plan, body, signed=True)
    plan.charge("bundle_digest")
    bundle_digest = authority_digest(body)
    bundle = {
        **body,
        "bundle_digest": bundle_digest,
        "bundle_signature": hmac.new(
            seal_key, bundle_digest.encode("ascii"), hashlib.sha256
        ).hexdigest(),
    }
    _validate_bundle_with_plan(
        bundle, plan,
        result_payload_preimage=preimage,
        bundle_verification_key_id=seal_key_id,
        bundle_verification_key=seal_key,
    )
    return bundle


#: Issue #15: identity proof で確定した結果の provenance と、その proof が
#: 束縛する execution の field。provenance は判定の authority ではないが、
#: receipt と食い違ったまま保存されることは内部不変条件の違反なので拒否する。
_IDENTICAL_FUNCTION_IDENTITY_PROVENANCE_KIND = "identical_function_identity"
_IDENTICAL_FUNCTION_IDENTITY_PAYLOAD_BINDING = (
    ("left_binary_id", "binary1_id"),
    ("right_binary_id", "binary2_id"),
    ("function_name", "function_name1"),
    ("function_name", "function_name2"),
    ("observation_contract_id", "observation_contract_id"),
)


def _validate_decisive_proof_provenance(
    provenance: Any, *, decisive_receipts: tuple[Any, ...],
    execution_identity: Mapping[str, Any], execution_payload: Any,
) -> None:
    """`decisive_proof_provenance` が bundle の receipt と execution に join するか。

    主たる fail-closed は producer 側の encoder（artifact を session と照合してから
    でないと event を出さない）で、ここはその結果が保存物として矛盾していない
    ことの再検証。到達したら内部不変条件違反なので `ValueError`。
    """

    if provenance is None:
        return
    if not isinstance(provenance, Mapping):
        raise ValueError("decisive proof provenance is not a mapping")
    if provenance.get("kind") != _IDENTICAL_FUNCTION_IDENTITY_PROVENANCE_KIND:
        raise ValueError("decisive proof provenance kind is not recognized")
    artifact = provenance.get("artifact")
    if not isinstance(artifact, Mapping):
        raise ValueError("decisive proof provenance lacks its artifact body")
    artifact_digest = authority_digest(dict(artifact))
    if provenance.get("proof_artifact_digest") != artifact_digest:
        raise ValueError("decisive proof provenance digest differs from its artifact")
    from scripts.function_tracer_pcode.authority.domains.identical_function_identity import (
        identical_function_identity_body_is_canonical,
    )

    # 保存物にも producer 側と**同じ**body 不変条件を掛ける（digest の一致だけを
    # 見ると、body ごと作り替えた artifact が保存物として通ってしまう）。
    if not identical_function_identity_body_is_canonical(artifact, artifact_digest):
        raise ValueError("identity proof provenance artifact body is not canonical")
    if len(decisive_receipts) != 1:
        raise ValueError(
            "identity proof provenance requires exactly one decisive receipt"
        )
    receipt = decisive_receipts[0]
    if (
        receipt.proof_kind is not DecisiveProofKind.EQ_CLOSURE
        or receipt.proof_artifact_digest != artifact_digest
    ):
        raise ValueError("identity proof provenance is not the decisive EQ_CLOSURE")
    if (
        artifact.get("result_occurrence_id")
        != execution_identity["result_occurrence_id"]
        or artifact.get("execution_identity_digest")
        != execution_identity["execution_identity_digest"]
    ):
        raise ValueError("identity proof provenance does not join the execution identity")
    if execution_payload is None:
        raise ValueError("identity proof provenance lacks its execution payload")
    payload = dict(execution_payload)
    for artifact_key, payload_key in _IDENTICAL_FUNCTION_IDENTITY_PAYLOAD_BINDING:
        if artifact.get(artifact_key) != payload.get(payload_key):
            raise ValueError(
                "identity proof provenance does not join the execution payload"
            )
    content = canonical_value(artifact.get("binary_content_identity"))
    for payload_key in ("binary1_content_identity", "binary2_content_identity"):
        if content != _operational_content_identity(payload.get(payload_key)):
            raise ValueError(
                "identity proof provenance content identity differs from the input"
            )


def _operational_content_identity(value: Any) -> str:
    from scripts.function_tracer_pcode.authority.lifecycle.production_boundary import (
        _operational_binary_content_identity,
    )

    return _operational_binary_content_identity(
        tuple(value) if type(value) in (tuple, list) else value
    )


def validate_canonical_result_finalization_bundle(
    bundle: Mapping[str, Any], *,
    work: Any,
    result_payload_preimage: Mapping[str, Any] | None = None,
    bundle_verification_key_id: str | None = None,
    bundle_verification_key: bytes | None = None,
) -> Mapping[str, Any]:
    """Replay-verify a persisted bundle within the finite seal ``work`` (Issue #110)."""

    _require_bundle_fields(bundle)
    plan = _price_bundle(work, bundle, result_payload_preimage)
    return _validate_bundle_with_plan(
        bundle, plan,
        result_payload_preimage=result_payload_preimage,
        bundle_verification_key_id=bundle_verification_key_id,
        bundle_verification_key=bundle_verification_key,
    )


_BUNDLE_FIELDS = frozenset({
    "schema", "authority_kind", "execution_identity",
    "execution_payload",
    "execution_payload_digest",
    "result_entry_occurrence_receipt", "sealed_event_stream",
    "terminalizations", "final_lifecycle_projection",
    "decisive_proof_receipts", "terminal_timeout_receipts",
    "terminal_timeout_candidate_selection_receipt",
    "error_receipts", "decision_receipt",
    "canonical_result_payload_preimage_digest",
    "canonical_semantic_result_projection", "bundle_seal_key_id",
    "bundle_digest", "bundle_signature",
})


def _require_bundle_fields(bundle: Any) -> None:
    """O(1) の形の確認（数える前に: 形の違う bundle は main と同じ ``ValueError``）。"""

    if type(bundle) is not dict or set(bundle) != _BUNDLE_FIELDS:
        raise ValueError("canonical result bundle fields differ")
    if not isinstance(bundle["sealed_event_stream"], Mapping):
        raise ValueError("canonical result bundle fields differ")


def _price_bundle(
    work: Any, bundle: Mapping[str, Any], preimage: Mapping[str, Any] | None,
) -> SealPlan:
    """Measure the whole encoded bundle (dict) before any decode, digest or replay.

    The stream (event by event) and the projection are measured on their own;
    every other field (receipts, identity, digests, terminalizations) is
    measured as one rest-of-bundle component.
    """

    _require_bundle_fields(bundle)
    return SealPlan.price(work, preimage=preimage, **_bundle_parts(bundle))


def _bundle_parts(bundle: Mapping[str, Any]) -> dict[str, Any]:
    """The parts a reader measures: stream, projection, execution payload, and the rest as one."""

    rest = {
        key: value for key, value in bundle.items()
        if key not in {
            "sealed_event_stream", "final_lifecycle_projection", "execution_payload",
        }
    }
    return {
        "stream": bundle["sealed_event_stream"],
        "projection": bundle["final_lifecycle_projection"],
        "receipts": (rest,),
        "execution": bundle["execution_payload"],
    }


#: 封印の前に測る bundle の digest / 署名の場所を埋める値（本物と同じ長さの 16 進 64 文字）
_DIGEST_PLACEHOLDER = "0" * 64


def _check_sealed_form(plan: SealPlan, body: Mapping[str, Any], *, signed: bool) -> None:
    """Issue #110: the encoded bundle a reader will measure is within the contract, before the digest.

    The digest and signature are not known yet; placeholders of the same
    length stand in, so the check measures exactly what the reader measures.
    """

    plan.check_sealed_form(**_bundle_parts({
        **body,
        "bundle_digest": _DIGEST_PLACEHOLDER,
        "bundle_signature": _DIGEST_PLACEHOLDER if signed else None,
    }))


def _validate_bundle_with_plan(
    bundle: Mapping[str, Any], plan: SealPlan, *,
    result_payload_preimage: Mapping[str, Any] | None = None,
    bundle_verification_key_id: str | None = None,
    bundle_verification_key: bytes | None = None,
) -> Mapping[str, Any]:
    from scripts.function_tracer_pcode.authority.lifecycle.stream import (
        EventStreamPrefixView,
        EventType,
    )

    _require_bundle_fields(bundle)
    body = {
        key: value for key, value in bundle.items()
        if key not in {"bundle_digest", "bundle_signature"}
    }
    if (
        bundle["schema"] != BUNDLE_SCHEMA
        or bundle["authority_kind"] != BUNDLE_KIND
    ):
        raise ValueError("canonical result bundle seal is invalid")
    plan.charge("verify_bundle_digest")
    if authority_digest(body) != bundle["bundle_digest"]:
        raise ValueError("canonical result bundle seal is invalid")
    if bool(bundle_verification_key_id) != bool(bundle_verification_key):
        raise ValueError("canonical result bundle verification key is incomplete")
    if bundle_verification_key is not None:
        expected_signature = hmac.new(
            bundle_verification_key, bundle["bundle_digest"].encode("ascii"),
            hashlib.sha256,
        ).hexdigest()
        if (
            bundle["bundle_seal_key_id"] != bundle_verification_key_id
            or type(bundle["bundle_signature"]) is not str
            or not hmac.compare_digest(
                bundle["bundle_signature"], expected_signature
            )
        ):
            raise ValueError("canonical result bundle signature is invalid")
    if result_payload_preimage is not None:
        plan.charge("verify_preimage_digest")
        if authority_digest(
            result_payload_preimage
        ) != bundle["canonical_result_payload_preimage_digest"]:
            raise ValueError("canonical result payload preimage differs from bundle")
    codec = _codec()
    plan.charge("decode_stream")
    stream = codec.loads(json.dumps(bundle["sealed_event_stream"]))
    plan.charge("decode_projection")
    projection = codec.loads(json.dumps(bundle["final_lifecycle_projection"]))
    plan.charge("decode_receipts")
    decisive = tuple(
        codec.loads(json.dumps(item))
        for item in bundle["decisive_proof_receipts"]
    )
    timeouts = tuple(
        codec.loads(json.dumps(item))
        for item in bundle["terminal_timeout_receipts"]
    )
    errors = tuple(
        codec.loads(json.dumps(item)) for item in bundle["error_receipts"]
    )
    decision = codec.loads(json.dumps(bundle["decision_receipt"]))
    reducer = ShadowLifecycleReducer(
        reason_registry=PROCESS_DURABLE_REASON_REGISTRY,
        recovery_registry=PROCESS_DURABLE_RECOVERY_REGISTRY,
    )
    plan.charge("verify_replay")
    reduction = reducer.replay(stream)
    if reduction.projection != projection:
        raise ValueError("canonical result lifecycle replay drifted")
    from scripts.function_tracer_pcode.authority.lifecycle.pilot import (
        TerminalizationIntent,
        run_dual_write_pilot,
    )

    terminalizations = tuple(
        TerminalizationIntent(
            event_sequence_number=item["event_sequence_number"],
            proof_requirement_id=item["proof_requirement_id"],
        )
        for item in bundle["terminalizations"]
    )
    plan.charge("verify_dual_write_replay")
    replayed = run_dual_write_pilot(
        legacy_outcome=Outcome.UNKNOWN,
        reducer=reducer,
        stream=stream,
        terminalizations=terminalizations,
    )
    selection_payload = bundle[
        "terminal_timeout_candidate_selection_receipt"
    ]
    # Issue #110: one pass (was events x terminalizations comparisons).
    terminal_sequences = {item.event_sequence_number for item in terminalizations}
    selected_timeout_events = tuple(
        event for event in stream.events
        if event.header.sequence_number in terminal_sequences
    )
    solver_timeout_is_terminal = any(
        event.header.event_type is EventType.SOLVER_TIMEOUT
        for event in selected_timeout_events
    )
    if solver_timeout_is_terminal:
        plan.charge("verify_timeout_selection")
        if type(selection_payload) is not dict:
            raise ValueError(
                "canonical solver TIMEOUT lacks candidate selection authority"
            )
        from scripts.function_tracer_pcode.authority.sites.activation import (
            TerminalTimeoutCandidateSelectionReceipt,
        )
        from scripts.function_tracer_pcode.authority.lifecycle.pilot import TerminalCandidateView

        prefix_projection = reducer.replay_prefix(
            EventStreamPrefixView.from_sealed_stream(stream)
        )
        open_ids = {
            row.proof_requirement_id
            for row in prefix_projection.q_open_base
        }
        timeout_candidates = tuple(sorted(
            (
                event.header.sequence_number,
                event.authority_payload.proof_requirement_id,
                event.authority_digest,
            )
            for event in stream.events
            if event.header.event_type in {
                EventType.SOLVER_TIMEOUT, EventType.PROCESS_TIMEOUT,
            }
            and getattr(
                event.authority_payload, "proof_requirement_id", None
            ) in open_ids
        ))
        view_payload = {
            "result_occurrence_id": stream.envelope.result_occurrence_id,
            "lifecycle_projection_digest": (
                prefix_projection.prefix_projection_digest
            ),
            "timeout_candidates": timeout_candidates,
            "counterexample_event_digests": tuple(sorted(
                event.authority_digest for event in stream.events
                if event.header.event_type is EventType.COUNTEREXAMPLE
            )),
            "error_event_digests": tuple(sorted(
                event.authority_digest for event in stream.events
                if event.header.event_type is EventType.ERROR
            )),
            "competing_decisive_event_digests": tuple(sorted(
                event.authority_digest for event in stream.events
                if event.header.event_type is EventType.EQ_CLOSURE
            )),
        }
        candidate_view = TerminalCandidateView(
            view_payload["lifecycle_projection_digest"],
            view_payload["timeout_candidates"],
            view_payload["counterexample_event_digests"],
            view_payload["error_event_digests"],
            view_payload["competing_decisive_event_digests"],
            authority_digest(view_payload),
        )
        expected_selection = TerminalTimeoutCandidateSelectionReceipt.issue(
            stream,
            candidate_view,
            event_sequence_number=selection_payload[
                "event_sequence_number"
            ],
            proof_requirement_id=selection_payload[
                "proof_requirement_id"
            ],
            resolver_candidate_bindings=tuple(
                tuple(item) for item in selection_payload[
                    "resolver_candidate_bindings"
                ]
            ),
        )
        expected_selection_payload = json.loads(json.dumps(
            expected_selection.to_authority_dict()
        ))
        actual_selection_payload = json.loads(json.dumps(selection_payload))
        if expected_selection_payload != actual_selection_payload:
            differing_fields = tuple(sorted(
                key for key in expected_selection_payload
                if expected_selection_payload[key]
                != actual_selection_payload.get(key)
            ))
            raise ValueError(
                "canonical solver TIMEOUT candidate selection receipt differs: "
                + repr(differing_fields)
            )
        if (
            len(selected_timeout_events) != 1
            or selected_timeout_events[0].header.sequence_number
            != expected_selection.event_sequence_number
        ):
            raise ValueError(
                "canonical solver TIMEOUT terminalization differs from selection"
            )
        if (
            len(timeouts) != 1
            or timeouts[0].execution_event_digest
            != expected_selection.event_digest
        ):
            raise ValueError(
                "canonical solver TIMEOUT receipt differs from selection"
            )
    elif selection_payload is not None:
        raise ValueError(
            "canonical non-solver terminal carries timeout selection authority"
        )
    plan.charge("verify_equality")
    if (
        replayed.reduction.projection != projection
        or replayed.decisive_proof_receipts != decisive
        or replayed.terminal_timeout_receipts != timeouts
        or replayed.error_receipts != errors
        or replayed.candidate.decision_receipt != decision
    ):
        raise ValueError("canonical result decision replay drifted")
    identity = bundle["execution_identity"]
    plan.charge("verify_execution_identity")
    execution_payload = (
        canonical_value(bundle["execution_payload"])
        if bundle["execution_payload"] is not None else None
    )
    execution_payload_digest = bundle["execution_payload_digest"]
    identity_kind = identity.get("execution_identity_authority_kind")
    if (
        decision.result_occurrence_id != identity["result_occurrence_id"]
        or stream.envelope.result_occurrence_id != identity["result_occurrence_id"]
        or stream.envelope.stream_id != identity["stream_id"]
        or stream.envelope.source_snapshot_fingerprint
        != identity["source_snapshot_fingerprint"]
        or execution_payload_digest != identity["source_snapshot_fingerprint"]
        or (
            execution_payload is not None
            and authority_digest(execution_payload) != execution_payload_digest
        )
        or (
            identity_kind == "ProductionPilotExecutionIdentity"
            and (
                execution_payload is None
                or authority_digest({
                    "production_execution_identity": execution_payload
                }) != identity["execution_identity_digest"]
            )
        )
        or identity_kind not in {
            "ProductionPilotExecutionIdentity",
            "SupervisorCanonicalExecutionIdentity",
        }
    ):
        raise ValueError("canonical result execution identity does not join")
    occurrence_payload = bundle["result_entry_occurrence_receipt"]
    if (
        bundle["bundle_signature"] is not None
        and execution_payload is not None
        and occurrence_payload is None
    ):
        raise ValueError("signed canonical result lacks entry occurrence authority")
    if occurrence_payload is not None and occurrence_payload.get(
        "authority_kind"
    ) == "SupervisorResultEntryOccurrenceReceipt":
        required_occurrence = {
            "authority_kind", "result_entry_occurrence_id",
            "execution_payload_digest", "occurrence_nonce",
            "launch_receipt_digest", "receipt_digest",
        }
        occurrence_body = {
            key: value for key, value in occurrence_payload.items()
            if key != "receipt_digest"
        }
        if (
            set(occurrence_payload) != required_occurrence
            or authority_digest(occurrence_body)
            != occurrence_payload["receipt_digest"]
            or occurrence_payload["result_entry_occurrence_id"]
            != identity["result_occurrence_id"]
            or occurrence_payload["result_entry_occurrence_id"]
            != decision.result_occurrence_id
            or occurrence_payload["execution_payload_digest"]
            != execution_payload_digest
            or identity_kind != "SupervisorCanonicalExecutionIdentity"
            or identity["execution_identity_digest"] != authority_digest({
                "supervisor_canonical_execution_identity": {
                    "result_occurrence_id": identity["result_occurrence_id"],
                    "source_snapshot_fingerprint": identity[
                        "source_snapshot_fingerprint"
                    ],
                    "stream_id": identity["stream_id"],
                    "launch_receipt_digest": occurrence_payload[
                        "launch_receipt_digest"
                    ],
                }
            })
        ):
            raise ValueError("supervisor result-entry occurrence is invalid")
    elif occurrence_payload is not None and occurrence_payload.get(
        "authority_kind"
    ) == "EarlyErrorResultEntryOccurrenceReceipt":
        required_occurrence = {
            "authority_kind", "result_entry_occurrence_id",
            "execution_payload_digest", "error_kind",
            "error_artifact_digest", "occurrence_nonce", "receipt_digest",
        }
        occurrence_body = {
            key: value for key, value in occurrence_payload.items()
            if key != "receipt_digest"
        }
        if (
            set(occurrence_payload) != required_occurrence
            or decision.outcome is not Outcome.ERROR
            or authority_digest(occurrence_body)
            != occurrence_payload["receipt_digest"]
            or occurrence_payload["result_entry_occurrence_id"]
            != identity["result_occurrence_id"]
            or occurrence_payload["result_entry_occurrence_id"]
            != decision.result_occurrence_id
            or occurrence_payload["execution_payload_digest"]
            != execution_payload_digest
            or not occurrence_payload["error_kind"]
            or not occurrence_payload["error_artifact_digest"]
            or not occurrence_payload["occurrence_nonce"]
        ):
            raise ValueError("early ERROR result-entry occurrence is invalid")
    elif occurrence_payload is not None:
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            SolverResultEntryOccurrenceReceipt,
        )

        occurrence = SolverResultEntryOccurrenceReceipt.from_persisted(
            occurrence_payload
        )
        if execution_payload is None:
            raise ValueError("solver result-entry occurrence lacks execution payload")
        raw_execution_payload = dict(execution_payload)
        nonce = raw_execution_payload.pop("result_entry_occurrence_nonce", None)
        if (
            nonce != occurrence.occurrence_nonce
            or occurrence.result_entry_occurrence_id
            != identity["result_occurrence_id"]
            or occurrence.result_entry_occurrence_id
            != decision.result_occurrence_id
            or occurrence.execution_payload_digest
            != authority_digest(raw_execution_payload)
        ):
            raise ValueError("result-entry occurrence does not join execution payload")
    if result_payload_preimage is not None:
        plan.charge("verify_decisive_provenance")
        _validate_decisive_proof_provenance(
            result_payload_preimage.get("decisive_proof_provenance"),
            decisive_receipts=decisive,
            execution_identity=identity,
            execution_payload=execution_payload,
        )
    semantic = bundle["canonical_semantic_result_projection"]
    plan.charge("verify_semantic_projection")
    if result_payload_preimage is not None:
        rebuilt_semantic = _semantic_projection(
            result_payload_preimage, replayed, execution_payload
        )
    else:
        rebuilt_semantic = {
            "payload": semantic["payload"],
            "semantic_projection_digest": authority_digest(semantic["payload"]),
        }
    if authority_digest(semantic) != authority_digest(rebuilt_semantic):
        raise ValueError("canonical semantic result projection drifted")
    return {
        "outcome": decision.outcome.value,
        "decision_receipt_digest": decision.receipt_digest,
        "bundle_digest": bundle["bundle_digest"],
        "payload_preimage_digest": bundle[
            "canonical_result_payload_preimage_digest"
        ],
        "semantic_projection_digest": semantic["semantic_projection_digest"],
        "execution_identity": identity,
    }


def persist_canonical_result_envelope(
    result_payload: Mapping[str, Any], *, work: Any,
) -> Path | None:
    """Verify and persist the canonical result envelope within the finite seal ``work`` (Issue #110)."""

    root = os.environ.get("UNKNOWN_TAXONOMY_V2_SUPERVISOR_ROOT")
    nonce = os.environ.get("UNKNOWN_TAXONOMY_V2_EXECUTION_NONCE")
    bundle = result_payload.get("canonical_result_finalization_bundle")
    if not root or not nonce or bundle is None:
        return None
    preimage = {
        key: value for key, value in result_payload.items()
        if key != "canonical_result_finalization_bundle"
    }
    plan = _price_bundle(work, bundle, preimage)
    _validate_bundle_with_plan(bundle, plan, result_payload_preimage=preimage)
    plan.charge("persist_project")
    projected_payload = _project_json_primitives(
        result_payload, path="$.canonical_result_payload"
    )
    plan.charge("persist_surface")
    _validate_json_surface(projected_payload, path="$.canonical_result_payload")
    plan.charge("persist_seal")
    envelope = seal_envelope(projected_payload)
    plan.charge("persist_write")
    # Issue #110: never write an envelope its reader rejects (the reader
    # refuses files over this bound before decoding them).
    text = json.dumps(envelope, sort_keys=True, separators=(",", ":")) + "\n"
    limit = persisted_envelope_byte_limit()
    if len(text.encode("utf-8")) > limit:
        raise BundleWorkExceeded(
            "the canonical result envelope is outside the persisted bound",
            kind="contract", step="persist_write",
            consumed=getattr(work, "consumed", 0), limit=limit,
        )
    directory = Path(root) / nonce
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / layout.RESULT_ENVELOPE
    descriptor, temporary = tempfile.mkstemp(prefix=".canonical-result-", dir=directory)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            handle.write(text)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)
    return path


def _validate_json_surface(value: Any, *, path: str) -> None:
    """Reject non-JSON values with the exact canonical payload field path."""

    if value is None or type(value) in {str, int, float, bool}:
        return
    if isinstance(value, Mapping):
        for key, child in value.items():
            if type(key) is not str:
                raise TypeError(
                    f"canonical JSON key at {path} is not a string: "
                    f"{type(key).__name__}"
                )
            _validate_json_surface(child, path=f"{path}.{key}")
        return
    if isinstance(value, (list, tuple)):
        for index, child in enumerate(value):
            _validate_json_surface(child, path=f"{path}[{index}]")
        return
    raise TypeError(
        f"canonical JSON value at {path} is not serializable: "
        f"{type(value).__name__}"
    )


def _project_json_primitives(value: Any, *, path: str) -> Any:
    """Losslessly normalize boxed JSON scalars and reject every other object."""

    if value is None:
        return None
    if isinstance(value, bool):
        return bool(value)
    if isinstance(value, int):
        return int(value)
    if isinstance(value, float):
        return float(value)
    if isinstance(value, str):
        return str(value)
    if isinstance(value, Mapping):
        projected = {}
        for key, child in value.items():
            if isinstance(key, str):
                normalized_key = str(key)
            elif isinstance(key, bool):
                normalized_key = str(bool(key))
            elif isinstance(key, int):
                normalized_key = str(int(key))
            elif isinstance(key, float):
                normalized_key = str(float(key))
            elif key is None:
                normalized_key = "None"
            else:
                raise TypeError(
                    f"canonical JSON key at {path} is not a primitive: "
                    f"{type(key).__name__}"
                )
            if normalized_key in projected:
                raise ValueError(
                    f"canonical JSON keys collide after normalization at {path}: "
                    f"{normalized_key}"
                )
            projected[normalized_key] = _project_json_primitives(
                child, path=f"{path}.{normalized_key}"
            )
        return projected
    if isinstance(value, (list, tuple)):
        return [
            _project_json_primitives(child, path=f"{path}[{index}]")
            for index, child in enumerate(value)
        ]
    raise TypeError(
        f"canonical JSON value at {path} is not serializable: "
        f"{type(value).__name__}"
    )


def conditional_pair_status_projection(
    result_payload: Mapping[str, Any], *, result_occurrence_id: str,
    unconditional_outcome: Outcome, decision_receipt_digest: str,
) -> Mapping[str, Any]:
    """Project the conditional column of one canonical result into pair-status.

    Returns an empty mapping when the pair has no conditional decision, which is
    every pair until the conditional lane is activated, so the sealed body keeps
    exactly its v1 field set.  When there is one, the receipt is re-validated
    against the unconditional authority the supervisor just verified -- not
    against the digests the payload states about itself -- so a conditional
    result cannot travel into another pair's signed status.
    """
    from scripts.function_tracer_pcode.authority.decision.conditional import (
        conditional_decision_receipt_from_payload,
        validate_conditional_decision_join,
    )
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        conditional_outcome_from_payload,
    )

    conditional = conditional_outcome_from_payload(result_payload)
    if conditional is None:
        return {}
    receipt_payload = result_payload["conditional_decision_receipt"]
    receipt = conditional_decision_receipt_from_payload(receipt_payload)
    validate_conditional_decision_join(
        receipt,
        result_occurrence_id=result_occurrence_id,
        unconditional_outcome=unconditional_outcome,
        unconditional_receipt_digest=decision_receipt_digest,
    )
    return {
        "conditional_outcome": conditional.value,
        "conditional_decision_receipt": dict(receipt_payload),
    }


def _adopted_terminal(store: Any, status: Any) -> TerminalAuthority:
    """store が ``status`` の終端を採用する状態なら、その authority を返す（Issue #165）。

    判断は supervisor と同じ ``terminal_driver.inspect``（``next_step`` と
    ``adopt``）をそのまま使い、検証・競合の規則を分類器に複製しない。exit
    mode は推測せず、E に記録された supervisor の mode で読む。
    """

    if status not in TERMINAL_STATUSES:
        raise ValueError(
            "supervisor projection is not a terminal authority: "
            f"status={status!r}"
        )
    inspection = inspect_terminal(store, mode=None, process_alive=process_is_alive)
    authority = inspection.authority
    if authority is None or authority.status != status:
        step = inspection.step
        raise ValueError(
            f"{status} projection is not the durable terminal authority: "
            f"{step.kind.value} {getattr(step.invalid_code, 'value', None)} "
            f"{step.detail}"
        )
    return authority


def _require_logged_result(log_path: Path, envelope: CanonicalEnvelope) -> None:
    """pair log に結果 JSON があれば、durable な canonical 結果と同じであること。"""

    text = Path(log_path).read_text(encoding="utf-8", errors="replace")
    begin = "=== EQUIVALENCE_RESULT_JSON_BEGIN ==="
    end = "=== EQUIVALENCE_RESULT_JSON_END ==="
    if begin in text and end in text:
        raw = text.rsplit(begin, 1)[1].split(end, 1)[0].strip()
        if authority_digest(json.loads(raw)) != authority_digest(envelope.payload):
            raise ValueError("pair log and persisted canonical result differ")


def classify_pair_status(
    log_path: Path, projection_path: Path, *, checkpoint_root: Path,
    execution_nonce: str, supervisor_signing_key_id: str,
    supervisor_signing_key_file: Path, worker_signing_key_id: str,
    worker_signing_key_file: Path,
) -> Mapping[str, Any]:
    """supervisor の projection を、durable な store から同じ判断で作り直して照合する。

    projection の field は supervisor と同じ ``terminal_projection`` で作った
    ものと完全に一致しなければならない（分類器は条件を写さず、同じ関数で
    再検証する）。分類器に固有なのは pair log との照合と conditional 列だけ。
    """
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        DurableCheckpointStore,
        ProcessSupervisorAuthorityFactory,
    )
    from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
        activate_process_worker_execution_authority_deployment,
    )

    worker_key = Path(worker_signing_key_file).read_bytes()
    activate_process_worker_execution_authority_deployment(
        key_id=worker_signing_key_id,
        key=worker_key,
        key_source_id=str(Path(worker_signing_key_file).resolve()),
    )
    factory = ProcessSupervisorAuthorityFactory(
        supervisor_signing_key_id=supervisor_signing_key_id,
        supervisor_signing_key=Path(supervisor_signing_key_file).read_bytes(),
        worker_signing_key_id=worker_signing_key_id,
        worker_signing_key=worker_key,
    )
    store = DurableCheckpointStore(checkpoint_root, factory, execution_nonce)
    launch = factory.decode(json.loads(
        (store.directory / layout.LAUNCH).read_text(encoding="utf-8")
    ))
    if (
        launch.receipt_kind != vocabulary.LAUNCH_RECEIPT_KIND
        or launch.payload["execution_nonce"] != execution_nonce
    ):
        raise ValueError("durable launch authority is invalid")
    supervisor = json.loads(Path(projection_path).read_text(encoding="utf-8"))
    projection_digest = supervisor.pop("projection_digest")
    if authority_digest(supervisor) != projection_digest:
        raise ValueError("supervisor projection digest drifted")
    if supervisor.get("launch_receipt_digest") != launch.receipt_digest:
        raise ValueError("supervisor projection does not join durable launch")
    status = supervisor.get("status")
    authority = _adopted_terminal(store, status)
    if authority.launch.receipt_digest != launch.receipt_digest:
        raise ValueError("adopted terminal does not join the durable launch")
    expected = terminal_projection(authority, factory)
    if (
        set(supervisor) != set(expected) | {"projection_schema"}
        or any(supervisor[key] != value for key, value in expected.items())
    ):
        raise ValueError(
            f"{status} projection does not join the durable terminal authority"
        )
    conditional: Mapping[str, Any] = {}
    if status == "RESOLVED":
        envelope = authority.envelope
        _require_logged_result(log_path, envelope)
        conditional = conditional_pair_status_projection(
            envelope.payload,
            result_occurrence_id=expected["result_occurrence_id"],
            unconditional_outcome=envelope.outcome,
            decision_receipt_digest=expected["decision_receipt_digest"],
        )
    return {
        **{key: value for key, value in expected.items() if key != "status"},
        "execution_nonce": launch.payload["execution_nonce"],
        # Issue #20: the assumption-dependent column travels with the pair only
        # when it exists, and only bound to the authority validated above.  The
        # payload it comes from is covered by
        # ``canonical_result_payload_preimage_digest`` in the signed bundle.
        **conditional,
        "supervisor_status": status,
        "supervisor_projection_digest": projection_digest,
    }


def main(arguments: list[str] | None = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--classify-pair-log")
    parser.add_argument("--supervisor-projection")
    parser.add_argument("--checkpoint-root")
    parser.add_argument("--execution-nonce")
    parser.add_argument("--supervisor-signing-key-id")
    parser.add_argument("--supervisor-signing-key-file")
    parser.add_argument("--worker-signing-key-id")
    parser.add_argument("--worker-signing-key-file")
    parser.add_argument("--pair-status-signing-private-key-file")
    parser.add_argument("--pair-status-verification-key-file")
    parser.add_argument("--pair-execution-target-file")
    parser.add_argument("--classification-diagnostic-log")
    args = parser.parse_args(arguments)
    if not all((
        args.classify_pair_log, args.supervisor_projection,
        args.checkpoint_root, args.execution_nonce,
        args.supervisor_signing_key_id, args.supervisor_signing_key_file,
        args.worker_signing_key_id, args.worker_signing_key_file,
        args.pair_status_signing_private_key_file,
        args.pair_status_verification_key_file,
        args.pair_execution_target_file,
    )):
        parser.error("pair classification requires log and durable authority inputs")
    try:
        status = classify_pair_status(
            Path(args.classify_pair_log), Path(args.supervisor_projection),
            checkpoint_root=Path(args.checkpoint_root),
            execution_nonce=args.execution_nonce,
            supervisor_signing_key_id=args.supervisor_signing_key_id,
            supervisor_signing_key_file=Path(args.supervisor_signing_key_file),
            worker_signing_key_id=args.worker_signing_key_id,
            worker_signing_key_file=Path(args.worker_signing_key_file),
        )
        target = json.loads(Path(args.pair_execution_target_file).read_text(encoding="utf-8"))
        sealed_status = seal_pair_status(
            {**status, "pair_execution_target": target},
            private_key_path=Path(args.pair_status_signing_private_key_file),
            public_key_path=Path(args.pair_status_verification_key_file),
        )
    except Exception as exc:
        detail = f"{type(exc).__name__}: {exc}"
        message = f"Primary pair classification error: {detail}"
        print(message, file=sys.stderr)
        if args.classification_diagnostic_log:
            try:
                with Path(args.classification_diagnostic_log).open(
                    "a", encoding="utf-8"
                ) as stream:
                    stream.write(f"\n{message}\n")
            except OSError as log_exc:
                print(
                    "Pair classification diagnostic log append failed: "
                    f"{type(log_exc).__name__}: {log_exc}",
                    file=sys.stderr,
                )
        print(json.dumps({
            "classification_valid": False,
            "error_kind": "PAIR_STATUS_AUTHORITY_INVALID",
            "detail": detail,
        }, sort_keys=True))
        return 2
    print(json.dumps(sealed_status, sort_keys=True))
    return 1 if status["canonical_outcome"] == Outcome.ERROR.value else 0


if __name__ == "__main__":
    raise SystemExit(main())

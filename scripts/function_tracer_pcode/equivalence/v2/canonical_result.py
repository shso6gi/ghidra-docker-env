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

from .codecs import StrictV2JsonCodec
from .contracts import Outcome, authority_digest, canonical_value
from .pair_status_authority import seal_pair_status
from .process_supervisor import (
    PROCESS_DURABLE_REASON_REGISTRY,
    PROCESS_DURABLE_RECOVERY_REGISTRY,
)
from .reducer import ShadowLifecycleReducer


BUNDLE_SCHEMA = "canonical-result-finalization-bundle-v1"
BUNDLE_KIND = "CanonicalResultFinalizationBundle"
SEMANTIC_SCHEMA = "canonical-semantic-result-projection-v1"
RESULT_ENVELOPE_FILE = "canonical-result-envelope.json"
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


def validate_durable_child_returncode_observation(
    *, child_exit_disposition: str, child_returncode: Any,
    observation_kind: str,
) -> None:
    """Join an OS return code to the signed terminal disposition authority."""

    if type(child_exit_disposition) is not str or not child_exit_disposition:
        raise ValueError("durable child exit disposition is missing")
    if observation_kind == "DURABLE_RESTART_NO_CHILD_STATUS":
        if child_returncode is not None:
            raise ValueError("durable restart cannot invent a child return code")
        return
    if observation_kind != "LIVE_PROCESS_WAIT":
        raise ValueError("child return-code observation kind is invalid")
    if type(child_returncode) is not int:
        raise ValueError("live terminal observation lacks an exact return code")
    if child_exit_disposition == "SIGTERM_AFTER_DEADLINE":
        expected = -15
    elif child_exit_disposition == "SIGKILL_AFTER_DEADLINE":
        expected = -9
    elif child_exit_disposition.startswith("EXIT_CODE_"):
        suffix = child_exit_disposition[len("EXIT_CODE_"):]
        try:
            expected = int(suffix)
        except ValueError as exc:
            raise ValueError("child exit disposition code is malformed") from exc
    elif child_exit_disposition.startswith("EXITED_"):
        suffix = child_exit_disposition[len("EXITED_"):]
        code_text = suffix.split("_", 1)[0]
        try:
            expected = int(code_text)
        except ValueError as exc:
            raise ValueError("child exit disposition code is malformed") from exc
    else:
        raise ValueError(
            "live return code is not derivable from durable disposition authority"
        )
    if child_returncode != expected:
        raise ValueError("child return code differs from durable disposition")


def attach_durable_error_finalization(
    result: Any, *, execution_payload: Mapping[str, Any], error_kind: str,
    error_artifact_digest: str,
) -> Any:
    """Create the same replayable canonical bundle context for early errors."""

    from .phase8_cutover import attach_canonical_decision
    from .pilot import ProductionDualWritePilotConnector
    from .stream import ErrorEventAuthority, EventIntent, EventType

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
) -> Mapping[str, Any]:
    """Seal all replay material for one normal production-pilot finalization."""

    pilot = evidence.pilot_result
    pilot.validate()
    codec = _codec()
    semantic = _semantic_projection(
        result_payload_preimage, pilot, session.execution_payload
    )
    occurrence = evidence.result_entry_occurrence_receipt
    seal_key_id = os.environ.get("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID")
    seal_key_file = os.environ.get("UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE")
    if bool(seal_key_id) != bool(seal_key_file):
        raise ValueError("canonical result bundle seal configuration is incomplete")
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
        "execution_payload_digest": authority_digest(session.execution_payload),
        "result_entry_occurrence_receipt": (
            occurrence.to_authority_dict() if occurrence is not None else None
        ),
        "sealed_event_stream": _encoded(codec, pilot.sealed_event_stream),
        "terminalizations": tuple(
            {
                "event_sequence_number": item.event_sequence_number,
                "proof_requirement_id": item.proof_requirement_id,
            }
            for item in session.terminalizations
        ),
        "final_lifecycle_projection": _encoded(
            codec, pilot.reduction.projection
        ),
        "decisive_proof_receipts": tuple(
            _encoded(codec, item) for item in pilot.decisive_proof_receipts
        ),
        "terminal_timeout_receipts": tuple(
            _encoded(codec, item) for item in pilot.terminal_timeout_receipts
        ),
        "error_receipts": tuple(
            _encoded(codec, item) for item in pilot.error_receipts
        ),
        "decision_receipt": _encoded(codec, pilot.candidate.decision_receipt),
        "canonical_result_payload_preimage_digest": authority_digest(
            result_payload_preimage
        ),
        "canonical_semantic_result_projection": semantic,
        "bundle_seal_key_id": seal_key_id,
    }
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
    validate_canonical_result_finalization_bundle(
        bundle, result_payload_preimage=result_payload_preimage
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
    seal_key_id: str, seal_key: bytes,
) -> Mapping[str, Any]:
    """Run the canonical reducer/finalizer for a supervisor terminal stream."""

    from .pilot import TerminalizationIntent, run_dual_write_pilot

    sealed_event_stream.validate()
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
    preimage = supervisor_canonical_result_payload_preimage(
        launch, outcome=expected_outcome, error_kind=error_kind
    )
    codec = _codec()
    semantic = _semantic_projection(preimage, replayed)
    body = {
        "schema": BUNDLE_SCHEMA,
        "authority_kind": BUNDLE_KIND,
        "execution_identity": execution_identity,
        "execution_payload": None,
        "execution_payload_digest": (
            stream_identity.source_snapshot_fingerprint
        ),
        "result_entry_occurrence_receipt": occurrence,
        "sealed_event_stream": _encoded(codec, sealed_event_stream),
        "terminalizations": tuple({
            "event_sequence_number": sequence,
            "proof_requirement_id": requirement,
        } for sequence, requirement in terminalizations),
        "final_lifecycle_projection": _encoded(
            codec, replayed.reduction.projection
        ),
        "decisive_proof_receipts": tuple(
            _encoded(codec, item) for item in replayed.decisive_proof_receipts
        ),
        "terminal_timeout_receipts": tuple(
            _encoded(codec, item)
            for item in replayed.terminal_timeout_receipts
        ),
        "error_receipts": tuple(
            _encoded(codec, item) for item in replayed.error_receipts
        ),
        "decision_receipt": _encoded(
            codec, replayed.candidate.decision_receipt
        ),
        "canonical_result_payload_preimage_digest": authority_digest(preimage),
        "canonical_semantic_result_projection": semantic,
        "bundle_seal_key_id": seal_key_id,
    }
    bundle_digest = authority_digest(body)
    bundle = {
        **body,
        "bundle_digest": bundle_digest,
        "bundle_signature": hmac.new(
            seal_key, bundle_digest.encode("ascii"), hashlib.sha256
        ).hexdigest(),
    }
    validate_canonical_result_finalization_bundle(
        bundle,
        result_payload_preimage=preimage,
        bundle_verification_key_id=seal_key_id,
        bundle_verification_key=seal_key,
    )
    return bundle


def validate_canonical_result_finalization_bundle(
    bundle: Mapping[str, Any], *,
    result_payload_preimage: Mapping[str, Any] | None = None,
    bundle_verification_key_id: str | None = None,
    bundle_verification_key: bytes | None = None,
) -> Mapping[str, Any]:
    expected_keys = {
        "schema", "authority_kind", "execution_identity",
        "execution_payload",
        "execution_payload_digest",
        "result_entry_occurrence_receipt", "sealed_event_stream",
        "terminalizations", "final_lifecycle_projection",
        "decisive_proof_receipts", "terminal_timeout_receipts",
        "error_receipts", "decision_receipt",
        "canonical_result_payload_preimage_digest",
        "canonical_semantic_result_projection", "bundle_seal_key_id",
        "bundle_digest", "bundle_signature",
    }
    if type(bundle) is not dict or set(bundle) != expected_keys:
        raise ValueError("canonical result bundle fields differ")
    body = {
        key: value for key, value in bundle.items()
        if key not in {"bundle_digest", "bundle_signature"}
    }
    if (
        bundle["schema"] != BUNDLE_SCHEMA
        or bundle["authority_kind"] != BUNDLE_KIND
        or authority_digest(body) != bundle["bundle_digest"]
    ):
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
    if result_payload_preimage is not None and authority_digest(
        result_payload_preimage
    ) != bundle["canonical_result_payload_preimage_digest"]:
        raise ValueError("canonical result payload preimage differs from bundle")
    codec = _codec()
    stream = codec.loads(json.dumps(bundle["sealed_event_stream"]))
    projection = codec.loads(json.dumps(bundle["final_lifecycle_projection"]))
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
    reduction = reducer.replay(stream)
    if reduction.projection != projection:
        raise ValueError("canonical result lifecycle replay drifted")
    from .pilot import TerminalizationIntent, run_dual_write_pilot

    terminalizations = tuple(
        TerminalizationIntent(
            event_sequence_number=item["event_sequence_number"],
            proof_requirement_id=item["proof_requirement_id"],
        )
        for item in bundle["terminalizations"]
    )
    replayed = run_dual_write_pilot(
        legacy_outcome=Outcome.UNKNOWN,
        reducer=reducer,
        stream=stream,
        terminalizations=terminalizations,
    )
    if (
        replayed.reduction.projection != projection
        or replayed.decisive_proof_receipts != decisive
        or replayed.terminal_timeout_receipts != timeouts
        or replayed.error_receipts != errors
        or replayed.candidate.decision_receipt != decision
    ):
        raise ValueError("canonical result decision replay drifted")
    identity = bundle["execution_identity"]
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
        from .execution_authority import SolverResultEntryOccurrenceReceipt

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
    semantic = bundle["canonical_semantic_result_projection"]
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


def persist_canonical_result_envelope(result_payload: Mapping[str, Any]) -> Path | None:
    root = os.environ.get("UNKNOWN_TAXONOMY_V2_SUPERVISOR_ROOT")
    nonce = os.environ.get("UNKNOWN_TAXONOMY_V2_EXECUTION_NONCE")
    bundle = result_payload.get("canonical_result_finalization_bundle")
    if not root or not nonce or bundle is None:
        return None
    preimage = {
        key: value for key, value in result_payload.items()
        if key != "canonical_result_finalization_bundle"
    }
    validate_canonical_result_finalization_bundle(
        bundle, result_payload_preimage=preimage
    )
    envelope = {
        "schema": "canonical-result-envelope-v1",
        "canonical_result_payload": result_payload,
        "canonical_result_bundle_digest": bundle["bundle_digest"],
    }
    envelope["envelope_digest"] = authority_digest(envelope)
    directory = Path(root) / nonce
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / RESULT_ENVELOPE_FILE
    descriptor, temporary = tempfile.mkstemp(prefix=".canonical-result-", dir=directory)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            json.dump(envelope, handle, sort_keys=True, separators=(",", ":"))
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)
    return path


@dataclass(frozen=True)
class SupervisorCanonicalResultResolvedReceipt:
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


def classify_pair_status(
    log_path: Path, projection_path: Path, *, checkpoint_root: Path,
    execution_nonce: str, supervisor_signing_key_id: str,
    supervisor_signing_key_file: Path, worker_signing_key_id: str,
    worker_signing_key_file: Path,
) -> Mapping[str, Any]:
    from .process_supervisor import (
        DurableCheckpointStore, ProcessSupervisorAuthorityFactory,
    )

    factory = ProcessSupervisorAuthorityFactory(
        supervisor_signing_key_id=supervisor_signing_key_id,
        supervisor_signing_key=Path(supervisor_signing_key_file).read_bytes(),
        worker_signing_key_id=worker_signing_key_id,
        worker_signing_key=Path(worker_signing_key_file).read_bytes(),
    )
    store = DurableCheckpointStore(checkpoint_root, factory, execution_nonce)
    launch = factory.decode(json.loads(
        (store.directory / "launch.json").read_text(encoding="utf-8")
    ))
    if (
        launch.receipt_kind != "SupervisorLaunchReceipt"
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
    if status in {"TIMEOUT", "ERROR"}:
        expected_outcome = (
            Outcome.TIMEOUT if status == "TIMEOUT" else Outcome.ERROR
        )
        if expected_outcome is Outcome.TIMEOUT:
            prefix = store.rematerialize_active_prefix()
            durable = store.rematerialize_timeout_bundle(prefix=prefix)
            expected_kind = "DurableTimeoutFinalizationBundle"
            expected_error_kind = None
        else:
            durable = store.rematerialize_operational_error_bundle()
            expected_kind = "DurableErrorFinalizationBundle"
            expected_error_kind = durable.error_kind
        preimage = supervisor_canonical_result_payload_preimage(
            launch, outcome=expected_outcome, error_kind=expected_error_kind
        )
        validated = validate_canonical_result_finalization_bundle(
            durable.canonical_result_bundle,
            result_payload_preimage=preimage,
            bundle_verification_key_id=supervisor_signing_key_id,
            bundle_verification_key=Path(
                supervisor_signing_key_file
            ).read_bytes(),
        )
        required_durable = {
            "status", "authority_kind", "supervisor_authority_kind",
            "supervisor_final_authority_digest", "launch_receipt_digest",
            "finalization_bundle_digest", "event_stream_authority_digest",
            "canonical_outcome", "decision_receipt_digest",
            "result_occurrence_id", "result_entry_occurrence_receipt_digest",
            "execution_identity_digest", "stream_id",
            "source_snapshot_fingerprint", "canonical_result_bundle_digest",
            "canonical_result_bundle_kind",
            "canonical_result_payload_preimage_digest",
            "semantic_projection_digest", "error_kind", "child_returncode",
            "child_exit_disposition", "child_returncode_observation_kind",
            "classification_valid", "projection_schema",
        }
        identity = validated["execution_identity"]
        occurrence = durable.canonical_result_bundle[
            "result_entry_occurrence_receipt"
        ]
        joins = {
            "authority_kind": expected_kind,
            "supervisor_authority_kind": expected_kind,
            "supervisor_final_authority_digest": durable.bundle_digest,
            "launch_receipt_digest": launch.receipt_digest,
            "finalization_bundle_digest": durable.bundle_digest,
            "event_stream_authority_digest": (
                durable.composite_stream_authority_digest
            ),
            "canonical_outcome": expected_outcome.value,
            "decision_receipt_digest": validated["decision_receipt_digest"],
            "result_occurrence_id": identity["result_occurrence_id"],
            "result_entry_occurrence_receipt_digest": occurrence[
                "receipt_digest"
            ],
            "execution_identity_digest": identity[
                "execution_identity_digest"
            ],
            "execution_nonce": launch.payload["execution_nonce"],
            "stream_id": identity["stream_id"],
            "source_snapshot_fingerprint": identity[
                "source_snapshot_fingerprint"
            ],
            "canonical_result_bundle_digest": validated["bundle_digest"],
            "canonical_result_bundle_kind": BUNDLE_KIND,
            "canonical_result_payload_preimage_digest": validated[
                "payload_preimage_digest"
            ],
            "semantic_projection_digest": validated[
                "semantic_projection_digest"
            ],
            "error_kind": expected_error_kind,
            "child_exit_disposition": durable.child_exit_disposition,
            "child_returncode_observation_kind": supervisor[
                "child_returncode_observation_kind"
            ],
            "classification_valid": True,
        }
        validate_durable_child_returncode_observation(
            child_exit_disposition=durable.child_exit_disposition,
            child_returncode=supervisor["child_returncode"],
            observation_kind=supervisor[
                "child_returncode_observation_kind"
            ],
        )
        if (
            set(supervisor) != required_durable
            or validated["outcome"] != expected_outcome.value
            or durable.canonical_result_bundle_digest
            != validated["bundle_digest"]
            or occurrence["launch_receipt_digest"] != launch.receipt_digest
            or occurrence["result_entry_occurrence_id"]
            != launch.payload["result_occurrence_id"]
            or any(
                supervisor[key] != value for key, value in joins.items()
                if key != "execution_nonce"
            )
        ):
            raise ValueError(
                f"{status} projection does not join canonical durable authority"
            )
        return {
            **joins,
            "child_returncode": supervisor["child_returncode"],
            "supervisor_status": status,
            "supervisor_projection_digest": projection_digest,
            "classification_valid": True,
        }
    if status != "RESOLVED":
        raise ValueError("supervisor projection is not a terminal authority")

    envelope = json.loads(
        (store.directory / RESULT_ENVELOPE_FILE).read_text(encoding="utf-8")
    )
    envelope_digest = envelope.pop("envelope_digest", None)
    if (
        set(envelope) != {
            "schema", "canonical_result_payload",
            "canonical_result_bundle_digest",
        }
        or envelope["schema"] != "canonical-result-envelope-v1"
        or authority_digest(envelope) != envelope_digest
    ):
        raise ValueError("persisted canonical result envelope is invalid")
    result_payload = envelope["canonical_result_payload"]
    if (
        result_payload["canonical_result_finalization_bundle"]["bundle_digest"]
        != envelope["canonical_result_bundle_digest"]
    ):
        raise ValueError("persisted canonical result envelope bundle differs")
    text = Path(log_path).read_text(encoding="utf-8", errors="replace")
    begin = "=== EQUIVALENCE_RESULT_JSON_BEGIN ==="
    end = "=== EQUIVALENCE_RESULT_JSON_END ==="
    if begin in text and end in text:
        raw = text.rsplit(begin, 1)[1].split(end, 1)[0].strip()
        logged_payload = json.loads(raw)
        if authority_digest(logged_payload) != authority_digest(result_payload):
            raise ValueError("pair log and persisted canonical result differ")
    bundle = result_payload["canonical_result_finalization_bundle"]
    preimage = {
        key: value for key, value in result_payload.items()
        if key != "canonical_result_finalization_bundle"
    }
    validated = validate_canonical_result_finalization_bundle(
        bundle,
        result_payload_preimage=preimage,
        bundle_verification_key_id=supervisor_signing_key_id,
        bundle_verification_key=Path(
            supervisor_signing_key_file
        ).read_bytes(),
    )
    required = {
        "status", "authority_kind", "supervisor_authority_kind",
        "supervisor_final_authority_digest", "launch_receipt_digest",
        "canonical_outcome", "decision_receipt_digest",
        "result_occurrence_id", "result_entry_occurrence_receipt_digest",
        "execution_identity_digest", "stream_id",
        "source_snapshot_fingerprint", "canonical_result_bundle_digest",
        "canonical_result_bundle_kind",
        "canonical_result_payload_preimage_digest",
        "semantic_projection_digest", "error_kind", "child_returncode",
        "classification_valid", "projection_schema",
    }
    if set(supervisor) != required:
        raise ValueError("supervisor canonical projection fields differ")
    identity = validated["execution_identity"]
    occurrence = bundle["result_entry_occurrence_receipt"]
    joins = {
        "authority_kind": "SupervisorCanonicalResultResolvedReceipt",
        "supervisor_authority_kind": (
            "SupervisorCanonicalResultResolvedReceipt"
        ),
        "supervisor_final_authority_digest": supervisor[
            "supervisor_final_authority_digest"
        ],
        "launch_receipt_digest": launch.receipt_digest,
        "canonical_outcome": validated["outcome"],
        "decision_receipt_digest": validated["decision_receipt_digest"],
        "result_occurrence_id": identity["result_occurrence_id"],
        "result_entry_occurrence_receipt_digest": occurrence[
            "receipt_digest"
        ],
        "execution_identity_digest": identity["execution_identity_digest"],
        "execution_nonce": launch.payload["execution_nonce"],
        "stream_id": identity["stream_id"],
        "source_snapshot_fingerprint": identity[
            "source_snapshot_fingerprint"
        ],
        "canonical_result_bundle_digest": validated["bundle_digest"],
        "canonical_result_bundle_kind": BUNDLE_KIND,
        "canonical_result_payload_preimage_digest": validated[
            "payload_preimage_digest"
        ],
        "semantic_projection_digest": validated[
            "semantic_projection_digest"
        ],
    }
    if any(
        supervisor[key] != value for key, value in joins.items()
        if key != "execution_nonce"
    ):
        raise ValueError("result and supervisor canonical authorities do not join")
    canonical_receipt_payload = json.loads(
        (store.directory / "canonical-resolved-receipt.json").read_text(
            encoding="utf-8"
        )
    )
    canonical_receipt = SupervisorCanonicalResultResolvedReceipt(
        **canonical_receipt_payload
    )
    canonical_receipt.validate()
    from .phase8_cutover import CLI_EXIT_MATRIX

    resolved_outcome = Outcome(validated["outcome"])
    if (
        canonical_receipt.launch_receipt_digest != launch.receipt_digest
        or canonical_receipt.receipt_digest
        != supervisor["supervisor_final_authority_digest"]
        or canonical_receipt.result_occurrence_id
        != identity["result_occurrence_id"]
        or canonical_receipt.execution_identity_digest
        != identity["execution_identity_digest"]
        or canonical_receipt.canonical_result_bundle_digest
        != validated["bundle_digest"]
        or canonical_receipt.payload_preimage_digest
        != validated["payload_preimage_digest"]
        or canonical_receipt.decision_receipt_digest
        != validated["decision_receipt_digest"]
        or canonical_receipt.child_returncode
        != supervisor["child_returncode"]
        or canonical_receipt.child_returncode != CLI_EXIT_MATRIX[resolved_outcome]
    ):
        raise ValueError("canonical resolved receipt does not join authorities")
    if (
        supervisor["status"] != "RESOLVED"
        or supervisor["authority_kind"]
        != "SupervisorCanonicalResultResolvedReceipt"
        or supervisor["supervisor_authority_kind"]
        != "SupervisorCanonicalResultResolvedReceipt"
        or supervisor["classification_valid"] is not True
    ):
        raise ValueError("supervisor authority kind is not canonical RESOLVED")
    outcome = Outcome(validated["outcome"])
    error_kind = supervisor["error_kind"]
    if (outcome is Outcome.ERROR) != (type(error_kind) is str and bool(error_kind)):
        raise ValueError("canonical ERROR/error_kind join is invalid")
    return {
        **joins,
        "error_kind": error_kind,
        "child_returncode": supervisor["child_returncode"],
        "supervisor_status": supervisor["status"],
        "supervisor_projection_digest": projection_digest,
        "supervisor_final_authority_digest": supervisor[
            "supervisor_final_authority_digest"
        ],
        "classification_valid": True,
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

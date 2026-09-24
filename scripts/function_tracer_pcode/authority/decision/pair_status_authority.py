"""Publicly verifiable authority for canonical EqBench pair status."""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile
from typing import Any, Mapping

from scripts.function_tracer_pcode.authority.contracts import (
    BATCH_RESUME_DISPOSITION_BY_OUTCOME,
    CLI_EXIT_CODE_BY_OUTCOME,
    Outcome,
    authority_digest,
)
from scripts.function_tracer_pcode.authority.process.child_exit import (
    validate_durable_child_returncode_observation,
)


PAIR_STATUS_SCHEMA = "signed-canonical-pair-status-v1"
PAIR_STATUS_AUTHORITY_KIND = "SignedCanonicalPairStatusProjection"
PAIR_STATUS_ALGORITHM = "Ed25519"
PAIR_STATUS_PUBLIC_KEY_SCHEMA = "pair-status-ed25519-public-key-v1"
PAIR_STATUS_PUBLIC_KEY_FILE = "pair-status-verification-key.json"

PAIR_STATUS_COMMON_FIELDS = frozenset({
    "authority_kind",
    "supervisor_authority_kind",
    "supervisor_final_authority_digest",
    "launch_receipt_digest",
    "canonical_outcome",
    "decision_receipt_digest",
    "result_occurrence_id",
    "result_entry_occurrence_receipt_digest",
    "execution_identity_digest",
    "execution_nonce",
    "stream_id",
    "source_snapshot_fingerprint",
    "canonical_result_bundle_digest",
    "canonical_result_bundle_kind",
    "canonical_result_payload_preimage_digest",
    "semantic_projection_digest",
    "error_kind",
    "child_returncode",
    "supervisor_status",
    "supervisor_projection_digest",
    "classification_valid",
    "pair_execution_target",
})
PAIR_STATUS_DURABLE_FIELDS = frozenset({
    "finalization_bundle_digest",
    "event_stream_authority_digest",
    "child_exit_disposition",
    "child_returncode_observation_kind",
})
# How a pair ended, as the supervisor projection resolved it.  ``RESOLVED``
# means the supervisor read the child's canonical result envelope, so the run
# holds that pair's result; the durable states mean it never got one -- the
# child was killed at the deadline (``TIMEOUT``) or failed to produce a usable
# canonical result (``ERROR``) -- and the durable fields above then carry what
# is known about the exit instead.  Consumers that ask "should this pair have
# left a result?" read these rather than guessing from the canonical outcome,
# which says ``ERROR`` in both the resolved and the durable case.
PAIR_STATUS_SUPERVISOR_RESOLVED = "RESOLVED"
PAIR_STATUS_DURABLE_SUPERVISOR_STATES = frozenset({"TIMEOUT", "ERROR"})

# How a *verified* pair status finalized, for consumers that have to know
# whether the run should hold that pair's result.  ``UNVERIFIED`` is not a
# fourth ending: it means this authority could not confirm any of them, and a
# consumer must not read it as permission for anything.
FINALIZATION_RESOLVED = "resolved"
FINALIZATION_DURABLE = "durable"
FINALIZATION_UNVERIFIED = "unverified"
PAIR_STATUS_SEAL_FIELDS = frozenset({
    "pair_status_schema",
    "pair_status_authority_kind",
    "pair_status_signing_algorithm",
    "pair_status_signing_key_id",
    "pair_status_body_digest",
    "pair_status_signature",
})
# Issue #20: the assumption-dependent column.  This is an *optional* field
# group, not a schema break: it is written only for a pair that actually has a
# conditional decision, so a pair-status file produced before the conditional
# lane existed carries exactly the v1 field set and keeps validating unchanged,
# and both fields must appear together or not at all.  The pair-status schema
# id therefore stays ``signed-canonical-pair-status-v1``; a future change that
# alters an existing field's meaning has to version the schema instead.
PAIR_STATUS_CONDITIONAL_FIELDS = frozenset({
    "conditional_outcome",
    "conditional_decision_receipt",
})
PAIR_STATUS_OPERATIONAL_DIAGNOSTIC_FIELDS = frozenset({
    "classification_valid",
    "error_kind",
    "detail",
})


def pair_status_operational_diagnostic(
    payload: Any,
) -> Mapping[str, Any] | None:
    """Recognize the exact unsigned diagnostic emitted on classification failure."""

    if (
        not isinstance(payload, Mapping)
        or set(payload) != set(PAIR_STATUS_OPERATIONAL_DIAGNOSTIC_FIELDS)
        or payload.get("classification_valid") is not False
        or payload.get("error_kind") != "PAIR_STATUS_AUTHORITY_INVALID"
        or type(payload.get("detail")) is not str
        or not payload["detail"]
    ):
        return None
    return dict(payload)


def _atomic_write(path: Path, data: bytes, mode: int) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(
        prefix=f".{path.name}.", dir=str(path.parent)
    )
    try:
        os.fchmod(descriptor, mode)
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    except Exception:
        try:
            os.close(descriptor)
        except OSError:
            pass
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def _public_key_payload(public_key_bytes: bytes) -> Mapping[str, Any]:
    public_key_sha256 = hashlib.sha256(public_key_bytes).hexdigest()
    body = {
        "schema": PAIR_STATUS_PUBLIC_KEY_SCHEMA,
        "authority_kind": "PairStatusEd25519PublicVerificationKey",
        "algorithm": PAIR_STATUS_ALGORITHM,
        "key_id": f"pair-status-ed25519:{public_key_sha256}",
        "public_key_base64": base64.b64encode(public_key_bytes).decode("ascii"),
        "public_key_sha256": public_key_sha256,
    }
    return {**body, "artifact_digest": authority_digest(body)}


def generate_pair_status_keypair(
    private_key_path: Path, public_key_path: Path,
) -> Mapping[str, Any]:
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

    private_key = Ed25519PrivateKey.generate()
    private_key_bytes = private_key.private_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PrivateFormat.Raw,
        encryption_algorithm=serialization.NoEncryption(),
    )
    public_key_bytes = private_key.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )
    public_payload = _public_key_payload(public_key_bytes)
    _atomic_write(Path(private_key_path), private_key_bytes, 0o600)
    _atomic_write(
        Path(public_key_path),
        (json.dumps(public_payload, sort_keys=True) + "\n").encode("utf-8"),
        0o644,
    )
    return public_payload


def write_pair_status_public_key(
    private_key_path: Path, public_key_path: Path,
) -> Mapping[str, Any]:
    """Materialize the public verifier without replacing retained secret state."""

    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

    try:
        private_key = Ed25519PrivateKey.from_private_bytes(
            Path(private_key_path).read_bytes()
        )
    except Exception as exc:
        raise ValueError("pair-status private signing key is invalid") from exc
    public_key_bytes = private_key.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )
    payload = _public_key_payload(public_key_bytes)
    _atomic_write(
        Path(public_key_path),
        (json.dumps(payload, sort_keys=True) + "\n").encode("utf-8"),
        0o644,
    )
    return payload


def load_pair_status_public_key(
    public_key_path: Path,
) -> tuple[Mapping[str, Any], Any]:
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

    payload = json.loads(Path(public_key_path).read_text(encoding="utf-8"))
    required = {
        "schema", "authority_kind", "algorithm", "key_id",
        "public_key_base64", "public_key_sha256", "artifact_digest",
    }
    if not isinstance(payload, Mapping) or set(payload) != required:
        raise ValueError("pair-status public-key schema differs")
    body = {key: payload[key] for key in required - {"artifact_digest"}}
    try:
        public_key_bytes = base64.b64decode(
            payload["public_key_base64"], validate=True
        )
    except Exception as exc:
        raise ValueError("pair-status public key encoding is invalid") from exc
    expected = _public_key_payload(public_key_bytes)
    if dict(payload) != expected or authority_digest(body) != payload["artifact_digest"]:
        raise ValueError("pair-status public-key authority drifted")
    try:
        public_key = Ed25519PublicKey.from_public_bytes(public_key_bytes)
    except Exception as exc:
        raise ValueError("pair-status public key is invalid") from exc
    return payload, public_key


def validate_pair_status_keypair(
    private_key_path: Path, public_key_path: Path,
) -> Mapping[str, Any]:
    """Fail closed unless a retained private key matches the public artifact."""

    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

    public_payload, _ = load_pair_status_public_key(public_key_path)
    try:
        private_key = Ed25519PrivateKey.from_private_bytes(
            Path(private_key_path).read_bytes()
        )
    except Exception as exc:
        raise ValueError("pair-status private signing key is invalid") from exc
    derived_public = private_key.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )
    if _public_key_payload(derived_public)["key_id"] != public_payload["key_id"]:
        raise ValueError("pair-status signing and verification keys differ")
    return public_payload


def _validate_durable_child_exit(body: Mapping[str, Any]) -> None:
    """rc と disposition の join（規則は ``child_exit`` の 1 箇所）。"""

    try:
        validate_durable_child_returncode_observation(
            child_exit_disposition=body["child_exit_disposition"],
            child_returncode=body["child_returncode"],
            observation_kind=body["child_returncode_observation_kind"],
        )
    except ValueError as exc:
        raise ValueError(f"pair-status durable child exit is invalid: {exc}") from exc


def _validate_pair_status_conditional_column(body: Mapping[str, Any]) -> None:
    """Bind the conditional column to this pair's own unconditional decision."""
    from scripts.function_tracer_pcode.authority.decision.conditional import (
        conditional_decision_receipt_from_payload,
        validate_conditional_decision_join,
    )

    if body.get("supervisor_status") != PAIR_STATUS_SUPERVISOR_RESOLVED:
        raise ValueError("pair-status conditional column requires a resolved pair")
    if body.get("canonical_outcome") != Outcome.UNKNOWN.value:
        # The conditional lane runs only after an unconditional UNKNOWN, so a
        # conditional column on a decided pair is not a column at all.
        raise ValueError("pair-status conditional column requires an unconditional UNKNOWN")
    receipt = conditional_decision_receipt_from_payload(
        body["conditional_decision_receipt"]
    )
    validate_conditional_decision_join(
        receipt,
        result_occurrence_id=body["result_occurrence_id"],
        unconditional_outcome=Outcome(body["canonical_outcome"]),
        unconditional_receipt_digest=body["decision_receipt_digest"],
    )
    if body["conditional_outcome"] != receipt.conditional_outcome.value:
        raise ValueError("pair-status conditional outcome contradicts its receipt")


def _validate_pair_status_body(body: Mapping[str, Any]) -> None:
    status = body.get("supervisor_status")
    expected = set(PAIR_STATUS_COMMON_FIELDS)
    if status in PAIR_STATUS_DURABLE_SUPERVISOR_STATES:
        expected.update(PAIR_STATUS_DURABLE_FIELDS)
    elif status != PAIR_STATUS_SUPERVISOR_RESOLVED:
        raise ValueError("pair-status supervisor disposition is invalid")
    conditional_fields = PAIR_STATUS_CONDITIONAL_FIELDS & set(body)
    if conditional_fields:
        # Naming either field requires both: a half-written column would let a
        # conditional outcome stand without the receipt that justifies it.
        expected.update(PAIR_STATUS_CONDITIONAL_FIELDS)
    if set(body) != expected:
        raise ValueError("pair-status authority fields differ")
    if body.get("classification_valid") is not True:
        raise ValueError("pair-status classification is not valid")
    outcome = body.get("canonical_outcome")
    if outcome not in {"EQUIVALENT", "NOT_EQ", "UNKNOWN", "TIMEOUT", "ERROR"}:
        raise ValueError("pair-status canonical outcome is invalid")
    if (outcome == "ERROR") != (
        type(body.get("error_kind")) is str and bool(body.get("error_kind"))
    ):
        raise ValueError("pair-status ERROR/error_kind join is invalid")
    required_strings = PAIR_STATUS_COMMON_FIELDS - {
        "error_kind", "child_returncode", "classification_valid",
        "pair_execution_target",
    }
    if any(type(body.get(field)) is not str or not body[field] for field in required_strings):
        raise ValueError("pair-status required authority field is empty")
    if body["child_returncode"] is not None and type(body["child_returncode"]) is not int:
        raise ValueError("pair-status child return code is invalid")
    target = body["pair_execution_target"]
    target_fields = {
        "schema", "authority_kind", "sample_identity",
        "output_sample_relative_path", "function_name", "left_binary_id",
        "right_binary_id", "source_path", "source_sha256",
        "left_binary_path", "left_binary_sha256", "right_binary_path",
        "right_binary_sha256", "analysis_source_digest",
        "analysis_config_digest", "target_digest",
    }
    if not isinstance(target, Mapping) or set(target) != target_fields:
        raise ValueError("pair execution target schema differs")
    target_body = {key: target[key] for key in target if key != "target_digest"}
    if (
        target["schema"] != "eqbench-pair-execution-target-v1"
        or target["authority_kind"] != "PairExecutionTargetReceipt"
        or any(type(target[field]) is not str or not target[field] for field in target_fields)
        or target["target_digest"] != authority_digest(target_body)
    ):
        raise ValueError("pair execution target authority is invalid")
    if status in PAIR_STATUS_DURABLE_SUPERVISOR_STATES and any(
        type(body.get(field)) is not str or not body[field]
        for field in PAIR_STATUS_DURABLE_FIELDS
    ):
        raise ValueError("pair-status durable authority field is empty")
    if body.get("canonical_result_bundle_kind") != "CanonicalResultFinalizationBundle":
        raise ValueError("pair-status canonical bundle kind is invalid")
    authority_kind = body.get("authority_kind")
    supervisor_kind = body.get("supervisor_authority_kind")
    if status == PAIR_STATUS_SUPERVISOR_RESOLVED:
        if (
            authority_kind != "SupervisorCanonicalResultResolvedReceipt"
            or supervisor_kind != "SupervisorCanonicalResultResolvedReceipt"
        ):
            raise ValueError("pair-status RESOLVED authority kind is invalid")
        if body["child_returncode"] != CLI_EXIT_CODE_BY_OUTCOME[Outcome(outcome)]:
            raise ValueError("pair-status resolved outcome/child exit join is invalid")
    else:
        expected_outcome = status
        expected_kind = f"Durable{status.title()}FinalizationBundle"
        if outcome != expected_outcome:
            raise ValueError("pair-status durable status/outcome join is invalid")
        if authority_kind != expected_kind or supervisor_kind != expected_kind:
            raise ValueError("pair-status durable authority kind is invalid")
        _validate_durable_child_exit(body)
    if conditional_fields:
        _validate_pair_status_conditional_column(body)


def seal_pair_status(
    projection: Mapping[str, Any], *, private_key_path: Path,
    public_key_path: Path,
) -> Mapping[str, Any]:
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

    body = dict(projection)
    _validate_pair_status_body(body)
    public_payload, _ = load_pair_status_public_key(public_key_path)
    private_key_bytes = Path(private_key_path).read_bytes()
    try:
        private_key = Ed25519PrivateKey.from_private_bytes(private_key_bytes)
    except Exception as exc:
        raise ValueError("pair-status private signing key is invalid") from exc
    derived_public = private_key.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )
    if _public_key_payload(derived_public)["key_id"] != public_payload["key_id"]:
        raise ValueError("pair-status signing and verification keys differ")
    body_digest = authority_digest(body)
    signature = private_key.sign(bytes.fromhex(body_digest))
    return {
        **body,
        "pair_status_schema": PAIR_STATUS_SCHEMA,
        "pair_status_authority_kind": PAIR_STATUS_AUTHORITY_KIND,
        "pair_status_signing_algorithm": PAIR_STATUS_ALGORITHM,
        "pair_status_signing_key_id": public_payload["key_id"],
        "pair_status_body_digest": body_digest,
        "pair_status_signature": base64.b64encode(signature).decode("ascii"),
    }


def validate_signed_pair_status(
    payload: Mapping[str, Any], *, public_key_path: Path,
) -> Mapping[str, Any]:
    if not isinstance(payload, Mapping):
        raise ValueError("pair-status payload is not an object")
    if set(payload) != set(PAIR_STATUS_SEAL_FIELDS) | (
        set(PAIR_STATUS_COMMON_FIELDS)
        | (set(PAIR_STATUS_DURABLE_FIELDS)
           if payload.get("supervisor_status") in PAIR_STATUS_DURABLE_SUPERVISOR_STATES
           else set())
        # The optional conditional group is accepted only as a whole; a payload
        # naming one of its fields fails the body check below.
        | (set(PAIR_STATUS_CONDITIONAL_FIELDS) & set(payload))
    ):
        raise ValueError("signed pair-status schema differs")
    body = {key: payload[key] for key in payload if key not in PAIR_STATUS_SEAL_FIELDS}
    public_payload, public_key = load_pair_status_public_key(public_key_path)
    body_digest = authority_digest(body)
    if (
        payload["pair_status_schema"] != PAIR_STATUS_SCHEMA
        or payload["pair_status_authority_kind"] != PAIR_STATUS_AUTHORITY_KIND
        or payload["pair_status_signing_algorithm"] != PAIR_STATUS_ALGORITHM
        or payload["pair_status_signing_key_id"] != public_payload["key_id"]
        or payload["pair_status_body_digest"] != body_digest
    ):
        raise ValueError("pair-status seal metadata is invalid")
    try:
        signature = base64.b64decode(payload["pair_status_signature"], validate=True)
        public_key.verify(signature, bytes.fromhex(body_digest))
    except Exception as exc:
        raise ValueError("pair-status signature is invalid") from exc
    _validate_pair_status_body(body)
    return body


def pair_status_finalization(
    payload: Any, *, public_key_path: Path | None = None,
    pair_status_path: Path | None = None,
) -> str:
    """How this pair ended, but only once the whole signed status validates.

    The supervisor state is a *claim* until the seal, the field set, the
    durable authority fields and the child-exit join have all been checked:
    a file that merely says ``supervisor_status: TIMEOUT`` is not a pair the
    supervisor killed, it is a file saying so.  Consumers that would excuse
    something on the strength of the ending (a missing result payload, say)
    must ask here rather than read the field, and anything this function
    cannot confirm comes back ``FINALIZATION_UNVERIFIED``.

    ``public_key_path`` defaults to the verification key the run wrote next to
    its results, found from ``pair_status_path``.
    """

    if public_key_path is None:
        if pair_status_path is None:
            return FINALIZATION_UNVERIFIED
        try:
            public_key_path = find_pair_status_public_key(Path(pair_status_path))
        except (OSError, ValueError):
            return FINALIZATION_UNVERIFIED
    try:
        body = validate_signed_pair_status(payload, public_key_path=public_key_path)
    except (OSError, TypeError, ValueError):
        return FINALIZATION_UNVERIFIED
    if body["supervisor_status"] == PAIR_STATUS_SUPERVISOR_RESOLVED:
        return FINALIZATION_RESOLVED
    return FINALIZATION_DURABLE


def pair_status_resume_disposition(body: Mapping[str, Any]) -> str:
    """Apply the production batch-resume contract to a verified status body."""

    _validate_pair_status_body(body)
    return BATCH_RESUME_DISPOSITION_BY_OUTCOME[Outcome(body["canonical_outcome"])]


def resume_disposition_should_skip(disposition: str, *, mode: str) -> bool:
    """Decide pair-level reuse after the signed status and target validate."""

    dispositions = frozenset(BATCH_RESUME_DISPOSITION_BY_OUTCOME.values())
    if disposition not in dispositions or mode not in {"NORMAL_RESUME", "ERROR_ONLY"}:
        raise ValueError("pair resume policy input is invalid")
    return mode == "NORMAL_RESUME" or disposition != "FAILED_INFRASTRUCTURE"


def pair_status_file_skip_decision(
    pair_status_path: Path, *, log_path: Path, public_key_path: Path,
    expected_pair_target_path: Path, mode: str,
    compatible_analysis_config_digest: str | None = None,
    compatible_analysis_source_digest: str | None = None,
) -> str:
    """Return SCHEDULE for every missing or unverifiable pair artifact."""

    try:
        if (
            not log_path.is_file() or log_path.stat().st_size == 0
            or not pair_status_path.is_file() or pair_status_path.stat().st_size == 0
        ):
            return "SCHEDULE"
        payload = json.loads(pair_status_path.read_text(encoding="utf-8"))
        body = validate_signed_pair_status(payload, public_key_path=public_key_path)
        expected_target = json.loads(
            expected_pair_target_path.read_text(encoding="utf-8")
        )
        accepted_targets = [expected_target]
        if ((compatible_analysis_config_digest is None)
                != (compatible_analysis_source_digest is None)):
            return "SCHEDULE"
        if compatible_analysis_config_digest is not None:
            if not all(re.fullmatch(r"[0-9a-f]{64}", value) for value in (
                compatible_analysis_config_digest,
                compatible_analysis_source_digest,
            )):
                return "SCHEDULE"
            compatible_target = {
                key: value for key, value in expected_target.items()
                if key != "target_digest"
            }
            compatible_target["analysis_config_digest"] = (
                compatible_analysis_config_digest
            )
            compatible_target["analysis_source_digest"] = (
                compatible_analysis_source_digest
            )
            accepted_targets.append({
                **compatible_target,
                "target_digest": authority_digest(compatible_target),
            })
        if body["pair_execution_target"] not in accepted_targets:
            return "SCHEDULE"
        disposition = pair_status_resume_disposition(body)
        return (
            "SKIP" if resume_disposition_should_skip(disposition, mode=mode)
            else "SCHEDULE"
        )
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError):
        return "SCHEDULE"


def legacy_pair_status_target_matches(
    pair_status_path: Path, *, expected_pair_target_path: Path,
) -> bool:
    """Compare concrete pair identity while ignoring analysis-code provenance.

    This is intentionally a narrow compatibility path for ERROR-only reruns
    of historical logs.  It does not validate the Ed25519 seal or the old
    analysis source/config digests.  It does require a well-formed target
    receipt, its own target digest, and equality of all concrete source,
    binary, sample, function, and pair fields.
    """

    target_fields = {
        "schema", "authority_kind", "sample_identity",
        "output_sample_relative_path", "function_name", "left_binary_id",
        "right_binary_id", "source_path", "source_sha256",
        "left_binary_path", "left_binary_sha256", "right_binary_path",
        "right_binary_sha256", "analysis_source_digest",
        "analysis_config_digest", "target_digest",
    }
    ignored_provenance = {
        "analysis_source_digest", "analysis_config_digest", "target_digest",
    }
    try:
        payload = json.loads(pair_status_path.read_text(encoding="utf-8"))
        expected = json.loads(
            expected_pair_target_path.read_text(encoding="utf-8")
        )
        actual = payload.get("pair_execution_target")
        if (
            not isinstance(actual, Mapping)
            or not isinstance(expected, Mapping)
            or set(actual) != target_fields
            or set(expected) != target_fields
            or any(type(actual[field]) is not str or not actual[field]
                   for field in target_fields)
            or any(type(expected[field]) is not str or not expected[field]
                   for field in target_fields)
            or actual["target_digest"] != authority_digest(
                {key: actual[key] for key in actual if key != "target_digest"}
            )
            or expected["target_digest"] != authority_digest(
                {key: expected[key] for key in expected if key != "target_digest"}
            )
        ):
            return False
        return all(
            actual[field] == expected[field]
            for field in target_fields - ignored_provenance
        )
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError, TypeError):
        return False


def find_pair_status_public_key(pair_status_path: Path) -> Path:
    for directory in (pair_status_path.parent, *pair_status_path.parents):
        candidate = directory / PAIR_STATUS_PUBLIC_KEY_FILE
        if candidate.is_file():
            return candidate
    raise ValueError(f"pair-status public verification key is missing: {pair_status_path}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generate-private-key")
    parser.add_argument("--write-public-key")
    parser.add_argument("--validate-private-key")
    parser.add_argument("--export-public-from-private")
    parser.add_argument("--public-key")
    parser.add_argument("--validate-pair-status")
    parser.add_argument("--legacy-pair-target-match")
    parser.add_argument("--pair-log")
    parser.add_argument("--allow-operational-diagnostic", action="store_true")
    parser.add_argument("--resume-disposition", action="store_true")
    parser.add_argument(
        "--resume-skip-mode", choices=("NORMAL_RESUME", "ERROR_ONLY")
    )
    parser.add_argument("--expected-pair-target")
    parser.add_argument("--compatible-analysis-config-digest")
    parser.add_argument("--compatible-analysis-source-digest")
    args = parser.parse_args(argv)
    if args.generate_private_key:
        if not args.generate_private_key or not args.write_public_key:
            parser.error("key generation requires private and public output paths")
        payload = generate_pair_status_keypair(
            Path(args.generate_private_key), Path(args.write_public_key)
        )
        print(payload["key_id"])
        return 0
    if args.validate_private_key:
        if not args.public_key:
            parser.error("private-key validation requires --public-key")
        payload = validate_pair_status_keypair(
            Path(args.validate_private_key), Path(args.public_key)
        )
        print(payload["key_id"])
        return 0
    if args.export_public_from_private:
        if not args.write_public_key:
            parser.error("public-key export requires --write-public-key")
        payload = write_pair_status_public_key(
            Path(args.export_public_from_private), Path(args.write_public_key)
        )
        print(payload["key_id"])
        return 0
    if args.write_public_key:
        parser.error("--write-public-key requires key generation or export")
    if args.validate_pair_status:
        pair_status_path = Path(args.validate_pair_status)
        if args.resume_skip_mode:
            if not args.public_key or not args.expected_pair_target or not args.pair_log:
                parser.error(
                    "resume skip mode requires public key, pair log and expected target"
                )
            print(pair_status_file_skip_decision(
                pair_status_path,
                log_path=Path(args.pair_log),
                public_key_path=Path(args.public_key),
                expected_pair_target_path=Path(args.expected_pair_target),
                mode=args.resume_skip_mode,
                compatible_analysis_config_digest=(
                    args.compatible_analysis_config_digest
                ),
                compatible_analysis_source_digest=(
                    args.compatible_analysis_source_digest
                ),
            ))
            return 0
        payload = json.loads(pair_status_path.read_text(encoding="utf-8"))
        diagnostic = pair_status_operational_diagnostic(payload)
        if args.allow_operational_diagnostic and diagnostic is not None:
            print("ERROR")
            return 0
        public_key_path = (
            Path(args.public_key) if args.public_key
            else find_pair_status_public_key(pair_status_path)
        )
        body = validate_signed_pair_status(
            payload,
            public_key_path=public_key_path,
        )
        if args.expected_pair_target:
            expected_target = json.loads(
                Path(args.expected_pair_target).read_text(encoding="utf-8")
            )
            if body["pair_execution_target"] != expected_target:
                raise ValueError("signed pair-status target differs from current execution target")
        disposition = pair_status_resume_disposition(body)
        print(disposition if args.resume_disposition else body["canonical_outcome"])
        return 0
    if args.legacy_pair_target_match:
        if not args.expected_pair_target:
            parser.error(
                "legacy pair target matching requires --expected-pair-target"
            )
        print(
            "MATCH" if legacy_pair_status_target_matches(
                Path(args.legacy_pair_target_match),
                expected_pair_target_path=Path(args.expected_pair_target),
            ) else "MISMATCH"
        )
        return 0
    parser.error("one pair-status authority operation is required")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

"""Single factory for legacy and recurrence unary premises."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from scripts.function_tracer_pcode.core.recurrence_contracts import (
    FUNCTION_UNARY_PREMISE_SCHEMA_ID,
    RECURRENCE_PREMISE_CODEC_ID,
    RECURRENCE_UNARY_DOMAIN,
    RecurrenceDigestCodec,
)
from scripts.function_tracer_pcode.proof.obligations.model import UnaryArtifactDomain
from scripts.function_tracer_pcode.proof.obligations.snapshot import SnapshotFingerprintCodec


LEGACY_PREMISE_CODEC_ID = "snapshot_fingerprint_codec_v1"


@dataclass(frozen=True)
class FunctionUnaryPremise:
    semantic_seed_digest: str
    function_premise_digest: str
    premise_schema_id: str
    premise_codec_id: str
    canonical_payload: Any


def build_function_unary_premise(
    domain: str,
    function_snapshot_fingerprint: str,
    semantic_seed: Any,
    domain_contract: Any,
    normalization_policy_digest: str,
) -> FunctionUnaryPremise:
    normalized_domain = UnaryArtifactDomain.normalize(domain)
    seed_key = (
        semantic_seed.stable_key()
        if callable(getattr(semantic_seed, "stable_key", None))
        else semantic_seed
    )
    if normalized_domain != RECURRENCE_UNARY_DOMAIN:
        seed_digest = SnapshotFingerprintCodec.digest(seed_key)
        payload = (
            FUNCTION_UNARY_PREMISE_SCHEMA_ID,
            normalized_domain,
            function_snapshot_fingerprint,
            SnapshotFingerprintCodec.freeze(domain_contract),
            str(normalization_policy_digest),
            seed_digest,
        )
        return FunctionUnaryPremise(
            seed_digest,
            SnapshotFingerprintCodec.digest(payload),
            FUNCTION_UNARY_PREMISE_SCHEMA_ID,
            LEGACY_PREMISE_CODEC_ID,
            payload,
        )
    seed_digest = RecurrenceDigestCodec.digest("recurrence_seed_core_v1", seed_key)
    payload = {
        "schema_id": FUNCTION_UNARY_PREMISE_SCHEMA_ID,
        "codec_id": RECURRENCE_PREMISE_CODEC_ID,
        "unary_domain": RECURRENCE_UNARY_DOMAIN,
        "function_snapshot_fingerprint": str(function_snapshot_fingerprint),
        "recurrence_domain_contract": domain_contract,
        "normalization_policy_digest": str(normalization_policy_digest),
        "recurrence_seed_core_digest": seed_digest,
    }
    return FunctionUnaryPremise(
        seed_digest,
        RecurrenceDigestCodec.digest(FUNCTION_UNARY_PREMISE_SCHEMA_ID, payload),
        FUNCTION_UNARY_PREMISE_SCHEMA_ID,
        RECURRENCE_PREMISE_CODEC_ID,
        payload,
    )

"""Sealed Phase 7 producer-site contracts for call/effect proof batches."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class CallEffectProducerSiteSpec:
    site_id: str
    producer_id: str
    disposition: str

    def __post_init__(self) -> None:
        if (
            type(self.site_id) is not str
            or not self.site_id
            or type(self.producer_id) is not str
            or not self.producer_id
            or self.disposition != "DECISIVE"
        ):
            raise ValueError("call/effect producer-site contract is invalid")


CALL_EFFECT_PROOF_BATCH_SITE = CallEffectProducerSiteSpec(
    "checker-call-effect-proof-batch",
    "call-effect-proof-batch-v2",
    "DECISIVE",
)

CALL_EFFECT_PRODUCER_SITE_SPECS = (CALL_EFFECT_PROOF_BATCH_SITE,)

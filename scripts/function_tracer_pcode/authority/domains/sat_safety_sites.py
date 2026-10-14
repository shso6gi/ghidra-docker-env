"""Sealed Phase 7 producer-site contracts for the SAT-safety lifecycle."""

from __future__ import annotations

from dataclasses import dataclass

from scripts.function_tracer_pcode.proof.sat_safety_resolution import (
    SAT_SAFETY_REASON_RESOLUTION,
    SatSafetyResolution,
)


def _reason_ids_of(*resolutions: SatSafetyResolution) -> tuple[str, ...]:
    """解消の型が ``resolutions`` の SAT-safety reason id（表から導く。手で写さない）。"""
    return tuple(sorted(
        reason_id for reason_id, resolution in SAT_SAFETY_REASON_RESOLUTION.items()
        if resolution in resolutions
    ))


@dataclass(frozen=True)
class SatSafetyProducerSiteSpec:
    site_id: str
    producer_id: str
    disposition: str
    reason_ids: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if (
            type(self.site_id) is not str
            or not self.site_id
            or type(self.producer_id) is not str
            or not self.producer_id
            or self.disposition not in {"ELIGIBLE", "DECISIVE"}
            or type(self.reason_ids) is not tuple
            or any(type(item) is not str or not item for item in self.reason_ids)
            or (self.disposition == "ELIGIBLE") != bool(self.reason_ids)
        ):
            raise ValueError("SAT-safety producer-site contract is invalid")


SAT_SAFETY_BLOCKER_OBSERVED_SITE = SatSafetyProducerSiteSpec(
    "sat-safety-blocker-observed",
    "sat_unsafety_reason_producer",
    "ELIGIBLE",
    _reason_ids_of(SatSafetyResolution.ANALYSIS_UNSAFETY, SatSafetyResolution.REPLAY),
)
SAT_SAFETY_BLOCKER_COMPLETED_SITE = SatSafetyProducerSiteSpec(
    "sat-safety-blocker-completed",
    "sat_unsafety_resolution_producer",
    "DECISIVE",
)
SAT_SAFETY_COUNTEREXAMPLE_BOUND_COMPLETED_SITE = SatSafetyProducerSiteSpec(
    "sat-safety-counterexample-bound-completed",
    "sat_counterexample_bound_resolution_producer",
    "DECISIVE",
)
SAT_SAFETY_AMBIGUITY_OBSERVED_SITE = SatSafetyProducerSiteSpec(
    "sat-safety-ambiguity-observed",
    "sat_counterexample_ambiguity_producer",
    "ELIGIBLE",
    _reason_ids_of(SatSafetyResolution.PARTITION_AMBIGUITY),
)
SAT_SAFETY_AMBIGUITY_COMPLETED_SITE = SatSafetyProducerSiteSpec(
    "sat-safety-ambiguity-completed",
    "sat_counterexample_ambiguity_resolution_producer",
    "DECISIVE",
)

SAT_SAFETY_PRODUCER_SITE_SPECS = (
    SAT_SAFETY_BLOCKER_OBSERVED_SITE,
    SAT_SAFETY_BLOCKER_COMPLETED_SITE,
    SAT_SAFETY_COUNTEREXAMPLE_BOUND_COMPLETED_SITE,
    SAT_SAFETY_AMBIGUITY_OBSERVED_SITE,
    SAT_SAFETY_AMBIGUITY_COMPLETED_SITE,
)

if len({spec.site_id for spec in SAT_SAFETY_PRODUCER_SITE_SPECS}) != len(
    SAT_SAFETY_PRODUCER_SITE_SPECS
):
    raise ValueError("SAT-safety producer-site IDs are duplicated")

"""Sealed Phase 7 producer-site contracts for the SAT-safety lifecycle."""

from __future__ import annotations

from dataclasses import dataclass


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
    (
        "counterexample_analysis_safety_unproven",
        "counterexample_same_function_replay_unproven",
    ),
)
SAT_SAFETY_BLOCKER_COMPLETED_SITE = SatSafetyProducerSiteSpec(
    "sat-safety-blocker-completed",
    "sat_unsafety_resolution_producer",
    "DECISIVE",
)
SAT_SAFETY_AMBIGUITY_OBSERVED_SITE = SatSafetyProducerSiteSpec(
    "sat-safety-ambiguity-observed",
    "sat_counterexample_ambiguity_producer",
    "ELIGIBLE",
    ("counterexample_partition_replay_ambiguous",),
)
SAT_SAFETY_AMBIGUITY_COMPLETED_SITE = SatSafetyProducerSiteSpec(
    "sat-safety-ambiguity-completed",
    "sat_counterexample_ambiguity_resolution_producer",
    "DECISIVE",
)

SAT_SAFETY_PRODUCER_SITE_SPECS = (
    SAT_SAFETY_BLOCKER_OBSERVED_SITE,
    SAT_SAFETY_BLOCKER_COMPLETED_SITE,
    SAT_SAFETY_AMBIGUITY_OBSERVED_SITE,
    SAT_SAFETY_AMBIGUITY_COMPLETED_SITE,
)

if len({spec.site_id for spec in SAT_SAFETY_PRODUCER_SITE_SPECS}) != len(
    SAT_SAFETY_PRODUCER_SITE_SPECS
):
    raise ValueError("SAT-safety producer-site IDs are duplicated")

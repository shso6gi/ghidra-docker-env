"""Compatibility snapshots for legacy-vs-obligation branch execution."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Mapping, Tuple

from .snapshot import SnapshotFingerprintCodec


@dataclass(frozen=True)
class LegacyExecutionSnapshot:
    semantic_result: Any
    legacy_timeout: bool
    stage_path: Tuple[str, ...]
    unknown_reason_keys: Tuple[Tuple[Any, ...], ...]
    root_blocker_keys: Tuple[Tuple[Any, ...], ...]
    decisive_counterexample: Any
    public_schema: Tuple[str, ...]
    proof_action_surface: Any
    proof_event_surface: Any

    @classmethod
    def from_result(cls, result: Any) -> "LegacyExecutionSnapshot":
        timeout_fn = getattr(result, "is_timeout", None)
        reasons = []
        for reason in getattr(result, "unknown_reasons", ()) or ():
            reasons.append((
                getattr(reason, "reason_id", None),
                getattr(reason, "decision_effect", None),
                getattr(reason, "reason_scope", None),
                getattr(reason, "recovery_proof_kind", None),
                getattr(reason, "pair_or_case", None),
            ))
        public_dict = getattr(result, "to_dict", None)
        public_payload = public_dict() if callable(public_dict) else {}
        schema = tuple(sorted(public_payload.keys()))
        blockers = []
        if public_payload:
            from ...validation.root_blocker_summary import summarize_root_blockers

            summary = summarize_root_blockers([public_payload])
            blockers = [blocker.blocker_id.to_key() for blocker in summary.active_root_blockers]
        action_surface = SnapshotFingerprintCodec.freeze(
            tuple(
                action.to_dict() if callable(getattr(action, "to_dict", None)) else action
                for action in getattr(result, "unknown_recovery_actions", ()) or ()
            )
        )
        debug_trace = getattr(result, "debug_trace", None)
        event_surface = SnapshotFingerprintCodec.freeze({
            "completed_evidence": tuple(getattr(result, "completed_recovery_proof_evidence", ()) or ()),
            "proof_completion_events": tuple(
                event.to_dict() for event in getattr(debug_trace, "proof_completion_events", ()) or ()
            ),
            "causal_transitions": tuple(
                event.to_dict() for event in getattr(debug_trace, "causal_transitions", ()) or ()
            ),
        })
        return cls(
            getattr(result, "is_equivalent", None),
            bool(timeout_fn()) if callable(timeout_fn) else False,
            tuple(getattr(result, "stage_path", ()) or ()),
            tuple(reasons),
            tuple(blockers),
            getattr(result, "counterexample", None),
            schema,
            action_surface,
            event_surface,
        )


@dataclass(frozen=True)
class ShadowComparisonReport:
    compatible: bool
    differences: Tuple[str, ...]
    legacy: LegacyExecutionSnapshot
    obligation: LegacyExecutionSnapshot

    @classmethod
    def compare(cls, legacy_result: Any, obligation_result: Any) -> "ShadowComparisonReport":
        legacy = LegacyExecutionSnapshot.from_result(legacy_result)
        obligation = LegacyExecutionSnapshot.from_result(obligation_result)
        differences = []
        for field_name in (
            "semantic_result", "legacy_timeout", "stage_path", "unknown_reason_keys",
            "root_blocker_keys", "decisive_counterexample", "public_schema",
            "proof_action_surface", "proof_event_surface",
        ):
            if getattr(legacy, field_name) != getattr(obligation, field_name):
                differences.append(field_name)
        return cls(not differences, tuple(differences), legacy, obligation)


@dataclass(frozen=True)
class ProductionShadowValidation:
    comparison: ShadowComparisonReport
    legacy_surface_hash: str
    obligation_surface_hash: str
    optimization_delta: Mapping[str, int]


class ProductionShadowValidator:
    """Run complete legacy/new workflows and compare their finalized results."""

    @classmethod
    def run(
        cls,
        legacy_workflow: Callable[[], Any],
        obligation_workflow: Callable[[], Any],
    ) -> ProductionShadowValidation:
        legacy = legacy_workflow()
        obligation = obligation_workflow()
        comparison = ShadowComparisonReport.compare(legacy, obligation)
        legacy_payload = legacy.to_dict()
        obligation_payload = obligation.to_dict()
        return ProductionShadowValidation(
            comparison=comparison,
            legacy_surface_hash=SnapshotFingerprintCodec.digest(legacy_payload),
            obligation_surface_hash=SnapshotFingerprintCodec.digest(obligation_payload),
            optimization_delta=cls._optimization_delta(legacy, obligation),
        )

    @staticmethod
    def _optimization_delta(legacy: Any, obligation: Any) -> Mapping[str, int]:
        left = getattr(legacy, "pairwise_debug_stats", None) or {}
        right = getattr(obligation, "pairwise_debug_stats", None) or {}
        keys = (
            "exact_query_attempt_cache_hits",
            "exact_query_attempt_cache_misses",
            "obligation_pair_cache_hits",
            "obligation_pair_cache_misses",
        )
        return {
            key: int(right.get(key, 0) or 0) - int(left.get(key, 0) or 0)
            for key in keys
        }

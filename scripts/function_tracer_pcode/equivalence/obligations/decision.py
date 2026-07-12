"""Aggregate current-generation obligation outcomes into the legacy result."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Tuple

from ..unknown_reason import build_unknown_recovery_actions
from .model import FunctionProofOutcome
from .runtime import ObligationRuntimeSession


@dataclass(frozen=True)
class DecisionAggregation:
    outcome: FunctionProofOutcome
    discharged_reason_ids: Tuple[str, ...] = ()
    remaining_reason_ids: Tuple[str, ...] = ()


class DecisionAggregator:
    """Rebuild a decision only from validated, current-generation outcomes."""

    @classmethod
    def apply(cls, result: Any, runtime: ObligationRuntimeSession) -> DecisionAggregation:
        reasons = tuple(getattr(result, "unknown_reasons", ()) or ())
        if not reasons:
            return DecisionAggregation(cls._outcome(result))

        discharged = []
        remaining = []
        decisive_not_eq = False
        discharged_pairs = set()
        for reason in reasons:
            outcome = runtime.outcome_for_reason(reason)
            if outcome == FunctionProofOutcome.EQUIVALENT:
                discharged.append(reason)
                pair_id = getattr(reason, "pair_or_case", None)
                if pair_id:
                    discharged_pairs.add(str(pair_id))
            elif outcome == FunctionProofOutcome.NOT_EQUIVALENT:
                decisive_not_eq = True
                discharged.append(reason)
            else:
                remaining.append(reason)

        if decisive_not_eq:
            result.is_equivalent = False
            result.unknown_reasons = []
            result.unknown_recovery_actions = []
            result.decision_gated_by_pending_proof = False
            return DecisionAggregation(
                FunctionProofOutcome.NOT_EQUIVALENT,
                tuple(reason.reason_id for reason in discharged),
            )

        result.unknown_reasons = list(remaining)
        result.unknown_recovery_actions = list(build_unknown_recovery_actions(remaining))
        stats = dict(getattr(result, "pairwise_stats", None) or {})
        total = int(stats.get("total_pairs", 0) or 0)
        unsat = int(stats.get("unsat_pairs", 0) or 0)
        sat = int(stats.get("sat_pairs", 0) or 0)
        unknown = int(stats.get("unknown_pairs", 0) or 0)
        errors = int(stats.get("error_pairs", 0) or 0)
        proof_resolved_pairs = min(unknown, len(discharged_pairs))
        if stats and proof_resolved_pairs:
            stats["unknown_pairs"] = unknown - proof_resolved_pairs
            stats["unsat_pairs"] = unsat + proof_resolved_pairs
            result.pairwise_stats = stats
            unknown -= proof_resolved_pairs
            unsat += proof_resolved_pairs

        all_pair_relations_proven = (
            total > 0 and sat == 0 and errors == 0 and unknown == 0 and unsat == total
        )
        if not remaining and all_pair_relations_proven:
            result.is_equivalent = True
            result.decision_gated_by_pending_proof = False
            outcome = FunctionProofOutcome.EQUIVALENT
        else:
            result.is_equivalent = None
            result.decision_gated_by_pending_proof = bool(remaining)
            outcome = FunctionProofOutcome.INCONCLUSIVE
        return DecisionAggregation(
            outcome,
            tuple(reason.reason_id for reason in discharged),
            tuple(reason.reason_id for reason in remaining),
        )

    @staticmethod
    def _outcome(result: Any) -> FunctionProofOutcome:
        value = getattr(result, "is_equivalent", None)
        if value is True:
            return FunctionProofOutcome.EQUIVALENT
        if value is False:
            return FunctionProofOutcome.NOT_EQUIVALENT
        return FunctionProofOutcome.INCONCLUSIVE

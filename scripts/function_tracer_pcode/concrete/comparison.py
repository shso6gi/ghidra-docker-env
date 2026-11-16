# -*- coding: utf-8 -*-
"""Deciding what two concrete runs on corresponding inputs establish.

``compare_runs`` returns either a ``ConcreteDifference`` -- both calls
completed without a hazard and the observed return values differ -- or a
``ConcreteNoEvidence`` with the reason nothing was established.

Neither is a final outcome of a pair.  ``ConcreteNoEvidence`` in particular is
internal: its reasons become registered UNKNOWN reasons where a proof consumes
them, and "the runs did not differ" is never evidence of equivalence.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Tuple, Union

from scripts.function_tracer_pcode.concrete.executor import (
    ExecutionResult,
    HazardKind,
    Termination,
)
from scripts.function_tracer_pcode.concrete.observation import (
    ObservationRefusal,
    ObservationRelation,
    ReturnObservationPlan,
    compare_return_values,
)


class NoEvidenceReason(str, Enum):
    RUN_DID_NOT_RETURN = "RUN_DID_NOT_RETURN"
    RUN_HAS_HAZARD = "RUN_HAS_HAZARD"
    OBSERVATION_MISSING = "OBSERVATION_MISSING"
    OBSERVATION_REFUSED = "OBSERVATION_REFUSED"
    NO_DIFFERENCE_OBSERVED = "NO_DIFFERENCE_OBSERVED"


@dataclass(frozen=True)
class ConcreteDifference:
    """Both calls returned cleanly and the return values differ."""

    plan: ReturnObservationPlan
    observed_values: Tuple[int, int]


@dataclass(frozen=True)
class ConcreteNoEvidence:
    reason: NoEvidenceReason
    # Which side (0 / 1) the reason comes from, when it is one-sided.
    side: Union[int, None] = None
    termination: Union[Termination, None] = None
    hazard_kinds: Tuple[HazardKind, ...] = ()
    observation_refusal: Union[ObservationRefusal, None] = None


def compare_runs(
    plan: ReturnObservationPlan, left: ExecutionResult, right: ExecutionResult
) -> Union[ConcreteDifference, ConcreteNoEvidence]:
    runs = (left, right)
    for side, run in enumerate(runs):
        if run.termination is not Termination.RETURNED:
            return ConcreteNoEvidence(
                NoEvidenceReason.RUN_DID_NOT_RETURN, side=side, termination=run.termination
            )
    for side, run in enumerate(runs):
        if run.hazards:
            return ConcreteNoEvidence(
                NoEvidenceReason.RUN_HAS_HAZARD, side=side, hazard_kinds=run.hazard_kinds()
            )
    values = []
    for side, (run, location) in enumerate(zip(runs, plan.locations)):
        value = run.observed(location.register)
        if value is None:
            return ConcreteNoEvidence(NoEvidenceReason.OBSERVATION_MISSING, side=side)
        values.append(value)
    relation = compare_return_values(plan, values[0], values[1])
    if isinstance(relation, ObservationRefusal):
        return ConcreteNoEvidence(
            NoEvidenceReason.OBSERVATION_REFUSED, observation_refusal=relation
        )
    if relation is ObservationRelation.DIFFERENT:
        return ConcreteDifference(plan, (values[0], values[1]))
    return ConcreteNoEvidence(NoEvidenceReason.NO_DIFFERENCE_OBSERVED)

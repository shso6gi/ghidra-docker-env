# -*- coding: utf-8 -*-
"""Replaying witnesses of the symbolic analysis on both binaries (#18).

A *replay plan* fixes, for one pair of functions, everything a run depends on
besides the witness: each side's ABI model and entry address, the
correspondence of their inputs (``concrete.input_surface``, read off the
formula's inputs), and what is compared after the runs
(``concrete.observation``).  A plan is refused, with the stage and the
reason, when any of these cannot be established.

For each witness the plan builds two execution requests on corresponding
inputs (``concrete.witness``), the executors run them, and
``concrete.comparison.compare_runs`` says what the two runs establish.  A
``WitnessReplay`` records all of it as facts: the witness's values, the
register images, each run's termination, hazards and observed value, and the
comparison.  It is never a verdict: a confirmed difference is evidence for
whoever owns the decision, and a witness that shows no difference shows
nothing about equivalence.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, replace
from enum import Enum
from typing import Any, Callable, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple, Union

from scripts.function_tracer_pcode.concrete.abi import AbiModel
from scripts.function_tracer_pcode.concrete.comparison import (
    ConcreteDifference,
    ConcreteNoEvidence,
    compare_runs,
)
from scripts.function_tracer_pcode.concrete.executor import (
    DEFAULT_STEP_LIMIT,
    ConcreteExecutor,
    ExecutionRequest,
    ExecutionResult,
    build_entry_state,
)
from scripts.function_tracer_pcode.concrete.input_surface import (
    InputCorrespondence,
    InputSurfaceRefusal,
    RegisterImage,
    bind_arguments,
    correspond_inputs,
)
from scripts.function_tracer_pcode.concrete.observation import (
    ObservationRefusal,
    ReturnObservationPlan,
    ReturnStorage,
    plan_return_observation,
    return_location,
)
from scripts.function_tracer_pcode.concrete.recording import request_to_json, result_to_json
from scripts.function_tracer_pcode.core.structural import exact_value_key
from scripts.function_tracer_pcode.concrete.witness import (
    FormulaInput,
    WitnessInput,
    WitnessRefusal,
    formula_surface,
    witness_input,
)

REPLAY_SCHEMA = "concrete-witness-replay-v1"


@dataclass(frozen=True)
class ReplaySide:
    """One function of the pair, as binary facts."""

    abi: AbiModel
    entry_address: int
    inputs: Tuple[FormulaInput, ...]
    return_storage: ReturnStorage


class PlanStage(str, Enum):
    INPUT_SURFACE = "INPUT_SURFACE"
    INPUT_CORRESPONDENCE = "INPUT_CORRESPONDENCE"
    RETURN_LOCATION = "RETURN_LOCATION"
    RETURN_OBSERVATION = "RETURN_OBSERVATION"


@dataclass(frozen=True)
class PlanRefusal:
    stage: PlanStage
    reason: Union[InputSurfaceRefusal, ObservationRefusal]
    side: Optional[int] = None

    def describe(self) -> str:
        side = "" if self.side is None else f"side{self.side}:"
        return f"{self.stage.value}:{side}{self.reason.value}"


@dataclass(frozen=True)
class ReplayPlan:
    sides: Tuple[ReplaySide, ReplaySide]
    correspondence: InputCorrespondence
    observation: ReturnObservationPlan
    step_limit: int = DEFAULT_STEP_LIMIT


def plan_replay(
    left: ReplaySide, right: ReplaySide, step_limit: int = DEFAULT_STEP_LIMIT
) -> Union[ReplayPlan, PlanRefusal]:
    surfaces = []
    for side, item in enumerate((left, right)):
        surface = formula_surface(item.abi, item.inputs)
        if isinstance(surface, InputSurfaceRefusal):
            return PlanRefusal(PlanStage.INPUT_SURFACE, surface, side)
        surfaces.append(surface)
    correspondence = correspond_inputs(surfaces[0], surfaces[1])
    if isinstance(correspondence, InputSurfaceRefusal):
        return PlanRefusal(PlanStage.INPUT_CORRESPONDENCE, correspondence)
    locations = []
    for side, item in enumerate((left, right)):
        location = return_location(item.abi, item.return_storage)
        if isinstance(location, ObservationRefusal):
            return PlanRefusal(PlanStage.RETURN_LOCATION, location, side)
        locations.append(location)
    observation = plan_return_observation(locations[0], locations[1])
    if isinstance(observation, ObservationRefusal):
        return PlanRefusal(PlanStage.RETURN_OBSERVATION, observation)
    return ReplayPlan((left, right), correspondence, observation, step_limit)


class WitnessStatus(str, Enum):
    # The runs on the witness's input returned different values (``ConcreteDifference``).
    CONFIRMED = "CONFIRMED"
    # The runs established nothing (``ConcreteNoEvidence``): a run did not
    # return, had a hazard, was not monitored, read writable data, or the
    # values did not differ on what was compared.
    NO_EVIDENCE = "NO_EVIDENCE"
    # The witness does not name one input of the pair; nothing was run.
    INPUT_REFUSED = "INPUT_REFUSED"


@dataclass(frozen=True)
class WitnessRequests:
    input: WitnessInput
    images: Tuple[Tuple[RegisterImage, ...], Tuple[RegisterImage, ...]]
    requests: Tuple[ExecutionRequest, ExecutionRequest]


def witness_requests(
    plan: ReplayPlan, witness: Mapping[str, object]
) -> Union[WitnessRequests, WitnessRefusal, InputSurfaceRefusal]:
    named = witness_input(plan.correspondence, (plan.sides[0].inputs, plan.sides[1].inputs), witness)
    if isinstance(named, WitnessRefusal):
        return named
    images = bind_arguments(named.correspondence, named.values)
    if isinstance(images, InputSurfaceRefusal):
        return images
    requests = []
    for side, item in enumerate(plan.sides):
        state = build_entry_state(item.abi, item.entry_address, images[side])
        observe = (plan.observation.locations[side].register,)
        requests.append(ExecutionRequest(item.entry_address, state, observe, plan.step_limit))
    return WitnessRequests(named, (images[0], images[1]), (requests[0], requests[1]))


@dataclass(frozen=True)
class WitnessReplay:
    """What replaying one witness established, as data."""

    status: WitnessStatus
    # ``NoEvidenceReason`` / refusal value, with the side and the details.
    reason: str
    witness_digest: str
    values: Tuple[int, ...] = ()
    images: Tuple[Tuple[Tuple[str, int], ...], Tuple[Tuple[str, int], ...]] = ((), ())
    requests: Tuple[Optional[ExecutionRequest], Optional[ExecutionRequest]] = (None, None)
    results: Tuple[Optional[ExecutionResult], Optional[ExecutionResult]] = (None, None)
    observed_values: Tuple[Optional[int], Optional[int]] = (None, None)
    seconds: float = 0.0

    def to_json(self) -> Dict[str, Any]:
        return {
            "schema": REPLAY_SCHEMA,
            "status": self.status.value,
            "reason": self.reason,
            "witness_digest": self.witness_digest,
            "values": list(self.values),
            "images": [[[r, v] for r, v in side] for side in self.images],
            "requests": [None if r is None else request_to_json(r) for r in self.requests],
            "results": [None if r is None else result_to_json(r) for r in self.results],
            "observed_values": list(self.observed_values),
            "seconds": round(self.seconds, 4),
        }


def witness_digest(witness: Mapping[str, object]) -> str:
    canonical = json.dumps(sorted((str(k), repr(v)) for k, v in witness.items()), separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _no_evidence_reason(outcome: ConcreteNoEvidence) -> str:
    parts = [outcome.reason.value]
    if outcome.side is not None:
        parts.append(f"side{outcome.side}")
    if outcome.termination is not None:
        parts.append(outcome.termination.value)
    if outcome.hazard_kinds:
        parts.append("+".join(kind.value for kind in outcome.hazard_kinds))
    if outcome.observation_refusal is not None:
        parts.append(outcome.observation_refusal.value)
    return ":".join(parts)


def judge_witness(
    plan: ReplayPlan,
    witness: Mapping[str, object],
    run: Callable[[int, ExecutionRequest], ExecutionResult],
    clock: Callable[[], float] = lambda: 0.0,
) -> WitnessReplay:
    """Replay one witness; ``run(side, request)`` executes on that side's binary."""
    digest = witness_digest(witness)
    prepared = witness_requests(plan, witness)
    if not isinstance(prepared, WitnessRequests):
        return WitnessReplay(WitnessStatus.INPUT_REFUSED, prepared.value, digest)
    started = clock()
    results = (run(0, prepared.requests[0]), run(1, prepared.requests[1]))
    elapsed = clock() - started
    images = tuple(tuple((image.register, image.value) for image in side) for side in prepared.images)
    observed = tuple(
        None if (value := result.observed(location.register)) is None else value.value
        for result, location in zip(results, plan.observation.locations)
    )
    outcome = compare_runs(plan.observation, results[0], results[1])
    common = dict(
        witness_digest=digest,
        values=prepared.input.values,
        images=images,
        requests=prepared.requests,
        results=results,
        observed_values=observed,
        seconds=elapsed,
    )
    if isinstance(outcome, ConcreteDifference):
        return WitnessReplay(WitnessStatus.CONFIRMED, plan.observation.arg_class.value, **common)
    return WitnessReplay(WitnessStatus.NO_EVIDENCE, _no_evidence_reason(outcome), **common)


def replay_witnesses(
    plan: ReplayPlan,
    witnesses: Iterable[Mapping[str, object]],
    executors: Tuple[ConcreteExecutor, ConcreteExecutor],
    *,
    stop_at_first_confirmation: bool = True,
    may_continue: Callable[[], bool] = lambda: True,
    clock: Callable[[], float] = lambda: 0.0,
    time_left: Callable[[], Optional[float]] = lambda: None,
) -> Tuple[WitnessReplay, ...]:
    """Replay distinct witnesses in order until one is confirmed (by default)
    or ``may_continue`` says the budget is spent.

    ``time_left()`` is the budget left (``None``: unbounded); each run gets it
    as its time limit, so no run outlasts the budget."""

    def run(side: int, request: ExecutionRequest) -> ExecutionResult:
        left = time_left()
        if left is not None:
            request = replace(request, time_limit_seconds=max(0.0, float(left)))
        return executors[side].execute(request)

    replays: List[WitnessReplay] = []
    seen = set()
    for witness in witnesses:
        # identity by exact comparison of the assignment (``core.structural``),
        # never by its digest
        identity = exact_value_key(tuple(sorted((str(name), value) for name, value in witness.items())))
        if identity in seen:
            continue
        seen.add(identity)
        if not may_continue():
            break
        replay = judge_witness(plan, witness, run, clock)
        replays.append(replay)
        if stop_at_first_confirmation and replay.status is WitnessStatus.CONFIRMED:
            break
    return tuple(replays)

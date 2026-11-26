# -*- coding: utf-8 -*-
"""Opening the concrete executors of a pair in the checker's process (#18, C2).

The checker already holds both programs, imported and analysed, in the
worker's JVM.  The concrete replay of the solver's witnesses
(``proof.concrete_counterexample``) runs on those same ``Program`` objects:
no second JVM, no second import or analysis of a binary.  This module opens
one executor per side (``ghidra.concrete_executor.open_executor``, which
checks the ABI model against the program's compiler specification) and
describes the function each side runs.

It is configured by the CLI (``ConcreteReplayOptions``); a checker built
without options -- library callers, the recorded-fixture replay, whose
programs are recordings -- never opens an executor.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple, Union

from scripts.function_tracer_pcode.core.fact_reliance import (
    FactHandle,
    FactKind,
    FactProvenance,
    FactSide,
    FactSlot,
    FactTarget,
)
from scripts.function_tracer_pcode.core.signature import is_pointer_data_type
from scripts.function_tracer_pcode.proof.concrete_counterexample import (
    ConcreteSideFacts,
    ConcreteSubject,
)

#: The stages of concrete execution a run can enable (Issue #323, C4).  The
#: runner's setting (``reporting.runner_concrete_policy``), the analysis config
#: identity and the per-pair record all name stages from this table, in this
#: order.  C4 has one stage: replaying the solver's witnesses (#18 C2).  A new
#: stage (C5: fixed-input search) is one more entry here plus its CLI flags.
STAGE_WITNESS_REPLAY = "witness_replay"
CONCRETE_STAGES: Tuple[str, ...] = (STAGE_WITNESS_REPLAY,)

#: Schema of the per-pair record of the concrete-execution setting
#: (``diagnostics.concrete_execution_setting``).
CONCRETE_SETTING_SCHEMA = "concrete-execution-setting-v1"
#: Why the requested stages cannot run in this pair (``inactive_reason``).
INACTIVE_NOT_REQUESTED = "not_requested"
INACTIVE_NO_ANALYSIS_DEADLINE = "no_analysis_deadline"


@dataclass(frozen=True)
class ConcreteReplayOptions:
    """Budgets of the concrete replay of one pair.

    ``budget_seconds`` bounds the replay of all witnesses (and never extends
    the pair's analysis deadline: the lane takes the smaller of the two);
    ``run_time_limit_seconds`` and ``step_limit`` bound one run.
    """

    budget_seconds: float = 60.0
    run_time_limit_seconds: float = 20.0
    step_limit: int = 300_000


def concrete_execution_setting(
    options: Optional[ConcreteReplayOptions],
    analysis_deadline_seconds: Optional[float],
) -> Dict[str, Any]:
    """The concrete-execution setting one pair ran under (Issue #323, C4).

    A diagnostic, never a verdict input: it lets an evaluation check, pair by
    pair, that the setting its run manifest declares is the one each pair
    actually had.  ``stages`` are the requested ones; ``effective_stages`` are
    those that can run, which needs an analysis deadline (the replay runs only
    inside it: ``authority.decision.conditional_lane._concrete_lane_budget``).
    Whether a stage then did run for this pair (only an unconditional UNKNOWN
    pair with witnesses reaches it) is recorded by the stage itself.
    """

    stages = [STAGE_WITNESS_REPLAY] if options is not None else []
    deadline = (
        float(analysis_deadline_seconds)
        if isinstance(analysis_deadline_seconds, (int, float))
        and not isinstance(analysis_deadline_seconds, bool)
        else None
    )
    if not stages:
        inactive = INACTIVE_NOT_REQUESTED
    elif deadline is None:
        inactive = INACTIVE_NO_ANALYSIS_DEADLINE
    else:
        inactive = None
    return {
        "schema": CONCRETE_SETTING_SCHEMA,
        "stages": stages,
        "effective_stages": [] if inactive is not None else list(stages),
        "inactive_reason": inactive,
        "budget_seconds": None if options is None else float(options.budget_seconds),
        "run_time_limit_seconds": None if options is None else float(options.run_time_limit_seconds),
        "step_limit": None if options is None else int(options.step_limit),
        "analysis_deadline_seconds": deadline,
    }


def _entry(analysis: Any) -> Optional[int]:
    """The function's entry offset, from the analysis' typed function reference."""
    offset = getattr(getattr(analysis, "function_ref", None), "entry_offset", None)
    return offset if type(offset) is int else None


#: The producer site of the side facts (the one module that reads an analysis for
#: the concrete proof; Issue #325).
SIDE_FACTS_PRODUCER_SITE = "checker.concrete_replay.concrete_side_facts"
#: Why the side facts' provenance is unrecorded: the analysis may come from a
#: type-hypothesis re-analysis phase, and which one is not recorded yet (E3).
SIDE_FACTS_UNRECORDED_REASON = "analysis_phase_and_type_hypothesis_not_recorded"


def concrete_side_facts(analysis: Any, side: FactSide) -> ConcreteSideFacts:
    """The facts the concrete proof reads of one side's analysis, as fact handles.

    This is the only place the concrete proof's inputs touch an analysis
    object.  The values are what ``proof.concrete_counterexample`` used to read
    directly (the parameter records, the return storage descriptor and the
    return's pointer class).  Their provenance is **unrecorded**: the analysis
    may be a type-hypothesis re-analysis whose phase is not recorded, so the
    evidence relies on every fact until the phase is recorded (fail-closed).
    """

    provenance = FactProvenance.unrecorded(
        producer_site=SIDE_FACTS_PRODUCER_SITE, reason=SIDE_FACTS_UNRECORDED_REASON,
    )
    facts = getattr(analysis, "return_abi_facts", None) or {}
    descriptor = facts.get("return_storage_descriptor") or None
    is_pointer = bool(is_pointer_data_type(
        getattr(analysis, "return_type_obj", None), getattr(analysis, "return_type", None)
    ))
    return ConcreteSideFacts(
        parameters=FactHandle(
            FactKind.PARAMETER_STORAGE, FactTarget(side, FactSlot.PARAMETERS),
            provenance=provenance, value=getattr(analysis, "parameters", None) or (),
        ),
        return_location=FactHandle(
            FactKind.RETURN_LOCATION, FactTarget(side, FactSlot.RETURN),
            provenance=provenance, value=descriptor,
        ),
        return_value_class=FactHandle(
            FactKind.RETURN_VALUE_CLASS, FactTarget(side, FactSlot.RETURN),
            provenance=provenance, value={"is_pointer": is_pointer},
        ),
    )


def open_concrete_subjects(
    programs: Tuple[Any, Any],
    analyses: Tuple[Any, Any],
    options: ConcreteReplayOptions,
) -> Tuple[Union[ConcreteSubject, str], Union[ConcreteSubject, str]]:
    """One ``ConcreteSubject`` per side, or the reason the concrete layer
    refuses that side (an unmodelled program, a calling convention other than
    the ABI model's, no function at the entry)."""
    from scripts.function_tracer_pcode.ghidra.concrete_executor import (
        ExecutorRefusal,
        open_executor,
    )

    subjects = []
    for program, analysis, side in zip(programs, analyses, (FactSide.LEFT, FactSide.RIGHT)):
        entry = _entry(analysis)
        executor = open_executor(program, time_limit_seconds=options.run_time_limit_seconds)
        if entry is None:
            subjects.append("ENTRY_UNKNOWN")
            continue
        if isinstance(executor, ExecutorRefusal):
            subjects.append(f"{executor.reason.value}:{executor.detail}"[:200])
            continue
        abi = executor.function_abi(entry)
        if isinstance(abi, ExecutorRefusal):
            subjects.append(f"{abi.reason.value}:{abi.detail}"[:200])
            continue
        subjects.append(ConcreteSubject(
            executor, abi, entry, executor.register_location, executor.program_facts,
            concrete_side_facts(analysis, side),
        ))
    return subjects[0], subjects[1]


def _impl_concrete_replay_subjects(self, analysis1: Any, analysis2: Any):
    """The checker's concrete subjects for the pair it is checking, or ``None``
    when the replay is off or the checker holds no programs."""
    options = getattr(self, "concrete_replay", None)
    programs = getattr(self, "_active_programs", None)
    if options is None or programs is None:
        return None
    return open_concrete_subjects(programs, (analysis1, analysis2), options)

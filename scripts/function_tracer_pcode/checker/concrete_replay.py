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
from typing import Any, Optional, Tuple, Union

from scripts.function_tracer_pcode.proof.concrete_counterexample import ConcreteSubject


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


def _entry(analysis: Any) -> Optional[int]:
    """The function's entry offset, from the analysis' typed function reference."""
    offset = getattr(getattr(analysis, "function_ref", None), "entry_offset", None)
    return offset if type(offset) is int else None


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
    for program, analysis in zip(programs, analyses):
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
        subjects.append(ConcreteSubject(executor, abi, entry, executor.register_location, executor.program_facts))
    return subjects[0], subjects[1]


def _impl_concrete_replay_subjects(self, analysis1: Any, analysis2: Any):
    """The checker's concrete subjects for the pair it is checking, or ``None``
    when the replay is off or the checker holds no programs."""
    options = getattr(self, "concrete_replay", None)
    programs = getattr(self, "_active_programs", None)
    if options is None or programs is None:
        return None
    return open_concrete_subjects(programs, (analysis1, analysis2), options)

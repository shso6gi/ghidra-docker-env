# -*- coding: utf-8 -*-
"""The concrete executor contract: entry state, request, result.

An executor runs one function of one binary from a fully specified entry
state and reports how the run ended, the values of the registers it was asked
to observe (with how many of their low-order bytes are defined at return), and
every *hazard* it noticed.  This module owns the contract
only; an implementation lives with the runtime it drives (the Ghidra P-code
emulator), and a recorded implementation can replay stored results.

Entry state.  Only what the ABI defines at a call is defined: the stack
pointer, the return address, callee-saved registers (they hold the caller's
values, whatever those are), ABI control registers, and the argument
registers that were bound.  Everything else -- unbound argument registers,
scratch registers, memory outside the loaded image and outside what the run
itself wrote -- is undefined, and a read of it is a hazard, not a zero.

A result is a set of facts about one run.  It is never a verdict: whether two
runs establish a difference is decided by ``concrete.comparison``, and what a
pair's outcome is stays with the authority layer.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Mapping, Optional, Protocol, Tuple

from scripts.function_tracer_pcode.concrete.abi import AbiModel
from scripts.function_tracer_pcode.concrete.input_surface import RegisterImage
from scripts.function_tracer_pcode.concrete.observation import ObservedRegister


# Addresses of the synthetic call frame.  They are outside any loaded image;
# the return address is a sentinel the executor stops at.
DEFAULT_STACK_POINTER = 0x6FF00000
DEFAULT_RETURN_ADDRESS = 0x7FF00000
DEFAULT_STEP_LIMIT = 1_000_000


def _callee_saved_value(index: int) -> int:
    # Arbitrary, distinct, recognisable: a callee may save and restore these
    # but a result must not depend on them.
    return 0x5A5A000000000000 + 0x1111 * (index + 1)


@dataclass(frozen=True)
class EntryState:
    """Register values defined at function entry (register name -> value)."""

    registers: Tuple[Tuple[str, int], ...]
    stack_pointer: int
    return_address: int

    def register_map(self) -> Mapping[str, int]:
        return dict(self.registers)


def build_entry_state(
    abi: AbiModel,
    entry_address: int,
    argument_images: Tuple[RegisterImage, ...],
    stack_pointer: int = DEFAULT_STACK_POINTER,
    return_address: int = DEFAULT_RETURN_ADDRESS,
) -> EntryState:
    registers = {}
    registers[abi.stack_pointer] = stack_pointer
    registers[abi.return_address_register] = return_address
    if abi.entry_address_register is not None:
        registers[abi.entry_address_register] = entry_address
    for index, name in enumerate(abi.callee_saved_registers):
        registers[name] = _callee_saved_value(index)
    for name, value in abi.control_register_defaults:
        registers[name] = value
    for image in argument_images:
        if image.register in registers:
            raise ValueError(f"argument register collides with ABI state: {image.register}")
        registers[image.register] = image.value
    return EntryState(tuple(sorted(registers.items())), stack_pointer, return_address)


@dataclass(frozen=True)
class ExecutionRequest:
    entry_address: int
    entry_state: EntryState
    observe_registers: Tuple[str, ...]
    step_limit: int = DEFAULT_STEP_LIMIT


class Termination(str, Enum):
    """How a run ended.  Only ``RETURNED`` is a completed call."""

    RETURNED = "RETURNED"
    STEP_LIMIT = "STEP_LIMIT"
    # Control left the program's own code (external call, computed jump out).
    LEFT_PROGRAM_CODE = "LEFT_PROGRAM_CODE"
    FAULT = "FAULT"
    UNSUPPORTED_OPERATION = "UNSUPPORTED_OPERATION"
    EXECUTOR_ERROR = "EXECUTOR_ERROR"


class HazardKind(str, Enum):
    """Something a run did that makes its result unusable as evidence.

    A kind is added by the change that first detects it; the comparison
    refuses a run with any hazard, so a new kind can only remove evidence.
    """

    UNDEFINED_REGISTER_READ = "UNDEFINED_REGISTER_READ"
    UNDEFINED_MEMORY_READ = "UNDEFINED_MEMORY_READ"
    STACK_POINTER_NOT_RESTORED = "STACK_POINTER_NOT_RESTORED"
    # A floating-point operation consumed or produced a NaN.  The executor's
    # arithmetic is not guaranteed to preserve NaN payloads or signalling
    # state, so nothing computed after it is known to match the machine.
    FP_NAN_OPERAND = "FP_NAN_OPERAND"
    # The run executed floating-point arithmetic whose result a conforming
    # compiler may round differently in another build of the same source: a
    # fused multiply-add, or a multiplication whose result feeds an addition
    # or subtraction (which another build may fuse).  A difference after it
    # can be a difference of rounding, not of the function -- in the returned
    # floating-point value or in anything derived from it.
    FP_ROUNDING_SENSITIVE = "FP_ROUNDING_SENSITIVE"


@dataclass(frozen=True)
class Hazard:
    kind: HazardKind
    # Location of the first occurrence, for diagnosis only.
    detail: str = ""


@dataclass(frozen=True)
class ExecutionResult:
    termination: Termination
    steps: int
    # (register name, value at return with its defined low-order bytes)
    observed_registers: Tuple[Tuple[str, ObservedRegister], ...] = ()
    hazards: Tuple[Hazard, ...] = ()
    # The executor examined every floating-point operation of the run for the
    # FP_* hazards.  A result that does not say so is not compared: the
    # absence of an FP hazard means something only when they were looked for.
    fp_operations_tracked: bool = False
    detail: str = ""

    def observed(self, register: str) -> Optional[ObservedRegister]:
        for name, value in self.observed_registers:
            if name == register:
                return value
        return None

    def hazard_kinds(self) -> Tuple[HazardKind, ...]:
        return tuple(sorted({hazard.kind for hazard in self.hazards}, key=lambda k: k.value))


class ConcreteExecutor(Protocol):
    """Runs one function of the program this executor was created for."""

    def execute(self, request: ExecutionRequest) -> ExecutionResult:
        ...

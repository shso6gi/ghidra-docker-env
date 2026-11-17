# -*- coding: utf-8 -*-
"""The concrete executor contract: entry state, request, result.

An executor runs one function of one binary from a fully specified entry
state and reports how the run ended, the values of the registers it was asked
to observe (with how many of their low-order bytes are defined at return), and
every *hazard* it noticed.  This module owns the contract only.  The
implementation lives with the runtime it drives
(``ghidra.concrete_executor.PcodeEmulatorExecutor``); the facts of a run are
derived from its events by ``concrete.run_observer``, and
``concrete.recording.RecordedExecutor`` replays recorded runs through that
same observer.

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
    """Register values defined at function entry (register name -> value).

    ``defined_bytes`` lists the registers of which only the low-order bytes are
    defined (register name -> byte count): an AArch64 floating-point argument
    is a 16-byte ``v`` register value although Ghidra's base register ``z`` is
    wider.  A register not listed is defined in full.
    """

    registers: Tuple[Tuple[str, int], ...]
    stack_pointer: int
    return_address: int
    defined_bytes: Tuple[Tuple[str, int], ...] = ()

    def register_map(self) -> Mapping[str, int]:
        return dict(self.registers)

    def defined_byte_count(self, register: str) -> Optional[int]:
        """Low-order bytes of ``register`` defined at entry; ``None`` = all."""
        return dict(self.defined_bytes).get(register)


def build_entry_state(
    abi: AbiModel,
    entry_address: int,
    argument_images: Tuple[RegisterImage, ...],
    stack_pointer: int = DEFAULT_STACK_POINTER,
    return_address: int = DEFAULT_RETURN_ADDRESS,
) -> EntryState:
    registers = {}
    defined_bytes = {}
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
        defined_bytes[image.register] = image.register_bytes
    return EntryState(
        tuple(sorted(registers.items())),
        stack_pointer,
        return_address,
        tuple(sorted(defined_bytes.items())),
    )


@dataclass(frozen=True)
class ExecutionRequest:
    entry_address: int
    entry_state: EntryState
    observe_registers: Tuple[str, ...]
    step_limit: int = DEFAULT_STEP_LIMIT


class Termination(str, Enum):
    """How a run ended.  Only ``RETURNED`` is a completed call."""

    RETURNED = "RETURNED"
    # The instruction budget of the request (``ExecutionRequest.step_limit``).
    STEP_LIMIT = "STEP_LIMIT"
    # The executor's wall-clock budget.
    TIME_LIMIT = "TIME_LIMIT"
    # The executor's budget for memory the run writes (runaway recursion or
    # writes would otherwise exhaust the executor's own memory).
    RESOURCE_LIMIT = "RESOURCE_LIMIT"
    # Control left the program's own code (external call, computed jump out).
    LEFT_PROGRAM_CODE = "LEFT_PROGRAM_CODE"
    # The machine semantics stopped: an operation without a defined result
    # (integer division by zero), an undecodable instruction, an emulator fault.
    FAULT = "FAULT"
    # An operation the executor does not execute (a P-code user operation).
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
    # The emulator's floating-point result differs from the IEEE 754 result of
    # the same operands (the emulator, not the machine, is in doubt).
    FP_EMULATION_MISMATCH = "FP_EMULATION_MISMATCH"
    # A floating-point value converted to an integer it does not fit (NaN,
    # infinity, out of range): undefined in C (6.3.1.4).
    FP_TO_INTEGER_OUT_OF_RANGE = "FP_TO_INTEGER_OUT_OF_RANGE"
    # The run used the result of an operation whose signed reading
    # overflowed (``IntegerOverflow.VALUE_USED``): the
    # binary cannot exclude that the source had a signed overflow, which C
    # leaves undefined (#314).  Also: a value computed through such an
    # overflow was used where its wrapped and its exact value differ.
    SIGNED_OVERFLOW = "SIGNED_OVERFLOW"
    # An integer division by zero (which some instructions define and C does
    # not) or of the most negative value by -1.
    INTEGER_DIVISION_UNDEFINED = "INTEGER_DIVISION_UNDEFINED"
    # A shift whose amount the instruction reduced modulo the width: C leaves
    # a shift by the width or more undefined.
    SHIFT_COUNT_OUT_OF_RANGE = "SHIFT_COUNT_OUT_OF_RANGE"


@dataclass(frozen=True)
class Hazard:
    kind: HazardKind
    # Location of the first occurrence, for diagnosis only.
    detail: str = ""


class OverflowDisposition(Enum):
    """What became of the result of an operation whose signed reading overflowed."""

    # The value was never used: it was overwritten, or only its own
    # instruction's condition flags were taken from it (a compare).
    VALUE_NOT_USED = "VALUE_NOT_USED"
    # The value was otherwise unused and still in an observed register at
    # return: that register is not evidence (``ObservedRegister.unreliable``),
    # the run is (the function may return another register).
    VALUE_RETURNED = "VALUE_RETURNED"
    # The value was used (an operand, a store, an address, a branch, the
    # return value): the binary cannot show that the operation was not a C
    # signed operation, so the run may have executed undefined behaviour.
    VALUE_USED = "VALUE_USED"


@dataclass(frozen=True)
class IntegerOverflow:
    """One operation of the run whose signed result did not fit (#314).

    The occurrence, kept apart from what it means for the evidence: a run
    hazard (``SIGNED_OVERFLOW``) follows from ``VALUE_USED`` only, and whether
    the observed value would agree with an exact computation is reported on
    the observed register (``ObservedRegister.reliable_low_bytes``).
    """

    address: int
    operation: str
    width: int
    disposition: OverflowDisposition
    # dynamic executions of this operation that overflowed
    count: int = 1
    # What used the value: the P-code operations, and ``STORE`` / ``ADDRESS``
    # / ``PARTIAL_OVERWRITE``.  Recorded for later stages; no use clears the
    # hazard.  An unsigned comparison alone (``INT_LESSEQUAL``: compilers
    # compile ``lo <= x && x <= hi`` to ``(unsigned)(x - lo) <= hi - lo``)
    # is also what a source with a signed overflow compiles to.
    uses: Tuple[str, ...] = ()


@dataclass(frozen=True)
class ExecutionResult:
    termination: Termination
    steps: int
    # (register name, value at return with its defined low-order bytes)
    observed_registers: Tuple[Tuple[str, ObservedRegister], ...] = ()
    hazards: Tuple[Hazard, ...] = ()
    # The executor examined every floating-point operation of the run with
    # its operand values (``concrete.value_monitor``: rounding alternatives,
    # NaN, the emulator's own results).  A result that does not say so is not
    # compared: the absence of an FP hazard means something only when they
    # were looked for.
    fp_operations_tracked: bool = False
    # The same for integer operations whose result C leaves undefined on some
    # inputs (signed overflow, division, shift counts; #314).  Two builds of one
    # source may return different values on such an input, so a run that was
    # not examined for them is not compared either.
    integer_ub_operations_tracked: bool = False
    # Address ranges (start, byte count) of writable, initialized program data
    # (global variables, the GOT) the run read before writing them: the run
    # depends on the program's state at start, which is a fact about the run
    # and not a hazard.
    writable_image_reads: Tuple[Tuple[int, int], ...] = ()
    # How many P-code operations of each kind the run executed (diagnosis and
    # the measurements of the monitors).
    operation_counts: Tuple[Tuple[str, int], ...] = ()
    # What the monitors saw, by event (``signed_overflow_INT_ADD``,
    # ``fp_rounding_alternatives``, ``fp_nan``, ...): diagnosis and measurement
    # only; nothing reads it to decide.
    monitor_events: Tuple[Tuple[str, int], ...] = ()
    # Every operation whose signed result overflowed, by address (#314).
    integer_overflows: Tuple[IntegerOverflow, ...] = ()
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

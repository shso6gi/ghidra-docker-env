# -*- coding: utf-8 -*-
"""What one concrete run did, from the stream of its execution events.

An executor drives a machine (the Ghidra P-code emulator) and reports, in
order, what happened: an instruction is about to execute, its P-code, which
P-code operation runs, the address of each load and store, each read of a
location that holds no value, how the executor itself stopped, and the
register values at return.  ``RunObserver`` turns that stream into an
``ExecutionResult``.  It is the only place the facts of a run are derived:

* how the run ended (``Termination``) and after how many instructions;
* the hazards (reads of undefined registers or memory, an unrestored stack
  pointer);
* which observed register bytes are defined at return;
* the floating-point format of an observed value (``value_format``), from the
  operation that produced it (below);
* the doubts of the integer-UB and floating-point monitors
  (``concrete.value_monitor``): hazards where they reached the control flow,
  and the reliable low-order bytes of each observed register;
* whether those monitors saw every operand value they needed
  (``fp_operations_tracked``, ``integer_ub_operations_tracked``);
* user operations: run only when ``concrete.userops`` establishes their
  meaning (the observer computes the value the executor writes);
* writable program data the run read before writing it.

Values.  The observer asks, per operation, for the operand values it needs
(``value_request``) and the executor supplies them with the operation
(``op(index, values)``) and, when asked, the operation's result
(``op_output``).  The same observer consumes a live run and a recorded one
(``concrete.recording``), so a recorded run replays through production code;
a recording without the values (schema v1) replays as unmonitored.

Undefined values.  The emulator itself tracks which bytes hold a value (the
entry state, the loaded program image, everything the run wrote) and reports
a read of any other byte.  Reads by the instruction decoder (which looks a few
bytes past the end of a code block) are not reads of the program and are
ignored; every other one is a hazard.

Format evidence.  Every byte of a register, temporary or memory location
carries a tag ``(producer, format, significance)`` when it is byte
``significance`` of a value produced by a scalar floating-point operation of
4 or 8 bytes.  Tags move only with exact copies -- ``COPY``, the low part of
``INT_ZEXT`` and ``SUBPIECE``, and ``LOAD``/``STORE`` -- and every other
operation clears the tags of what it writes: a constant written to a
floating-point register, a value assembled by ``PIECE`` (a vector), a value
computed by integer operations.  At return a register's value has a format
only when its low-order 4 or 8 bytes are exactly the bytes of one such value
in order.  Nothing is inferred from the bits themselves.

Memory at start.  The loaded image is defined; so is memory the ELF file
defines as zero at program start (``RunSetup.zero_initialized_ranges``,
``concrete.elf_sections``), which is writable program data like ``.data``.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple

from scripts.function_tracer_pcode.concrete.executor import (
    ExecutionRequest,
    ExecutionResult,
    Hazard,
    HazardKind,
    Termination,
)
from scripts.function_tracer_pcode.concrete.observation import FpFormat, ObservedRegister
from scripts.function_tracer_pcode.concrete.userops import UseropEffect
from scripts.function_tracer_pcode.concrete.value_monitor import (
    FP_OPS as FP_MONITORED_OPERATIONS,
    INTEGER_VALUE_OPS,
    NO_REQUEST,
    ValueMonitor,
    ValueRequest,
)

REGISTER_SPACE = "register"
UNIQUE_SPACE = "unique"
CONST_SPACE = "const"
PAGE_BYTES = 4096
DEFAULT_WRITE_PAGE_LIMIT = 4096   # 16 MiB written by one run

# Operations that produce a floating-point value of their output's size.
FP_VALUE_OPERATIONS = frozenset({
    "FLOAT_ADD", "FLOAT_SUB", "FLOAT_MULT", "FLOAT_DIV", "FLOAT_NEG", "FLOAT_ABS",
    "FLOAT_SQRT", "INT2FLOAT", "FLOAT2FLOAT", "CEIL", "FLOOR", "ROUND",
})
# Every operation the floating-point monitor examines with its operand values.
FP_OPERATIONS = FP_MONITORED_OPERATIONS
# The integer operations whose operand values the integer-UB monitor always
# needs (others only when an operand carries a monitor fact).
INTEGER_UB_OPERATIONS = INTEGER_VALUE_OPS
USER_OPERATION = "CALLOTHER"

_FORMAT_OF_SIZE = {4: FpFormat.BINARY32, 8: FpFormat.BINARY64}


@dataclass(frozen=True)
class Varnode:
    space: str
    offset: int
    size: int


@dataclass(frozen=True)
class OpDescriptor:
    """One P-code operation of an instruction, without values."""

    mnemonic: str
    output: Optional[Varnode]
    inputs: Tuple[Varnode, ...]
    # The user operation's name, for ``CALLOTHER``.
    userop: Optional[str] = None


@dataclass(frozen=True)
class RegisterFact:
    """Where a named register lives in the register space."""

    name: str
    offset: int
    size: int


@dataclass(frozen=True)
class RunSetup:
    """Facts of the program an observer needs, independent of one request.

    Ranges are ``(start, end)`` with ``end`` exclusive, in the memory space.
    ``external_entries`` maps an address in the program's code that stands for
    an external function (an import thunk) to that function's name.
    """

    big_endian: bool
    memory_space: str
    registers: Tuple[RegisterFact, ...]
    stack_pointer: str
    code_ranges: Tuple[Tuple[int, int], ...]
    external_entries: Tuple[Tuple[int, str], ...]
    writable_image_ranges: Tuple[Tuple[int, int], ...]
    write_page_limit: int = DEFAULT_WRITE_PAGE_LIMIT
    # Ghidra's processor name (``AARCH64``, ``MIPS``): selects user operations.
    processor: str = ""
    # Uninitialized blocks the ELF file defines as zero at program start; the
    # executor zero-fills them and they count as writable program data.
    zero_initialized_ranges: Tuple[Tuple[int, int], ...] = ()
    # ``AbiModel.c_int_bytes``; 0 when unknown (every width may be ``int``).
    c_int_bytes: int = 0

    def register(self, name: str) -> Optional[RegisterFact]:
        for fact in self.registers:
            if fact.name == name:
                return fact
        return None


def _in_ranges(address: int, ranges) -> bool:
    return any(start <= address < end for start, end in ranges)


def _merge(ranges: List[Tuple[int, int]]) -> Tuple[Tuple[int, int], ...]:
    """(start, byte count) ranges merged where they touch or overlap."""
    merged: List[List[int]] = []
    for start, end in sorted((start, start + count) for start, count in ranges):
        if merged and start <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], end)
        else:
            merged.append([start, end])
    return tuple((start, end - start) for start, end in merged)


class RunObserver:
    """Derives an ``ExecutionResult`` from the events of one run.

    The executor calls the event methods in the order things happen.  Methods
    returning a ``Termination`` ask the executor to stop the run before doing
    anything further; the executor then calls nothing but ``returned`` (only
    after ``RETURNED``) and ``result``.
    """

    def __init__(self, setup: RunSetup, request: ExecutionRequest):
        self._setup = setup
        self._request = request
        self._big_endian = setup.big_endian
        self._externals = dict(setup.external_entries)
        self._steps = 0
        self._termination: Optional[Termination] = None
        self._detail = ""
        self._hazards: Dict[HazardKind, Hazard] = {}
        self._counts: Dict[str, int] = {}
        self._decoded: Dict[int, Tuple[OpDescriptor, ...]] = {}
        self._address: Optional[int] = None
        self._pending: Optional[OpDescriptor] = None
        self._tags: Dict[Tuple[str, int], Tuple[int, FpFormat, int]] = {}
        self._producers = 0
        self._defined_registers: Set[int] = set()
        self._written_pages: Set[int] = set()
        self._written_writable: Set[int] = set()
        self._writable_reads: Set[int] = set()
        self._observed: Tuple[Tuple[str, ObservedRegister], ...] = ()
        self._writable = tuple(setup.writable_image_ranges) + tuple(setup.zero_initialized_ranges)
        self._monitor = ValueMonitor(setup.big_endian, setup.processor, setup.c_int_bytes)
        self._monitor_step = -1
        self._userop_value: Optional[int] = None
        for name, _ in request.entry_state.registers:
            fact = setup.register(name)
            if fact is None:
                continue
            count = request.entry_state.defined_byte_count(name) or fact.size
            count = min(count, fact.size)
            for significance in range(count):
                self._defined_registers.add(self._byte_address(fact.offset, fact.size, significance))

    # ------------------------------------------------------------ helpers

    def _byte_address(self, offset: int, size: int, significance: int) -> int:
        return offset + size - 1 - significance if self._big_endian else offset + significance

    def _stop(self, termination: Termination, detail: str) -> Termination:
        if self._termination is None:
            self._termination = termination
            self._detail = detail
        return self._termination

    def _hazard(self, kind: HazardKind, detail: str) -> None:
        self._hazards.setdefault(kind, Hazard(kind, detail))

    def _where(self) -> str:
        return "" if self._address is None else f" at {self._address:#x}"

    @property
    def stopped(self) -> Optional[Termination]:
        return self._termination

    # ------------------------------------------------------------- events

    def _check_no_pending(self) -> Optional[Termination]:
        if self._pending is not None:
            return self._stop(
                Termination.EXECUTOR_ERROR,
                f"{self._pending.mnemonic} without its address{self._where()}",
            )
        return None

    def instruction(self, address: int) -> Optional[Termination]:
        """The next instruction to execute is at ``address``."""
        if self._termination is not None:
            return self._termination
        if self._check_no_pending() is not None:
            return self._termination
        if address == self._request.entry_state.return_address:
            return self._stop(Termination.RETURNED, "")
        if self._steps >= self._request.step_limit:
            return self._stop(Termination.STEP_LIMIT, f"{self._steps} instructions")
        if address in self._externals:
            return self._stop(
                Termination.LEFT_PROGRAM_CODE, f"external call {self._externals[address]} at {address:#x}"
            )
        if not _in_ranges(address, self._setup.code_ranges):
            return self._stop(Termination.LEFT_PROGRAM_CODE, f"outside program code at {address:#x}")
        self._steps += 1
        self._address = address
        self._pending = None
        return None

    def decoded(self, address: int, ops: Tuple[OpDescriptor, ...]) -> None:
        """The P-code of the instruction at ``address`` (reported once per address)."""
        self._decoded[address] = tuple(ops)

    def _current_op(self, index: int) -> Optional[OpDescriptor]:
        ops = self._decoded.get(self._address)
        if ops is None or not 0 <= index < len(ops):
            return None
        if self._monitor_step != self._steps:
            self._monitor_step = self._steps
            self._monitor.begin_instruction(self._steps, self._address, ops)
        return ops[index]

    def value_request(self, index: int) -> ValueRequest:
        """Which values of operation ``index`` the monitors need (inputs, result)."""
        if self._termination is not None:
            return NO_REQUEST
        op = self._current_op(index)
        if op is None:
            return NO_REQUEST
        return self._monitor.value_request(index, op)

    def op(self, index: int, values: Optional[Tuple[int, ...]] = None) -> Optional[Termination]:
        """Operation ``index`` of the current instruction is about to run.

        ``values`` are the operation's input values (unsigned, in input order,
        constants included) when the executor supplies them.
        """
        if self._termination is not None:
            return self._termination
        if self._check_no_pending() is not None:
            return self._termination
        op = self._current_op(index)
        if op is None:
            return self._stop(Termination.EXECUTOR_ERROR, f"no P-code for operation {index}{self._where()}")
        self._counts[op.mnemonic] = self._counts.get(op.mnemonic, 0) + 1
        self._userop_value = None
        outcome = self._monitor.execute(index, op, values, self._where())
        if op.mnemonic == USER_OPERATION:
            if outcome is None or outcome.effect is UseropEffect.UNSUPPORTED:
                detail = "" if outcome is None else f": {outcome.detail}"
                return self._stop(Termination.UNSUPPORTED_OPERATION, f"user operation{self._where()}{detail}")
            if outcome.effect is UseropEffect.TRAP:
                return self._stop(Termination.FAULT, f"{op.userop}{self._where()}")
            if op.output is not None:
                if outcome.value is None:
                    return self._stop(
                        Termination.EXECUTOR_ERROR, f"{op.userop} without its operand values{self._where()}"
                    )
                self._userop_value = outcome.value
                fmt = _FORMAT_OF_SIZE.get(outcome.fp_size) if outcome.fp_size else None
                if fmt is not None:
                    self._producers += 1
                    for k in range(op.output.size):
                        self._set_tag(op.output, k, (self._producers, fmt, k))
                else:
                    for k in range(op.output.size):
                        self._set_tag(op.output, k, None)
                self._mark_output_defined(op.output)
            return None
        if op.mnemonic in ("LOAD", "STORE"):
            # Applied when the executor reports the address.
            self._pending = op
            return None
        self._apply(op)
        return None

    def op_output(self, value: int) -> None:
        """The value the last operation wrote (when ``value_request`` asked for it)."""
        if self._termination is not None:
            return
        self._monitor.output(value)

    def userop_value(self) -> Optional[int]:
        """The value the executor writes for the user operation that is running."""
        return self._userop_value

    def load(self, space: str, address: int, size: int) -> Optional[Termination]:
        """The pending ``LOAD`` reads ``size`` bytes at ``address`` of ``space``."""
        if self._termination is not None:
            return self._termination
        op = self._pending
        self._pending = None
        if op is None or op.mnemonic != "LOAD" or op.output is None or op.output.size != size:
            return self._stop(Termination.EXECUTOR_ERROR, f"load without its LOAD operation{self._where()}")
        if space == self._setup.memory_space:
            self._note_writable_read(address, size)
        self._monitor.address(op, self._where(), address)
        self._monitor.load(op, space, address, size)
        for significance in range(size):
            tag = self._tags.get((space, self._byte_address(address, size, significance)))
            self._set_tag(op.output, significance, tag)
        self._mark_output_defined(op.output)
        return None

    def store(self, space: str, address: int, size: int) -> Optional[Termination]:
        """The pending ``STORE`` writes ``size`` bytes at ``address`` of ``space``."""
        if self._termination is not None:
            return self._termination
        op = self._pending
        self._pending = None
        if op is None or op.mnemonic != "STORE" or len(op.inputs) < 3 or op.inputs[2].size != size:
            return self._stop(Termination.EXECUTOR_ERROR, f"store without its STORE operation{self._where()}")
        end = address + size
        if space == self._setup.memory_space:
            if any(start < end and address < stop for start, stop in self._setup.code_ranges):
                return self._stop(Termination.UNSUPPORTED_OPERATION, f"write to program code{self._where()}")
            for page in range(address // PAGE_BYTES, (end - 1) // PAGE_BYTES + 1):
                self._written_pages.add(page)
            if len(self._written_pages) > self._setup.write_page_limit:
                return self._stop(
                    Termination.RESOURCE_LIMIT, f"more than {self._setup.write_page_limit} pages written"
                )
            for byte in range(address, end):
                if _in_ranges(byte, self._writable):
                    self._written_writable.add(byte)
        self._monitor.address(op, self._where(), address)
        self._monitor.store(op, space, address, size, self._where())
        value = op.inputs[2]
        for significance in range(size):
            tag = self._tags.get((value.space, self._byte_address(value.offset, value.size, significance)))
            key = (space, self._byte_address(address, size, significance))
            if tag is None:
                self._tags.pop(key, None)
            else:
                self._tags[key] = tag
        return None

    def uninitialized_read(self, space: str, offset: int, size: int, decoding: bool) -> None:
        if decoding or self._termination is not None:
            return
        kind = (
            HazardKind.UNDEFINED_REGISTER_READ
            if space in (REGISTER_SPACE, UNIQUE_SPACE)
            else HazardKind.UNDEFINED_MEMORY_READ
        )
        self._hazard(kind, f"{space}:{offset:#x}:{size}{self._where()}")

    def stopped_by_executor(self, termination: str, detail: str) -> None:
        """The executor stopped the run (time budget, an emulator fault, its own error)."""
        self._stop(Termination(termination), detail)

    def returned(self, values: Tuple[Tuple[str, int], ...]) -> None:
        """Register values at return: the observed registers and the stack pointer."""
        if self._termination is not Termination.RETURNED:
            return
        by_name = dict(values)
        stack = by_name.get(self._setup.stack_pointer)
        if stack is None or stack != self._request.entry_state.stack_pointer:
            self._hazard(
                HazardKind.STACK_POINTER_NOT_RESTORED,
                f"{self._setup.stack_pointer}={stack if stack is None else hex(stack)}",
            )
        observed = []
        for name in self._request.observe_registers:
            fact = self._setup.register(name)
            if fact is None or name not in by_name:
                continue
            reliable, kinds = self._monitor.observe(fact.offset, fact.size, where=f" in {name} at return")
            observed.append((name, ObservedRegister(
                by_name[name], self._defined_low_bytes(fact), self._value_format(fact),
                reliable, tuple(kind.value for kind in kinds),
            )))
        self._observed = tuple(observed)

    # ------------------------------------------------------- the operations

    def _set_tag(self, varnode: Varnode, significance: int, tag) -> None:
        key = (varnode.space, self._byte_address(varnode.offset, varnode.size, significance))
        if tag is None:
            self._tags.pop(key, None)
        else:
            self._tags[key] = tag

    def _tag_of(self, varnode: Varnode, significance: int):
        if varnode.space == CONST_SPACE:
            return None
        return self._tags.get((varnode.space, self._byte_address(varnode.offset, varnode.size, significance)))

    def _mark_output_defined(self, output: Varnode) -> None:
        if output.space == REGISTER_SPACE:
            self._defined_registers.update(range(output.offset, output.offset + output.size))

    def _apply(self, op: OpDescriptor) -> None:
        output = op.output
        if output is None:
            return
        mnemonic = op.mnemonic
        tags = [None] * output.size
        if mnemonic in FP_VALUE_OPERATIONS and output.size in _FORMAT_OF_SIZE:
            self._producers += 1
            fmt = _FORMAT_OF_SIZE[output.size]
            tags = [(self._producers, fmt, k) for k in range(output.size)]
        elif mnemonic == "COPY" and op.inputs and op.inputs[0].size == output.size:
            tags = [self._tag_of(op.inputs[0], k) for k in range(output.size)]
        elif mnemonic == "INT_ZEXT" and op.inputs:
            source = op.inputs[0]
            tags = [self._tag_of(source, k) if k < source.size else None for k in range(output.size)]
        elif mnemonic == "SUBPIECE" and len(op.inputs) == 2 and op.inputs[1].space == CONST_SPACE:
            source, shift = op.inputs[0], op.inputs[1].offset
            tags = [
                self._tag_of(source, shift + k) if shift + k < source.size else None
                for k in range(output.size)
            ]
        for significance, tag in enumerate(tags):
            self._set_tag(output, significance, tag)
        self._mark_output_defined(output)

    def _note_writable_read(self, address: int, size: int) -> None:
        unwritten = [
            byte for byte in range(address, address + size)
            if _in_ranges(byte, self._writable)
            and byte not in self._written_writable
        ]
        self._writable_reads.update(unwritten)

    # --------------------------------------------------------- at return

    def _defined_low_bytes(self, fact: RegisterFact) -> int:
        count = 0
        while count < fact.size and self._byte_address(fact.offset, fact.size, count) in self._defined_registers:
            count += 1
        return count

    def _value_format(self, fact: RegisterFact) -> Optional[FpFormat]:
        reg = Varnode(REGISTER_SPACE, fact.offset, fact.size)
        first = self._tag_of(reg, 0)
        if first is None or first[2] != 0:
            return None
        producer, fmt = first[0], first[1]
        width = 4 if fmt is FpFormat.BINARY32 else 8
        if width > fact.size:
            return None
        for significance in range(width):
            if self._tag_of(reg, significance) != (producer, fmt, significance):
                return None
        return fmt

    # ------------------------------------------------------------- result

    def result(self) -> ExecutionResult:
        if self._termination is None:
            self._check_no_pending()
        termination = self._termination
        if termination is None:
            termination = Termination.EXECUTOR_ERROR
            self._detail = "the run ended without a termination"
        counts = self._counts
        for kind, detail in self._monitor.hazards:
            self._hazard(kind, detail)
        return ExecutionResult(
            termination=termination,
            steps=self._steps,
            observed_registers=self._observed if termination is Termination.RETURNED else (),
            hazards=tuple(self._hazards.values()),
            fp_operations_tracked=self._monitor.fp_complete,
            integer_ub_operations_tracked=self._monitor.integer_complete,
            writable_image_reads=_merge([(byte, 1) for byte in self._writable_reads]),
            operation_counts=tuple(sorted(counts.items())),
            monitor_events=tuple(sorted(self._monitor.counters.items())),
            integer_overflows=self._monitor.overflows(),
            detail=self._detail,
        )

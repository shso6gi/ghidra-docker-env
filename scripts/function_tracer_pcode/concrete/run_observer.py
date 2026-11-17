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
* whether the operations the hazard monitors need to examine ran
  (``fp_operations_tracked``, ``integer_ub_operations_tracked``);
* writable program data the run read before writing it.

The observer reads no values beyond the addresses of loads and stores and the
registers at return: it never decides anything from what a computation
produced.  The same observer consumes a live run and a recorded one
(``concrete.recording``), so a recorded run replays through production code.

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

Monitoring.  The NaN / rounding monitor (#317) and the integer-UB monitor
(#314) are not implemented yet.  A run is reported as examined for one of them
only when it executed none of the operations that monitor would have to look
at; any user operation counts against both, because its semantics are not
known here.
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
# Every operation the NaN / rounding monitor has to examine.
FP_OPERATIONS = FP_VALUE_OPERATIONS | frozenset({
    "FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL", "FLOAT_NAN", "TRUNC",
})
# Every operation the integer-UB monitor has to examine: the arithmetic C
# leaves undefined on some operands (overflow, division, shift counts).
INTEGER_UB_OPERATIONS = frozenset({
    "INT_ADD", "INT_SUB", "INT_MULT", "INT_2COMP", "INT_DIV", "INT_SDIV", "INT_REM",
    "INT_SREM", "INT_LEFT", "INT_RIGHT", "INT_SRIGHT",
})
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

    def op(self, index: int) -> Optional[Termination]:
        """Operation ``index`` of the current instruction is about to run."""
        if self._termination is not None:
            return self._termination
        if self._check_no_pending() is not None:
            return self._termination
        ops = self._decoded.get(self._address)
        if ops is None or not 0 <= index < len(ops):
            return self._stop(Termination.EXECUTOR_ERROR, f"no P-code for operation {index}{self._where()}")
        op = ops[index]
        self._counts[op.mnemonic] = self._counts.get(op.mnemonic, 0) + 1
        if op.mnemonic == USER_OPERATION:
            return self._stop(Termination.UNSUPPORTED_OPERATION, f"user operation{self._where()}")
        if op.mnemonic in ("LOAD", "STORE"):
            # Applied when the executor reports the address.
            self._pending = op
            return None
        self._apply(op)
        return None

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
                if _in_ranges(byte, self._setup.writable_image_ranges):
                    self._written_writable.add(byte)
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
            observed.append((name, ObservedRegister(
                by_name[name], self._defined_low_bytes(fact), self._value_format(fact)
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
            if _in_ranges(byte, self._setup.writable_image_ranges)
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
        fp_seen = any(name in counts for name in FP_OPERATIONS) or USER_OPERATION in counts
        ub_seen = any(name in counts for name in INTEGER_UB_OPERATIONS) or USER_OPERATION in counts
        return ExecutionResult(
            termination=termination,
            steps=self._steps,
            observed_registers=self._observed if termination is Termination.RETURNED else (),
            hazards=tuple(self._hazards.values()),
            fp_operations_tracked=not fp_seen,
            integer_ub_operations_tracked=not ub_seen,
            writable_image_reads=_merge([(byte, 1) for byte in self._writable_reads]),
            operation_counts=tuple(sorted(counts.items())),
            detail=self._detail,
        )

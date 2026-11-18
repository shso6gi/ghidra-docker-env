# -*- coding: utf-8 -*-
"""The concrete executor on Ghidra's P-code emulator (``PcodeEmulator``).

``PcodeEmulatorExecutor`` implements ``concrete.executor.ConcreteExecutor``
for one loaded program.  It is a thin driver: it opens the program's facts,
builds the emulator's entry state from the request, steps instruction by
instruction and forwards what the emulator reports -- each P-code operation,
each load and store address, each read of a location without a value -- to
``concrete.run_observer.RunObserver``, which derives every fact of the
result.  The driver never interprets a value.

Before anything runs, ``open_executor`` selects the program's ABI model
(``concrete.abi.select_abi``) and checks it against the program's own
compiler specification (``concrete.abi_conformance``); a program without a
model or with any disagreement is refused, and so is a function marked with
a calling convention other than the default.

Values.  For every P-code operation the observer names
(``RunObserver.value_request``), the driver reads the operation's input
values from the emulator's state before it runs and, when asked, the value
it wrote afterwards; the observer's monitors (``concrete.value_monitor``)
derive everything from them.  A user operation runs only when
``concrete.userops`` establishes its meaning; the driver writes the value the
observer computed (``handleMissingUserop``).

Initial memory.  The program's initialized blocks, and the uninitialized
blocks the ELF file defines as zero at program start (``.bss``; found in the
file's own section table by ``concrete.elf_sections``), zero-filled.  Every
other location starts undefined.

Isolation.  Every Java exception of the emulator becomes a result (``FAULT``
for the machine semantics, ``EXECUTOR_ERROR`` otherwise).  An error of the
executor's own Python code is not swallowed: it is recorded as an
``EXECUTOR_ERROR`` stop and then propagates, as a bug should.  A run is bounded by the request's instruction
budget, the executor's wall-clock budget and the observer's budget for
written memory.  A failure of the process itself (the JVM) is contained by
``ghidra.concrete_worker``, which runs executors in child processes.
"""

from __future__ import annotations

import sys
import time
from dataclasses import dataclass
from enum import Enum
from typing import Any, Dict, Optional, Tuple, Union

from scripts.function_tracer_pcode.concrete.abi import AbiModel, select_abi
from scripts.function_tracer_pcode.concrete.abi_conformance import (
    MIXED_PROBE,
    AbiConformance,
    CompilerSpecFacts,
    ReturnProbe,
    check_abi_conformance,
)
from scripts.function_tracer_pcode.concrete.abi import ArgClass
from scripts.function_tracer_pcode.concrete.executor import (
    ExecutionRequest,
    ExecutionResult,
    Termination,
)
from scripts.function_tracer_pcode.concrete.elf_sections import (
    MemoryBlockFact,
    parse_section_table,
    zero_initialized_blocks,
)
from scripts.function_tracer_pcode.concrete.recording import RecordingObserver, make_trace
from scripts.function_tracer_pcode.concrete.run_observer import (
    OpDescriptor,
    RegisterFact,
    RunObserver,
    RunSetup,
    Varnode,
)
from scripts.function_tracer_pcode.concrete.storage import StorageLocation

DEFAULT_TIME_LIMIT_SECONDS = 60.0
EXECUTOR_VERSION = "pcode-emulator-executor-v3"
# Zero-filling a larger block would cost more than any run needs; such a
# block stays undefined.
MAX_ZERO_FILL_BYTES = 64 << 20

_DIVISIONS = frozenset({"INT_DIV", "INT_SDIV", "INT_REM", "INT_SREM"})
# Exceptions of the emulator that are the machine semantics stopping, not a
# failure of the executor.
_FAULT_EXCEPTION_PREFIXES = ("ghidra.pcode.", "java.lang.ArithmeticException")


class ExecutorRefusalReason(str, Enum):
    COMPILER_SPEC_FACTS_UNAVAILABLE = "COMPILER_SPEC_FACTS_UNAVAILABLE"
    PROGRAM_NOT_MODELLED = "PROGRAM_NOT_MODELLED"
    ABI_DISAGREES_WITH_COMPILER_SPEC = "ABI_DISAGREES_WITH_COMPILER_SPEC"
    NO_FUNCTION_AT_ENTRY = "NO_FUNCTION_AT_ENTRY"
    FUNCTION_CONVENTION_NOT_DEFAULT = "FUNCTION_CONVENTION_NOT_DEFAULT"


@dataclass(frozen=True)
class ExecutorRefusal:
    reason: ExecutorRefusalReason
    detail: str = ""
    conformance: Optional[AbiConformance] = None
    facts: Optional[CompilerSpecFacts] = None


class _StopRun(Exception):
    """Raised inside an emulator callback after the observer stopped the run."""


# ------------------------------------------------------------ program facts

def _jclass(name: str):
    import jpype

    return jpype.JClass(name)


def _exact_register(language, address, size):
    """The register that is exactly ``size`` bytes at ``address``, or ``None``."""
    register = language.getRegister(address, size)
    if register is None or int(register.getNumBytes()) != size or not register.getAddress().equals(address):
        return None
    return register


def _location(language, storage) -> StorageLocation:
    """A ``StorageLocation`` of one Ghidra ``VariableStorage`` or ``Varnode``.

    ``register_name`` is set only when a register is exactly the piece; a
    piece inside a wider register (MIPS ``float`` in the low half of ``f12``)
    is located by its offset in the base register.
    """
    containing = None
    if hasattr(storage, "getVarnodes"):
        varnodes = list(storage.getVarnodes())
        if len(varnodes) != 1:
            return StorageLocation(False, None, None, 0, 0, int(storage.size()))
        varnode = varnodes[0]
        containing = storage.getRegister()
    else:
        varnode = storage
    address = varnode.getAddress()
    size = int(varnode.getSize())
    if not address.isRegisterAddress():
        return StorageLocation(False, None, None, 0, 0, size)
    exact = _exact_register(language, address, size)
    if containing is None:
        containing = exact if exact is not None else language.getRegister(address, size)
    if containing is None:
        return StorageLocation(False, None, None, 0, 0, size)
    base = containing.getBaseRegister()
    return StorageLocation(
        is_register=True,
        register_name=None if exact is None else str(exact.getName()),
        base_register_name=str(base.getName()),
        base_register_bytes=int(base.getNumBytes()),
        byte_offset_in_base=int(address.getOffset()) - int(base.getAddress().getOffset()),
        size_bytes=size,
    )


def compiler_spec_facts(program) -> CompilerSpecFacts:
    """Read ``CompilerSpecFacts`` from the program's own compiler specification."""
    data = "ghidra.program.model.data."
    long_type = _jclass(data + "LongLongDataType").dataType
    int_type = _jclass(data + "IntegerDataType").dataType
    char_type = _jclass(data + "CharDataType").dataType
    double_type = _jclass(data + "DoubleDataType").dataType
    float_type = _jclass(data + "FloatDataType").dataType
    language = program.getLanguage()
    spec = program.getCompilerSpec()
    model = spec.getDefaultCallingConvention()

    def storage(types):
        return [_location(language, s) for s in model.getStorageLocations(program, types, False)]

    probe_type = {
        (ArgClass.INT, 4): int_type,
        (ArgClass.FP, 8): double_type,
        (ArgClass.FP, 4): float_type,
    }
    int_arguments = storage([long_type] + [long_type] * 9)[1:]
    fp_arguments = storage([double_type] + [double_type] * 9)[1:]
    mixed = storage([int_type] + [probe_type[p] for p in MIXED_PROBE])[1:]
    returns = (
        (ReturnProbe.INT64, storage([long_type])[0]),
        (ReturnProbe.INT32, storage([int_type])[0]),
        (ReturnProbe.INT8, storage([char_type])[0]),
        (ReturnProbe.BINARY64, storage([double_type])[0]),
        (ReturnProbe.BINARY32, storage([float_type])[0]),
    )
    unaffected = tuple(_location(language, v) for v in model.getUnaffectedList())
    encoder = _jclass("ghidra.program.model.pcode.XmlEncode")()
    model.encode(encoder, spec.getPcodeInjectLibrary())
    return CompilerSpecFacts(
        language_id=str(program.getLanguageID()),
        compiler_spec_id=str(spec.getCompilerSpecID()),
        executable_format=str(program.getExecutableFormat()),
        default_prototype=str(model.getName()),
        stack_pointer=str(spec.getStackPointer().getName()),
        int_arguments=tuple(int_arguments[:9]),
        fp_arguments=tuple(fp_arguments[:9]),
        mixed_arguments=tuple(mixed),
        returns=returns,
        unaffected=unaffected,
        default_prototype_xml=str(encoder.toString()),
    )


def _int_of(data, big_endian: bool) -> int:
    raw = bytes(int(b) & 0xFF for b in data)
    return int.from_bytes(raw, "big" if big_endian else "little")


def _bytes_of(value: int, count: int, big_endian: bool):
    import jpype

    raw = (value & ((1 << (count * 8)) - 1)).to_bytes(count, "big" if big_endian else "little")
    return jpype.JArray(jpype.JByte)([b - 256 if b > 127 else b for b in raw])


def _varnode(vn) -> Varnode:
    return Varnode(str(vn.getAddress().getAddressSpace().getName()), int(vn.getOffset()), int(vn.getSize()))


def _op_descriptor(op, language) -> OpDescriptor:
    output = op.getOutput()
    mnemonic = str(op.getMnemonic())
    userop = None
    if mnemonic == "CALLOTHER":
        name = language.getUserDefinedOpName(int(op.getInput(0).getOffset()))
        userop = None if name is None else str(name)
    return OpDescriptor(
        mnemonic,
        None if output is None else _varnode(output),
        tuple(_varnode(op.getInput(i)) for i in range(op.getNumInputs())),
        userop,
    )


def _file_reader(program):
    """``(read(offset, count) -> bytes, length)`` of the program's original file bytes."""
    import jpype

    all_bytes = list(program.getMemory().getAllFileBytes())
    if len(all_bytes) != 1:
        return None, 0
    file_bytes = all_bytes[0]
    length = int(file_bytes.getSize())

    def read(offset: int, count: int) -> bytes:
        if offset < 0 or count < 0 or offset + count > length:
            return b""
        data = jpype.JArray(jpype.JByte)(count)
        got = int(file_bytes.getOriginalBytes(offset, data, 0, count))
        return bytes(int(b) & 0xFF for b in data[:got])

    return read, length


# ------------------------------------------------------------- callbacks

def _make_callbacks(executor: "PcodeEmulatorExecutor"):
    from jpype import JImplements, JOverride

    @JImplements("ghidra.pcode.emu.PcodeEmulationCallbacks")
    class Callbacks:
        # JPype proxies cannot reach the interface's default methods, so every
        # method is implemented; the ones the executor does not use do nothing.
        def __init__(self):
            self.observer = None
            self.decoding = False
            # True while the executor itself reads or sets up state (thread
            # creation reads the PC and context registers): not the program.
            self.inspecting = True
            self.address = None
            self.reported = set()
            self.opcode_cache = {}
            self.opcodes = ()
            self.big_endian = executor._big_endian
            self.arith = None
            self.state = None
            self.want_output = False
            self.reason_inspect = _jclass("ghidra.pcode.exec.PcodeExecutorStatePiece$Reason").INSPECT
            self.language = executor._language

        def _value(self, thread, varnode) -> int:
            if varnode.isConstant():
                return int(varnode.getOffset()) & ((1 << (8 * int(varnode.getSize()))) - 1)
            self.inspecting = True
            try:
                return _int_of(thread.getState().getVar(varnode, self.reason_inspect), self.big_endian)
            finally:
                self.inspecting = False

        @JOverride
        def emulatorCreated(self, machine):
            pass

        @JOverride
        def sharedStateCreated(self, machine):
            pass

        @JOverride
        def threadCreated(self, thread):
            pass

        @JOverride
        def getInject(self, thread, address):
            return None

        @JOverride
        def beforeExecuteInject(self, thread, address, program):
            pass

        @JOverride
        def afterExecuteInject(self, thread, address):
            pass

        @JOverride
        def beforeDecodeInstruction(self, thread, address, context):
            self.decoding = True

        def _guarded(self, function, *args):
            # An error of the executor's own code inside a callback is recorded as
            # an executor error before the emulator can wrap it as a machine fault;
            # the exception itself keeps propagating (nothing is swallowed).
            finished = False
            try:
                value = function(*args)
                finished = True
                return value
            finally:
                if not finished and self.observer.stopped is None:
                    error = sys.exc_info()[1]
                    self.observer.stopped_by_executor(
                        Termination.EXECUTOR_ERROR.value,
                        f"callback {type(error).__name__}: {str(error)[:300]}",
                    )

        @JOverride
        def beforeExecuteInstruction(self, thread, instruction, program):
            self.decoding = False
            self._guarded(self._before_execute_instruction, instruction, program)

        def _before_execute_instruction(self, instruction, program):
            address = int(instruction.getAddress().getOffset())
            self.address = address
            cached = self.opcode_cache.get(address)
            if cached is None:
                code = list(program.getCode())
                cached = tuple(int(op.getOpcode()) for op in code)
                self.opcode_cache[address] = cached
                self.reported.add(address)
                self.observer.decoded(address, tuple(_op_descriptor(op, self.language) for op in code))
            self.opcodes = cached

        @JOverride
        def afterExecuteInstruction(self, thread, instruction):
            pass

        @JOverride
        def beforeStepOp(self, thread, op, frame):
            self._guarded(self._before_step_op, thread, op, frame)

        def _before_step_op(self, thread, op, frame):
            # The frame has already advanced past ``op`` when the callback runs.
            index = int(frame.index()) - 1
            if index >= len(self.opcodes) or self.opcodes[index] != int(op.getOpcode()):
                self.observer.stopped_by_executor(
                    Termination.EXECUTOR_ERROR.value, f"P-code frame mismatch at {self.address:#x}"
                )
                raise _StopRun()
            request = self.observer.value_request(index)
            values = None
            if request.inputs:
                values = tuple(self._value(thread, op.getInput(i)) for i in range(op.getNumInputs()))
            self.want_output = request.output and op.getOutput() is not None
            if self.observer.op(index, values) is not None:
                raise _StopRun()
            if str(op.getMnemonic()) in _DIVISIONS:
                divisor = op.getInput(1)
                self.inspecting = True
                try:
                    value = _int_of(
                        thread.getState().getVar(divisor, _jclass(
                            "ghidra.pcode.exec.PcodeExecutorStatePiece$Reason").INSPECT),
                        self.big_endian,
                    ) if not divisor.isConstant() else int(divisor.getOffset())
                finally:
                    self.inspecting = False
                if value & ((1 << (8 * int(divisor.getSize()))) - 1) == 0:
                    self.observer.stopped_by_executor(
                        Termination.FAULT.value, f"integer division by zero at {self.address:#x}"
                    )
                    raise _StopRun()

        @JOverride
        def afterStepOp(self, thread, op, frame):
            if self.want_output:
                self.want_output = False
                self._guarded(self._after_step_op, thread, op)

        def _after_step_op(self, thread, op):
            self.observer.op_output(self._value(thread, op.getOutput()))

        def _address_of(self, offset) -> int:
            purpose = _jclass("ghidra.pcode.exec.PcodeArithmetic$Purpose").LOAD
            return int(self.arith.toLong(offset, purpose))

        @JOverride
        def beforeLoad(self, thread, op, space, offset, size):
            stop = self._guarded(
                self.observer.load, str(space.getName()), self._address_of(offset), int(size)
            )
            if stop is not None:
                raise _StopRun()

        @JOverride
        def afterLoad(self, thread, op, space, offset, size, value):
            pass

        @JOverride
        def beforeStore(self, thread, op, space, offset, size, value):
            stop = self._guarded(
                self.observer.store, str(space.getName()), self._address_of(offset), int(size)
            )
            if stop is not None:
                raise _StopRun()

        @JOverride
        def afterStore(self, thread, op, space, offset, size, value):
            pass

        @JOverride
        def afterBranch(self, thread, op, target):
            pass

        @JOverride
        def handleMissingUserop(self, thread, op, frame, name, library):
            return bool(self._guarded(self._userop, thread, op))

        def _userop(self, thread, op):
            # The observer decided in beforeStepOp that this user operation runs
            # and computed its value (concrete.userops).
            value = self.observer.userop_value()
            output = op.getOutput()
            if output is None:
                return True
            if value is None:
                return False
            self.inspecting = True
            try:
                thread.getState().setVar(output, _bytes_of(value, int(output.getSize()), self.big_endian))
            finally:
                self.inspecting = False
            return True

        @JOverride
        def dataWritten(self, *args):
            pass

        @JOverride
        def delegateDataWritten(self, *args):
            pass

        @JOverride
        def readUninitialized(self, *args):
            return self._guarded(self._read_uninitialized, *args)

        def _read_uninitialized(self, *args):
            if len(args) == 5:
                _thread, piece, space, offset, length = args
                if not self.inspecting:
                    self.observer.uninitialized_read(
                        str(space.getName()), self._offset(piece, offset), int(length), self.decoding
                    )
                return 0
            _thread, _piece, ranges = args
            if not self.inspecting:
                for rng in ranges:
                    self.observer.uninitialized_read(
                        str(rng.getAddressSpace().getName()),
                        int(rng.getMinAddress().getOffset()),
                        int(rng.getLength()),
                        self.decoding,
                    )
            return ranges

        @JOverride
        def delegateReadUninitialized(self, *args):
            return 0 if len(args) == 5 else args[-1]

        @JOverride
        def wrapFor(self, thread):
            return _jclass("ghidra.pcode.emu.PcodeEmulationCallbacks$Wrapper")(thread, self)

        def _offset(self, piece, offset) -> int:
            if hasattr(offset, "longValue"):
                return int(offset.longValue())
            if isinstance(offset, int):
                return int(offset)
            purpose = _jclass("ghidra.pcode.exec.PcodeArithmetic$Purpose").INSPECT
            return int(piece.getAddressArithmetic().toLong(offset, purpose))

    return Callbacks()


# --------------------------------------------------------------- executor

class PcodeEmulatorExecutor:
    """Runs functions of one program on Ghidra's ``PcodeEmulator``.

    Build it with ``open_executor``.  ``record=True`` keeps the trace of the
    last run in ``last_trace`` (``concrete.recording``).
    """

    def __init__(
        self,
        program,
        abi: AbiModel,
        facts: CompilerSpecFacts,
        conformance: AbiConformance,
        time_limit_seconds: float = DEFAULT_TIME_LIMIT_SECONDS,
        write_page_limit: Optional[int] = None,
        record: bool = False,
    ):
        self._program = program
        self._language = program.getLanguage()
        self._big_endian = bool(self._language.isBigEndian())
        self.abi = abi
        self.facts = facts
        self.conformance = conformance
        self._time_limit = float(time_limit_seconds)
        self._record = record
        self.last_trace: Optional[Dict[str, Any]] = None
        memory = program.getMemory()
        self._memory_space = str(program.getAddressFactory().getDefaultAddressSpace().getName())
        self._image = []
        code, writable, image_ranges = [], [], []
        import jpype

        for block in memory.getBlocks():
            start = block.getStart()
            if block.isExternalBlock() or not start.isMemoryAddress():
                continue
            if str(start.getAddressSpace().getName()) != self._memory_space:
                continue
            size = int(block.getSize())
            # every block of the image, initialized or not (``.bss``): the
            # provenance of addresses (``concrete.value_monitor``)
            image_ranges.append((int(start.getOffset()), int(start.getOffset()) + size))
            if not block.isInitialized():
                continue
            data = jpype.JArray(jpype.JByte)(size)
            block.getBytes(start, data)
            self._image.append((start, size, data))
            begin = int(start.getOffset())
            if block.isExecute():
                code.append((begin, begin + size))
            if block.isWrite():
                writable.append((begin, begin + size))
        externals = []
        for function in program.getFunctionManager().getFunctions(True):
            if not function.isThunk():
                continue
            target = function.getThunkedFunction(True)
            if target is not None and target.isExternal():
                externals.append((int(function.getEntryPoint().getOffset()), str(target.getName())))
        self._zero = self._zero_initialized(program, memory)
        self._code = tuple(sorted(code))
        self._image_ranges = tuple(sorted(image_ranges))
        self._writable = tuple(sorted(writable))
        self._externals = tuple(sorted(externals))
        self._write_page_limit = write_page_limit
        self._program_facts = {
            "sha256": str(program.getExecutableSHA256() or ""),
            "language_id": facts.language_id,
            "compiler_spec_id": facts.compiler_spec_id,
            "executable_format": facts.executable_format,
            "abi_id": abi.abi_id.value,
            "abi_conformance": [
                [m.item.value, m.expected, m.found] for m in conformance.mismatches
            ],
            "processor": str(self._language.getProcessor()),
            "zero_initialized_ranges": [[a, b] for a, b in self._zero.ranges],
            "left_undefined_blocks": [list(entry) for entry in self._zero.left_undefined],
        }

    def _zero_initialized(self, program, memory):
        blocks = []
        for block in memory.getBlocks():
            start = block.getStart()
            if not start.isMemoryAddress() or str(start.getAddressSpace().getName()) != self._memory_space:
                continue
            if block.isExternalBlock():
                continue
            blocks.append(MemoryBlockFact(
                str(block.getName()), int(start.getOffset()), int(block.getSize()), bool(block.isInitialized())
            ))
        read, length = _file_reader(program)
        table = None if read is None else parse_section_table(read, length)
        result = zero_initialized_blocks(table, blocks)
        kept = tuple((a, b) for a, b in result.ranges if b - a <= MAX_ZERO_FILL_BYTES)
        dropped = tuple(
            (f"{a:#x}", "larger than the zero-fill budget") for a, b in result.ranges if b - a > MAX_ZERO_FILL_BYTES
        )
        return type(result)(kept, result.left_undefined + dropped)

    # -------------------------------------------------------------- facts

    def function_abi(self, entry_address: int) -> Union[AbiModel, ExecutorRefusal]:
        """The ABI model of the function at ``entry_address``, or why there is none."""
        address = self._language.getDefaultSpace().getAddress(entry_address)
        function = self._program.getFunctionManager().getFunctionAt(address)
        if function is None or function.isThunk() or function.isExternal():
            return ExecutorRefusal(ExecutorRefusalReason.NO_FUNCTION_AT_ENTRY, f"{entry_address:#x}")
        convention = function.getCallingConventionName()
        model = select_abi(
            self.facts.language_id,
            self.facts.compiler_spec_id,
            self.facts.executable_format,
            None if convention is None else str(convention),
        )
        if model is not self.abi:
            return ExecutorRefusal(ExecutorRefusalReason.FUNCTION_CONVENTION_NOT_DEFAULT, str(convention))
        return self.abi

    def _setup(self, request: ExecutionRequest) -> RunSetup:
        names = [name for name, _ in request.entry_state.registers]
        names += list(request.observe_registers) + [self.abi.stack_pointer]
        facts = []
        for name in dict.fromkeys(names):
            register = self._language.getRegister(name)
            if register is None:
                raise ValueError(f"the language has no register {name!r}")
            facts.append(RegisterFact(
                name, int(register.getAddress().getOffset()), int(register.getNumBytes())
            ))
        kwargs = {}
        if self._write_page_limit is not None:
            kwargs["write_page_limit"] = self._write_page_limit
        return RunSetup(
            big_endian=self._big_endian,
            memory_space=self._memory_space,
            registers=tuple(facts),
            stack_pointer=self.abi.stack_pointer,
            code_ranges=self._code,
            image_ranges=self._image_ranges,
            external_entries=self._externals,
            writable_image_ranges=self._writable,
            processor=str(self._language.getProcessor()),
            zero_initialized_ranges=self._zero.ranges,
            c_int_bytes=self.abi.c_int_bytes,
            **kwargs,
        )

    # -------------------------------------------------------------- execute

    def execute(self, request: ExecutionRequest) -> ExecutionResult:
        self.last_trace = None
        try:
            setup = self._setup(request)
        except ValueError as error:  # the request names something this program lacks
            return ExecutionResult(Termination.EXECUTOR_ERROR, 0, detail=f"setup: {error}")
        refusal = self.function_abi(request.entry_address)
        if isinstance(refusal, ExecutorRefusal):
            return ExecutionResult(
                Termination.EXECUTOR_ERROR, 0, detail=f"refused: {refusal.reason.value} {refusal.detail}"
            )
        inner = RunObserver(setup, request)
        observer = RecordingObserver(inner) if self._record else inner
        self._run(setup, request, observer)
        result = observer.result()
        if self._record:
            self.last_trace = make_trace(
                self._program_facts, setup, request, observer.events, result,
                {"executor": EXECUTOR_VERSION, "ghidra": self._ghidra_version()},
            )
        return result

    @staticmethod
    def _ghidra_version() -> str:
        import jpype

        try:
            return str(_jclass("ghidra.framework.Application").getApplicationVersion())
        except jpype.JException:
            return "unknown"

    def _run(self, setup: RunSetup, request: ExecutionRequest, observer) -> None:
        import jpype

        emulator_class = _jclass("ghidra.pcode.emu.PcodeEmulator")
        reason = _jclass("ghidra.pcode.exec.PcodeExecutorStatePiece$Reason")
        callbacks = _make_callbacks(self)
        callbacks.observer = observer
        emulator = emulator_class(self._language, callbacks)
        callbacks.arith = emulator.getArithmetic()
        shared = emulator.getSharedState()
        for start, size, data in self._image:
            shared.setVar(start, size, True, data)
        space = self._language.getDefaultSpace()
        for begin, end in self._zero.ranges:
            shared.setVar(space.getAddress(begin), end - begin, True, jpype.JArray(jpype.JByte)(end - begin))
        thread = emulator.newThread()
        state = thread.getState()
        # (``callbacks.inspecting`` stays set until the first instruction.)
        for name, value in request.entry_state.registers:
            register = self._language.getRegister(name)
            size = int(register.getNumBytes())
            count = min(request.entry_state.defined_byte_count(name) or size, size)
            address = register.getAddress()
            if self._big_endian:
                address = address.add(size - count)
            state.setVar(address, count, True, _bytes_of(value, count, self._big_endian))
        thread.overrideCounter(space.getAddress(request.entry_address))
        thread.overrideContextWithDefault()

        callbacks.inspecting = False
        limit = self._time_limit
        if request.time_limit_seconds is not None:
            limit = max(0.0, min(limit, float(request.time_limit_seconds)))
        deadline = time.monotonic() + limit
        while True:
            counter = int(thread.getCounter().getOffset())
            if observer.instruction(counter) is not None:
                break
            if time.monotonic() > deadline:
                observer.stopped_by_executor(Termination.TIME_LIMIT.value, f"{limit:g} s")
                break
            try:
                thread.stepInstruction()
            except (jpype.JException, _StopRun) as error:
                # A stop the observer asked for, or a Java exception of the emulator
                # (wrapping the stop, or the machine semantics stopping).
                if observer.stopped is None:
                    observer.stopped_by_executor(*self._classify(error))
                break
            if observer.stopped is not None:
                break

        if observer.stopped is Termination.RETURNED:
            callbacks.inspecting = True
            values = []
            for fact in setup.registers:
                if fact.name not in request.observe_registers and fact.name != setup.stack_pointer:
                    continue
                register = self._language.getRegister(fact.name)
                data = state.getVar(register, reason.INSPECT)
                values.append((fact.name, _int_of(data, self._big_endian)))
            callbacks.inspecting = False
            observer.returned(tuple(values))

    @staticmethod
    def _classify(error) -> Tuple[str, str]:
        get_class = getattr(error, "getClass", None)
        java_name = str(get_class().getName()) if callable(get_class) else ""
        detail = f"{java_name or type(error).__name__}: {str(error)[:300]}"
        if any(java_name.startswith(prefix) for prefix in _FAULT_EXCEPTION_PREFIXES):
            return Termination.FAULT.value, detail
        return Termination.EXECUTOR_ERROR.value, detail


def open_executor(
    program, **options
) -> Union[PcodeEmulatorExecutor, ExecutorRefusal]:
    """An executor for ``program``, or the reason it is refused.

    The program must be one ``concrete.abi.select_abi`` models, and the model
    must agree with the program's compiler specification in every fact both
    state (``concrete.abi_conformance``).
    """
    import jpype

    try:
        facts = compiler_spec_facts(program)
    except jpype.JException as error:  # a specification without the facts the check needs
        return ExecutorRefusal(
            ExecutorRefusalReason.COMPILER_SPEC_FACTS_UNAVAILABLE, f"{type(error).__name__}: {error}"
        )
    abi = select_abi(facts.language_id, facts.compiler_spec_id, facts.executable_format)
    if abi is None:
        return ExecutorRefusal(
            ExecutorRefusalReason.PROGRAM_NOT_MODELLED,
            f"{facts.language_id} / {facts.compiler_spec_id} / {facts.executable_format}",
            facts=facts,
        )
    conformance = check_abi_conformance(abi, facts)
    if not conformance.conforms:
        return ExecutorRefusal(
            ExecutorRefusalReason.ABI_DISAGREES_WITH_COMPILER_SPEC,
            "; ".join(f"{m.item.value}: expected {m.expected}, found {m.found}" for m in conformance.mismatches),
            conformance,
            facts,
        )
    return PcodeEmulatorExecutor(program, abi, facts, conformance, **options)

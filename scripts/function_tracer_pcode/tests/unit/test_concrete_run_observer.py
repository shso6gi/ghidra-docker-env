# -*- coding: utf-8 -*-
"""The run observer: termination, hazards, defined bytes, FP format evidence, monitoring.

Synthetic event streams in the shapes the Ghidra P-code emulator produces
(measured: an AArch64 ``fmov d0`` writes ``z0`` low 8 bytes by the operation
and the upper bytes by separate ``COPY 0``; a MIPS ``add.s`` writes the low 4
bytes of a big-endian ``f`` register; ``fmadd`` is ``FLOAT_MULT`` then
``FLOAT_ADD``; thread creation and the decoder read locations that hold no
value).  Pure Python.
"""
import pytest

from scripts.function_tracer_pcode.concrete.executor import (
    EntryState,
    ExecutionRequest,
    HazardKind,
    Termination,
)
from scripts.function_tracer_pcode.concrete.observation import FpFormat
from scripts.function_tracer_pcode.concrete.recording import RecordingObserver, replay_events
from scripts.function_tracer_pcode.concrete.run_observer import (
    FP_OPERATIONS,
    INTEGER_UB_OPERATIONS,
    OpDescriptor,
    RegisterFact,
    RunObserver,
    RunSetup,
    Varnode,
)

RET = 0x7FF00000
SP = 0x6FF00000
CODE = (0x1000, 0x2000)
DATA = (0x3000, 0x3100)          # writable, initialized
EXTERNAL = 0x1F00


def R(offset, size):
    return Varnode("register", offset, size)


def U(offset, size):
    return Varnode("unique", offset, size)


def C(value, size):
    return Varnode("const", value, size)


def op(mnemonic, out, *inputs):
    return OpDescriptor(mnemonic, out, tuple(inputs))


# A little-endian machine shaped like AArch64 (x0 at 0x4000, z0 at 0x5000 with 32 bytes)
X0, X1, Z0, Z1, SPR = RegisterFact("x0", 0x4000, 8), RegisterFact("x1", 0x4008, 8), \
    RegisterFact("z0", 0x5000, 32), RegisterFact("z1", 0x5020, 32), RegisterFact("sp", 0x8, 8)
# A big-endian machine shaped like MIPS64 (f0 at 0x1000, 8 bytes; single precision in the low half)
F0, F12, V0, MSP = RegisterFact("f0", 0x1000, 8), RegisterFact("f12", 0x1060, 8), \
    RegisterFact("v0", 0x10, 8), RegisterFact("sp", 0xE8, 8)


def _setup(big_endian=False, registers=(X0, X1, Z0, Z1, SPR), write_page_limit=4096):
    return RunSetup(
        big_endian=big_endian,
        memory_space="ram",
        registers=tuple(registers),
        stack_pointer="sp",
        code_ranges=(CODE,),
        external_entries=((EXTERNAL, "log"),),
        writable_image_ranges=(DATA,),
        write_page_limit=write_page_limit,
    )


def _request(registers=(("sp", SP), ("x0", 5)), observe=("x0",), step_limit=100, defined=()):
    return ExecutionRequest(
        0x1000, EntryState(tuple(registers), SP, RET, tuple(defined)), tuple(observe), step_limit
    )


class Run:
    """Drives an observer the way the executor does, one instruction at a time."""

    def __init__(self, setup=None, request=None):
        self.observer = RecordingObserver(RunObserver(setup or _setup(), request or _request()))
        self.address = 0x1000

    def ins(self, *ops, loads=(), stores=()):
        stop = self.observer.instruction(self.address)
        if stop is not None:
            return stop
        self.observer.decoded(self.address, tuple(ops))
        loads, stores = list(loads), list(stores)
        for index, descriptor in enumerate(ops):
            stop = self.observer.op(index)
            if stop is not None:
                return stop
            if descriptor.mnemonic == "LOAD":
                stop = self.observer.load(*loads.pop(0))
            elif descriptor.mnemonic == "STORE":
                stop = self.observer.store(*stores.pop(0))
            if stop is not None:
                return stop
        self.address += 4
        return None

    def ret(self, values):
        assert self.observer.instruction(RET) is Termination.RETURNED
        self.observer.returned(tuple(values))
        return self.result()

    def result(self):
        result = self.observer.result()
        # Every run replays to the same result from its own event list.
        setup, request = self.observer._inner._setup, self.observer._inner._request
        assert replay_events(setup, request, self.observer.events) == result
        return result


# ------------------------------------------------------------- termination

def test_a_return_to_the_return_address_is_returned_with_the_observed_value():
    run = Run()
    run.ins(op("COPY", R(0x4000, 8), C(9, 8)))
    result = run.ret([("x0", 9), ("sp", SP)])
    assert result.termination is Termination.RETURNED and result.steps == 1
    observed = result.observed("x0")
    assert observed.value == 9 and observed.defined_low_bytes == 8 and observed.value_format is None
    assert result.hazards == ()


def test_the_step_budget_external_code_and_unmapped_code_end_the_run_distinctly():
    run = Run(request=_request(step_limit=2))
    assert run.ins(op("COPY", R(0x4000, 8), C(1, 8))) is None
    assert run.ins(op("COPY", R(0x4000, 8), C(1, 8))) is None
    assert run.ins(op("COPY", R(0x4000, 8), C(1, 8))) is Termination.STEP_LIMIT
    result = run.result()
    assert result.termination is Termination.STEP_LIMIT and result.steps == 2 and result.observed_registers == ()

    run = Run()
    run.address = EXTERNAL
    assert run.ins() is Termination.LEFT_PROGRAM_CODE
    assert "log" in run.result().detail

    run = Run()
    run.address = 0x9000
    assert run.ins() is Termination.LEFT_PROGRAM_CODE
    assert "outside program code" in run.result().detail


def test_user_operations_and_writes_to_code_are_not_executed():
    run = Run()
    assert run.ins(op("CALLOTHER", None, C(3, 4))) is Termination.UNSUPPORTED_OPERATION
    result = run.result()
    assert result.termination is Termination.UNSUPPORTED_OPERATION
    assert not result.fp_operations_tracked and not result.integer_ub_operations_tracked

    run = Run()
    store = op("STORE", None, C(0x1b1, 8), R(0x4008, 8), R(0x4000, 8))
    assert run.ins(store, stores=[("ram", 0x1800, 8)]) is Termination.UNSUPPORTED_OPERATION


def test_the_written_memory_budget_stops_runaway_writes():
    run = Run(setup=_setup(write_page_limit=2))
    store = op("STORE", None, C(0x1b1, 8), R(0x4008, 8), R(0x4000, 8))
    assert run.ins(store, stores=[("ram", 0x10000, 8)]) is None
    assert run.ins(store, stores=[("ram", 0x20000, 8)]) is None
    assert run.ins(store, stores=[("ram", 0x30000, 8)]) is Termination.RESOURCE_LIMIT


def test_executor_stops_and_inconsistent_streams_are_reported_not_guessed():
    run = Run()
    run.ins(op("COPY", R(0x4000, 8), C(1, 8)))
    run.observer.stopped_by_executor("TIME_LIMIT", "60 s")
    assert run.result().termination is Termination.TIME_LIMIT

    run = Run()
    run.observer.instruction(0x1000)
    run.observer.decoded(0x1000, (op("LOAD", R(0x4000, 8), C(0x1b1, 8), R(0x4008, 8)),))
    run.observer.op(0)
    # The executor never reported the load's address.
    assert run.observer.instruction(0x1004) is Termination.EXECUTOR_ERROR
    assert "without its address" in run.result().detail

    run = Run()
    run.observer.instruction(0x1000)
    run.observer.decoded(0x1000, (op("COPY", R(0x4000, 8), C(1, 8)),))
    assert run.observer.op(3) is Termination.EXECUTOR_ERROR
    assert Run().observer.result().termination is Termination.EXECUTOR_ERROR    # never ended


@pytest.mark.parametrize("termination", [t for t in Termination if t is not Termination.RETURNED])
def test_only_a_returned_run_reports_observed_registers(termination):
    run = Run()
    run.ins(op("COPY", R(0x4000, 8), C(1, 8)))
    run.observer.stopped_by_executor(termination.value, "x")
    run.observer.returned((("x0", 1), ("sp", SP)))
    result = run.result()
    assert result.termination is termination and result.observed_registers == ()


# ------------------------------------------------------------------ hazards

def test_undefined_reads_are_hazards_except_reads_by_the_decoder():
    run = Run()
    run.observer.uninitialized_read("ram", 0x2000, 4, True)          # decoder look-ahead
    run.ins(op("COPY", R(0x4000, 8), R(0x4008, 8)))
    run.observer.uninitialized_read("register", 0x4008, 8, False)    # x1 was never bound
    run.observer.uninitialized_read("ram", 0x6000, 8, False)
    result = run.ret([("x0", 0), ("sp", SP)])
    assert result.hazard_kinds() == (HazardKind.UNDEFINED_MEMORY_READ, HazardKind.UNDEFINED_REGISTER_READ)
    assert "0x1000" in dict((h.kind, h.detail) for h in result.hazards)[HazardKind.UNDEFINED_REGISTER_READ]


def test_an_unrestored_stack_pointer_is_a_hazard():
    run = Run()
    run.ins(op("INT_ADD", R(0x8, 8), R(0x8, 8), C(16, 8)))
    result = run.ret([("x0", 5), ("sp", SP + 16)])
    assert result.hazard_kinds() == (HazardKind.STACK_POINTER_NOT_RESTORED,)


# ------------------------------------------------------------ defined bytes

def test_defined_bytes_count_from_the_low_end_and_follow_the_entry_widths():
    # z0 bound as a 16-byte FP argument: bytes 16..31 of the base register are undefined.
    request = _request(registers=(("sp", SP), ("z0", 1)), observe=("z0", "x0"), defined=(("z0", 16),))
    run = Run(request=request)
    run.ins(op("COPY", R(0x4000, 4), C(7, 4)))                  # only w0 written
    result = run.ret([("z0", 1), ("x0", 7), ("sp", SP)])
    assert result.observed("z0").defined_low_bytes == 16
    assert result.observed("x0").defined_low_bytes == 4

    big = _setup(big_endian=True, registers=(F0, F12, V0, MSP))
    run = Run(big, _request(registers=(("sp", SP),), observe=("f0",)))
    run.ins(op("FLOAT_ADD", R(0x1004, 4), R(0x1064, 4), R(0x1064, 4)))   # add.s f0: low half on BE
    assert run.ret([("f0", 0), ("sp", SP)]).observed("f0").defined_low_bytes == 4


# ------------------------------------------------------------ format evidence

def _fp_result(*instructions, setup=None, request=None, observe="z0", value=0):
    run = Run(setup, request or _request(registers=(("sp", SP),), observe=(observe,)))
    for ops, loads, stores in instructions:
        assert run.ins(*ops, loads=loads, stores=stores) is None
    sp = "sp"
    return run.ret([(observe, value), (sp, SP)]).observed(observe)


def _ins(*ops, loads=(), stores=()):
    return (ops, loads, stores)


def _fmov_d0(op_name="FLOAT_ADD", *inputs):
    # AArch64 scalar write: d0 by the operation, the rest of z0 by COPY 0.
    return _ins(
        op(op_name, R(0x5000, 8), *(inputs or (R(0x5020, 8), R(0x5020, 8)))),
        op("COPY", R(0x5008, 8), C(0, 8)),
        op("COPY", R(0x5010, 8), C(0, 8)),
        op("COPY", R(0x5018, 8), C(0, 8)),
    )


def test_a_scalar_fp_operation_establishes_the_format_of_its_value():
    assert _fp_result(_fmov_d0()).value_format is FpFormat.BINARY64
    single = _ins(op("FLOAT_MULT", R(0x5000, 4), R(0x5020, 4), R(0x5020, 4)))
    assert _fp_result(single).value_format is FpFormat.BINARY32
    big = _setup(big_endian=True, registers=(F0, F12, V0, MSP))
    add_s = _ins(op("FLOAT_ADD", R(0x1004, 4), R(0x1064, 4), R(0x1064, 4)))
    assert _fp_result(add_s, setup=big, observe="f0").value_format is FpFormat.BINARY32
    add_d = _ins(op("FLOAT_ADD", R(0x1000, 8), R(0x1060, 8), R(0x1060, 8)))
    assert _fp_result(add_d, setup=big, observe="f0").value_format is FpFormat.BINARY64


def test_constants_integer_results_and_vectors_carry_no_format():
    constant = _ins(op("COPY", R(0x5000, 8), C(0x3FF0000000000000, 8)))       # fmov d0, #1.0
    assert _fp_result(constant).value_format is None
    integer = _ins(op("INT_AND", R(0x5000, 8), R(0x5020, 8), C(0x7FFFFFFFFFFFFFFF, 8)))
    assert _fp_result(integer).value_format is None
    vector = _ins(
        op("FLOAT_ADD", U(0x100, 8), R(0x5020, 8), R(0x5020, 8)),
        op("FLOAT_ADD", U(0x108, 8), R(0x5028, 8), R(0x5028, 8)),
        op("PIECE", R(0x5000, 16), U(0x108, 8), U(0x100, 8)),
    )
    assert _fp_result(vector).value_format is None
    # A binary64 result overwritten in its low 4 bytes is not one value any more.
    partial = _fmov_d0()
    overwrite = _ins(op("COPY", R(0x5000, 4), R(0x4000, 4)))
    assert _fp_result(partial, overwrite).value_format is None


def test_the_format_follows_exact_copies_through_registers_and_memory():
    to_x0 = _ins(op("COPY", R(0x4000, 8), R(0x5000, 8)))                     # fmov x0, d0
    back = _ins(op("COPY", R(0x5000, 8), R(0x4000, 8)), op("COPY", R(0x5008, 8), C(0, 8)))
    assert _fp_result(_fmov_d0(), to_x0, back).value_format is FpFormat.BINARY64
    store = op("STORE", None, C(0x1b1, 8), R(0x8, 8), R(0x5000, 8))
    load = op("LOAD", R(0x5000, 8), C(0x1b1, 8), R(0x8, 8))
    spill = _ins(store, stores=[("ram", 0x6000, 8)])
    reload = _ins(load, loads=[("ram", 0x6000, 8)])
    assert _fp_result(_fmov_d0(), spill, reload).value_format is FpFormat.BINARY64
    # Reloaded from another address, or with another width, it is not that value.
    elsewhere = _ins(load, loads=[("ram", 0x6004, 8)])
    assert _fp_result(_fmov_d0(), spill, elsewhere).value_format is None
    clobber = _ins(op("STORE", None, C(0x1b1, 8), R(0x8, 8), R(0x4000, 4)), stores=[("ram", 0x6000, 4)])
    assert _fp_result(_fmov_d0(), spill, clobber, reload).value_format is None
    zext = _ins(op("INT_ZEXT", R(0x5000, 16), R(0x4000, 8)))
    assert _fp_result(_fmov_d0(), to_x0, zext).value_format is FpFormat.BINARY64
    low = _ins(op("SUBPIECE", R(0x5000, 4), U(0x200, 8), C(0, 4)))
    single = _ins(op("FLOAT2FLOAT", U(0x200, 8), R(0x5020, 4)))
    assert _fp_result(single, low).value_format is None          # half of a binary64 value
    big = _setup(big_endian=True, registers=(F0, F12, V0, MSP))
    mips_spill = _ins(
        op("FLOAT_ADD", R(0x1000, 8), R(0x1060, 8), R(0x1060, 8)),
        op("STORE", None, C(0x1b1, 8), U(0x300, 8), R(0x1000, 8)),
        op("LOAD", R(0x1000, 8), C(0x1b1, 8), U(0x300, 8)),
        stores=[("ram", 0x6000, 8)], loads=[("ram", 0x6000, 8)],
    )
    assert _fp_result(mips_spill, setup=big, observe="f0").value_format is FpFormat.BINARY64


# ---------------------------------------------------------------- monitoring

def test_a_run_without_fp_or_integer_arithmetic_is_tracked_for_both():
    run = Run()
    run.ins(op("COPY", R(0x4000, 8), C(1, 8)), op("INT_AND", R(0x4000, 8), R(0x4000, 8), C(1, 8)))
    result = run.ret([("x0", 1), ("sp", SP)])
    assert result.fp_operations_tracked and result.integer_ub_operations_tracked
    assert dict(result.operation_counts) == {"COPY": 1, "INT_AND": 1}


@pytest.mark.parametrize("mnemonic", sorted(FP_OPERATIONS))
def test_any_fp_operation_leaves_the_run_unexamined_until_the_monitor_exists(mnemonic):
    run = Run()
    run.ins(op(mnemonic, U(0x10, 8), R(0x5020, 8), R(0x5020, 8)))
    result = run.ret([("x0", 5), ("sp", SP)])
    assert not result.fp_operations_tracked and result.integer_ub_operations_tracked


@pytest.mark.parametrize("mnemonic", sorted(INTEGER_UB_OPERATIONS))
def test_any_integer_operation_c_may_leave_undefined_leaves_the_run_unexamined(mnemonic):
    run = Run()
    run.ins(op(mnemonic, U(0x10, 8), R(0x4000, 8), R(0x4008, 8)))
    result = run.ret([("x0", 5), ("sp", SP)])
    assert not result.integer_ub_operations_tracked and result.fp_operations_tracked


def test_fmadd_is_two_operations_in_the_emulator():
    # Measured: Ghidra's AArch64 fmadd is FLOAT_MULT into a temporary, then FLOAT_ADD.
    fmadd = _ins(
        op("FLOAT_MULT", U(0x166E00, 8), R(0x5020, 8), R(0x5140, 8)),
        op("FLOAT_ADD", R(0x50A0, 8), R(0x50A0, 8), U(0x166E00, 8)),
    )
    run = Run(request=_request(registers=(("sp", SP),), observe=("z0",)))
    run.ins(*fmadd[0])
    result = run.ret([("z0", 0), ("sp", SP)])
    assert dict(result.operation_counts) == {"FLOAT_ADD": 1, "FLOAT_MULT": 1}
    assert not result.fp_operations_tracked


# ----------------------------------------------------- writable program data

def test_reads_of_writable_program_data_before_writing_it_are_recorded():
    load = op("LOAD", R(0x4000, 8), C(0x1b1, 8), R(0x4008, 8))
    store = op("STORE", None, C(0x1b1, 8), R(0x4008, 8), R(0x4000, 4))
    run = Run()
    run.ins(load, loads=[("ram", 0x3000, 8)])
    run.ins(store, stores=[("ram", 0x3010, 4)])
    run.ins(load, loads=[("ram", 0x3010, 8)])        # 0x3010..13 written by the run
    run.ins(load, loads=[("ram", 0x6000, 8)])        # not program data
    result = run.ret([("x0", 0), ("sp", SP)])
    assert result.writable_image_reads == ((0x3000, 8), (0x3014, 4))
    assert result.hazards == ()                       # a fact, not a hazard

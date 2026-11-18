# -*- coding: utf-8 -*-
"""The integer-UB and floating-point monitors (C3; #314, #317).

Each test drives the production ``RunObserver`` the way the executor does:
a small P-code machine in this file executes the operations (integer
semantics from ``value_monitor.evaluate_int``, floating point unfused and
correctly rounded, as Ghidra's emulator does), supplies the operand values
the observer asks for and the results it asks for, and every run is replayed
from its recorded events to the same result.  The P-code shapes are the ones
Ghidra produces for AArch64 and MIPS64 (taken from the census of the 964
validation binaries and the recorded fixtures).  Pure Python.
"""
import struct

import pytest

from scripts.function_tracer_pcode.concrete import ieee
from scripts.function_tracer_pcode.concrete.executor import (
    EntryState,
    ExecutionRequest,
    HazardKind,
    IntegerOverflow,
    OverflowDisposition,
    Termination,
)
from scripts.function_tracer_pcode.concrete.observation import FpFormat
from scripts.function_tracer_pcode.concrete.recording import (
    TRACE_SCHEMA_V1,
    RecordingObserver,
    make_trace,
    replay_events,
    replay_trace,
    result_from_json,
    result_to_json,
)
from scripts.function_tracer_pcode.concrete.run_observer import (
    OpDescriptor,
    RegisterFact,
    RunObserver,
    RunSetup,
    Varnode,
)
from scripts.function_tracer_pcode.concrete.value_monitor import evaluate_int

RET = 0x7FF00000
SP = 0x6FF00000
CODE = (0x1000, 0x9000)
B64 = FpFormat.BINARY64
INT_MIN32 = 0x80000000


def R(offset, size):
    return Varnode("register", offset, size)


def U(offset, size):
    return Varnode("unique", offset, size)


def C(value, size):
    return Varnode("const", value & ((1 << (8 * size)) - 1), size)


def op(mnemonic, out, *inputs, userop=None):
    return OpDescriptor(mnemonic, out, tuple(inputs), userop)


# AArch64-shaped little-endian registers; MIPS64-shaped big-endian ones.
X0, X1, X2, D0, D1, D2, SPR = (
    RegisterFact("x0", 0x4000, 8), RegisterFact("x1", 0x4008, 8), RegisterFact("x2", 0x4010, 8),
    RegisterFact("z0", 0x5000, 32), RegisterFact("z1", 0x5020, 32), RegisterFact("z2", 0x5040, 32),
    RegisterFact("sp", 0x8, 8),
)
NG, ZR, CY, OV = R(0x100, 1), R(0x101, 1), R(0x102, 1), R(0x103, 1)
V0, A0, MSP = RegisterFact("v0", 0x10, 8), RegisterFact("a0", 0x20, 8), RegisterFact("sp", 0xE8, 8)


def _setup(big_endian=False, processor="AARCH64", c_int_bytes=4):
    registers = (V0, A0, MSP) if big_endian else (X0, X1, X2, D0, D1, D2, SPR)
    return RunSetup(
        big_endian=big_endian, memory_space="ram", registers=registers, stack_pointer="sp",
        code_ranges=(CODE,), external_entries=(), writable_image_ranges=(), processor=processor,
        c_int_bytes=c_int_bytes,
    )


def _request(registers, observe, big_endian=False):
    registers = tuple(registers) + (("sp", SP),)
    return ExecutionRequest(0x1000, EntryState(registers, SP, RET), tuple(observe), 1000)


def _nan_bits(size):
    return 0x7FC00000 if size == 4 else 0x7FF8000000000000


class Machine:
    """Executes P-code on concrete values and drives the observer like the executor."""

    def __init__(self, registers=(), observe=("x0",), big_endian=False, processor="AARCH64", fp_override=None,
                 c_int_bytes=4):
        self.big_endian = big_endian
        self.setup = _setup(big_endian, processor, c_int_bytes)
        self.request = _request(registers, observe, big_endian)
        self.observer = RecordingObserver(RunObserver(self.setup, self.request))
        self.state = {}
        self.address = 0x1000
        self.fp_override = fp_override or {}
        for name, value in self.request.entry_state.registers:
            fact = self.setup.register(name)
            self.write(Varnode("register", fact.offset, fact.size), value)

    # little machine state, byte addressed like the emulator
    def _keys(self, vn):
        if self.big_endian:
            return [(vn.space, vn.offset + vn.size - 1 - k) for k in range(vn.size)]
        return [(vn.space, vn.offset + k) for k in range(vn.size)]

    def read(self, vn):
        if vn.space == "const":
            return vn.offset & ((1 << (8 * vn.size)) - 1)
        return sum(self.state.get(key, 0) << (8 * k) for k, key in enumerate(self._keys(vn)))

    def write(self, vn, value):
        for k, key in enumerate(self._keys(vn)):
            self.state[key] = (value >> (8 * k)) & 0xFF

    def _compute(self, o, values):
        m = o.mnemonic
        if m in self.fp_override:
            return self.fp_override[m]
        sizes = [v.size for v in o.inputs]
        if m in ("FLOAT_ADD", "FLOAT_SUB", "FLOAT_MULT", "FLOAT_DIV"):
            fmt = ieee.FORMAT_OF_SIZE[sizes[0]]
            fn = {"FLOAT_ADD": ieee.add, "FLOAT_SUB": ieee.sub, "FLOAT_MULT": ieee.mul, "FLOAT_DIV": ieee.div}[m]
            r = fn(values[0], values[1], fmt)
            return _nan_bits(o.output.size) if r is None else r
        if m in ("FLOAT_NEG", "FLOAT_ABS", "FLOAT_SQRT"):
            fmt = ieee.FORMAT_OF_SIZE[sizes[0]]
            r = {"FLOAT_NEG": ieee.neg, "FLOAT_ABS": ieee.fabs, "FLOAT_SQRT": ieee.sqrt}[m](values[0], fmt)
            if r is None and m == "FLOAT_NEG":
                return _nan_bits(o.output.size)   # the emulator loses the payload
            return _nan_bits(o.output.size) if r is None else r
        if m in ("FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL"):
            return int(ieee.compare(m, values[0], values[1], ieee.FORMAT_OF_SIZE[sizes[0]]))
        if m == "FLOAT_NAN":
            return int(ieee.is_nan(values[0], ieee.FORMAT_OF_SIZE[sizes[0]]))
        if m == "TRUNC":
            r = ieee.to_int_truncated(values[0], ieee.FORMAT_OF_SIZE[sizes[0]], o.output.size)
            return 0 if r is None else r & ((1 << (8 * o.output.size)) - 1)
        if m == "INT2FLOAT":
            from scripts.function_tracer_pcode.concrete.value_monitor import _signed
            return ieee.from_int(_signed(values[0], sizes[0]), ieee.FORMAT_OF_SIZE[o.output.size])
        return evaluate_int(m, values, sizes, o.output.size)

    def ins(self, *ops, memory=None):
        stop = self.observer.instruction(self.address)
        if stop is not None:
            return stop
        self.observer.decoded(self.address, tuple(ops))
        for index, o in enumerate(ops):
            request = self.observer.value_request(index)
            values = tuple(self.read(v) for v in o.inputs) if request.inputs else None
            stop = self.observer.op(index, values)
            if stop is not None:
                return stop
            values = tuple(self.read(v) for v in o.inputs)
            if o.mnemonic == "LOAD":
                address = values[1]
                stop = self.observer.load("ram", address, o.output.size)
                self.write(o.output, self.read(Varnode("ram", address, o.output.size)))
            elif o.mnemonic == "STORE":
                address = values[1]
                stop = self.observer.store("ram", address, o.inputs[2].size)
                self.write(Varnode("ram", address, o.inputs[2].size), values[2])
            elif o.mnemonic == "CALLOTHER":
                if o.output is not None:
                    self.write(o.output, self.observer.userop_value())
            elif o.output is not None and o.mnemonic not in ("CBRANCH", "BRANCH"):
                result = self._compute(o, values)
                self.write(o.output, result)
                if request.output:
                    self.observer.op_output(result)
            if stop is not None:
                return stop
        self.address += 4
        return None

    def ret(self):
        assert self.observer.instruction(RET) is Termination.RETURNED
        values = []
        for name in tuple(self.request.observe_registers) + ("sp",):
            fact = self.setup.register(name)
            values.append((name, self.read(Varnode("register", fact.offset, fact.size))))
        self.observer.returned(tuple(values))
        result = self.observer.result()
        assert replay_events(self.setup, self.request, self.observer.events) == result
        assert result_from_json(result_to_json(result)) == result
        return result


def _kinds(result):
    return set(result.hazard_kinds())


def _double(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


W0 = R(0x4000, 4)
W1 = R(0x4008, 4)
W2 = R(0x4010, 4)


# ------------------------------------------------------------ signed overflow

USED, NOT_USED, RETURNED = (
    OverflowDisposition.VALUE_USED, OverflowDisposition.VALUE_NOT_USED, OverflowDisposition.VALUE_RETURNED,
)


def _dispositions(result):
    return [(o.operation, o.disposition) for o in result.integer_overflows]


def test_an_overflowed_result_returned_as_is_makes_the_register_unreliable():
    # AArch64 ``add w0, w0, w1``: INT_ADD at 4 bytes, the register write is a
    # zero extension.  INT_MAX + 1 wraps.  Every build agrees modulo 2**32, but
    # the binary cannot show that the addition was not a C signed addition,
    # so the returned value is no evidence; the run itself is not refused (the
    # function may return another register).
    m = Machine([("x0", 0x7FFFFFFF), ("x1", 1)])
    m.ins(op("INT_ADD", U(0x10, 4), W0, W1), op("INT_ZEXT", R(0x4000, 8), U(0x10, 4)))
    result = m.ret()
    assert result.integer_ub_operations_tracked and result.fp_operations_tracked
    observed = result.observed("x0")
    assert observed.value == INT_MIN32 and observed.reliable_low_bytes == 0
    assert observed.unreliable == ("SIGNED_OVERFLOW",) and result.hazards == ()
    assert result.integer_overflows == (IntegerOverflow(0x1000, "INT_ADD", 4, RETURNED, 1, ()),)
    # diagnosis only: what the monitor saw
    assert dict(result.monitor_events) == {"signed_overflow_INT_ADD": 1}


def test_a_wrapped_value_that_decides_a_branch_is_a_hazard():
    # ``if (x + 1 > x)``: a build that assumes no overflow takes the other path.
    m = Machine([("x0", 0x7FFFFFFF), ("x1", 1)])
    m.ins(op("INT_ADD", U(0x10, 4), W0, W1))
    m.ins(op("INT_SLESS", U(0x20, 1), W0, U(0x10, 4)), op("CBRANCH", None, C(0x2000, 8), U(0x20, 1)))
    assert _kinds(m.ret()) == {HazardKind.SIGNED_OVERFLOW}


@pytest.mark.parametrize("use", [
    # a comparison that comes out the same for the exact value
    lambda v: [op("INT_NOTEQUAL", U(0x20, 1), v, C(5, 4)), op("CBRANCH", None, C(0x2000, 8), U(0x20, 1))],
    # arithmetic that undoes the overflow modulo 2**32
    lambda v: [op("INT_SUB", U(0x14, 4), v, W1), op("INT_SEXT", R(0x4000, 8), U(0x14, 4))],
    # masking to a non-negative value
    lambda v: [op("INT_AND", U(0x18, 4), v, C(0x7FFFFFFF, 4)), op("INT_ZEXT", R(0x4000, 8), U(0x18, 4))],
    # a signed division
    lambda v: [op("INT_SDIV", U(0x18, 4), v, C(1009, 4)), op("INT_ZEXT", R(0x4000, 8), U(0x18, 4))],
    # a truncation
    lambda v: [op("SUBPIECE", U(0x18, 1), v, C(0, 4)), op("INT_ZEXT", R(0x4000, 8), U(0x18, 1))],
], ids=["comparison-agrees", "undone-modularly", "masked", "signed-division", "truncated"])
def test_any_use_of_an_overflowed_result_is_a_run_hazard(use):
    # Whether the later computation would agree with an exact one does not
    # matter: the source may have had a signed overflow, which C leaves
    # undefined, so the run is no evidence of a difference.
    m = Machine([("x0", 0x7FFFFFFF), ("x1", 1)])
    m.ins(op("INT_ADD", U(0x10, 4), W0, W1))
    m.ins(*use(U(0x10, 4)))
    result = m.ret()
    assert _kinds(result) == {HazardKind.SIGNED_OVERFLOW}
    assert _dispositions(result) == [("INT_ADD", USED)]
    assert "overflow of INT_ADD at 0x1000 used by" in result.hazards[0].detail


def test_an_unsigned_use_is_recorded_but_does_not_clear_the_overflow():
    # ``h * 31 + c`` then ``h % n``: an unsigned hash is defined modulo 2**n,
    # but compilers also emit unsigned operations for signed values they
    # assume do not overflow; the use is kept for later stages as a fact.
    m = Machine([("x0", 0x12345678), ("x1", 31)])
    m.ins(op("INT_MULT", U(0x10, 4), W0, W1))
    m.ins(op("INT_REM", U(0x18, 4), U(0x10, 4), C(1009, 4)), op("INT_ZEXT", R(0x4000, 8), U(0x18, 4)))
    m.ins(op("STORE", None, C(0x1B1, 8), C(SP - 16, 8), U(0x10, 4)))
    result = m.ret()
    assert _kinds(result) == {HazardKind.SIGNED_OVERFLOW}
    assert result.integer_overflows == (IntegerOverflow(0x1000, "INT_MULT", 4, USED, 1, ("INT_REM", "STORE")),)


def test_a_range_check_through_a_wrapped_difference_is_still_refused():
    # clang -O3 compiles ``if (x < 5) { if (x > 0) ...`` to ``sub w8, w0, #1;
    # cmp w8, #3; b.hi`` -- (unsigned)(x - 1) <= 3.  x = INT_MIN wraps without
    # an overflow in that source, but a source converting an overflowed
    # ``x - 1`` compiles to the same instructions: refused, the use recorded.
    m = Machine([("x0", INT_MIN32)])
    w8 = R(0x4040, 4)
    m.ins(op("INT_SUB", U(0x10, 4), W0, C(1, 4)), op("INT_ZEXT", R(0x4040, 8), U(0x10, 4)))
    m.ins(op("INT_LESSEQUAL", CY, C(3, 4), w8), op("INT_SBORROW", OV, w8, C(3, 4)),
          op("INT_SUB", U(0x30, 4), w8, C(3, 4)), op("INT_SLESS", NG, U(0x30, 4), C(0, 4)),
          op("INT_EQUAL", ZR, U(0x30, 4), C(0, 4)))
    m.ins(op("BOOL_NEGATE", U(0x41, 1), ZR), op("BOOL_AND", U(0x42, 1), CY, U(0x41, 1)),
          op("CBRANCH", None, C(0x2000, 8), U(0x42, 1)))
    result = m.ret()
    assert _kinds(result) == {HazardKind.SIGNED_OVERFLOW}
    assert result.integer_overflows == (
        IntegerOverflow(0x1000, "INT_SUB", 4, USED, 1, ("INT_LESSEQUAL", "INT_SBORROW", "INT_SUB")),
    )


def test_a_narrow_operation_that_stands_for_an_int_overflow_is_a_hazard():
    # ``unsigned short f(unsigned short a, unsigned short b) { return a * b; }``:
    # C multiplies in ``int``; 0xFFFF * 0xFFFF = 4294836225 overflows ``int``
    # (undefined).  A build that needs only the low 16 bits may multiply at
    # 16 bits (a vectorised lane): that operation's wrap is the only trace of
    # the ``int`` overflow, so the width of the operation clears nothing.
    m = Machine([("x0", 0xFFFF), ("x1", 0xFFFF)])
    h0, h1 = R(0x4000, 2), R(0x4008, 2)
    m.ins(op("INT_MULT", U(0x10, 2), h0, h1))
    m.ins(op("STORE", None, C(0x1B1, 8), C(SP - 16, 8), U(0x10, 2)))
    result = m.ret()
    assert _kinds(result) == {HazardKind.SIGNED_OVERFLOW}
    assert _dispositions(result) == [("INT_MULT", USED)]


def test_a_narrow_overflowed_result_returned_makes_the_register_unreliable():
    # the same product returned as is (zero-extended into w0)
    m = Machine([("x0", 0xFFFF), ("x1", 0xFFFF)])
    m.ins(op("INT_MULT", U(0x10, 2), R(0x4000, 2), R(0x4008, 2)), op("INT_ZEXT", R(0x4000, 8), U(0x10, 2)))
    result = m.ret()
    assert result.hazards == () and result.observed("x0").reliable_low_bytes == 0
    assert _dispositions(result) == [("INT_MULT", RETURNED)]


def test_a_narrow_operation_that_wraps_under_neither_reading_is_clean():
    # 0x8000 + 0 at 16 bits: -32768 signed, 32768 unsigned -- no wrap either way
    m = Machine([("x0", 0x8000), ("x1", 0)])
    m.ins(op("INT_ADD", U(0x10, 2), R(0x4000, 2), R(0x4008, 2)))
    m.ins(op("STORE", None, C(0x1B1, 8), C(SP - 16, 8), U(0x10, 2)))
    result = m.ret()
    assert result.hazards == () and result.integer_overflows == ()


def test_the_unsigned_reading_applies_below_int_width_only():
    # 32-bit 0xFFFFFFFF * 0xFFFFFFFF: -1 * -1 in the signed reading, the
    # unsigned product wraps -- defined for ``unsigned int`` (no promotion)
    m = Machine([("x0", 0xFFFFFFFF), ("x1", 0xFFFFFFFF)])
    m.ins(op("INT_MULT", U(0x10, 4), W0, W1))
    m.ins(op("STORE", None, C(0x1B1, 8), C(SP - 16, 8), U(0x10, 4)))
    assert m.ret().integer_overflows == ()
    # without the ABI's int width every width is checked both ways
    m = Machine([("x0", 0xFFFFFFFF), ("x1", 0xFFFFFFFF)], c_int_bytes=0)
    m.ins(op("INT_MULT", U(0x10, 4), W0, W1))
    m.ins(op("STORE", None, C(0x1B1, 8), C(SP - 16, 8), U(0x10, 4)))
    assert _kinds(m.ret()) == {HazardKind.SIGNED_OVERFLOW}


def test_an_overflowed_result_overwritten_unused_is_not_a_hazard():
    # clang -O0 ``subs w8, w8, w9`` for a comparison, then ``cset w8, lt``.
    m = Machine([("x0", INT_MIN32), ("x1", 1)])
    w8 = R(0x4040, 4)
    m.ins(op("INT_SUB", U(0x30, 4), W0, W1), op("INT_ZEXT", R(0x4040, 8), U(0x30, 4)))
    m.ins(op("COPY", R(0x4040, 8), C(1, 8)))
    m.ins(op("INT_ZEXT", R(0x4000, 8), w8))
    result = m.ret()
    assert result.hazards == () and result.observed("x0").reliable_low_bytes == 8
    assert _dispositions(result) == [("INT_SUB", NOT_USED)]


def test_a_stored_overflowed_result_is_used():
    # ``s = a + b`` at -O0: the assignment stores it.
    m = Machine([("x0", 0x7FFFFFFF), ("x1", 1)])
    m.ins(op("INT_ADD", U(0x10, 4), W0, W1))
    m.ins(op("STORE", None, C(0x1B1, 8), C(SP - 16, 8), U(0x10, 4)))
    result = m.ret()
    assert _kinds(result) == {HazardKind.SIGNED_OVERFLOW}
    assert "used by STORE at 0x1004" in result.hazards[0].detail


def _cmp(a, b):
    """AArch64 ``cmp a, b`` (measured shape: SBORROW before SUB, flags NG ZR CY OV)."""
    return (
        op("INT_LESSEQUAL", CY, b, a),
        op("INT_SBORROW", OV, a, b),
        op("INT_SUB", U(0x30, 4), a, b),
        op("INT_SLESS", NG, U(0x30, 4), C(0, 4)),
        op("INT_EQUAL", ZR, U(0x30, 4), C(0, 4)),
    )


def test_the_aarch64_signed_comparison_through_flags_is_exact():
    # ``cmp w0, w1; b.lt``: the subtraction INT_MIN - 1 overflows, but
    # NG != OV is the exact sign of w0 - w1 -- the C comparison has no UB.
    m = Machine([("x0", INT_MIN32), ("x1", 1)])
    m.ins(*_cmp(W0, W1))
    m.ins(op("INT_NOTEQUAL", U(0x40, 1), NG, OV), op("CBRANCH", None, C(0x2000, 8), U(0x40, 1)))
    m.ins(op("BOOL_NEGATE", U(0x41, 1), ZR), op("INT_EQUAL", U(0x42, 1), NG, OV),
          op("BOOL_AND", U(0x43, 1), U(0x41, 1), U(0x42, 1)), op("CBRANCH", None, C(0x2000, 8), U(0x43, 1)))
    result = m.ret()
    assert result.hazards == ()
    # the subtraction overflowed; only its own instruction's flags were taken
    assert _dispositions(result) == [("INT_SUB", NOT_USED)]


def test_the_sign_flag_of_an_overflowed_subtraction_alone_is_a_hazard():
    # ``subs w0, w0, w1; b.mi`` -- ``x - y < 0`` with an overflowing subtraction.
    m = Machine([("x0", INT_MIN32), ("x1", 1)])
    m.ins(*_cmp(W0, W1))
    m.ins(op("CBRANCH", None, C(0x2000, 8), NG))
    assert _kinds(m.ret()) == {HazardKind.SIGNED_OVERFLOW}


def test_comparing_a_wrapped_value_through_flags_is_evaluated_on_the_exact_value():
    # w0 = INT_MAX + 1 (exact 2**31); ``cmp w0, 5; b.lt`` holds for the wrapped
    # value and not for the exact one.
    m = Machine([("x0", 0x7FFFFFFF), ("x1", 1), ("x2", 5)])
    m.ins(op("INT_ADD", W0, W0, W1))
    m.ins(*_cmp(W0, W2))
    m.ins(op("INT_NOTEQUAL", U(0x40, 1), NG, OV), op("CBRANCH", None, C(0x2000, 8), U(0x40, 1)))
    assert _kinds(m.ret()) == {HazardKind.SIGNED_OVERFLOW}


def test_negating_int_min_then_comparing_is_a_hazard():
    # Measured: pow/test (one source, clang -O0 / -O1) returns 13 and 14 for
    # y = INT_MIN on the real machine; ``-y`` overflows.
    m = Machine([("x0", INT_MIN32)])
    m.ins(op("INT_2COMP", U(0x10, 4), W0))
    m.ins(op("INT_SLESS", U(0x20, 1), C(0, 4), U(0x10, 4)), op("CBRANCH", None, C(0x2000, 8), U(0x20, 1)))
    assert _kinds(m.ret()) == {HazardKind.SIGNED_OVERFLOW}


def test_mips_sign_extended_results_keep_their_overflow_through_moves():
    # MIPS64 ``addiu a0, a0, 1``: INT_ADD on the low half (big-endian offset +4),
    # INT_SEXT into the register; ``move v0, a0`` copies it to the return.
    m = Machine([("a0", 0x7FFFFFFF)], observe=("v0",), big_endian=True, processor="MIPS")
    a0_lo = R(0x24, 4)
    m.ins(op("INT_ADD", a0_lo, a0_lo, C(1, 4)), op("INT_SEXT", R(0x20, 8), a0_lo))
    m.ins(op("COPY", R(0x10, 8), R(0x20, 8)))
    result = m.ret()
    assert result.observed("v0").reliable_low_bytes == 0 and result.hazards == ()
    assert _dispositions(result) == [("INT_ADD", RETURNED)]


def test_mips_slt_on_a_sign_extended_wrapped_value_is_a_hazard():
    m = Machine([("a0", 0x7FFFFFFF)], observe=("v0",), big_endian=True, processor="MIPS")
    a0_lo = R(0x24, 4)
    m.ins(op("INT_ADD", a0_lo, a0_lo, C(1, 4)), op("INT_SEXT", R(0x20, 8), a0_lo))
    m.ins(op("INT_SLESSEQUAL", U(0x40, 1), R(0x20, 8), C(0, 8)), op("CBRANCH", None, C(0x2000, 8), U(0x40, 1)))
    assert _kinds(m.ret()) == {HazardKind.SIGNED_OVERFLOW}


def test_a_wrapped_index_used_as_an_address_is_a_hazard():
    m = Machine([("x0", 0x7FFFFFFF), ("x1", 1)])
    m.ins(op("INT_ADD", U(0x10, 4), W0, W1), op("INT_SEXT", U(0x18, 8), U(0x10, 4)))
    m.ins(op("INT_ADD", U(0x20, 8), C(0x80000000, 8), U(0x18, 8)), op("LOAD", R(0x4000, 8), C(0x1B1, 8), U(0x20, 8)))
    assert HazardKind.SIGNED_OVERFLOW in _kinds(m.ret())


def test_wrapped_values_survive_memory():
    m = Machine([("x0", 0x7FFFFFFF), ("x1", 1)])
    m.ins(op("INT_ADD", U(0x10, 4), W0, W1))
    m.ins(op("STORE", None, C(0x1B1, 8), C(SP - 16, 8), U(0x10, 4)))
    m.ins(op("LOAD", U(0x18, 4), C(0x1B1, 8), C(SP - 16, 8)))
    m.ins(op("INT_SLESS", U(0x20, 1), U(0x18, 4), C(0, 4)), op("CBRANCH", None, C(0x2000, 8), U(0x20, 1)))
    assert _kinds(m.ret()) == {HazardKind.SIGNED_OVERFLOW}


def test_operations_without_overflow_leave_nothing_behind():
    m = Machine([("x0", 100), ("x1", -3 & 0xFFFFFFFFFFFFFFFF)])
    m.ins(op("INT_ADD", U(0x10, 4), W0, W1), op("INT_MULT", U(0x14, 4), U(0x10, 4), C(7, 4)))
    m.ins(op("INT_SLESS", U(0x20, 1), U(0x14, 4), C(0, 4)), op("CBRANCH", None, C(0x2000, 8), U(0x20, 1)))
    m.ins(op("INT_SEXT", R(0x4000, 8), U(0x14, 4)))
    result = m.ret()
    assert result.hazards == () and result.observed("x0").reliable_low_bytes == 8


# ------------------------------------------------- division, shifts, conversion

def _sdiv(rd, rn, rm):
    """AArch64 ``sdiv`` (measured): result 0 unless the divisor is non-zero."""
    return (
        op("COPY", U(0x50, 4), C(0, 4)),
        op("INT_EQUAL", U(0x58, 1), rm, C(0, 4)),
        op("CBRANCH", None, C(4, 8), U(0x58, 1)),
        op("INT_SDIV", U(0x50, 4), rn, rm),
        op("INT_ZEXT", rd, U(0x50, 4)),
    )


class _GuardedMachine(Machine):
    def ins(self, *ops, memory=None):
        # the CBRANCH of the guard skips the division when the divisor is zero
        if ops and ops[0].mnemonic == "COPY" and len(ops) == 5 and self.read(ops[1].inputs[0]) == 0:
            stop = self.observer.instruction(self.address)
            self.observer.decoded(self.address, tuple(ops))
            for index in (0, 1, 2, 4):
                o = ops[index]
                request = self.observer.value_request(index)
                values = tuple(self.read(v) for v in o.inputs) if request.inputs else None
                assert self.observer.op(index, values) is None
                if o.output is not None:
                    self.write(o.output, self._compute(o, tuple(self.read(v) for v in o.inputs)))
            self.address += 4
            return stop
        return super().ins(*ops, memory=memory)


def test_a_division_by_zero_the_instruction_defines_taints_its_result():
    m = _GuardedMachine([("x0", 7), ("x1", 0)])
    m.ins(*_sdiv(R(0x4000, 8), W0, W1))
    result = m.ret()
    assert result.observed("x0").reliable_low_bytes == 0
    assert result.observed("x0").unreliable == ("INTEGER_DIVISION_UNDEFINED",)
    assert result.hazards == ()     # the guard's own branch is not a hazard


def test_int_min_divided_by_minus_one_taints_its_result():
    m = Machine([("x0", INT_MIN32), ("x1", 0xFFFFFFFF)])
    m.ins(*_sdiv(R(0x4000, 8), W0, W1))
    assert m.ret().observed("x0").unreliable == ("INTEGER_DIVISION_UNDEFINED",)
    m = Machine([("x0", 7), ("x1", 2)])
    m.ins(*_sdiv(R(0x4000, 8), W0, W1))
    assert m.ret().observed("x0").reliable_low_bytes == 8


def _lsr(rd, rn, rm):
    """AArch64 ``lsr w8, w9, w8`` (measured): the instruction reduces the amount mod 32."""
    return (
        op("INT_AND", U(0x60, 4), rm, C(0x1F, 4)),
        op("INT_ZEXT", U(0x68, 8), U(0x60, 4)),
        op("INT_RIGHT", U(0x70, 4), rn, U(0x68, 8)),
        op("INT_ZEXT", rd, U(0x70, 4)),
    )


@pytest.mark.parametrize("amount, reliable", [(3, 8), (31, 8), (32, 0), (40, 0), (0xFFFFFFFF, 0)])
def test_a_shift_amount_the_instruction_reduced_taints_the_result(amount, reliable):
    m = Machine([("x0", 0), ("x1", 0x80000000), ("x2", amount)])
    m.ins(*_lsr(R(0x4000, 8), W1, W2))
    observed = m.ret().observed("x0")
    assert observed.reliable_low_bytes == reliable
    if not reliable:
        assert observed.unreliable == ("SHIFT_COUNT_OUT_OF_RANGE",)


def test_an_explicit_mask_in_another_instruction_is_the_program_s_own():
    m = Machine([("x0", 0), ("x1", 0x80000000), ("x2", 40)])
    m.ins(op("INT_AND", W2, W2, C(0x1F, 4)))
    m.ins(*_lsr(R(0x4000, 8), W1, W2))
    assert m.ret().observed("x0").reliable_low_bytes == 8


def test_converting_an_out_of_range_double_to_int_taints_the_result():
    m = Machine([("x0", 0)], observe=("x0",))
    d = R(0x5000, 8)
    m.write(d, _double(1e300))
    m.ins(op("TRUNC", U(0x10, 4), d), op("INT_ZEXT", R(0x4000, 8), U(0x10, 4)))
    assert m.ret().observed("x0").unreliable == ("FP_TO_INTEGER_OUT_OF_RANGE",)


# ------------------------------------------------------------ floating point

D0V, D1V, D2V = R(0x5000, 8), R(0x5020, 8), R(0x5040, 8)


def _fmadd(rd, rn, rm, ra):
    """AArch64 ``fmadd`` as Ghidra emulates it (measured): two roundings."""
    return (op("FLOAT_MULT", U(0x166E00, 8), rn, rm), op("FLOAT_ADD", rd, ra, U(0x166E00, 8)))


def _fp_machine(a, b, c, **kw):
    m = Machine([("x0", 0)], observe=("x0", "z0"), **kw)
    m.write(D0V, _double(a))
    m.write(D1V, _double(b))
    m.write(D2V, _double(c))
    return m


def test_a_fused_multiply_add_with_an_inexact_product_is_not_reliable():
    # Measured on the machine: bess/bessk0 -O0 / -O2 (one source) differ in the last
    # place for 0.1 because -O2 fuses; Ghidra emulates fmadd with two roundings.
    # 0.1 * 10 is 1.0000000000000000555...: rounded to 1.0 the sum is 0, fused it
    # is 5.55e-17.
    m = _fp_machine(0.1, 10.0, -1.0)
    m.ins(*_fmadd(D0V, D0V, D1V, D2V))
    result = m.ret()
    observed = result.observed("z0")
    assert observed.value_format is B64 and observed.reliable_low_bytes == 0
    assert observed.unreliable == ("FP_ROUNDING_SENSITIVE",)
    assert result.fp_operations_tracked and result.hazards == ()
    # both possible values, the machine's (unfused, 0.0) among them
    fused = ieee.fma(_double(0.1), _double(10.0), _double(-1.0), ieee.FORMAT_OF_SIZE[8])
    assert observed.rounding_bytes == 8 and observed.rounding_values == tuple(sorted({0, fused}))


def _rounding_sensitive_and(other, value):
    """z0 of an fmadd-shaped 0.1 * 10 + c, and of ``other`` (a build of another
    source) returning ``value`` exactly."""
    m = _fp_machine(0.1, 10.0, -1.0)
    m.ins(*_fmadd(D0V, D0V, D1V, D2V))
    sensitive = m.ret().observed("z0")
    m = _fp_machine(value, 0.0, 0.0)
    m.ins(op("FLOAT_ADD", D0V, D0V, D1V))
    return sensitive, m.ret().observed("z0")


def test_a_rounding_sensitive_value_differs_only_from_values_none_of_its_roundings_has():
    from scripts.function_tracer_pcode.concrete.abi import ArgClass
    from scripts.function_tracer_pcode.concrete.observation import (
        ObservationRefusal, ObservationRelation, ReturnLocation, compare_return_values, plan_return_observation,
    )
    location = ReturnLocation(ArgClass.FP, "z0", 32, 8)
    plan = plan_return_observation(location, location)
    # a build of another source returning 1.0: no rounding of 0.1 * 10 - 1 is 1.0
    sensitive, other = _rounding_sensitive_and("other", 1.0)
    assert compare_return_values(plan, sensitive, other) is ObservationRelation.DIFFERENT
    assert compare_return_values(plan, other, sensitive) is ObservationRelation.DIFFERENT
    # a build of the same source that fused: 5.55e-17 is one of the possible values
    fused = ieee.fma(_double(0.1), _double(10.0), _double(-1.0), ieee.FORMAT_OF_SIZE[8])
    m = _fp_machine(0.0, 0.0, 0.0)
    m.write(D0V, fused)
    m.ins(op("FLOAT_ADD", D0V, D0V, D1V))
    same_source = m.ret().observed("z0")
    assert compare_return_values(plan, sensitive, same_source) is ObservationRefusal.VALUE_NOT_RELIABLE
    # and two rounding-sensitive values whose sets meet
    assert compare_return_values(plan, sensitive, sensitive) is ObservationRefusal.VALUE_NOT_RELIABLE


def test_an_exact_product_fuses_to_the_same_value():
    m = _fp_machine(1.5, 4.0, 0.1)
    m.ins(*_fmadd(D0V, D0V, D1V, D2V))
    assert m.ret().observed("z0").reliable_low_bytes == 32


def test_a_product_stored_and_reloaded_before_the_addition_is_followed():
    # -O0: fmul, str d0, ..., ldr d0, fadd -- another build may fuse them.
    m = _fp_machine(0.1, 10.0, -1.0)
    m.ins(op("FLOAT_MULT", D0V, D0V, D1V))
    m.ins(op("STORE", None, C(0x1B1, 8), C(SP - 8, 8), D0V))
    m.ins(op("LOAD", D1V, C(0x1B1, 8), C(SP - 8, 8)))
    m.ins(op("FLOAT_ADD", D0V, D1V, D2V))
    assert m.ret().observed("z0").reliable_low_bytes == 0


def test_a_comparison_both_roundings_agree_on_is_clean_and_one_they_do_not_is_a_hazard():
    m = _fp_machine(0.1, 10.0, -1.0)
    m.ins(*_fmadd(D0V, D0V, D1V, D2V))
    # 0 and 5.55e-17 are both greater than -1
    m.ins(op("FLOAT_LESS", U(0x20, 1), D0V, D2V), op("CBRANCH", None, C(0x2000, 8), U(0x20, 1)))
    assert m.ret().hazards == ()
    # 0.1 * 10 - 1 is zero unfused and not zero fused (fmsub shape).
    m = _fp_machine(0.1, 10.0, 1.0)
    m.ins(op("FLOAT_MULT", U(0x30, 8), D0V, D1V), op("FLOAT_SUB", D0V, U(0x30, 8), D2V))
    m.ins(op("FLOAT_EQUAL", U(0x20, 1), D0V, C(0, 8)), op("CBRANCH", None, C(0x2000, 8), U(0x20, 1)))
    assert _kinds(m.ret()) == {HazardKind.FP_ROUNDING_SENSITIVE}


def test_floating_point_without_products_feeding_additions_is_reliable():
    m = _fp_machine(0.1, 3.0, 0.7)
    m.ins(op("FLOAT_ADD", D0V, D0V, D1V))
    m.ins(op("FLOAT_DIV", D0V, D0V, D2V))
    m.ins(op("FLOAT_SQRT", D0V, D0V))
    result = m.ret()
    assert result.observed("z0").reliable_low_bytes == 32 and result.fp_operations_tracked


def test_a_nan_operand_taints_a_value_but_not_a_comparison():
    # Measured: Ghidra's FLOAT_NEG loses a NaN payload (airy/airy SIGN).
    m = _fp_machine(0.0, 1.0, 2.0)
    m.write(D0V, 0x7FF0000000000001)   # signalling NaN
    m.ins(op("FLOAT_LESS", U(0x20, 1), D0V, D1V), op("CBRANCH", None, C(0x2000, 8), U(0x20, 1)))
    m.ins(op("FLOAT_NAN", U(0x21, 1), D0V), op("CBRANCH", None, C(0x2000, 8), U(0x21, 1)))
    m.ins(op("FLOAT_NEG", D0V, D0V))
    result = m.ret()
    assert result.hazards == ()
    assert result.observed("z0").unreliable == ("FP_NAN_OPERAND",)
    assert result.observed("z0").reliable_low_bytes == 0


def test_a_nan_produced_by_an_operation_taints_it():
    m = _fp_machine(0.0, 0.0, 1.0)
    m.ins(op("FLOAT_DIV", D0V, D0V, D1V))
    assert m.ret().observed("z0").unreliable == ("FP_NAN_OPERAND",)


def test_an_emulator_result_that_is_not_the_ieee_result_is_reported():
    m = _fp_machine(0.1, 3.0, 0.7, fp_override={"FLOAT_DIV": _double(42.0)})
    m.ins(op("FLOAT_DIV", D0V, D0V, D1V))
    assert m.ret().observed("z0").unreliable == ("FP_EMULATION_MISMATCH",)


def test_an_integer_computed_from_a_rounding_sensitive_value_is_not_reliable():
    m = _fp_machine(0.1, 10.0, -1.0)
    m.ins(*_fmadd(D0V, D0V, D1V, D2V))
    m.ins(op("FLOAT_MULT", D0V, D0V, C(_double(1e17), 8)))
    m.ins(op("TRUNC", U(0x10, 8), D0V), op("COPY", R(0x4000, 8), U(0x10, 8)))
    assert m.ret().observed("x0").unreliable == ("FP_ROUNDING_SENSITIVE",)


# ------------------------------------------------------------ user operations

def test_neon_ext_runs_with_its_established_meaning():
    m = Machine([("x0", 0)], observe=("z1",))
    q0, q1 = R(0x5000, 16), R(0x5020, 16)
    m.write(q0, int.from_bytes(bytes(range(16)), "little"))
    m.ins(op("CALLOTHER", q1, C(0x96, 4), q0, q0, C(8, 1), C(1, 1), userop="NEON_ext"))
    result = m.ret()
    value = result.observed("z1").value & ((1 << 128) - 1)
    assert value.to_bytes(16, "little") == bytes(list(range(8, 16)) + list(range(0, 8)))
    assert result.termination is Termination.RETURNED and result.fp_operations_tracked


def test_fminnm_runs_and_carries_the_format():
    m = _fp_machine(2.5, -1.0, 0.0)
    m.ins(op("CALLOTHER", D0V, C(0xA9, 4), D0V, D1V, userop="NEON_fminnm"))
    observed = m.ret().observed("z0")
    assert observed.value & ((1 << 64) - 1) == _double(-1.0) and observed.value_format is B64


def test_a_mips_trap_stops_the_call_and_unknown_user_operations_are_not_run():
    m = Machine([("a0", 0)], observe=("v0",), big_endian=True, processor="MIPS")
    assert m.ins(op("CALLOTHER", None, C(1, 4), C(7, 2), userop="trap")) is Termination.FAULT
    m = Machine([("x0", 0)])
    assert m.ins(op("CALLOTHER", U(0x10, 8), C(3, 4), R(0x4000, 8), userop="NEON_sha1")) \
        is Termination.UNSUPPORTED_OPERATION
    m = Machine([("x0", 0)])
    # a name known on another processor is not known here
    assert m.ins(op("CALLOTHER", None, C(1, 4), C(7, 2), userop="trap")) is Termination.UNSUPPORTED_OPERATION


# ------------------------------------------------------------ record / replay

def test_a_version_1_trace_replays_as_not_monitored():
    m = Machine([("x0", 0x7FFFFFFF), ("x1", 1)])
    m.ins(op("INT_ADD", U(0x10, 4), W0, W1), op("INT_ZEXT", R(0x4000, 8), U(0x10, 4)))
    result = m.ret()
    trace = make_trace({"sha256": "x"}, m.setup, m.request, m.observer.events, result)
    replayed, recorded = replay_trace(trace)
    assert replayed == recorded == result
    trace["schema"] = TRACE_SCHEMA_V1
    trace["events"] = [e[:2] if e[0] == "O" else e for e in trace["events"] if e[0] != "P"]
    replayed, _ = replay_trace(trace)
    assert not replayed.integer_ub_operations_tracked

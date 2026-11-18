# -*- coding: utf-8 -*-
"""The provenance of addresses in a concrete run (#18, C2).

Two binaries place their stack frame and their image differently, so a value
computed from an address -- a returned pointer, an integer made from one, a
branch on the bits of one -- is no evidence of a difference between the
functions.  The tests drive the production ``RunObserver`` with the P-code
machine of ``test_concrete_value_monitor`` (AArch64 and MIPS64 shapes) and
replay every run from its recorded events.  Real-binary counterparts are the
``*_ptrsyn_*`` fixtures (``test_concrete_recording``).  Pure Python.
"""
import pytest

from scripts.function_tracer_pcode.concrete.executor import HazardKind
from scripts.function_tracer_pcode.concrete.recording import RecordingObserver
from scripts.function_tracer_pcode.concrete.run_observer import RunObserver, Varnode
from scripts.function_tracer_pcode.tests.unit.test_concrete_value_monitor import (
    C,
    Machine,
    R,
    SP,
    U,
    V0,
    op,
)

IMAGE = ((0x100000, 0x120000),)
GLOBAL = 0x111030
X0R, X1R, X2R, SPV = R(0x4000, 8), R(0x4008, 8), R(0x4010, 8), R(0x8, 8)
STACK, IMG, BITS = HazardKind.STACK_ADDRESS, HazardKind.IMAGE_ADDRESS, HazardKind.ADDRESS_BITS


def _arm(registers=(), image=IMAGE):
    return Machine(list(registers), image_ranges=image, address_registers=(("sp", STACK),))


def _returned(m):
    result = m.ret()
    assert result.address_provenance_tracked
    return result, result.observed("x0")


def test_a_returned_image_address_from_a_constant_is_not_reliable():
    # AArch64 ``adrp x0, page; add x0, x0, #off``: a pointer-sized constant in the image.
    m = _arm()
    m.ins(op("COPY", X0R, C(0x111000, 8)))
    m.ins(op("INT_ADD", X0R, X0R, C(0x30, 8)))
    result, observed = _returned(m)
    assert observed.value == GLOBAL and observed.reliable_low_bytes == 0
    assert observed.unreliable == ("IMAGE_ADDRESS",) and result.hazards == ()


def test_a_returned_address_loaded_from_the_image_is_not_reliable():
    # A GOT entry: the loaded value is an address of the image, whatever the
    # load address.  The value must be reported (the observer asks for it).
    m = _arm([("x1", 0x200000)])
    m.write(Varnode("ram", 0x200000, 8), GLOBAL)
    m.ins(op("LOAD", X0R, C(0, 8), X1R))
    _, observed = _returned(m)
    assert observed.unreliable == ("IMAGE_ADDRESS",) and observed.reliable_low_bytes == 0


def test_a_returned_stack_address_is_not_reliable():
    m = _arm()
    m.ins(op("INT_ADD", X0R, SPV, C(16, 8)))
    _, observed = _returned(m)
    assert observed.value == SP + 16 and observed.unreliable == ("STACK_ADDRESS",)


def test_the_return_address_register_is_an_image_address():
    m = Machine([], image_ranges=IMAGE, address_registers=(("x1", IMG),))
    m.ins(op("COPY", X0R, X1R))
    _, observed = _returned(m)
    assert observed.unreliable == ("IMAGE_ADDRESS",)


def test_the_difference_of_two_pointers_into_one_frame_is_reliable():
    # ``p - q`` within one object: the placement cancels.
    m = _arm()
    m.ins(op("INT_ADD", X1R, SPV, C(8, 8)), op("INT_ADD", X2R, SPV, C(40, 8)))
    m.ins(op("INT_SUB", U(0x10, 8), X2R, X1R), op("INT_SRIGHT", X0R, U(0x10, 8), C(2, 8)))
    result, observed = _returned(m)
    assert observed.value == 8 and observed.reliable_low_bytes == 8 and result.hazards == ()


def test_a_loop_bound_comparison_of_two_pointers_is_no_hazard():
    # ``for (p = buf; p != end; ++p)`` and ``p < end``
    m = _arm()
    m.ins(op("INT_ADD", X1R, SPV, C(8, 8)), op("INT_ADD", X2R, SPV, C(40, 8)))
    m.ins(op("INT_NOTEQUAL", U(0x20, 1), X1R, X2R), op("CBRANCH", None, C(0x2000, 8), U(0x20, 1)))
    m.ins(op("INT_LESS", U(0x21, 1), X1R, X2R), op("CBRANCH", None, C(0x2000, 8), U(0x21, 1)))
    # AArch64 ``cmp x1, x2``: the flags come from the difference
    m.ins(op("INT_SUB", U(0x30, 8), X1R, X2R), op("INT_SLESS", U(0x22, 1), U(0x30, 8), C(0, 8)),
          op("INT_SBORROW", U(0x23, 1), X1R, X2R), op("CBRANCH", None, C(0x2000, 8), U(0x22, 1)))
    m.ins(op("COPY", X0R, C(1, 8)))
    result, observed = _returned(m)
    assert result.hazards == () and observed.reliable_low_bytes == 8


def test_a_null_test_of_a_pointer_is_no_hazard():
    m = _arm()
    m.ins(op("COPY", X1R, C(GLOBAL, 8)))
    m.ins(op("INT_EQUAL", U(0x20, 1), X1R, C(0, 8)), op("CBRANCH", None, C(0x2000, 8), U(0x20, 1)))
    m.ins(op("COPY", X0R, C(6, 8)))
    result, _ = _returned(m)
    assert result.hazards == ()


@pytest.mark.parametrize("bits", [
    # ``(unsigned long)&g & 0x10``
    lambda p: [op("INT_AND", U(0x40, 8), p, C(0x10, 8))],
    # a shift of an address
    lambda p: [op("INT_RIGHT", U(0x40, 8), p, C(4, 8))],
    # the sum of two addresses
    lambda p: [op("INT_ADD", U(0x40, 8), p, p)],
])
def test_a_branch_on_the_bits_of_an_address_is_a_hazard(bits):
    m = _arm()
    m.ins(op("COPY", X1R, C(GLOBAL, 8)))
    m.ins(*bits(X1R), op("INT_NOTEQUAL", U(0x20, 1), U(0x40, 8), C(0, 8)),
          op("CBRANCH", None, C(0x2000, 8), U(0x20, 1)))
    m.ins(op("COPY", X0R, C(1, 8)))
    result, observed = _returned(m)
    assert set(result.hazard_kinds()) == {BITS}
    assert observed.reliable_low_bytes == 8   # the returned constant itself is clean


def test_a_branch_comparing_a_stack_and_an_image_address_is_a_hazard():
    m = _arm()
    m.ins(op("COPY", X1R, C(GLOBAL, 8)), op("INT_ADD", X2R, SPV, C(8, 8)))
    m.ins(op("INT_LESS", U(0x20, 1), X1R, X2R), op("CBRANCH", None, C(0x2000, 8), U(0x20, 1)))
    m.ins(op("COPY", X0R, C(1, 8)))
    result, _ = _returned(m)
    assert set(result.hazard_kinds()) == {BITS}


def test_an_address_kept_in_memory_keeps_its_provenance():
    m = _arm()
    m.ins(op("COPY", X1R, C(GLOBAL, 8)), op("INT_ADD", X2R, SPV, C(8, 8)))
    m.ins(op("STORE", None, C(0, 8), X2R, X1R))
    m.ins(op("LOAD", X0R, C(0, 8), X2R))
    _, observed = _returned(m)
    assert observed.unreliable == ("IMAGE_ADDRESS",)


def test_addresses_used_as_addresses_and_branch_targets_are_no_hazard():
    # a load through the frame, a jump through a table of image addresses
    m = _arm([("x1", 0x200000)])
    m.write(Varnode("ram", 0x200000, 8), 0x1008)
    m.write(Varnode("ram", SP + 8, 8), 42)
    m.ins(op("INT_ADD", X2R, SPV, C(8, 8)), op("LOAD", X0R, C(0, 8), X2R))
    m.ins(op("LOAD", U(0x50, 8), C(0, 8), X1R))
    result, observed = _returned(m)
    assert result.hazards == () and observed.value == 42 and observed.reliable_low_bytes == 8


def test_an_integer_return_inside_the_image_is_not_reliable_however_computed():
    # an address assembled from constants narrower than a pointer (MIPS lui/daddiu)
    m = _arm()
    m.ins(op("COPY", U(0x10, 4), C(0x11, 4)), op("INT_ZEXT", X1R, U(0x10, 4)))
    m.ins(op("INT_LEFT", X0R, X1R, C(16, 8)))
    _, observed = _returned(m)
    assert observed.value == 0x110000 and observed.unreliable == ("IMAGE_ADDRESS",)


def test_mips_move_of_a_pointer_is_a_move():
    # MIPS ``move s8, sp`` is ``or s8, sp, zero``; ``or`` with a non-zero value is not.
    zero = R(0x0, 8)
    s8 = R(0xF0, 8)
    m = Machine([("a0", 0)], observe=("v0",), big_endian=True, processor="MIPS",
                image_ranges=IMAGE, address_registers=(("sp", STACK),))
    msp = R(0xE8, 8)
    m.write(zero, 0)
    m.ins(op("INT_OR", s8, msp, zero))
    m.ins(op("INT_ADD", U(0x10, 8), s8, C(8, 8)), op("INT_SUB", R(V0.offset, 8), U(0x10, 8), msp))
    result = m.ret()
    assert result.address_provenance_tracked and result.observed("v0").reliable_low_bytes == 8
    m = Machine([("a0", 0x4)], observe=("v0",), big_endian=True, processor="MIPS",
                image_ranges=IMAGE, address_registers=(("sp", STACK),))
    m.ins(op("INT_OR", s8, msp, R(0x20, 8)))
    m.ins(op("INT_SUB", R(V0.offset, 8), s8, msp))
    assert m.ret().observed("v0").unreliable == ("ADDRESS_BITS",)


def test_a_run_without_the_values_of_its_pointer_sized_loads_is_not_tracked():
    m = _arm([("x1", 0x200000)])
    observer = m.observer
    inner = RunObserver(m.setup, m.request)
    m.observer = RecordingObserver(inner)
    m.observer.op_output = lambda value: None      # the executor never reports the value
    m.ins(op("LOAD", X0R, C(0, 8), X1R))
    assert observer is not m.observer
    assert m.observer.instruction(0x7FF00000) is not None
    m.observer.returned((("x0", 0), ("sp", SP)))
    assert not m.observer.result().address_provenance_tracked


def test_a_setup_without_image_ranges_is_not_tracked():
    # a version 2 trace
    m = _arm(image=())
    m.ins(op("COPY", X0R, C(1, 8)))
    assert not m.ret().address_provenance_tracked

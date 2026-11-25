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


# Two addresses are never compared or subtracted without a mark (review of
# PR #321): the binary does not show that they point into one object, and for
# two objects the result is the placement itself.  Measured on real builds of
# one source (``fixtures/concrete/ptrsyn2.c``): with a same-kind cancellation,
# ``(uintptr_t)&g_b - (uintptr_t)&g_a``, ``&g_b < &g_a`` and ``&g_a + 1 == &g_b``
# gave ConcreteDifference between 5, 6 and 10 pairs of builds.

def _two(first, second):
    """x1 = first, x2 = second (each an op list writing that register)."""
    m = _arm()
    m.ins(*first(X1R), *second(X2R))
    return m


GLOBAL_A = lambda r: [op("COPY", r, C(0x111030, 8))]                     # &g_a (adrp + add folded)
GLOBAL_B = lambda r: [op("COPY", r, C(0x111034, 8))]                     # &g_b, another object
LOCAL_U = lambda r: [op("INT_ADD", r, SPV, C(8, 8))]                     # &u
LOCAL_V = lambda r: [op("INT_ADD", r, SPV, C(12, 8))]                    # &v, another object
SAME_BASE_ELEMENT = lambda r: [op("INT_ADD", r, X1R, C(12, 8))]          # derived from x1


@pytest.mark.parametrize("first, second", [
    (GLOBAL_A, GLOBAL_B), (LOCAL_U, LOCAL_V), (GLOBAL_A, LOCAL_V),
    # derived from the same register: still not shown to be one object (a compiler
    # may address one global or local from another's address)
    (GLOBAL_A, SAME_BASE_ELEMENT), (LOCAL_U, SAME_BASE_ELEMENT),
], ids=["two-globals", "two-locals", "global-local", "global-derived", "local-derived"])
@pytest.mark.parametrize("use", ["difference", "less", "less-equal", "signed-less", "equal", "not-equal", "cmp-flags"])
def test_two_addresses_are_never_compared_or_subtracted_without_a_mark(first, second, use):
    m = _two(first, second)
    if use == "difference":
        # (long)((uintptr_t)q - (uintptr_t)p), returned
        m.ins(op("INT_SUB", X0R, X2R, X1R))
        _, observed = _returned(m)
        assert observed.reliable_low_bytes == 0 and observed.unreliable == ("ADDRESS_BITS",)
        return
    mnemonic = {"less": "INT_LESS", "less-equal": "INT_LESSEQUAL", "signed-less": "INT_SLESS",
                "equal": "INT_EQUAL", "not-equal": "INT_NOTEQUAL"}.get(use)
    if mnemonic is not None:
        m.ins(op(mnemonic, U(0x20, 1), X1R, X2R), op("CBRANCH", None, C(0x2000, 8), U(0x20, 1)))
    else:
        # AArch64 ``cmp x1, x2; b.lt``: flags from the difference and the borrow
        m.ins(op("INT_SUB", U(0x30, 8), X1R, X2R), op("INT_SLESS", U(0x22, 1), U(0x30, 8), C(0, 8)),
              op("INT_SBORROW", U(0x23, 1), X1R, X2R), op("BOOL_XOR", U(0x24, 1), U(0x22, 1), U(0x23, 1)),
              op("CBRANCH", None, C(0x2000, 8), U(0x24, 1)))
    m.ins(op("COPY", X0R, C(1, 8)))
    result, _ = _returned(m)
    assert set(result.hazard_kinds()) == {BITS}


def test_a_comparison_value_of_two_addresses_returned_is_not_reliable():
    # ``return &g_b < &g_a`` computed without a branch (cset)
    m = _two(GLOBAL_A, GLOBAL_B)
    m.ins(op("INT_LESS", U(0x20, 1), X2R, X1R), op("INT_ZEXT", X0R, U(0x20, 1)))
    _, observed = _returned(m)
    assert observed.reliable_low_bytes == 0 and observed.unreliable == ("ADDRESS_BITS",)


def test_a_pointer_loop_bound_is_refused_where_it_decides_a_branch():
    # ``for (p = buf; p != end; ++p)``: one object in the source, two addresses in
    # the binary -- refused (a lost witness, never a wrong one)
    m = _arm()
    m.ins(op("INT_ADD", X1R, SPV, C(8, 8)), op("INT_ADD", X2R, X1R, C(32, 8)))
    m.ins(op("INT_NOTEQUAL", U(0x20, 1), X1R, X2R), op("CBRANCH", None, C(0x2000, 8), U(0x20, 1)))
    m.ins(op("COPY", X0R, C(1, 8)))
    result, _ = _returned(m)
    assert set(result.hazard_kinds()) == {BITS}


@pytest.mark.parametrize("operand", [
    lambda r: [op("INT_ADD", r, X1R, C(4, 8))],             # p + 4 == 0 is not a null test
    lambda r: [op("INT_AND", r, X1R, C(0xFFFFFFFF, 8))],    # neither are bits of p
])
def test_only_an_unmodified_pointer_compared_with_zero_is_a_null_test(operand):
    m = _arm()
    m.ins(op("COPY", X1R, C(GLOBAL, 8)), *operand(X2R))
    m.ins(op("INT_EQUAL", U(0x20, 1), X2R, C(0, 8)), op("CBRANCH", None, C(0x2000, 8), U(0x20, 1)))
    m.ins(op("COPY", X0R, C(1, 8)))
    result, _ = _returned(m)
    # p + 4 stays a pointer (the test is then a null test of a pointer value);
    # masked bits are not a pointer and the branch is a hazard
    if operand(X2R)[0].mnemonic == "INT_AND":
        assert set(result.hazard_kinds()) == {BITS}
    else:
        assert result.hazards == ()


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
    # (Before the review fix this test subtracted two pointers, which no longer clears.)
    zero = R(0x0, 8)
    s8 = R(0xF0, 8)
    m = Machine([("a0", 0)], observe=("v0",), big_endian=True, processor="MIPS",
                image_ranges=IMAGE, address_registers=(("sp", STACK),))
    msp = R(0xE8, 8)
    m.write(zero, 0)
    m.ins(op("INT_OR", s8, msp, zero))
    m.ins(op("INT_ADD", U(0x10, 8), s8, C(8, 8)), op("COPY", R(V0.offset, 8), U(0x10, 8)))
    result = m.ret()
    # the copy through ``or`` kept the pointer: still a stack address, not bits
    assert result.address_provenance_tracked and result.observed("v0").unreliable == ("STACK_ADDRESS",)
    m = Machine([("a0", 0x4)], observe=("v0",), big_endian=True, processor="MIPS",
                image_ranges=IMAGE, address_registers=(("sp", STACK),))
    m.ins(op("INT_OR", s8, msp, R(0x20, 8)))
    m.ins(op("COPY", R(V0.offset, 8), s8))
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

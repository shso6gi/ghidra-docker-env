# -*- coding: utf-8 -*-
"""Issue #327 (E2): the callers' demanded bits of the return registers (E-b).

The engine reads raw P-code as data; these synthetic regions pin each rule
against the counterexamples the PoC found (#327 issuecomment-7207552713):
a shift amount computed in a temporary, a store that copies padding, a
narrowing that drops high bits, interprocedural register allocation.
"""

from scripts.function_tracer_pcode.ghidra.return_use_evidence import (
    CallsiteDemand,
    Op,
    ReturnUseEvidence,
    Vn,
    demanded_bits,
    fold_constants,
    own_write,
    prefix_bits,
    producer_limit,
)

X0 = Vn("register", 0x4000, 8, "x0")
W0 = Vn("register", 0x4000, 4, "w0")
X1 = Vn("register", 0x4008, 8, "x1")
W1 = Vn("register", 0x4008, 4, "w1")
SP = Vn("register", 0x8, 8, "sp")
FLAG = Vn("register", 0x100, 1, "ZR")
GLOBAL = Vn("register", 0x4010, 8, "x2")   # an address that is not a stack slot


def c(value, size=4):
    return Vn("const", value, size)


def u(offset, size=4):
    return Vn("unique", offset, size)


def demand_of(ops, vn=X0, big_endian=False):
    return demanded_bits(ops, big_endian).get(vn)


def test_a_comparison_demands_every_bit_of_its_operand():
    ops = [Op("INT_EQUAL", FLAG, (W0, c(0))), Op("CBRANCH", None, (c(0x10, 8), FLAG))]
    assert prefix_bits(demand_of(ops)) == 32


def test_a_shift_amount_computed_from_constants_is_folded_not_treated_as_variable():
    # the processor specification computes ``64 - 3`` in a temporary before shifting (ubfx x1, x0, #3, #13)
    ops = [
        Op("INT_SUB", u(0x10, 8), (c(0x40, 8), c(3, 8))),
        Op("INT_RIGHT", u(0x20, 8), (X0, c(3, 8))),
        Op("INT_AND", X1, (u(0x20, 8), c(0x1FFF, 8))),
        Op("INT_EQUAL", FLAG, (X1, c(0, 8))),
        Op("CBRANCH", None, (c(0x10, 8), FLAG)),
    ]
    assert fold_constants(ops)[0] == (0x40, 3)
    mask = demand_of(ops)
    assert mask == 0x1FFF << 3            # exactly bits 3..15
    assert prefix_bits(mask) == 0         # nothing from bit 0


def test_a_variable_shift_amount_folded_from_a_temporary_is_exact():
    ops = [
        Op("INT_SUB", u(0x10, 4), (c(0x20, 4), c(0x18, 4))),       # 8
        Op("INT_LEFT", u(0x20, 4), (W0, u(0x10, 4))),               # w0 << 8
        Op("INT_EQUAL", FLAG, (u(0x20, 4), c(0))),
        Op("CBRANCH", None, (c(0x10, 8), FLAG)),
    ]
    assert demand_of(ops) == 0x00FFFFFF   # the top 8 bits are shifted out


def test_a_store_is_a_copy_not_a_sink():
    # copying a small aggregate register to memory copies its padding too
    ops = [Op("STORE", None, (c(0, 8), GLOBAL, W0))]
    assert demand_of(ops) == 0
    ops = [Op("STORE", None, (c(0, 8), SP, W0))]   # a stack slot never read back
    assert demand_of(ops) == 0


def test_a_stack_slot_read_back_carries_only_the_reloaded_bytes():
    slot = u(0x30, 8)
    ops = [
        Op("INT_ADD", slot, (SP, c(16, 8))),
        Op("STORE", None, (c(0, 8), slot, W0)),          # spill the whole 4-byte value
        Op("INT_ADD", u(0x38, 8), (SP, c(16, 8))),
        Op("LOAD", u(0x40, 1), (c(0, 8), u(0x38, 8))),   # read back one byte (a char member)
        Op("INT_EQUAL", FLAG, (u(0x40, 1), c(7, 1))),
        Op("CBRANCH", None, (c(0x10, 8), FLAG)),
    ]
    assert demand_of(ops) == 0xFF


def test_a_store_to_an_unknown_address_forgets_the_tracked_slots():
    slot = u(0x30, 8)
    ops = [
        Op("STORE", None, (c(0, 8), SP, W0)),
        Op("STORE", None, (c(0, 8), GLOBAL, W1)),        # may alias the slot
        Op("LOAD", u(0x40, 4), (c(0, 8), SP)),
        Op("INT_EQUAL", FLAG, (u(0x40, 4), c(7))),
        Op("CBRANCH", None, (c(0x10, 8), FLAG)),
    ]
    assert demand_of(ops) == 0
    assert slot  # (the slot name only documents the shape)


def test_arithmetic_then_narrowing_demands_only_the_low_bits():
    # vsc = (signed char)(f() + 1): a 32-bit add whose result is truncated to one byte
    ops = [
        Op("INT_ADD", u(0x10), (W0, c(1))),
        Op("SUBPIECE", u(0x20, 1), (u(0x10), c(0))),
        Op("INT_EQUAL", FLAG, (u(0x20, 1), c(5, 1))),
        Op("CBRANCH", None, (c(0x10, 8), FLAG)),
    ]
    assert demand_of(ops) == 0xFF


def test_a_mask_demands_only_its_bits_and_a_sign_extension_its_sign_bit():
    ops = [Op("INT_AND", u(0x10), (W0, c(0xFF))), Op("INT_EQUAL", FLAG, (u(0x10), c(1))),
           Op("CBRANCH", None, (c(0x10, 8), FLAG))]
    assert demand_of(ops) == 0xFF
    ops = [Op("SUBPIECE", u(0x10, 1), (W0, c(0))), Op("INT_SEXT", u(0x20), (u(0x10, 1),)),
           Op("INT_SLESS", FLAG, (u(0x20), c(5))), Op("CBRANCH", None, (c(0x10, 8), FLAG))]
    assert demand_of(ops) == 0xFF


def test_an_unmodelled_op_or_a_value_leaving_the_region_demands_nothing():
    ops = [Op("CALLOTHER", u(0x10), (c(1), W0)), Op("INT_EQUAL", FLAG, (u(0x10), c(1))),
           Op("CBRANCH", None, (c(0x10, 8), FLAG))]
    assert demand_of(ops) == 0
    ops = [Op("COPY", X1, (X0,)), Op("RETURN", None, (c(0, 8),))]   # the caller returns it
    assert demand_of(ops) == 0
    ops = [Op("CALL", None, (c(0x900, 8),))]                          # passed to another call
    assert demand_of(ops) == 0


def test_a_big_endian_register_low_part_maps_to_its_high_address():
    v0 = Vn("register", 0x10, 8, "v0")
    v0_lo = Vn("register", 0x14, 4, "v0_lo")
    ops = [Op("INT_EQUAL", FLAG, (v0_lo, c(0))), Op("CBRANCH", None, (c(0x10, 8), FLAG))]
    assert demanded_bits(ops, True).get(v0) == 0xFFFFFFFF


def test_own_write_counts_the_callees_instructions_not_its_calls():
    # interprocedural register allocation: a call inside the callee does not prove it clobbers x0
    assert not own_write([Op("CALL", None, (c(0x900, 8),)), Op("COPY", X1, (W0,))], X0)
    assert own_write([Op("INT_ZEXT", X0, (u(0x10),))], X0)
    assert own_write([Op("COPY", W0, (c(3),))], X0)


def test_the_return_path_limit_follows_extensions_and_masks_in_the_block():
    block = [Op("INT_AND", u(0x10), (W1, c(0xFF))), Op("INT_ZEXT", X0, (u(0x10),)),
             Op("RETURN", None, (c(0, 8),))]
    assert producer_limit(block, 2, X0) == 8
    block = [Op("INT_ADD", u(0x10), (W1, c(1))), Op("INT_ZEXT", X0, (u(0x10),)), Op("RETURN", None, (c(0, 8),))]
    assert producer_limit(block, 2, X0) == 32      # a 32-bit write: no value-width knowledge
    assert producer_limit([Op("RETURN", None, (c(0, 8),))], 0, X0) is None   # defined outside the block
    block = [Op("INT_SLESS", FLAG, (W1, c(3))), Op("INT_ZEXT", X0, (FLAG,)), Op("RETURN", None, (c(0, 8),))]
    assert producer_limit(block, 2, X0) == 1


def test_the_record_is_plain_ordered_data():
    record = ReturnUseEvidence(
        "SCANNED", (("FP", "z0"), ("INT", "x0")), "", (("FP", False), ("INT", True)),
        (CallsiteDemand(0x200, 0x100, "CBRANCH", (("FP", 0), ("INT", 0xFFFFFFFF))),), False,
        (("FP", (None,)), ("INT", (32,))),
    ).to_json()
    assert record["status"] == "SCANNED" and record["own_writes"] == {"FP": False, "INT": True}
    assert record["callsites"][0]["demand"]["INT"] == 0xFFFFFFFF

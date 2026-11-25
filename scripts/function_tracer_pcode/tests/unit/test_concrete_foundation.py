# -*- coding: utf-8 -*-
"""Concrete-execution foundation: ABI models, input surface, observation, comparison.

Pure Python.  The cases are the facts measured while prototyping concrete
replay on EqBench binaries (MIPS n64 narrow integers, cross-ABI argument
order, 16-byte AArch64 FP return locations, NaN payloads).
"""
import dataclasses
import struct

import pytest

from scripts.function_tracer_pcode.concrete.abi import (
    ELF_FORMAT,
    AbiId,
    ArgClass,
    ArgumentSlot,
    NarrowIntImage,
    NarrowIntRule,
    abi_model,
    select_abi,
)
from scripts.function_tracer_pcode.concrete.comparison import (
    ConcreteDifference,
    ConcreteNoEvidence,
    NoEvidenceReason,
    compare_runs,
)
from scripts.function_tracer_pcode.concrete.executor import (
    DEFAULT_RETURN_ADDRESS,
    DEFAULT_STACK_POINTER,
    ExecutionResult,
    Hazard,
    HazardKind,
    Termination,
    build_entry_state,
)
from scripts.function_tracer_pcode.concrete.input_surface import (
    InputCorrespondence,
    InputSurfaceRefusal,
    SideInputSurface,
    bind_arguments,
    correspond_inputs,
    side_input_surface,
)
from scripts.function_tracer_pcode.concrete.observation import (
    FpFormat,
    ObservationRefusal,
    ObservationRelation,
    ObservedRegister,
    ReturnStorage,
    compare_return_values,
    plan_return_observation,
    return_location,
)
from scripts.function_tracer_pcode.concrete.storage import StorageLocation

ARM = abi_model(AbiId.AARCH64_AAPCS64)
MIPS = abi_model(AbiId.MIPS_N64)


def _arm_int(n, size=4):
    return StorageLocation(True, f"w{n}" if size < 8 else f"x{n}", f"x{n}", 8, 0, size)


def _arm_fp(n, size=8):
    return StorageLocation(True, {4: "s", 8: "d", 16: "q"}[size] + str(n), f"z{n}", 32, 0, size)


def _mips_int(n, size=4, name=None):
    # Big-endian: the low-order bytes of a register are at its highest addresses.
    register = f"a{n}" if n < 4 else f"t{n - 4}"
    return StorageLocation(True, name or (register if size == 8 else register + "_lo"), register, 8, 8 - size, size)


def _mips_fp(n, size=8):
    return StorageLocation(True, f"f{12 + n}", f"f{12 + n}", 8, 8 - size, size)


def _surface(abi, *parameters) -> SideInputSurface:
    surface = side_input_surface(abi, parameters)
    assert isinstance(surface, SideInputSurface), surface
    return surface


def _double_bits(value: float) -> int:
    return struct.unpack(">Q", struct.pack(">d", value))[0]


# ---------------------------------------------------------------- ABI models

def test_select_abi_is_exact_on_language_compiler_spec_and_format():
    assert select_abi("AARCH64:LE:64:v8A", "default", ELF_FORMAT) is ARM
    assert select_abi("MIPS:BE:64:default", "default", ELF_FORMAT) is MIPS
    # The same processors under other conventions are not the modelled ABI.
    for language, spec, fmt in [
        ("AARCH64:LE:64:v8A", "golang", ELF_FORMAT),
        ("AARCH64:LE:64:v8A", "windows", "Portable Executable (PE)"),
        ("AARCH64:LE:64:AppleSilicon", "default", "Mac OS X Mach-O"),
        ("AARCH64:LE:64:v8A", "default", "Mac OS X Mach-O"),
        ("AARCH64:BE:64:v8A", "default", ELF_FORMAT),
        ("AARCH64:LE:32:ilp32", "default", ELF_FORMAT),
        ("MIPS:BE:64:64-32addr", "n32", ELF_FORMAT),
        ("MIPS:BE:64:64-32addr", "default", ELF_FORMAT),
        ("MIPS:LE:64:default", "default", ELF_FORMAT),
        ("MIPS:LE:64:default", "windows", ELF_FORMAT),
        ("MIPS:BE:64:micro", "default", ELF_FORMAT),
        ("MIPS:BE:64:R6", "default", ELF_FORMAT),
        ("MIPS:BE:64:default", "default", "Raw Binary"),
        ("x86:LE:64:default", "gcc", ELF_FORMAT),
    ]:
        assert select_abi(language, spec, fmt) is None, (language, spec, fmt)


def test_select_abi_refuses_a_function_marked_with_another_convention():
    arm = ("AARCH64:LE:64:v8A", "default", ELF_FORMAT)
    mips = ("MIPS:BE:64:default", "default", ELF_FORMAT)
    for name in ("unknown", "default", "__cdecl"):
        assert select_abi(*arm, calling_convention=name) is ARM
    for name in ("unknown", "default", "__stdcall"):
        assert select_abi(*mips, calling_convention=name) is MIPS
    assert select_abi(*arm, calling_convention="__stdcall") is None
    assert select_abi(*arm, calling_convention="processEntry") is None
    assert select_abi(*mips, calling_convention="__cdecl") is None


def test_mips_n64_integer_argument_registers_use_the_processor_modules_names():
    # Ghidra's MIPS module keeps the o32 names for $8-$11: the fifth to eighth n64
    # integer arguments are t0-t3 there (mips64be.cspec lists a0-a3, t0-t3).
    assert MIPS.int_argument_registers == ("a0", "a1", "a2", "a3", "t0", "t1", "t2", "t3")
    assert MIPS.argument_slot_of("t0") == ArgumentSlot(ArgClass.INT, 4)
    assert MIPS.argument_slot_of("a4") is None


def test_slot_assignment_follows_each_abis_numbering():
    classes = (ArgClass.INT, ArgClass.INT, ArgClass.FP)
    assert ARM.assign_slots(classes) == (
        ArgumentSlot(ArgClass.INT, 0), ArgumentSlot(ArgClass.INT, 1), ArgumentSlot(ArgClass.FP, 0),
    )
    assert MIPS.assign_slots(classes) == (
        ArgumentSlot(ArgClass.INT, 0), ArgumentSlot(ArgClass.INT, 1), ArgumentSlot(ArgClass.FP, 2),
    )
    assert MIPS.argument_register(ArgumentSlot(ArgClass.FP, 2)) == "f14"
    assert MIPS.argument_register(ArgumentSlot(ArgClass.INT, 5)) == "t1"
    assert ARM.assign_slots((ArgClass.INT,) * 9) is None  # the ninth goes to the stack


def test_no_register_has_two_roles_in_one_abi():
    for abi in (ARM, MIPS):
        arguments = set(abi.int_argument_registers) | set(abi.fp_argument_registers)
        state = set(abi.callee_saved_registers) | {abi.stack_pointer, abi.return_address_register}
        assert not arguments & state
        assert len(arguments) == len(abi.int_argument_registers) + len(abi.fp_argument_registers)


# ------------------------------------------------------------- input surface

def test_side_surface_refuses_what_it_cannot_place():
    stack = StorageLocation(False, None, None, 0, 0, 8)
    assert side_input_surface(ARM, [stack]) is InputSurfaceRefusal.PARAMETER_NOT_IN_REGISTER
    assert (
        side_input_surface(ARM, [StorageLocation(True, "x8", "x8", 8, 0, 8)])
        is InputSurfaceRefusal.PARAMETER_REGISTER_NOT_AN_ARGUMENT_SLOT
    )
    # The high half of a MIPS register is not an argument.
    assert (
        side_input_surface(MIPS, [StorageLocation(True, "a1_hi", "a1", 8, 0, 4)])
        is InputSurfaceRefusal.PARAMETER_NOT_LOW_PART_OF_REGISTER
    )
    assert (
        side_input_surface(MIPS, [StorageLocation(True, "f12", "f12", 8, 0, 16)])
        is InputSurfaceRefusal.PARAMETER_WIDTH_UNSUPPORTED
    )
    assert (
        side_input_surface(ARM, [_arm_int(0), _arm_int(0, 8)])
        is InputSurfaceRefusal.DUPLICATE_ARGUMENT_SLOT
    )


def test_a_narrowed_type_on_a_whole_register_is_the_whole_register():
    # Measured: after a type hypothesis an `int` parameter is recorded as the base
    # register `a0` itself with size 4; its offset is the register's start, which on a
    # big-endian processor would otherwise read as the high half.
    whole = side_input_surface(MIPS, [StorageLocation(True, "a1", "a1", 8, 0, 4)])
    assert isinstance(whole, SideInputSurface) and whole.readings[0].width_bytes == 4


def test_the_position_of_a_piece_is_exact_not_that_of_its_containing_register():
    # Measured: a 1-byte value in the lowest-order byte of v0 (address v0+7) has no
    # register of its own size; the register found for it is v0_lo, which starts at v0+4.
    low_byte = StorageLocation(True, "v0_lo", "v0", 8, 7, 1)
    assert low_byte.is_low_order_part(big_endian=True)
    assert not StorageLocation(True, "v0_lo", "v0", 8, 4, 1).is_low_order_part(big_endian=True)
    assert StorageLocation(True, "w0", "x0", 8, 0, 1).is_low_order_part(big_endian=False)
    assert not StorageLocation(True, "w0", "x0", 8, 4, 4).is_low_order_part(big_endian=False)


def test_storage_location_is_built_from_exact_storage_offsets():
    class Storage:  # the fields of core.storage.StorageInfo this layer reads
        is_register = True
        register_name = "v0_lo"
        base_register_name = "v0"
        base_register_size_bits = 64
        offset = 0x17
        base_register_offset = 0x10
        size = 1

    location = StorageLocation.from_storage_info(Storage())
    assert location == StorageLocation(True, "v0_lo", "v0", 8, 7, 1)
    assert StorageLocation.from_storage_info(Storage(), size_bytes=4).size_bytes == 4


def test_same_abi_correspondence_is_by_register_and_keeps_every_reading():
    left = _surface(MIPS, _mips_int(0, 8), _mips_int(1, 4))
    right = _surface(MIPS, _mips_int(0, 4))          # the second parameter was optimised away
    assert _surface(MIPS, _mips_int(5)).readings[0].slot == ArgumentSlot(ArgClass.INT, 5)
    correspondence = correspond_inputs(left, right)
    assert isinstance(correspondence, InputCorrespondence)
    first, second = correspondence.arguments
    assert first.slots == (ArgumentSlot(ArgClass.INT, 0),) * 2 and first.readings == (4, 8)
    assert second.slots == (ArgumentSlot(ArgClass.INT, 1),) * 2 and second.readings == (4,)


def test_cross_abi_correspondence_reads_the_order_off_the_positional_side():
    # int f(int, int, double): MIPS a0, a1, f14  <->  AArch64 x0, x1, v0
    mips = _surface(MIPS, _mips_int(0), _mips_int(1), _mips_fp(2))
    arm = _surface(ARM, _arm_fp(0), _arm_int(0), _arm_int(1))
    for left, right, m in ((mips, arm, 0), (arm, mips, 1)):
        correspondence = correspond_inputs(left, right)
        assert isinstance(correspondence, InputCorrespondence)
        classes = [a.arg_class for a in correspondence.arguments]
        assert classes == [ArgClass.INT, ArgClass.INT, ArgClass.FP]
        third = correspondence.arguments[2]
        assert third.slots[m] == ArgumentSlot(ArgClass.FP, 2)
        assert third.slots[1 - m] == ArgumentSlot(ArgClass.FP, 0)


def test_cross_abi_correspondence_refuses_gaps_and_disagreement():
    arm_two = _surface(ARM, _arm_int(0), _arm_int(1))
    gap = _surface(MIPS, _mips_int(0), _mips_int(2))
    assert correspond_inputs(gap, arm_two) is InputSurfaceRefusal.CROSS_ABI_POSITIONS_NOT_CONTIGUOUS
    one = _surface(MIPS, _mips_int(0))
    assert correspond_inputs(one, arm_two) is InputSurfaceRefusal.CROSS_ABI_SLOTS_DISAGREE
    fp_instead = _surface(MIPS, _mips_int(0), _mips_fp(1))
    assert correspond_inputs(fp_instead, arm_two) is InputSurfaceRefusal.CROSS_ABI_SLOTS_DISAGREE


def test_two_different_abis_without_a_positional_side_have_no_common_order():
    # Not reachable with the two modelled ABIs; a second per-class ABI shows the rule.
    other = dataclasses.replace(ARM, abi_id=AbiId.MIPS_N64)
    left = _surface(ARM, _arm_int(0))
    right = SideInputSurface(other, left.readings)
    assert correspond_inputs(left, right) is InputSurfaceRefusal.CROSS_ABI_NUMBERING_UNSUPPORTED


def test_a_32bit_integer_is_written_in_each_abis_own_extension():
    # Measured: writing 0x80000000 zero-extended into a MIPS n64 register made the
    # emulator disagree with the real machine (the entry state was not conforming).
    # AAPCS64 leaves the upper bits unspecified and Ghidra's AArch64 compiler
    # specification declares zero extension, so the AArch64 image is zero-extended.
    assert MIPS.narrow_int_rule is NarrowIntRule.SIGN_EXTENDED_REQUIRED
    assert MIPS.narrow_int_image is NarrowIntImage.SIGN_EXTENDED
    assert ARM.narrow_int_rule is NarrowIntRule.UPPER_BITS_UNSPECIFIED
    assert ARM.narrow_int_image is NarrowIntImage.ZERO_EXTENDED
    correspondence = correspond_inputs(_surface(MIPS, _mips_int(0)), _surface(ARM, _arm_int(0)))
    (mips_image,), (arm_image,) = bind_arguments(correspondence, [0x80000000])
    assert mips_image.register == "a0" and mips_image.value == 0xFFFFFFFF80000000
    assert arm_image.register == "x0" and arm_image.value == 0x0000000080000000
    (mips_image,), (arm_image,) = bind_arguments(correspondence, [5])
    assert mips_image.value == 5 and arm_image.value == 5


def test_an_aarch64_argument_read_as_int_and_long_needs_one_image_for_both():
    # Zero-extended as an int, sign-extended as a long: a value with bit 31 set has
    # no image that is the same argument under both readings.
    correspondence = correspond_inputs(_surface(ARM, _arm_int(0, 4)), _surface(ARM, _arm_int(0, 8)))
    assert correspondence.arguments[0].readings == (4, 8)
    assert (
        bind_arguments(correspondence, [0xFFFFFFFFFFFFFFFF])
        is InputSurfaceRefusal.VALUE_NOT_CONFORMING_UNDER_EVERY_READING
    )
    assert bind_arguments(correspondence, [0x7FFFFFFF])[0][0].value == 0x7FFFFFFF
    # Read as int on both sides, -1 is the zero-extended image.
    narrow = correspond_inputs(_surface(ARM, _arm_int(0, 4)), _surface(ARM, _arm_int(0, 4)))
    assert bind_arguments(narrow, [0xFFFFFFFF])[0][0].value == 0x00000000FFFFFFFF


def test_a_value_must_conform_under_every_width_reading():
    # One signature says 4 bytes, the other 8: only images that are the same
    # argument under both readings are admitted.
    correspondence = correspond_inputs(
        _surface(MIPS, _mips_int(0, 4)), _surface(MIPS, _mips_int(0, 8))
    )
    assert correspondence.arguments[0].readings == (4, 8)
    images = bind_arguments(correspondence, [0xFFFFFFFFFFFFFFFF])       # -1 under both
    assert images[0][0].value == 0xFFFFFFFFFFFFFFFF
    assert (
        bind_arguments(correspondence, [0x0000000080000000])            # 2^31 as long, INT_MIN as int
        is InputSurfaceRefusal.VALUE_NOT_CONFORMING_UNDER_EVERY_READING
    )
    assert (
        bind_arguments(correspondence, [0x0000000100000000])
        is InputSurfaceRefusal.VALUE_NOT_CONFORMING_UNDER_EVERY_READING
    )
    wide = correspond_inputs(_surface(MIPS, _mips_int(0, 8)), _surface(MIPS, _mips_int(0, 8)))
    assert bind_arguments(wide, [0x0000000100000000])[0][0].value == 0x0000000100000000


def test_sub_int_readings_admit_only_values_whose_promotions_agree():
    correspondence = correspond_inputs(_surface(ARM, _arm_int(0, 1)), _surface(ARM, _arm_int(0, 1)))
    assert bind_arguments(correspondence, [0x7F])[0][0].value == 0x7F
    assert (
        bind_arguments(correspondence, [0x80])
        is InputSurfaceRefusal.VALUE_NOT_CONFORMING_UNDER_EVERY_READING
    )
    assert bind_arguments(correspondence, [0x100]) is InputSurfaceRefusal.VALUE_WIDER_THAN_REGISTER


def test_fp_arguments_take_any_bit_pattern():
    correspondence = correspond_inputs(_surface(MIPS, _mips_fp(0)), _surface(ARM, _arm_fp(0)))
    nan = 0x7FF0000000000001
    (mips_image,), (arm_image,) = bind_arguments(correspondence, [nan])
    assert (mips_image.register, mips_image.value) == ("f12", nan)
    assert (arm_image.register, arm_image.register_bytes, arm_image.value) == ("z0", 16, nan)
    assert MIPS.argument_slot_of("f12") == ArgumentSlot(ArgClass.FP, 0)


# ----------------------------------------------------------------- entry state

def test_entry_state_defines_only_what_the_abi_defines():
    correspondence = correspond_inputs(_surface(MIPS, _mips_int(0)), _surface(MIPS, _mips_int(0)))
    (image,), _ = bind_arguments(correspondence, [7])
    state = build_entry_state(MIPS, 0x120000A70, (image,))
    registers = state.register_map()
    assert registers["sp"] == DEFAULT_STACK_POINTER and registers["ra"] == DEFAULT_RETURN_ADDRESS
    assert registers["t9"] == 0x120000A70          # PIC entry address
    assert registers["a0"] == 7 and registers["fcsr"] == 0
    assert set(MIPS.callee_saved_registers) <= set(registers)
    # Unbound argument registers and scratch registers stay undefined.
    assert "a1" not in registers and "v0" not in registers and "f12" not in registers
    saved = [registers[name] for name in MIPS.callee_saved_registers]
    assert len(set(saved)) == len(saved)

    arm_state = build_entry_state(ARM, 0x100000, ()).register_map()
    assert "x30" in arm_state and "x0" not in arm_state and "z0" not in arm_state


# ------------------------------------------------------------------ observation

def _ret(location, is_void=False, count=1):
    return ReturnStorage(is_void, (location,) * count)


ARM_W0 = StorageLocation(True, "w0", "x0", 8, 0, 4)
ARM_X0 = StorageLocation(True, "x0", "x0", 8, 0, 8)
ARM_S0 = StorageLocation(True, "s0", "z0", 32, 0, 4)
ARM_D0 = StorageLocation(True, "d0", "z0", 32, 0, 8)
ARM_Q0 = StorageLocation(True, "q0", "z0", 32, 0, 16)
MIPS_V0 = StorageLocation(True, "v0", "v0", 8, 0, 8)
MIPS_V0_LO = StorageLocation(True, "v0_lo", "v0", 8, 4, 4)
MIPS_F0 = StorageLocation(True, "f0", "f0", 8, 0, 8)
MIPS_F0_LO = StorageLocation(True, "f0_lo", "f0", 8, 4, 4)


def _plan_for(abi_left, left, abi_right=None, right=None):
    plan = plan_return_observation(
        return_location(abi_left, _ret(left)),
        return_location(abi_right or abi_left, _ret(right or left)),
    )
    assert not isinstance(plan, ObservationRefusal), plan
    return plan


def _seen(value, defined=16, fmt=None, reliable=16):
    return ObservedRegister(value, defined, fmt, reliable)


B32, B64 = FpFormat.BINARY32, FpFormat.BINARY64


def test_return_location_refusals():
    assert return_location(ARM, _ret(ARM_W0, is_void=True)) is ObservationRefusal.RETURN_VOID
    assert return_location(ARM, _ret(ARM_W0, count=2)) is ObservationRefusal.RETURN_NOT_SINGLE_LOCATION
    assert return_location(ARM, ReturnStorage(False, ())) is ObservationRefusal.RETURN_NOT_SINGLE_LOCATION
    assert (
        return_location(ARM, _ret(StorageLocation(False, None, None, 0, 0, 8)))
        is ObservationRefusal.RETURN_NOT_IN_REGISTER
    )
    assert (
        return_location(ARM, _ret(StorageLocation(True, "x1", "x1", 8, 0, 8)))
        is ObservationRefusal.RETURN_REGISTER_NOT_A_RETURN_REGISTER
    )
    assert (
        return_location(MIPS, _ret(StorageLocation(True, "v0_hi", "v0", 8, 0, 4)))
        is ObservationRefusal.RETURN_NOT_LOW_PART_OF_REGISTER
    )
    assert (
        return_location(MIPS, _ret(StorageLocation(True, "f0", "f0", 8, 0, 16)))
        is ObservationRefusal.RETURN_WIDTH_UNSUPPORTED
    )


def test_a_one_byte_mips_return_is_the_low_part():
    # Measured (`bool` returns): the decompiler places the value at v0+7, size 1.
    location = return_location(MIPS, _ret(StorageLocation(True, "v0_lo", "v0", 8, 7, 1)))
    assert location.arg_class is ArgClass.INT and location.width_bytes == 1


def test_integer_returns_are_compared_on_the_narrower_width():
    plan = _plan_for(ARM, ARM_W0, MIPS, MIPS_V0)
    assert plan.arg_class is ArgClass.INT and plan.narrowed
    # -1 as int: AArch64 leaves the upper half zero, MIPS sign-extends.
    assert (
        compare_return_values(plan, _seen(0x00000000FFFFFFFF), _seen(0xFFFFFFFFFFFFFFFF))
        is ObservationRelation.NOT_DIFFERENT_ON_OBSERVED_PART
    )
    assert compare_return_values(plan, _seen(13), _seen(14)) is ObservationRelation.DIFFERENT


def test_only_defined_bytes_of_an_integer_return_are_compared():
    plan = _plan_for(MIPS, MIPS_V0)
    left, right = 0x1111111100000005, 0x2222222200000005
    assert compare_return_values(plan, _seen(left, 8), _seen(right, 8)) is ObservationRelation.DIFFERENT
    # One run defined only the low 4 bytes: the rest is not part of what it returned.
    assert (
        compare_return_values(plan, _seen(left, 4), _seen(right, 8))
        is ObservationRelation.NOT_DIFFERENT_ON_OBSERVED_PART
    )
    assert (
        compare_return_values(plan, _seen(left, 0), _seen(right, 8))
        is ObservationRefusal.RETURN_VALUE_NOT_DEFINED
    )


def test_return_classes_must_agree():
    arm_int = return_location(ARM, _ret(ARM_W0))
    arm_fp = return_location(ARM, _ret(ARM_D0))
    assert plan_return_observation(arm_int, arm_fp) is ObservationRefusal.RETURN_CLASS_MISMATCH


def test_fp_values_are_compared_only_in_a_format_the_run_established():
    # AArch64 reports q0 (16 bytes) for most functions that return a double, so the
    # storage width does not say which bytes are the value or what they mean.
    plan = _plan_for(ARM, ARM_Q0)
    one, two = _double_bits(1.0), _double_bits(2.0)
    assert compare_return_values(plan, _seen(one, fmt=B64), _seen(two, fmt=B64)) is ObservationRelation.DIFFERENT
    assert (
        compare_return_values(plan, _seen(one, fmt=B64), _seen(one, fmt=B64))
        is ObservationRelation.NOT_DIFFERENT_ON_OBSERVED_PART
    )
    assert (
        compare_return_values(plan, _seen(0x3F800000, fmt=B32), _seen(0x40000000, fmt=B32))
        is ObservationRelation.DIFFERENT
    )
    # No evidence on one side or on both: the bits are not compared, whatever they are.
    for left, right in (
        (_seen(one), _seen(two)),
        (_seen(one, fmt=B64), _seen(two)),
        (_seen(one), _seen(two, fmt=B64)),
    ):
        assert compare_return_values(plan, left, right) is ObservationRefusal.FP_FORMAT_UNRESOLVED


def test_the_same_number_in_two_formats_is_not_a_difference():
    # binary32 1.0 and binary64 1.0 are different bits and the same number.
    plan = _plan_for(ARM, ARM_Q0)
    assert (
        compare_return_values(plan, _seen(0x3F800000, fmt=B32), _seen(_double_bits(1.0), fmt=B64))
        is ObservationRefusal.FP_FORMAT_UNRESOLVED
    )
    # The shape of a value is not evidence of its format: these bits could be a
    # binary32 1.0 or a tiny binary64, and without evidence they are neither.
    assert (
        compare_return_values(plan, _seen(0x3F800000), _seen(_double_bits(1.0), fmt=B64))
        is ObservationRefusal.FP_FORMAT_UNRESOLVED
    )
    # A binary32 against a wider value whose low half happens to equal it.
    assert (
        compare_return_values(plan, _seen(0x3F800000, fmt=B32), _seen(0x400000003F800000, fmt=B64))
        is ObservationRefusal.FP_FORMAT_UNRESOLVED
    )


def test_format_evidence_must_agree_with_the_recovered_width():
    double_location = _plan_for(MIPS, MIPS_F0)
    assert (
        compare_return_values(double_location, _seen(0x3F800000, 8, B32), _seen(0x40000000, 8, B32))
        is ObservationRefusal.FP_FORMAT_UNRESOLVED
    )
    single_location = _plan_for(MIPS, MIPS_F0_LO)
    assert (
        compare_return_values(single_location, _seen(1, 8, B64), _seen(2, 8, B64))
        is ObservationRefusal.FP_FORMAT_UNRESOLVED
    )
    assert (
        compare_return_values(single_location, _seen(0x3F800000, 8, B32), _seen(0x40000000, 8, B32))
        is ObservationRelation.DIFFERENT
    )
    # A 4-byte location against an 8-byte one never shares a format.
    mixed = _plan_for(ARM, ARM_S0, ARM, ARM_D0)
    assert (
        compare_return_values(mixed, _seen(0x3F800000, fmt=B32), _seen(_double_bits(1.0), fmt=B64))
        is ObservationRefusal.FP_FORMAT_UNRESOLVED
    )
    # A 16-byte location against an 8-byte one (AArch64 q0 and MIPS f0): binary64 on both.
    cross = _plan_for(ARM, ARM_Q0, MIPS, MIPS_F0)
    assert (
        compare_return_values(cross, _seen(_double_bits(1.0), fmt=B64), _seen(_double_bits(2.0), 8, B64))
        is ObservationRelation.DIFFERENT
    )


def test_a_register_holding_more_than_the_scalar_is_not_compared():
    plan = _plan_for(ARM, ARM_Q0)
    one, two = _double_bits(1.0), _double_bits(2.0)
    # Defined bytes above the scalar are not zero: a vector, an aggregate or a binary128.
    assert (
        compare_return_values(plan, _seen((1 << 64) | one, fmt=B64), _seen(two, fmt=B64))
        is ObservationRefusal.FP_FORMAT_UNRESOLVED
    )
    assert (
        compare_return_values(plan, _seen((0x40000000 << 32) | 0x3F800000, fmt=B32), _seen(0x3F800000, fmt=B32))
        is ObservationRefusal.FP_FORMAT_UNRESOLVED
    )
    # Bytes the run did not define are not part of the value.
    assert (
        compare_return_values(plan, _seen((1 << 64) | one, 8, B64), _seen(two, 8, B64))
        is ObservationRelation.DIFFERENT
    )
    assert (
        compare_return_values(plan, _seen(one, 4, B64), _seen(two, fmt=B64))
        is ObservationRefusal.RETURN_VALUE_NOT_DEFINED
    )
    assert (
        compare_return_values(plan, _seen(0x3F800000, 3, B32), _seen(0x40000000, fmt=B32))
        is ObservationRefusal.RETURN_VALUE_NOT_DEFINED
    )


def test_a_nan_is_never_compared():
    # Measured: the emulator returned fff8000000000000 where the machine returned
    # fff0000000000001 (airy SIGN, same source).  A payload difference is not evidence.
    plan = _plan_for(MIPS, MIPS_F0)
    assert (
        compare_return_values(plan, _seen(0xFFF8000000000000, 8, B64), _seen(0xFFF0000000000001, 8, B64))
        is ObservationRefusal.NAN_OBSERVED
    )
    assert (
        compare_return_values(plan, _seen(0x7FF8000000000000, 8, B64), _seen(_double_bits(1.0), 8, B64))
        is ObservationRefusal.NAN_OBSERVED
    )
    infinity = 0x7FF0000000000000
    assert (
        compare_return_values(plan, _seen(infinity, 8, B64), _seen(_double_bits(1.0), 8, B64))
        is ObservationRelation.DIFFERENT
    )
    single = _plan_for(MIPS, MIPS_F0_LO)
    assert (
        compare_return_values(single, _seen(0x7FC00000, 8, B32), _seen(0x3F800000, 8, B32))
        is ObservationRefusal.NAN_OBSERVED
    )
    wide = _plan_for(ARM, ARM_Q0)
    assert (
        compare_return_values(wide, _seen(0x7FC00001, fmt=B32), _seen(0x3F800000, fmt=B32))
        is ObservationRefusal.NAN_OBSERVED
    )


def test_integer_returns_need_no_format_evidence():
    plan = _plan_for(ARM, ARM_W0)
    assert compare_return_values(plan, _seen(13), _seen(14)) is ObservationRelation.DIFFERENT


# ------------------------------------------------------------------- comparison

def _plan():
    return _plan_for(ARM, ARM_W0)


def _returned(value, **kw):
    kw.setdefault("fp_operations_tracked", True)
    kw.setdefault("integer_ub_operations_tracked", True)
    kw.setdefault("address_provenance_tracked", True)
    return ExecutionResult(Termination.RETURNED, 10, (("x0", ObservedRegister(value, 8, None, 8)),), **kw)


def test_two_clean_returns_with_different_values_are_a_difference():
    result = compare_runs(_plan(), _returned(13), _returned(14))
    assert isinstance(result, ConcreteDifference) and result.observed_values == (13, 14)


@pytest.mark.parametrize("termination", [t for t in Termination if t is not Termination.RETURNED])
def test_a_run_that_did_not_return_establishes_nothing(termination):
    stopped = ExecutionResult(termination, 5, (("x0", ObservedRegister(99, 8)),))
    for left, right, side in ((stopped, _returned(1), 0), (_returned(1), stopped, 1)):
        result = compare_runs(_plan(), left, right)
        assert isinstance(result, ConcreteNoEvidence)
        assert result.reason is NoEvidenceReason.RUN_DID_NOT_RETURN
        assert result.side == side and result.termination is termination


@pytest.mark.parametrize("kind", list(HazardKind))
def test_any_hazard_on_either_side_establishes_nothing(kind):
    hazardous = _returned(13, hazards=(Hazard(kind, "x1"),))
    result = compare_runs(_plan(), _returned(14), hazardous)
    assert isinstance(result, ConcreteNoEvidence)
    assert result.reason is NoEvidenceReason.RUN_HAS_HAZARD
    assert result.side == 1 and result.hazard_kinds == (kind,)


def test_equal_values_missing_observations_and_refused_observations_are_no_evidence():
    assert compare_runs(_plan(), _returned(3), _returned(3)).reason is NoEvidenceReason.NO_DIFFERENCE_OBSERVED
    missing = ExecutionResult(Termination.RETURNED, 1, (), fp_operations_tracked=True, integer_ub_operations_tracked=True, address_provenance_tracked=True)
    assert compare_runs(_plan(), _returned(3), missing).reason is NoEvidenceReason.OBSERVATION_MISSING
    fp_plan = _plan_for(MIPS, MIPS_F0)
    nan = ExecutionResult(
        Termination.RETURNED, 1, (("f0", ObservedRegister(0x7FF8000000000000, 8, B64, 8)),),
        fp_operations_tracked=True, integer_ub_operations_tracked=True, address_provenance_tracked=True,
    )
    one = ExecutionResult(
        Termination.RETURNED, 1, (("f0", ObservedRegister(_double_bits(1.0), 8, B64, 8)),),
        fp_operations_tracked=True, integer_ub_operations_tracked=True, address_provenance_tracked=True,
    )
    result = compare_runs(fp_plan, nan, one)
    assert result.reason is NoEvidenceReason.OBSERVATION_REFUSED
    assert result.observation_refusal is ObservationRefusal.NAN_OBSERVED


def test_a_run_whose_fp_operations_were_not_examined_establishes_nothing():
    # The absence of an FP hazard means something only when the executor looked for
    # them; an integer return can depend on floating-point arithmetic too.
    untracked = _returned(13, fp_operations_tracked=False)
    for left, right, side in ((untracked, _returned(14), 0), (_returned(14), untracked, 1)):
        result = compare_runs(_plan(), left, right)
        assert isinstance(result, ConcreteNoEvidence)
        assert result.reason is NoEvidenceReason.FP_OPERATIONS_NOT_TRACKED and result.side == side
    assert ExecutionResult(Termination.RETURNED, 1).fp_operations_tracked is False


def test_a_run_whose_integer_ub_operations_were_not_examined_establishes_nothing():
    # Measured: pow/test (one source, clang -O0 / -O1) returns 13 and 14 for
    # y = INT_MIN on the real machine (signed overflow of -y).  Without the
    # integer-UB monitor such a run is not evidence.
    untracked = _returned(13, integer_ub_operations_tracked=False)
    for left, right, side in ((untracked, _returned(14), 0), (_returned(14), untracked, 1)):
        result = compare_runs(_plan(), left, right)
        assert isinstance(result, ConcreteNoEvidence)
        assert result.reason is NoEvidenceReason.INTEGER_UB_NOT_TRACKED and result.side == side
    assert ExecutionResult(Termination.RETURNED, 1).integer_ub_operations_tracked is False


def test_rounding_sensitive_arithmetic_is_a_hazard_of_the_run():
    # Measured on the target machine: one source (bess/bessk0), gcc -O0 against
    # gcc -O2, returns 40036aa32a3732d7 and 40036aa32a3732d8 for 0.1 -- the -O2 build
    # fuses a multiplication and an addition.  The bits differ; the functions do not.
    assert HazardKind.FP_ROUNDING_SENSITIVE in HazardKind and HazardKind.FP_NAN_OPERAND in HazardKind
    location = return_location(MIPS, _ret(MIPS_F0))
    plan = plan_return_observation(location, location)

    def run(bits, hazards=()):
        return ExecutionResult(
            Termination.RETURNED, 1, (("f0", ObservedRegister(bits, 8, B64, 8)),),
            hazards=hazards, fp_operations_tracked=True, integer_ub_operations_tracked=True, address_provenance_tracked=True,
        )

    fused = (Hazard(HazardKind.FP_ROUNDING_SENSITIVE, "fmadd"),)
    result = compare_runs(plan, run(0x40036AA32A3732D7), run(0x40036AA32A3732D8, fused))
    assert isinstance(result, ConcreteNoEvidence)
    assert result.reason is NoEvidenceReason.RUN_HAS_HAZARD
    assert result.hazard_kinds == (HazardKind.FP_ROUNDING_SENSITIVE,)
    # Without such arithmetic in either run the same bits are a difference.
    assert isinstance(compare_runs(plan, run(0x40036AA32A3732D7), run(0x40036AA32A3732D8)), ConcreteDifference)


def test_only_the_reliable_low_bytes_of_a_return_value_are_compared():
    # C3: the monitors report how many low bytes of each observed register do
    # not depend on an undefined operation or a rounding choice.  A comparison
    # that needs more bytes, or a register without that report, is refused.
    plan = _plan()

    def run(value, reliable, unreliable=()):
        return ExecutionResult(
            Termination.RETURNED, 1, (("x0", ObservedRegister(value, 8, None, reliable, unreliable)),),
            fp_operations_tracked=True, integer_ub_operations_tracked=True, address_provenance_tracked=True,
        )

    assert isinstance(compare_runs(plan, run(13, 4), run(14, 8)), ConcreteDifference)   # w0: 4 bytes
    for reliable in (None, 0, 3):
        result = compare_runs(plan, run(13, reliable, ("SIGNED_OVERFLOW",)), run(14, 8))
        assert result.reason is NoEvidenceReason.OBSERVATION_REFUSED
        assert result.observation_refusal is ObservationRefusal.VALUE_NOT_RELIABLE
    location = return_location(MIPS, _ret(MIPS_F0))
    fp_plan = plan_return_observation(location, location)

    def fp(bits, reliable):
        return ExecutionResult(
            Termination.RETURNED, 1, (("f0", ObservedRegister(bits, 8, B64, reliable)),),
            fp_operations_tracked=True, integer_ub_operations_tracked=True, address_provenance_tracked=True,
        )

    refused = compare_runs(fp_plan, fp(0x40036AA32A3732D7, 0), fp(0x40036AA32A3732D8, 8))
    assert refused.observation_refusal is ObservationRefusal.VALUE_NOT_RELIABLE
    assert isinstance(compare_runs(fp_plan, fp(0x40036AA32A3732D7, 8), fp(0x40036AA32A3732D8, 8)), ConcreteDifference)


def test_rounding_sensitive_values_are_compared_by_their_possible_values_only():
    location = return_location(MIPS, _ret(MIPS_F0))
    plan = plan_return_observation(location, location)
    one, two, nan = 0x3FF0000000000000, 0x4000000000000000, 0x7FF8000000000000

    def fp(bits, values=(), unreliable=("FP_ROUNDING_SENSITIVE",), size=8):
        observed = ObservedRegister(bits, 8, B64, 0 if values or unreliable else 8, unreliable, values, size)
        return ExecutionResult(
            Termination.RETURNED, 1, (("f0", observed),),
            fp_operations_tracked=True, integer_ub_operations_tracked=True, address_provenance_tracked=True,
        )

    exact_two = fp(two, unreliable=())
    # disjoint sets: a difference whichever value each build holds
    assert isinstance(compare_runs(plan, fp(one, (one, one + 1)), exact_two), ConcreteDifference)
    # the sets meet: no evidence
    met = compare_runs(plan, fp(one, (one, two)), exact_two)
    assert met.observation_refusal is ObservationRefusal.VALUE_NOT_RELIABLE
    # fail-closed: no set, a set without the machine's value, a wrong size,
    # another doubt besides rounding, or a NaN among the possible values
    for refused in (
        fp(one), fp(one, (one + 1, one + 2)), fp(one, (one, one + 1), size=4),
        fp(one, (one, one + 1), ("FP_NAN_OPERAND", "FP_ROUNDING_SENSITIVE")), fp(one, (one, nan)),
    ):
        result = compare_runs(plan, refused, exact_two)
        assert result.observation_refusal is ObservationRefusal.VALUE_NOT_RELIABLE


# ------------------------------------------- addresses and program state (#18)

def test_a_run_whose_address_provenance_was_not_examined_establishes_nothing():
    # A returned pointer differs between two binaries because the image and the
    # frame are placed differently; without the provenance monitor that is not seen.
    untracked = _returned(13, address_provenance_tracked=False)
    for left, right, side in ((untracked, _returned(14), 0), (_returned(14), untracked, 1)):
        result = compare_runs(_plan(), left, right)
        assert isinstance(result, ConcreteNoEvidence)
        assert result.reason is NoEvidenceReason.ADDRESS_PROVENANCE_NOT_TRACKED and result.side == side
    assert ExecutionResult(Termination.RETURNED, 1).address_provenance_tracked is False


def test_a_run_that_read_writable_program_data_establishes_nothing():
    # The value of .data / .bss / the GOT at a call is the program's state, not an
    # input both binaries share: only its value at program start is known.
    reader = _returned(13, writable_image_reads=((0x412000, 4),))
    for left, right, side in ((reader, _returned(14), 0), (_returned(14), reader, 1)):
        result = compare_runs(_plan(), left, right)
        assert isinstance(result, ConcreteNoEvidence)
        assert result.reason is NoEvidenceReason.WRITABLE_IMAGE_READ and result.side == side


@pytest.mark.parametrize("kind", [HazardKind.STACK_ADDRESS, HazardKind.IMAGE_ADDRESS, HazardKind.ADDRESS_BITS])
def test_a_returned_value_derived_from_an_address_is_not_compared(kind):
    def run(value):
        return ExecutionResult(
            Termination.RETURNED, 1, (("x0", ObservedRegister(value, 8, None, 0, (kind.value,))),),
            fp_operations_tracked=True, integer_ub_operations_tracked=True, address_provenance_tracked=True,
        )
    result = compare_runs(_plan_for(ARM, ARM_X0), run(0x111034), run(0x112014))
    assert result.reason is NoEvidenceReason.OBSERVATION_REFUSED
    assert result.observation_refusal is ObservationRefusal.VALUE_NOT_RELIABLE


def test_a_pointer_typed_return_is_refused_before_any_run():
    pointer = ReturnStorage(False, (ARM_X0,), is_pointer=True)
    assert return_location(ARM, pointer) is ObservationRefusal.RETURN_TYPE_POINTER
    assert return_location(ARM, ReturnStorage(True, (ARM_X0,), is_pointer=True)) is ObservationRefusal.RETURN_VOID
    assert not isinstance(return_location(ARM, ReturnStorage(False, (ARM_X0,))), ObservationRefusal)


def test_the_entry_state_marks_the_registers_that_hold_addresses():
    arm = build_entry_state(ARM, 0x1000, ())
    assert dict(arm.address_registers) == {
        "sp": HazardKind.STACK_ADDRESS, "x30": HazardKind.IMAGE_ADDRESS,
    }
    mips = build_entry_state(MIPS, 0x1000, ())
    assert dict(mips.address_registers) == {
        "sp": HazardKind.STACK_ADDRESS, "ra": HazardKind.IMAGE_ADDRESS, "t9": HazardKind.IMAGE_ADDRESS,
    }

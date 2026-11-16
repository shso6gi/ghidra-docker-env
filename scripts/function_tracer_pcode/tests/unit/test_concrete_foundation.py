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
    AbiId,
    ArgClass,
    ArgumentSlot,
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
    ParameterStorage,
    SideInputSurface,
    bind_arguments,
    correspond_inputs,
    side_input_surface,
)
from scripts.function_tracer_pcode.concrete.observation import (
    ObservationRefusal,
    ObservationRelation,
    ReturnStorage,
    compare_return_values,
    plan_return_observation,
    return_location,
)

ARM = abi_model(AbiId.AARCH64_AAPCS64)
MIPS = abi_model(AbiId.MIPS_N64)


def _arm_int(n, size=4):
    return ParameterStorage(True, f"x{n}", 64, 0, size)


def _arm_fp(n, size=8):
    return ParameterStorage(True, f"z{n}", 256, 0, size)


def _mips_int(n, size=4):
    # Big-endian: the low 32 bits of a 64-bit register start at address-bit 32.
    return ParameterStorage(True, f"a{n}", 64, 64 - size * 8, size)


def _mips_fp(n, size=8):
    return ParameterStorage(True, f"f{12 + n}", 64, 64 - size * 8, size)


def _surface(abi, *parameters) -> SideInputSurface:
    surface = side_input_surface(abi, parameters)
    assert isinstance(surface, SideInputSurface), surface
    return surface


def _double_bits(value: float) -> int:
    return struct.unpack(">Q", struct.pack(">d", value))[0]


# ---------------------------------------------------------------- ABI models

def test_select_abi_knows_only_the_modelled_programs():
    assert select_abi("AARCH64", 8, False) is ARM
    assert select_abi("MIPS", 8, True) is MIPS
    assert select_abi("MIPS", 4, True) is None        # o32 / n32
    assert select_abi("MIPS", 8, False) is None       # mips64el: not modelled
    assert select_abi("x86", 8, False) is None


def test_slot_assignment_follows_each_abis_numbering():
    classes = (ArgClass.INT, ArgClass.INT, ArgClass.FP)
    assert ARM.assign_slots(classes) == (
        ArgumentSlot(ArgClass.INT, 0), ArgumentSlot(ArgClass.INT, 1), ArgumentSlot(ArgClass.FP, 0),
    )
    assert MIPS.assign_slots(classes) == (
        ArgumentSlot(ArgClass.INT, 0), ArgumentSlot(ArgClass.INT, 1), ArgumentSlot(ArgClass.FP, 2),
    )
    assert MIPS.argument_register(ArgumentSlot(ArgClass.FP, 2)) == "f14"
    assert ARM.assign_slots((ArgClass.INT,) * 9) is None  # the ninth goes to the stack


def test_no_register_has_two_roles_in_one_abi():
    for abi in (ARM, MIPS):
        arguments = set(abi.int_argument_registers) | set(abi.fp_argument_registers)
        state = set(abi.callee_saved_registers) | {abi.stack_pointer, abi.return_address_register}
        assert not arguments & state
        assert len(arguments) == len(abi.int_argument_registers) + len(abi.fp_argument_registers)


# ------------------------------------------------------------- input surface

def test_side_surface_refuses_what_it_cannot_place():
    stack = ParameterStorage(False, None, 0, 0, 8)
    assert side_input_surface(ARM, [stack]) is InputSurfaceRefusal.PARAMETER_NOT_IN_REGISTER
    assert (
        side_input_surface(ARM, [ParameterStorage(True, "x8", 64, 0, 8)])
        is InputSurfaceRefusal.PARAMETER_REGISTER_NOT_AN_ARGUMENT_SLOT
    )
    # The high half of a MIPS register is not an argument.
    assert (
        side_input_surface(MIPS, [ParameterStorage(True, "a1", 64, 0, 4)])
        is InputSurfaceRefusal.PARAMETER_NOT_LOW_PART_OF_REGISTER
    )
    # ... unless the storage names the whole register and only the recovered type is
    # narrow (measured: `int` parameters stored as the full `a0` after a type hypothesis).
    whole = side_input_surface(MIPS, [ParameterStorage(True, "a1", 64, 0, 4, register_name="a1")])
    assert isinstance(whole, SideInputSurface) and whole.readings[0].width_bytes == 4
    assert (
        side_input_surface(MIPS, [ParameterStorage(True, "f12", 64, 0, 16)])
        is InputSurfaceRefusal.PARAMETER_WIDTH_UNSUPPORTED
    )
    assert (
        side_input_surface(ARM, [_arm_int(0), _arm_int(0, 8)])
        is InputSurfaceRefusal.DUPLICATE_ARGUMENT_SLOT
    )


def test_same_abi_correspondence_is_by_register_and_keeps_every_reading():
    left = _surface(MIPS, _mips_int(0, 8), _mips_int(1, 4))
    right = _surface(MIPS, _mips_int(0, 4))          # the second parameter was optimised away
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


def test_a_32bit_integer_is_written_sign_extended_on_both_abis():
    # Measured: writing 0x80000000 zero-extended into a MIPS n64 register made the
    # emulator disagree with the real machine (the entry state was not conforming).
    assert MIPS.narrow_int_rule is NarrowIntRule.SIGN_EXTENDED_REQUIRED
    correspondence = correspond_inputs(_surface(MIPS, _mips_int(0)), _surface(ARM, _arm_int(0)))
    (mips_image,), (arm_image,) = bind_arguments(correspondence, [0x80000000])
    assert mips_image.register == "a0" and mips_image.value == 0xFFFFFFFF80000000
    assert arm_image.register == "x0" and arm_image.value == 0xFFFFFFFF80000000
    (mips_image,), _ = bind_arguments(correspondence, [5])
    assert mips_image.value == 5


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

def _ret(base, base_bits, offset, size, **kw):
    record = dict(is_void=False, location_count=1, is_register=True, base_register_name=base,
                  base_register_bits=base_bits, bit_offset_in_base=offset, size_bytes=size)
    record.update(kw)
    return ReturnStorage(**record)


def test_return_location_refusals():
    assert return_location(ARM, _ret("x0", 64, 0, 4, is_void=True)) is ObservationRefusal.RETURN_VOID
    assert (
        return_location(ARM, _ret("x0", 64, 0, 4, location_count=2))
        is ObservationRefusal.RETURN_NOT_SINGLE_LOCATION
    )
    assert (
        return_location(ARM, _ret(None, 0, 0, 8, is_register=False))
        is ObservationRefusal.RETURN_NOT_IN_REGISTER
    )
    assert (
        return_location(ARM, _ret("x1", 64, 0, 8))
        is ObservationRefusal.RETURN_REGISTER_NOT_A_RETURN_REGISTER
    )
    assert (
        return_location(MIPS, _ret("v0", 64, 0, 4))
        is ObservationRefusal.RETURN_NOT_LOW_PART_OF_REGISTER
    )
    assert return_location(MIPS, _ret("f0", 64, 0, 16)) is ObservationRefusal.RETURN_WIDTH_UNSUPPORTED


def test_integer_returns_are_compared_on_the_narrower_width():
    arm = return_location(ARM, _ret("x0", 64, 0, 4))
    mips = return_location(MIPS, _ret("v0", 64, 0, 8))
    plan = plan_return_observation(arm, mips)
    assert plan.arg_class is ArgClass.INT and plan.compare_bytes == 4 and plan.narrowed
    # -1 as int: AArch64 leaves the upper half zero, MIPS sign-extends.
    assert (
        compare_return_values(plan, 0x00000000FFFFFFFF, 0xFFFFFFFFFFFFFFFF)
        is ObservationRelation.NOT_DIFFERENT_ON_OBSERVED_PART
    )
    assert compare_return_values(plan, 13, 14) is ObservationRelation.DIFFERENT


def test_return_class_and_fp_format_must_agree():
    arm_int = return_location(ARM, _ret("x0", 64, 0, 4))
    arm_fp = return_location(ARM, _ret("z0", 256, 0, 8))
    assert plan_return_observation(arm_int, arm_fp) is ObservationRefusal.RETURN_CLASS_MISMATCH
    arm_float = return_location(ARM, _ret("z0", 256, 0, 4))
    assert plan_return_observation(arm_float, arm_fp) is ObservationRefusal.FP_FORMAT_UNRESOLVED


def test_a_16_byte_fp_location_is_binary64_only_with_a_zero_upper_half():
    wide = return_location(ARM, _ret("z0", 256, 0, 16))
    plan = plan_return_observation(wide, wide)
    assert plan.compare_bytes == 16 and not plan.narrowed
    one, two = _double_bits(1.0), _double_bits(2.0)
    assert compare_return_values(plan, one, two) is ObservationRelation.DIFFERENT
    assert compare_return_values(plan, one, one) is ObservationRelation.NOT_DIFFERENT_ON_OBSERVED_PART
    assert (
        compare_return_values(plan, (1 << 64) | one, two) is ObservationRefusal.FP_FORMAT_UNRESOLVED
    )


def test_a_nan_is_never_compared():
    # Measured: the emulator returned fff8000000000000 where the machine returned
    # fff0000000000001 (airy SIGN, same source).  A payload difference is not evidence.
    location = return_location(MIPS, _ret("f0", 64, 0, 8))
    plan = plan_return_observation(location, location)
    assert (
        compare_return_values(plan, 0xFFF8000000000000, 0xFFF0000000000001)
        is ObservationRefusal.NAN_OBSERVED
    )
    assert (
        compare_return_values(plan, 0x7FF8000000000000, _double_bits(1.0))
        is ObservationRefusal.NAN_OBSERVED
    )
    infinity = 0x7FF0000000000000
    assert compare_return_values(plan, infinity, _double_bits(1.0)) is ObservationRelation.DIFFERENT
    single = return_location(MIPS, _ret("f0", 64, 32, 4))
    single_plan = plan_return_observation(single, single)
    assert compare_return_values(single_plan, 0x7FC00000, 0x3F800000) is ObservationRefusal.NAN_OBSERVED


# ------------------------------------------------------------------- comparison

def _plan():
    location = return_location(ARM, _ret("x0", 64, 0, 4))
    return plan_return_observation(location, location)


def _returned(value, **kw):
    return ExecutionResult(Termination.RETURNED, 10, (("x0", value),), **kw)


def test_two_clean_returns_with_different_values_are_a_difference():
    result = compare_runs(_plan(), _returned(13), _returned(14))
    assert isinstance(result, ConcreteDifference) and result.observed_values == (13, 14)


@pytest.mark.parametrize("termination", [t for t in Termination if t is not Termination.RETURNED])
def test_a_run_that_did_not_return_establishes_nothing(termination):
    stopped = ExecutionResult(termination, 5, (("x0", 99),))
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
    missing = ExecutionResult(Termination.RETURNED, 1, ())
    assert compare_runs(_plan(), _returned(3), missing).reason is NoEvidenceReason.OBSERVATION_MISSING
    fp = return_location(MIPS, _ret("f0", 64, 0, 8))
    fp_plan = plan_return_observation(fp, fp)
    nan = ExecutionResult(Termination.RETURNED, 1, (("f0", 0x7FF8000000000000),))
    one = ExecutionResult(Termination.RETURNED, 1, (("f0", _double_bits(1.0)),))
    result = compare_runs(fp_plan, nan, one)
    assert result.reason is NoEvidenceReason.OBSERVATION_REFUSED
    assert result.observation_refusal is ObservationRefusal.NAN_OBSERVED

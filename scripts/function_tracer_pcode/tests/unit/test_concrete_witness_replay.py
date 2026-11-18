# -*- coding: utf-8 -*-
"""Turning a formula witness into corresponding inputs and replaying it (#18, C2).

Pure Python: the executors are stand-ins that return given results, and the
results go through the production ``compare_runs``.
"""
import json
import struct

import pytest

from scripts.function_tracer_pcode.concrete.abi import AbiId, ArgClass, abi_model
from scripts.function_tracer_pcode.concrete.executor import (
    ExecutionResult,
    Hazard,
    HazardKind,
    Termination,
)
from scripts.function_tracer_pcode.concrete.input_surface import (
    InputSurfaceRefusal,
    correspond_inputs,
)
from scripts.function_tracer_pcode.concrete.observation import (
    ObservationRefusal,
    ObservedRegister,
    ReturnStorage,
)
from scripts.function_tracer_pcode.concrete.replay import (
    PlanRefusal,
    PlanStage,
    ReplayPlan,
    ReplaySide,
    WitnessStatus,
    judge_witness,
    plan_replay,
    replay_witnesses,
    witness_requests,
)
from scripts.function_tracer_pcode.concrete.storage import StorageLocation
from scripts.function_tracer_pcode.concrete.witness import (
    FormulaInput,
    WitnessRefusal,
    formula_surface,
    witness_input,
)

ARM = abi_model(AbiId.AARCH64_AAPCS64)
MIPS = abi_model(AbiId.MIPS_N64)


def arm_int(index, size=4):
    name = f"w{index}" if size == 4 else f"x{index}"
    return StorageLocation(True, name, f"x{index}", 8, 0, size)


def arm_fp(index):
    return StorageLocation(True, f"d{index}", f"z{index}", 32, 0, 8)


def mips_int(index, size=4):
    base = ("a0", "a1", "a2", "a3")[index]
    if size == 8:
        return StorageLocation(True, base, base, 8, 0, 8)
    return StorageLocation(True, f"{base}_lo", base, 8, 4, 4)


def mips_fp(position):
    name = f"f{12 + position}"
    return StorageLocation(True, name, name, 8, 0, 8)


def fi(variable, bits, location):
    return FormulaInput(variable, bits, location)


ARM_RET_W0 = ReturnStorage(False, (arm_int(0),))
ARM_RET_X0 = ReturnStorage(False, (arm_int(0, 8),))
MIPS_RET_V0 = ReturnStorage(False, (StorageLocation(True, "v0_lo", "v0", 8, 4, 4),))


def _correspondence(left_abi, left, right_abi, right):
    surfaces = [formula_surface(left_abi, left), formula_surface(right_abi, right)]
    return correspond_inputs(*surfaces)


def _double(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


# ----------------------------------------------------------------- witnesses

def test_a_witness_names_one_value_per_argument_found_by_storage():
    left = [fi("param_1_1", 32, arm_int(0)), fi("param_2_1", 32, arm_int(1))]
    right = [fi("param_2_2", 32, arm_int(1)), fi("param_1_2", 32, arm_int(0))]
    corr = _correspondence(ARM, left, ARM, right)
    named = witness_input(corr, (left, right), {"param_1_1": 7, "param_1_2": 7, "param_2_1": 0xFFFFFFFF,
                                                "param_2_2": 0xFFFFFFFF, "rtunk_x_32": 3})
    assert named.values == (7, 0xFFFFFFFF)
    assert named.variables == (("param_1_1", "param_1_2"), ("param_2_1", "param_2_2"))


def test_a_cross_abi_witness_follows_the_positional_order_not_the_names():
    # int f(int, int, double): MIPS a0, a1, f14 <-> AArch64 x0, x1, d0.  The
    # variable names of the right side are deliberately scrambled.
    left = [fi("p_a", 32, mips_int(0)), fi("p_b", 32, mips_int(1)), fi("p_c", 64, mips_fp(2))]
    right = [fi("q_z", 64, arm_fp(0)), fi("q_x", 32, arm_int(0)), fi("q_y", 32, arm_int(1))]
    corr = _correspondence(MIPS, left, ARM, right)
    one = _double(1.5)
    named = witness_input(corr, (left, right), {"p_a": 1, "q_x": 1, "p_b": 2, "q_y": 2, "p_c": one, "q_z": one})
    assert named.values == (1, 2, one)
    assert witness_input(corr, (left, right), {"p_a": 1, "q_x": 2, "p_b": 2, "q_y": 2, "p_c": one,
                                               "q_z": one}) is WitnessRefusal.SIDES_DISAGREE


def test_a_witness_whose_sides_are_related_by_zero_extension_is_refused():
    # unsigned -> unsigned long: 0xFFFFFFFF on one side, 0x00000000FFFFFFFF on the other
    left = [fi("a_1", 32, arm_int(0))]
    right = [fi("a_2", 64, arm_int(0, 8))]
    corr = _correspondence(ARM, left, ARM, right)
    assert witness_input(corr, (left, right), {"a_1": 0xFFFFFFFF, "a_2": 0xFFFFFFFF}) is WitnessRefusal.SIDES_DISAGREE
    # the sign-extended reading is the same argument, and is then refused by the readings
    named = witness_input(corr, (left, right), {"a_1": 0xFFFFFFFF, "a_2": (1 << 64) - 1})
    assert named.values == ((1 << 64) - 1,)
    assert named.correspondence.arguments[0].readings == (4, 8)


@pytest.mark.parametrize("witness, refusal", [
    ({"a_1": 1}, WitnessRefusal.VALUE_MISSING),
    ({"a_1": 1, "a_2": True}, WitnessRefusal.VALUE_NOT_A_BIT_PATTERN),
    ({"a_1": 1, "a_2": -1}, WitnessRefusal.VALUE_NOT_A_BIT_PATTERN),
    ({"a_1": 1, "a_2": 1 << 32}, WitnessRefusal.VALUE_NOT_A_BIT_PATTERN),
])
def test_missing_and_malformed_values_are_refused_not_defaulted(witness, refusal):
    left, right = [fi("a_1", 32, arm_int(0))], [fi("a_2", 32, arm_int(0))]
    corr = _correspondence(ARM, left, ARM, right)
    assert witness_input(corr, (left, right), witness) is refusal


def test_unsupported_widths_and_foreign_storage_are_refused():
    left, right = [fi("a_1", 32, arm_int(0))], [fi("a_2", 32, arm_int(0))]
    corr = _correspondence(ARM, left, ARM, right)
    assert witness_input(corr, ([fi("a_1", 1, arm_int(0))], right), {"a_1": 1, "a_2": 1}) \
        is WitnessRefusal.VARIABLE_WIDTH_UNSUPPORTED
    assert witness_input(corr, ([fi("a_1", 32, arm_int(3))], right), {"a_1": 1, "a_2": 1}) \
        is WitnessRefusal.VARIABLE_NOT_AN_ARGUMENT


def test_the_formula_width_is_a_reading_of_the_argument():
    # The storage is the whole register (a type hypothesis narrowed only the type);
    # the formula reads 32 bits.  INT_MIN as int is not the same AArch64 image as
    # the 64-bit reading, so it is refused, while 5 is admitted.
    left = [fi("a_1", 32, arm_int(0, 8))]
    right = [fi("a_2", 32, arm_int(0, 8))]
    plan = plan_replay(_side(ARM, left, ARM_RET_W0), _side(ARM, right, ARM_RET_W0))
    assert witness_requests(plan, {"a_1": 0x80000000, "a_2": 0x80000000}) \
        is InputSurfaceRefusal.VALUE_NOT_CONFORMING_UNDER_EVERY_READING
    ok = witness_requests(plan, {"a_1": 5, "a_2": 5})
    assert [(i.register, i.value) for i in ok.images[0]] == [("x0", 5)]


# ---------------------------------------------------------------------- plans

def _side(abi, inputs, ret, entry=0x1000):
    return ReplaySide(abi, entry, tuple(inputs), ret)


def test_a_plan_is_refused_at_the_stage_that_fails():
    stack = StorageLocation(False, None, None, 0, 0, 4)
    refused = plan_replay(_side(ARM, [fi("a", 32, stack)], ARM_RET_W0), _side(ARM, [], ARM_RET_W0))
    assert refused == PlanRefusal(PlanStage.INPUT_SURFACE, InputSurfaceRefusal.PARAMETER_NOT_IN_REGISTER, 0)
    pointer = ReturnStorage(False, (arm_int(0, 8),), is_pointer=True)
    refused = plan_replay(_side(ARM, [], ARM_RET_X0), _side(ARM, [], pointer))
    assert refused == PlanRefusal(PlanStage.RETURN_LOCATION, ObservationRefusal.RETURN_TYPE_POINTER, 1)
    assert refused.describe() == "RETURN_LOCATION:side1:RETURN_TYPE_POINTER"
    void = ReturnStorage(True, ())
    assert plan_replay(_side(ARM, [], void), _side(ARM, [], ARM_RET_W0)).reason is ObservationRefusal.RETURN_VOID
    fp_ret = ReturnStorage(False, (arm_fp(0),))
    assert plan_replay(_side(ARM, [], ARM_RET_W0), _side(ARM, [], fp_ret)).stage is PlanStage.RETURN_OBSERVATION


def test_the_requests_bind_the_images_and_observe_the_return_registers():
    left = [fi("a_1", 32, mips_int(0))]
    right = [fi("a_2", 32, arm_int(0))]
    plan = plan_replay(_side(MIPS, left, MIPS_RET_V0, 0x120000A00), _side(ARM, right, ARM_RET_W0, 0x100700))
    assert isinstance(plan, ReplayPlan)
    prepared = witness_requests(plan, {"a_1": 0xFFFFFFFE, "a_2": 0xFFFFFFFE})
    mips, arm = prepared.requests
    # MIPS n64 sign-extends a 32-bit argument, AArch64 zero-extends it (C1)
    assert dict(mips.entry_state.registers)["a0"] == 0xFFFFFFFFFFFFFFFE
    assert dict(arm.entry_state.registers)["x0"] == 0xFFFFFFFE
    assert mips.observe_registers == ("v0",) and arm.observe_registers == ("x0",)
    assert dict(mips.entry_state.registers)["t9"] == 0x120000A00
    assert dict(mips.entry_state.address_registers)["sp"] is HazardKind.STACK_ADDRESS


# -------------------------------------------------------------------- replays

def _clean(value, **kw):
    kw.setdefault("fp_operations_tracked", True)
    kw.setdefault("integer_ub_operations_tracked", True)
    kw.setdefault("address_provenance_tracked", True)
    return ExecutionResult(Termination.RETURNED, 3, (("x0", ObservedRegister(value, 8, None, 8)),), **kw)


class Fixed:
    """Answers every request with the next result."""

    def __init__(self, *results):
        self.results = list(results)
        self.requests = []

    def execute(self, request):
        self.requests.append(request)
        return self.results.pop(0)


def _arm_plan():
    left, right = [fi("a_1", 32, arm_int(0))], [fi("a_2", 32, arm_int(0))]
    return plan_replay(_side(ARM, left, ARM_RET_W0), _side(ARM, right, ARM_RET_W0, 0x2000))


def test_a_witness_whose_runs_differ_is_confirmed_and_recorded():
    plan = _arm_plan()
    left, right = Fixed(_clean(13)), Fixed(_clean(14))
    replay = judge_witness(plan, {"a_1": 3, "a_2": 3}, lambda s, r: (left, right)[s].execute(r))
    assert replay.status is WitnessStatus.CONFIRMED and replay.observed_values == (13, 14)
    assert replay.values == (3,) and replay.images == ((("x0", 3),), (("x0", 3),))
    record = json.loads(json.dumps(replay.to_json()))
    assert record["status"] == "CONFIRMED" and record["results"][1]["observed_registers"][0][1] == 14
    assert record["requests"][1]["entry_address"] == 0x2000


@pytest.mark.parametrize("left_result, reason", [
    (_clean(13), "NO_DIFFERENCE_OBSERVED"),
    (_clean(14, writable_image_reads=((0x412000, 4),)), "WRITABLE_IMAGE_READ:side0"),
    (_clean(14, address_provenance_tracked=False), "ADDRESS_PROVENANCE_NOT_TRACKED:side0"),
    (_clean(14, hazards=(Hazard(HazardKind.ADDRESS_BITS, "x"),)), "RUN_HAS_HAZARD:side0:ADDRESS_BITS"),
    (ExecutionResult(Termination.LEFT_PROGRAM_CODE, 9), "RUN_DID_NOT_RETURN:side0:LEFT_PROGRAM_CODE"),
])
def test_a_witness_whose_runs_establish_nothing_is_no_evidence(left_result, reason):
    plan = _arm_plan()
    replay = judge_witness(plan, {"a_1": 3, "a_2": 3},
                           lambda s, r: (Fixed(left_result), Fixed(_clean(13)))[s].execute(r))
    assert replay.status is WitnessStatus.NO_EVIDENCE and replay.reason == reason


def test_a_refused_witness_runs_nothing():
    plan = _arm_plan()

    def never(side, request):
        raise AssertionError("must not run")

    replay = judge_witness(plan, {"a_1": 3, "a_2": 4}, never)
    assert replay.status is WitnessStatus.INPUT_REFUSED and replay.reason == "SIDES_DISAGREE"


def test_replay_skips_repeated_witnesses_stops_at_a_confirmation_and_honours_the_budget():
    plan = _arm_plan()
    left = Fixed(_clean(1), _clean(5), _clean(9))
    right = Fixed(_clean(1), _clean(6), _clean(9))
    witnesses = [{"a_1": 1, "a_2": 1}, {"a_1": 1, "a_2": 1}, {"a_1": 2, "a_2": 2}, {"a_1": 3, "a_2": 3}]
    replays = replay_witnesses(plan, witnesses, (left, right))
    assert [r.status for r in replays] == [WitnessStatus.NO_EVIDENCE, WitnessStatus.CONFIRMED]
    assert len(left.requests) == 2
    budget = iter([True, False])
    replays = replay_witnesses(plan, witnesses, (Fixed(_clean(1)), Fixed(_clean(1))),
                               may_continue=lambda: next(budget))
    assert len(replays) == 1


def test_witnesses_are_told_apart_by_exact_values_not_by_their_rendering():
    # A Boolean and an integer that print alike are different assignments.
    plan = _arm_plan()
    left, right = Fixed(_clean(1), _clean(1)), Fixed(_clean(1), _clean(1))
    witnesses = [{"a_1": 1, "a_2": 1, "b": True}, {"a_1": 1, "a_2": 1, "b": 1}, {"a_2": 1, "b": True, "a_1": 1}]
    replays = replay_witnesses(plan, witnesses, (left, right), stop_at_first_confirmation=False)
    assert len(replays) == 2

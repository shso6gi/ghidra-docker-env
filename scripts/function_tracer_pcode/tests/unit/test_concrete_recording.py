# -*- coding: utf-8 -*-
"""Recorded concrete runs of real EqBench binaries, replayed without Ghidra.

Each ``tests/fixtures/concrete/*.json`` trace is one run of the Ghidra P-code
emulator executor (recorded by ``tests/tools/record_concrete_fixture.py``
through ``ghidra.concrete_worker``).  Replaying its events through the
production ``RunObserver`` must give the recorded result exactly; the
results themselves pin what the executor reports on real code: each kind of
end, undefined register and memory reads, an external call, the floating-
point format of a returned value (also through an AArch64 ``-O0`` stack
round trip), and -- since C3 (schema v2, operand values recorded) -- the
monitors' findings on real code: a signed overflow deciding a branch, a NaN
operand, a zero-initialised ``.bss`` read and a user operation run with its
established meaning.
"""
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.concrete.executor import HazardKind, Termination
from scripts.function_tracer_pcode.concrete.observation import FpFormat
from scripts.function_tracer_pcode.concrete.recording import (
    TRACE_SCHEMA,
    RecordedExecutor,
    replay_trace,
    request_from_json,
    request_to_json,
    result_from_json,
    result_to_json,
)

FIXTURES = Path(__file__).resolve().parents[1] / "fixtures" / "concrete"
TRACES = sorted(p for p in FIXTURES.glob("*.json") if not p.name.startswith("facts_"))


def _trace(name):
    return json.loads((FIXTURES / f"{name}.json").read_text())


def test_the_corpus_is_present():
    assert {p.stem for p in TRACES} >= {
        "arm64_ackermann_returned", "mips64_ackermann_returned", "arm64_ackermann_unbound_argument",
        "mips64_ackermann_step_limit", "arm64_bessk0_external_call", "arm64_loop_float_o0",
        "mips64_loop_float_o2", "arm64_addvalue_bss_read", "arm64_pow_signed_overflow",
        "mips64_pow_signed_overflow", "mips64_airy_sign_nan", "arm64_factorial_neon_ext",
    }


@pytest.mark.parametrize("path", TRACES, ids=lambda p: p.stem)
def test_every_trace_replays_to_its_recorded_result(path):
    trace = json.loads(path.read_text())
    assert trace["schema"] == TRACE_SCHEMA
    assert trace["program"]["sha256"] and trace["provenance"]["executor"]
    replayed, recorded = replay_trace(trace)
    assert replayed == recorded
    assert result_from_json(result_to_json(recorded)) == recorded
    request = request_from_json(trace["request"])
    assert request_from_json(request_to_json(request)) == request


def _result(name):
    return replay_trace(_trace(name))[0]


def test_ackermann_returns_its_value_on_both_isas():
    for name, register in (("arm64_ackermann_returned", "x0"), ("mips64_ackermann_returned", "v0")):
        result = _result(name)
        assert result.termination is Termination.RETURNED and result.hazards == ()
        assert result.observed(register).value == 3 and result.observed(register).defined_low_bytes == 8
        # Integer arithmetic examined with its operand values, no overflow.
        assert result.fp_operations_tracked and result.integer_ub_operations_tracked
        assert result.observed(register).reliable_low_bytes == 8


def test_each_kind_of_unusable_run_is_reported_distinctly():
    unbound = _result("arm64_ackermann_unbound_argument")
    assert unbound.termination is Termination.RETURNED
    assert unbound.hazard_kinds() == (HazardKind.UNDEFINED_REGISTER_READ,)     # x1 (w1) never bound
    assert "0x4008" in unbound.hazards[0].detail

    limited = _result("mips64_ackermann_step_limit")
    assert limited.termination is Termination.STEP_LIMIT and limited.steps == 40

    external = _result("arm64_bessk0_external_call")
    assert external.termination is Termination.LEFT_PROGRAM_CODE and "log" in external.detail

    bss = _result("arm64_addvalue_bss_read")                                   # global `count` in .bss
    # C3: .bss is an ELF NOBITS+ALLOC section, zero at program start: its read
    # is a read of program data before the run wrote it, not a hazard (C1:
    # UNDEFINED_MEMORY_READ).
    assert bss.hazards == () and bss.writable_image_reads == ((0x100120, 4),)
    trace = _trace("arm64_addvalue_bss_read")
    assert trace["setup"]["zero_initialized_ranges"] and trace["program"]["zero_initialized_ranges"]
    assert bss.termination is Termination.LEFT_PROGRAM_CODE                    # then printf


def test_a_computed_float_return_has_its_format_from_the_run():
    # REVE/loop f(3.0f) returns 4.0f (0x40800000).
    arm = _result("arm64_loop_float_o0")              # returned through a stack spill at -O0
    observed = arm.observed("z0")
    assert observed.value == 0x40800000 and observed.value_format is FpFormat.BINARY32
    assert observed.defined_low_bytes == 32
    mips = _result("mips64_loop_float_o2")
    observed = mips.observed("f0")
    assert observed.value == 0x40800000 and observed.value_format is FpFormat.BINARY32
    assert observed.defined_low_bytes == 4            # add.s writes the low half only
    for run in (arm, mips):
        # additions only (no product feeds an addition): every bit is reliable
        assert run.fp_operations_tracked and run.hazards == ()
    assert arm.observed("z0").reliable_low_bytes == 32 and mips.observed("f0").reliable_low_bytes == 8


def test_a_signed_overflow_that_decides_a_branch_is_a_hazard_on_real_code():
    # pow/test (one source; clang -O0 and -O1 return 13 and 14 for y = INT_MIN
    # on the machine): ``-y < -8`` with y = INT_MIN.  Both ISAs' -O0 builds.
    for name, register in (("arm64_pow_signed_overflow", "x0"), ("mips64_pow_signed_overflow", "v0")):
        result = _result(name)
        assert result.termination is Termination.RETURNED and result.observed(register).value == 13
        assert result.hazard_kinds() == (HazardKind.SIGNED_OVERFLOW,)
        assert result.integer_ub_operations_tracked


def test_a_nan_operand_makes_the_returned_value_unreliable_on_real_code():
    # airy/airy SIGN (MIPS clang -O1) with a signalling NaN: the emulator's
    # ``neg.d`` loses the payload (the machine returns fff0000000000001).
    result = _result("mips64_airy_sign_nan")
    observed = result.observed("f0")
    assert observed.reliable_low_bytes == 0 and observed.unreliable == ("FP_NAN_OPERAND",)
    assert result.hazards == () and result.fp_operations_tracked


def test_a_user_operation_with_an_established_meaning_runs_on_real_code():
    # CLEVER/factorial oldV clang -O3 uses NEON ``ext`` (C1: UNSUPPORTED_OPERATION).
    result = _result("arm64_factorial_neon_ext")
    assert result.termination is Termination.RETURNED and result.observed("x0").value == 6
    assert dict(result.operation_counts)["CALLOTHER"] >= 1


def test_a_recorded_executor_replays_known_requests_and_refuses_unknown_ones():
    trace = _trace("arm64_ackermann_returned")
    executor = RecordedExecutor([trace, _trace("arm64_ackermann_unbound_argument")])
    request = request_from_json(trace["request"])
    assert executor.execute(request) == result_from_json(trace["result"])
    other = request_from_json(dict(trace["request"], step_limit=7))
    assert other != request
    missing = executor.execute(other)
    assert missing.termination is Termination.EXECUTOR_ERROR and "no recorded run" in missing.detail
    with pytest.raises(ValueError):
        RecordedExecutor([trace, _trace("mips64_ackermann_returned")])     # two programs
    with pytest.raises(ValueError):
        RecordedExecutor([dict(trace, schema="other")])

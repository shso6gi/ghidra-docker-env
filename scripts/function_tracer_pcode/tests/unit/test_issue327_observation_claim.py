# -*- coding: utf-8 -*-
"""Issue #327 (E2): which return-observation elements binary evidence verifies.

Pins the decisions of #327 (2026-11-27): E-a (SMT_PARITY) is an evidence level
of an ASSUMED element and never verifies; E-b verifies O1/O2 only with its
conditions and never O3 (C-b5 and H3 cannot be confirmed); E-b and E-d alone
verify nothing; R_V is empty unless every element of both sides is verified,
and never wider than R_C.
"""

import pytest

from scripts.function_tracer_pcode.concrete.observation_claim import (
    Condition,
    DifferenceRange,
    ElementState,
    EvidenceLevel,
    EvidenceStatus,
    Method,
    ObservationElement as E,
    classify_pair,
    classify_side,
)

OK = EvidenceStatus.CONSULTED


def demand(int_mask=0, fp_mask=0, own_int=True, own_fp=False, status="SCANNED"):
    return {"status": status, "own_writes": {"INT": own_int, "FP": own_fp},
            "callsites": [{"call": 0x200, "caller": 0x100, "end": "CBRANCH", "demand": {"INT": int_mask, "FP": fp_mask}}]}


def side(value_class="INT", *, caller=None, caller_status=OK, parity=None, parity_status=OK, fmt=None, width=32, index=0):
    return classify_side(
        index, value_class=value_class, register="x0" if value_class == "INT" else "z0",
        prototype_width_bits=width, caller_demand=caller, caller_demand_status=caller_status,
        smt_parity=parity, parity_status=parity_status, executed_format=fmt,
    )


def test_caller_demand_with_a_callee_write_verifies_existence_and_class_but_not_valid_bits():
    s = side(caller=demand(int_mask=0xFFFFFFFF))
    assert s.element(E.O1_EXISTS).state is ElementState.VERIFIED
    assert s.element(E.O2_CLASS).state is ElementState.VERIFIED
    o3 = s.element(E.O3_VALID_BITS)
    assert o3.state is ElementState.ASSUMED and o3.diagnostic_bits == 32 and o3.assumed == 32
    assert set(o3.unconfirmed) == {Condition.STANDARD_CALLING_CONVENTION, Condition.NO_INTERPROCEDURAL_RELIANCE}
    assert s.element(E.O4_FP_FORMAT).state is ElementState.NOT_APPLICABLE


def test_caller_demand_without_a_callee_write_verifies_nothing():
    # interprocedural register allocation may keep a caller value in the register (C-b2)
    s = side(caller=demand(int_mask=0xFFFFFFFF, own_int=False))
    assert all(c.state is not ElementState.VERIFIED for c in s.elements)
    assert Condition.CALLEE_WRITES_REGISTER in s.element(E.O1_EXISTS).unconfirmed


def test_a_callee_write_alone_verifies_nothing():
    s = side(caller=demand(int_mask=0, own_int=True))
    assert all(c.state is not ElementState.VERIFIED for c in s.elements)


@pytest.mark.parametrize("status", [EvidenceStatus.NOT_CONSULTED, EvidenceStatus.FAILED, EvidenceStatus.DEADLINE])
def test_evidence_not_consulted_verifies_nothing(status):
    s = side(caller=demand(int_mask=0xFF), caller_status=status)
    assert all(c.state is not ElementState.VERIFIED for c in s.elements)


@pytest.mark.parametrize("record_status", ["STOPPED", "NO_FUNCTION", "FAILED"])
def test_an_incomplete_scan_is_not_evidence(record_status):
    s = side(caller=demand(int_mask=0xFF, status=record_status))
    assert all(c.state is not ElementState.VERIFIED for c in s.elements)


def test_smt_parity_is_an_evidence_level_of_an_assumed_element_never_verification():
    s = side(parity={"complete": True, "payload_bits": 64}, width=64)
    for element in (E.O1_EXISTS, E.O2_CLASS, E.O3_VALID_BITS):
        claim = s.element(element)
        assert claim.state is ElementState.ASSUMED and claim.level is EvidenceLevel.SMT_PARITY
    assert s.element(E.O3_VALID_BITS).parity_bits == 64 and s.element(E.O3_VALID_BITS).bound_bits is None
    pair = classify_pair(s, side(parity={"complete": True, "payload_bits": 64}, width=64, index=1),
                         compared_bits=64, first_difference_bit=40, evidence={})
    assert pair.verified_bits == 0 and pair.difference_range is DifferenceRange.ASSUMED_RANGE_ONLY
    incomplete = side(parity={"complete": False, "payload_bits": None})
    assert incomplete.element(E.O1_EXISTS).level is EvidenceLevel.PROTOTYPE


def test_callers_using_only_the_other_class_register_is_a_conflict():
    s = side("INT", caller=demand(int_mask=0, fp_mask=0xFFFFFFFFFFFFFFFF, own_int=True, own_fp=True))
    assert s.element(E.O2_CLASS).state is ElementState.CONFLICT and s.conflict
    pair = classify_pair(s, side(index=1), compared_bits=32, first_difference_bit=0, evidence={})
    assert pair.conflict and pair.verified_bits == 0


def test_callers_using_both_classes_leave_the_class_assumed():
    s = side("INT", caller=demand(int_mask=0xFF, fp_mask=0xFF, own_int=True, own_fp=True))
    assert s.element(E.O1_EXISTS).state is ElementState.VERIFIED
    assert s.element(E.O2_CLASS).state is ElementState.ASSUMED


def test_a_floating_point_value_is_verified_through_the_executed_format_once_its_location_is():
    fp = dict(caller=demand(fp_mask=0xFFFFFFFFFFFFFFFF, own_int=False, own_fp=True), fmt="BINARY64", width=128)
    left, right = side("FP", **fp), side("FP", index=1, **fp)
    assert left.element(E.O4_FP_FORMAT).state is ElementState.VERIFIED
    assert left.element(E.O4_FP_FORMAT).methods == (Method.EXECUTED_FORMAT,)
    assert left.element(E.O3_VALID_BITS).bound_bits == 64
    pair = classify_pair(left, right, compared_bits=64, first_difference_bit=None, evidence={})
    assert pair.verified_bits == 64 and pair.difference_range is DifferenceRange.VERIFIED_RANGE


def test_the_executed_format_without_a_verified_location_stays_assumed():
    s = side("FP", fmt="BINARY64", width=128)
    assert s.element(E.O4_FP_FORMAT).state is ElementState.ASSUMED
    assert Condition.VERIFIED_LOCATION in s.element(E.O4_FP_FORMAT).unconfirmed
    assert s.element(E.O3_VALID_BITS).state is ElementState.ASSUMED


def test_the_verified_range_needs_both_sides_and_never_exceeds_the_compared_range():
    fp = dict(caller=demand(fp_mask=0xFFFFFFFF, own_int=False, own_fp=True), fmt="BINARY64")
    verified = side("FP", **fp)
    assumed = side("FP", fmt="BINARY64", index=1)
    assert classify_pair(verified, assumed, compared_bits=64, first_difference_bit=3, evidence={}).verified_bits == 0
    narrow = classify_pair(verified, side("FP", index=1, **fp), compared_bits=32, first_difference_bit=3, evidence={})
    assert narrow.verified_bits == 32


def test_no_default_width_an_integer_value_is_never_verified():
    # a difference in the lowest byte does not make O3 verified (v2.1 §2.3)
    s = side(caller=demand(int_mask=0xFF))
    pair = classify_pair(s, side(caller=demand(int_mask=0xFF), index=1), compared_bits=32, first_difference_bit=0,
                         evidence={})
    assert pair.verified_bits == 0 and pair.difference_range is DifferenceRange.ASSUMED_RANGE_ONLY


def test_the_evidence_digest_is_deterministic_and_covers_the_evidence():
    a = classify_pair(side(), side(index=1), compared_bits=32, first_difference_bit=0, evidence={"x": 1})
    b = classify_pair(side(), side(index=1), compared_bits=32, first_difference_bit=0, evidence={"x": 1})
    c = classify_pair(side(), side(index=1), compared_bits=32, first_difference_bit=0, evidence={"x": 2})
    assert a.evidence_digest == b.evidence_digest != c.evidence_digest

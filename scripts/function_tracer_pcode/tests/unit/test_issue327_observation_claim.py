# -*- coding: utf-8 -*-
"""Issue #327 (E2): which return-observation elements binary evidence verifies.

Pins the decisions of #327 (2026-11-27, revised before merge):

* E-a (SMT_PARITY) is an evidence level of an ASSUMED element and never verifies;
* the E-b fact (callers demand the register, the callee's own flow writes it,
  one symbol names the entry) verifies O1 only: O2 needs C-b5 (a memory-returned
  aggregate's address or an internally narrowed value may sit in the result
  register) and O3 needs C-b5 and H3, which production cannot confirm;
* E-b and E-d alone verify nothing; a lack of evidence is never a CONFLICT;
* CONFLICT is a positive contradiction on a single-class-return ABI only;
* R_V is empty unless every element of both sides is verified, never wider than R_C;
* only evidence that decided an element (VERIFIED / CONFLICT) is relied on.
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
    relied_methods,
)

OK = EvidenceStatus.CONSULTED
C_B5 = Condition.STANDARD_CALLING_CONVENTION
H3 = Condition.NO_INTERPROCEDURAL_RELIANCE


def demand(int_mask=0, fp_mask=0, own_int=True, own_fp=False, status="SCANNED", symbols=1, callsites=True):
    sites = [{"call": 0x200, "caller": 0x100, "end": "CBRANCH", "demand": {"INT": int_mask, "FP": fp_mask}}]
    return {"status": status, "own_writes": {"INT": own_int, "FP": own_fp},
            "callsites": sites if callsites else [], "entry_symbol_count": symbols}


def side(value_class="INT", *, caller=None, caller_status=OK, parity=None, parity_status=OK, fmt=None, width=32,
         index=0, single=True, confirmed=frozenset()):
    return classify_side(
        index, value_class=value_class, register="x0" if value_class == "INT" else "z0",
        prototype_width_bits=width, caller_demand=caller, caller_demand_status=caller_status,
        smt_parity=parity, parity_status=parity_status, executed_format=fmt,
        single_class_return=single, confirmed=confirmed,
    )


def states(s):
    return [c.state for c in s.elements]


def test_the_caller_demand_fact_verifies_existence_only():
    s = side(caller=demand(int_mask=0xFFFFFFFF))
    assert s.element(E.O1_EXISTS).state is ElementState.VERIFIED
    assert s.element(E.O1_EXISTS).methods == (Method.CALLER_DEMAND,)
    # the register the callers read as the result need not hold the value itself without C-b5
    o2 = s.element(E.O2_CLASS)
    assert o2.state is ElementState.ASSUMED and o2.diagnostic_classes == ("INT",) and o2.unconfirmed == (C_B5,)
    o3 = s.element(E.O3_VALID_BITS)
    assert o3.state is ElementState.ASSUMED and o3.diagnostic_bits == 32 and o3.assumed == 32
    assert set(o3.unconfirmed) == {C_B5, H3}
    assert s.element(E.O4_FP_FORMAT).state is ElementState.NOT_APPLICABLE


def test_caller_demand_without_a_callee_write_verifies_nothing():
    # interprocedural register allocation may keep a caller value in the register (C-b2)
    s = side(caller=demand(int_mask=0xFFFFFFFF, own_int=False))
    assert ElementState.VERIFIED not in states(s)
    assert Condition.CALLEE_WRITES_REGISTER in s.element(E.O1_EXISTS).unconfirmed


def test_a_callee_write_alone_verifies_nothing():
    s = side(caller=demand(int_mask=0, own_int=True))
    assert ElementState.VERIFIED not in states(s)


@pytest.mark.parametrize("symbols", [0, 2])
def test_an_entry_shared_by_folded_functions_or_without_a_symbol_verifies_nothing(symbols):
    s = side(caller=demand(int_mask=0xFFFFFFFF, symbols=symbols))
    assert ElementState.VERIFIED not in states(s)
    assert s.element(E.O1_EXISTS).unconfirmed == (Condition.ENTRY_UNSHARED,)


@pytest.mark.parametrize("status", [EvidenceStatus.NOT_CONSULTED, EvidenceStatus.FAILED, EvidenceStatus.DEADLINE])
def test_evidence_not_consulted_verifies_nothing(status):
    s = side(caller=demand(int_mask=0xFF), caller_status=status)
    assert ElementState.VERIFIED not in states(s) and not s.conflict


@pytest.mark.parametrize("record_status", ["STOPPED", "NO_FUNCTION", "FAILED"])
def test_an_incomplete_scan_is_not_evidence(record_status):
    s = side(caller=demand(fp_mask=0xFF, own_fp=True, status=record_status))
    assert ElementState.VERIFIED not in states(s) and not s.conflict


def test_smt_parity_is_an_evidence_level_of_an_assumed_element_never_verification():
    s = side(parity={"complete": True, "payload_bits": 64}, width=64)
    for element in (E.O1_EXISTS, E.O2_CLASS, E.O3_VALID_BITS):
        claim = s.element(element)
        assert claim.state is ElementState.ASSUMED and claim.level is EvidenceLevel.SMT_PARITY
    assert s.element(E.O3_VALID_BITS).parity_bits == 64 and s.element(E.O3_VALID_BITS).bound_bits is None
    pair = classify_pair(s, side(parity={"complete": True, "payload_bits": 64}, width=64, index=1),
                         compared_bits=64, first_difference_bit=40, evidence={})
    assert pair.verified_bits == 0 and pair.difference_range is DifferenceRange.ASSUMED_RANGE_ONLY
    assert relied_methods(s) == frozenset()
    incomplete = side(parity={"complete": False, "payload_bits": None})
    assert incomplete.element(E.O1_EXISTS).level is EvidenceLevel.PROTOTYPE


def test_callers_reading_only_the_other_class_on_a_single_class_abi_is_a_conflict():
    s = side("INT", caller=demand(int_mask=0, fp_mask=0xFFFFFFFFFFFFFFFF, own_int=True, own_fp=True))
    o2 = s.element(E.O2_CLASS)
    assert o2.state is ElementState.CONFLICT and s.conflict
    assert o2.diagnostic_classes == ("FP",) and o2.unconfirmed == (C_B5,)   # the contradiction's own premise
    pair = classify_pair(s, side(index=1), compared_bits=32, first_difference_bit=0, evidence={})
    assert pair.conflict and pair.verified_bits == 0
    assert relied_methods(s) == {Method.CALLER_DEMAND}


def test_the_same_evidence_on_an_abi_not_known_to_be_single_class_is_not_a_contradiction():
    s = side("INT", caller=demand(int_mask=0, fp_mask=0xFF, own_int=True, own_fp=True), single=False)
    assert not s.conflict
    assert s.element(E.O1_EXISTS).state is ElementState.VERIFIED      # it returns a value
    o2 = s.element(E.O2_CLASS)
    assert o2.state is ElementState.ASSUMED and o2.diagnostic_classes == ("FP",)


@pytest.mark.parametrize("caller", [
    demand(callsites=False),                                  # no caller in the binary
    demand(int_mask=0, fp_mask=0),                            # callers read nothing
    demand(int_mask=0, fp_mask=0xFF, own_fp=False),           # the other class without a callee write
    demand(int_mask=0, fp_mask=0xFF, own_fp=True, symbols=2),  # the other class at a shared entry
])
def test_a_lack_of_evidence_is_never_a_conflict(caller):
    s = side("INT", caller=caller)
    assert not s.conflict and ElementState.VERIFIED not in states(s)


def test_both_classes_on_a_single_class_abi_is_inconsistent_evidence_and_not_used():
    s = side("INT", caller=demand(int_mask=0xFF, fp_mask=0xFF, own_int=True, own_fp=True))
    assert ElementState.VERIFIED not in states(s) and not s.conflict
    o1 = s.element(E.O1_EXISTS)
    assert o1.unconfirmed == (Condition.CONSISTENT_CLASS_EVIDENCE,) and o1.diagnostic_classes == ("FP", "INT")
    mixed = side("INT", caller=demand(int_mask=0xFF, fp_mask=0xFF, own_int=True, own_fp=True), single=False)
    assert mixed.element(E.O1_EXISTS).state is ElementState.VERIFIED and not mixed.conflict


def test_the_executed_format_without_a_verified_class_stays_assumed():
    s = side("FP", caller=demand(fp_mask=0xFFFFFFFFFFFFFFFF, own_int=False, own_fp=True), fmt="BINARY64", width=128)
    assert s.element(E.O1_EXISTS).state is ElementState.VERIFIED
    assert s.element(E.O2_CLASS).state is ElementState.ASSUMED
    assert s.element(E.O4_FP_FORMAT).state is ElementState.ASSUMED
    assert Condition.VERIFIED_LOCATION in s.element(E.O4_FP_FORMAT).unconfirmed
    assert s.element(E.O3_VALID_BITS).state is ElementState.ASSUMED


def test_a_producer_that_confirms_the_conditions_is_the_only_way_to_verify_class_and_bits():
    # the extension point (#327 Preferred design); nothing in production confirms C-b5 / H3 today
    fp = dict(caller=demand(fp_mask=0xFFFFFFFFFFFFFFFF, own_int=False, own_fp=True), fmt="BINARY64", width=128,
              confirmed=frozenset({C_B5}))
    left, right = side("FP", **fp), side("FP", index=1, **fp)
    assert left.element(E.O2_CLASS).state is ElementState.VERIFIED
    assert left.element(E.O4_FP_FORMAT).state is ElementState.VERIFIED
    assert left.element(E.O3_VALID_BITS).bound_bits == 64
    pair = classify_pair(left, right, compared_bits=64, first_difference_bit=None, evidence={})
    assert pair.verified_bits == 64 and pair.difference_range is DifferenceRange.VERIFIED_RANGE
    narrow = classify_pair(left, right, compared_bits=32, first_difference_bit=3, evidence={})
    assert narrow.verified_bits == 32                                  # never wider than R_C
    assumed = side("FP", fmt="BINARY64", index=1)
    assert classify_pair(left, assumed, compared_bits=64, first_difference_bit=3, evidence={}).verified_bits == 0

    only_cb5 = side(caller=demand(int_mask=0xFF), confirmed=frozenset({C_B5}))
    assert only_cb5.element(E.O3_VALID_BITS).state is ElementState.ASSUMED
    assert only_cb5.element(E.O3_VALID_BITS).unconfirmed == (H3,)
    both = side(caller=demand(int_mask=0xFF), confirmed=frozenset({C_B5, H3}))
    assert both.element(E.O3_VALID_BITS).state is ElementState.VERIFIED and both.element(E.O3_VALID_BITS).bound_bits == 8


def test_no_default_width_an_integer_value_is_never_verified():
    # a difference in the lowest byte does not make O3 verified (v2.1 §2.3)
    s = side(caller=demand(int_mask=0xFF))
    pair = classify_pair(s, side(caller=demand(int_mask=0xFF), index=1), compared_bits=32, first_difference_bit=0,
                         evidence={})
    assert pair.verified_bits == 0 and pair.difference_range is DifferenceRange.ASSUMED_RANGE_ONLY


def test_only_evidence_that_decided_an_element_is_relied_on():
    assert relied_methods(side(caller=demand(int_mask=0xFF))) == {Method.CALLER_DEMAND}     # O1 verified
    assert relied_methods(side(caller=demand(int_mask=0xFF, own_int=False))) == frozenset()  # diagnostic only
    assert relied_methods(side("FP", fmt="BINARY32")) == frozenset()                          # format annotates


def test_the_evidence_digest_is_deterministic_and_covers_the_evidence():
    a = classify_pair(side(), side(index=1), compared_bits=32, first_difference_bit=0, evidence={"x": 1})
    b = classify_pair(side(), side(index=1), compared_bits=32, first_difference_bit=0, evidence={"x": 1})
    c = classify_pair(side(), side(index=1), compared_bits=32, first_difference_bit=0, evidence={"x": 2})
    assert a.evidence_digest == b.evidence_digest != c.evidence_digest

# -*- coding: utf-8 -*-
"""Which elements of a concrete return observation binary evidence verified (Issue #327, E2).

A concrete difference compares bits of one return register.  That comparison
is only a difference *of the functions' return values* if, on both sides:

* O1 -- the function returns a value (it is not void);
* O2 -- the compared register holds bits of that value (the value's class);
* O3 -- the compared bits are defined bits of the value;
* O4 -- for a floating-point value, the bits are read in the value's format.

This module classifies each element of each side into one **state**:

``VERIFIED``
    an accepted method's conditions all hold (the method is recorded);
``ASSUMED``
    no accepted method verified it: the comparison used the recovered
    prototype's value, and the conditional verdict names it as a residual
    assumption.  An assumed element carries the **evidence level** behind the
    assumption -- ``PROTOTYPE`` (the recovered prototype only) or
    ``SMT_PARITY`` (the symbolic path's static return-width proof completed for
    this side: the same premise an SMT NOT_EQ rests on, still not independent
    of the prototype) -- and, when one exists, the **diagnostic** evidence that
    was seen but does not verify it (with the conditions left unconfirmed);
``CONFLICT``
    two pieces of evidence contradict each other positively: the concrete
    difference is refused;
``NOT_APPLICABLE``
    O4 of an integer value.

Two comparison ranges are recorded and kept apart:

* R_C, the **conditional comparison range**: exactly what the comparison read
  (``concrete.observation.compared_extent``).  Nothing here changes it.
* R_V, the **verified comparison range**: bits from bit 0 that every element of
  both sides verifies; empty unless all of O1-O3 (and O4) are ``VERIFIED`` on
  both sides; never wider than R_C.  It decides nothing today; it is the only
  range a later main-verdict contract may rely on without an observation
  assumption.

Accepted methods and why (the evidence is plain data produced elsewhere:
``ghidra.return_use_evidence`` reads the program; this module reads no program
and no analysis):

* **E-b, callers' demanded bits**, verifies O1 and O2 when a direct call to the
  entry (C-b1) is followed by straight-line code (C-b6) whose sinks demand bits
  of the compared register (C-b3, exact or under-approximating), and the
  callee's own instructions write that register (C-b2: under interprocedural
  register allocation a caller may keep a value in a register the callee
  provably preserves, even across a void function; a callee that writes the
  register on some path cannot be relied on to preserve it).  A correctly
  compiled caller then reads that register only as the callee's result: the
  function returns a value and the register holds bits of it, whatever calling
  convention the compiler chose for the call (C-b5 is not needed for O1/O2).
  E-b does **not** verify O3: that the demanded bits are *defined bits of the
  value* additionally needs the call to follow the standard calling
  convention (C-b5: Ghidra's convention name does not reveal a compiler-internal
  one) and the caller not to rely on interprocedural knowledge of the callee
  beyond the ABI (H3: a known value range or extension).  Neither can be
  confirmed from the binary today, so E-b's demanded width is recorded as
  diagnostic evidence of an ``ASSUMED`` O3 with both conditions named.
* **E-e, the executed format**: the run reports the format of the scalar
  floating-point instruction that produced the compared bits.  With O2
  verified (the register holds bits of the value) it verifies O4, and O3 of a
  floating-point value follows from O4 (the format's width).
* **E-a, the static return-width provenance** (``SMT_PARITY``) is never a
  verifying method: it agrees with the recovered prototype's width whenever
  both exist and inherits the prototype's errors (#327 PoC).  It is an evidence
  level of an assumed element only.
* **E-d, a write of the register** alone shows nothing (a void function may use
  the register as scratch); it is only C-b2.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from enum import Enum
from typing import Any, Mapping, Optional, Tuple

OBSERVATION_CLAIM_VERSION = "return-observation-claim-v1"

VALUE_CLASSES = ("INT", "FP")


class ObservationElement(str, Enum):
    O1_EXISTS = "O1_EXISTS"
    O2_CLASS = "O2_CLASS"
    O3_VALID_BITS = "O3_VALID_BITS"
    O4_FP_FORMAT = "O4_FP_FORMAT"


class ElementState(str, Enum):
    VERIFIED = "VERIFIED"
    ASSUMED = "ASSUMED"
    CONFLICT = "CONFLICT"
    NOT_APPLICABLE = "NOT_APPLICABLE"


class EvidenceLevel(str, Enum):
    """The evidence behind an ``ASSUMED`` element."""

    PROTOTYPE = "PROTOTYPE"
    SMT_PARITY = "SMT_PARITY"


class Method(str, Enum):
    CALLER_DEMAND = "E-b"
    EXECUTED_FORMAT = "E-e"


class Condition(str, Enum):
    """Conditions of a method that could not be confirmed (named on the element)."""

    #: the call follows the standard calling convention (not confirmable from the binary today)
    STANDARD_CALLING_CONVENTION = "C-b5_standard_calling_convention"
    #: the caller relies on no interprocedural knowledge of the callee beyond the ABI
    NO_INTERPROCEDURAL_RELIANCE = "H3_no_interprocedural_reliance"
    #: the callee's own instructions write the register (C-b2) -- failed
    CALLEE_WRITES_REGISTER = "C-b2_callee_writes_register"
    #: the compared register is the one the callers read (O2 verified) -- missing
    VERIFIED_LOCATION = "O2_verified"


class EvidenceStatus(str, Enum):
    """Whether a method's evidence was consulted for a side."""

    CONSULTED = "CONSULTED"
    #: not requested (no confirmation needed a classification)
    NOT_CONSULTED = "NOT_CONSULTED"
    #: the producer raised or returned an incomplete record: not used (fail closed)
    FAILED = "FAILED"
    #: the pair's analysis deadline had passed: not read
    DEADLINE = "DEADLINE"


@dataclass(frozen=True)
class ElementClaim:
    element: ObservationElement
    state: ElementState
    level: Optional[EvidenceLevel] = None
    methods: Tuple[Method, ...] = ()
    bound_bits: Optional[int] = None
    assumed: Optional[Any] = None
    diagnostic_bits: Optional[int] = None
    unconfirmed: Tuple[Condition, ...] = ()
    #: the SMT_PARITY width (the completed static return-width proof's payload width); a record of the
    #: evidence level, never a verified bound
    parity_bits: Optional[int] = None

    def to_json(self) -> Mapping[str, Any]:
        return {
            "element": self.element.value,
            "state": self.state.value,
            "level": None if self.level is None else self.level.value,
            "methods": [m.value for m in self.methods],
            "bound_bits": self.bound_bits,
            "assumed": self.assumed,
            "diagnostic_bits": self.diagnostic_bits,
            "unconfirmed": [c.value for c in self.unconfirmed],
            "parity_bits": self.parity_bits,
        }

    def premise_record(self) -> Tuple[Tuple[str, Any], ...]:
        return tuple(sorted({
            "element": self.element.value,
            "state": self.state.value,
            "basis": None if self.level is None else self.level.value,
            "methods": tuple(m.value for m in self.methods),
            "bound_bits": self.bound_bits,
            "assumed": self.assumed,
            "unconfirmed": tuple(c.value for c in self.unconfirmed),
            "parity_bits": self.parity_bits,
        }.items()))


@dataclass(frozen=True)
class SideObservation:
    side: int
    register: str
    value_class: str
    elements: Tuple[ElementClaim, ...]
    caller_demand_status: EvidenceStatus
    parity_status: EvidenceStatus

    def element(self, element: ObservationElement) -> ElementClaim:
        return next(claim for claim in self.elements if claim.element is element)

    @property
    def assumed(self) -> Tuple[ElementClaim, ...]:
        return tuple(claim for claim in self.elements if claim.state is ElementState.ASSUMED)

    @property
    def conflict(self) -> bool:
        return any(claim.state is ElementState.CONFLICT for claim in self.elements)

    def to_json(self) -> Mapping[str, Any]:
        return {
            "side": self.side,
            "register": self.register,
            "value_class": self.value_class,
            "caller_demand": self.caller_demand_status.value,
            "smt_parity": self.parity_status.value,
            "elements": [claim.to_json() for claim in self.elements],
        }


class DifferenceRange(str, Enum):
    #: the difference lies in bits every element of both sides verifies
    VERIFIED_RANGE = "VERIFIED_RANGE"
    #: the difference lies only in bits that rest on an assumed element
    ASSUMED_RANGE_ONLY = "ASSUMED_RANGE_ONLY"


@dataclass(frozen=True)
class ObservationClassification:
    sides: Tuple[SideObservation, SideObservation]
    verified_bits: int
    compared_bits: int
    first_difference_bit: Optional[int]
    difference_range: DifferenceRange
    evidence_digest: str

    @property
    def conflict(self) -> bool:
        return any(side.conflict for side in self.sides)

    def to_json(self) -> Mapping[str, Any]:
        return {
            "version": OBSERVATION_CLAIM_VERSION,
            "verified_bits": self.verified_bits,
            "compared_bits": self.compared_bits,
            "first_difference_bit": self.first_difference_bit,
            "difference_range": self.difference_range.value,
            "conflict": self.conflict,
            "evidence_digest": self.evidence_digest,
            "sides": [side.to_json() for side in self.sides],
        }


# --------------------------------------------------------------- evidence input

def _caller_demand(evidence: Optional[Mapping[str, Any]]) -> Mapping[str, Mapping[str, Any]]:
    """Per value class: ``{"demanded": mask, "own_write": bool}`` from a
    ``ghidra.return_use_evidence.ReturnUseEvidence.to_json()`` record; empty when
    the record is missing or not a complete scan."""
    if not isinstance(evidence, Mapping) or evidence.get("status") != "SCANNED":
        return {}
    own = evidence.get("own_writes") or {}
    out = {}
    for value_class in VALUE_CLASSES:
        mask = 0
        for site in evidence.get("callsites") or ():
            demand = (site.get("demand") or {}).get(value_class, 0)
            if type(demand) is int and demand > 0:
                mask |= demand
        out[value_class] = {"demanded": mask, "own_write": own.get(value_class) is True}
    return out


def _prefix(mask: int) -> int:
    n = 0
    while (mask >> n) & 1:
        n += 1
    return n


def classify_side(
    side: int,
    *,
    value_class: str,
    register: str,
    prototype_width_bits: int,
    caller_demand: Optional[Mapping[str, Any]],
    caller_demand_status: EvidenceStatus,
    smt_parity: Optional[Mapping[str, Any]],
    parity_status: EvidenceStatus,
    executed_format: Optional[str],
) -> SideObservation:
    """Classify the four elements of one side (see the module docstring)."""
    if value_class not in VALUE_CLASSES:
        raise ValueError(f"unknown value class: {value_class}")
    parity = parity_status is EvidenceStatus.CONSULTED and isinstance(smt_parity, Mapping) and smt_parity.get("complete") is True
    level = EvidenceLevel.SMT_PARITY if parity else EvidenceLevel.PROTOTYPE
    demand = _caller_demand(caller_demand) if caller_demand_status is EvidenceStatus.CONSULTED else {}
    # E-b holds for a class when callers demand bits of its register and the callee writes it (C-b1/C-b3/C-b6
    # are properties of the producer's record; C-b2 is the own write)
    holds = {c for c, d in demand.items() if d["demanded"] and d["own_write"]}
    seen_without_write = {c for c, d in demand.items() if d["demanded"] and not d["own_write"]}
    other = "FP" if value_class == "INT" else "INT"

    if holds:
        o1 = ElementClaim(ObservationElement.O1_EXISTS, ElementState.VERIFIED, methods=(Method.CALLER_DEMAND,))
    else:
        o1 = ElementClaim(ObservationElement.O1_EXISTS, ElementState.ASSUMED, level, assumed=True,
                          unconfirmed=(Condition.CALLEE_WRITES_REGISTER,) if seen_without_write else ())
    if holds == {value_class}:
        o2 = ElementClaim(ObservationElement.O2_CLASS, ElementState.VERIFIED, methods=(Method.CALLER_DEMAND,))
    elif holds == {other}:
        o2 = ElementClaim(ObservationElement.O2_CLASS, ElementState.CONFLICT, methods=(Method.CALLER_DEMAND,),
                          assumed=value_class)
    else:
        o2 = ElementClaim(ObservationElement.O2_CLASS, ElementState.ASSUMED, level, assumed=value_class)

    if value_class == "INT":
        o4 = ElementClaim(ObservationElement.O4_FP_FORMAT, ElementState.NOT_APPLICABLE)
        diag = _prefix(demand["INT"]["demanded"]) if "INT" in holds else None
        o3 = ElementClaim(
            ObservationElement.O3_VALID_BITS, ElementState.ASSUMED, level,
            methods=(Method.CALLER_DEMAND,) if diag else (),
            assumed=prototype_width_bits,
            diagnostic_bits=diag,
            unconfirmed=(Condition.STANDARD_CALLING_CONVENTION, Condition.NO_INTERPROCEDURAL_RELIANCE) if diag else (),
            parity_bits=(smt_parity or {}).get("payload_bits") if parity else None,
        )
    else:
        format_bits = {"BINARY32": 32, "BINARY64": 64}.get(executed_format or "")
        if o2.state is ElementState.VERIFIED and format_bits:
            o4 = ElementClaim(ObservationElement.O4_FP_FORMAT, ElementState.VERIFIED,
                              methods=(Method.EXECUTED_FORMAT,), assumed=None, bound_bits=format_bits)
            o3 = ElementClaim(ObservationElement.O3_VALID_BITS, ElementState.VERIFIED,
                              methods=(Method.EXECUTED_FORMAT,), bound_bits=format_bits)
        else:
            o4 = ElementClaim(ObservationElement.O4_FP_FORMAT, ElementState.ASSUMED, level,
                              methods=(Method.EXECUTED_FORMAT,) if format_bits else (), assumed=executed_format,
                              unconfirmed=(Condition.VERIFIED_LOCATION,) if format_bits else ())
            o3 = ElementClaim(ObservationElement.O3_VALID_BITS, ElementState.ASSUMED, level,
                              assumed=format_bits or prototype_width_bits,
                              unconfirmed=(Condition.VERIFIED_LOCATION,) if format_bits else ())
    return SideObservation(side, register, value_class, (o1, o2, o3, o4), caller_demand_status, parity_status)


def classify_pair(
    left: SideObservation,
    right: SideObservation,
    *,
    compared_bits: int,
    first_difference_bit: Optional[int],
    evidence: Mapping[str, Any],
) -> ObservationClassification:
    """R_V, where the difference lies, and the digest of the evidence read."""
    verified = 0
    if not left.conflict and not right.conflict:
        bounds = []
        for side in (left, right):
            needed = [ObservationElement.O1_EXISTS, ObservationElement.O2_CLASS, ObservationElement.O3_VALID_BITS]
            if side.value_class == "FP":
                needed.append(ObservationElement.O4_FP_FORMAT)
            claims = [side.element(e) for e in needed]
            if any(c.state is not ElementState.VERIFIED for c in claims):
                bounds = None
                break
            bounds.append(side.element(ObservationElement.O3_VALID_BITS).bound_bits or 0)
        if bounds:
            verified = max(0, min(min(bounds), compared_bits))
    if first_difference_bit is None:
        # a difference between two sets of possible values covers the whole compared range
        in_verified = verified >= compared_bits > 0
    else:
        in_verified = first_difference_bit < verified
    digest = hashlib.sha256(json.dumps(
        {"sides": [left.to_json(), right.to_json()], "evidence": evidence, "compared_bits": compared_bits},
        sort_keys=True, separators=(",", ":"), default=repr,
    ).encode("utf-8")).hexdigest()
    return ObservationClassification(
        (left, right), verified, compared_bits, first_difference_bit,
        DifferenceRange.VERIFIED_RANGE if in_verified else DifferenceRange.ASSUMED_RANGE_ONLY, digest,
    )


__all__ = [
    "Condition", "DifferenceRange", "ElementClaim", "ElementState", "EvidenceLevel", "EvidenceStatus",
    "Method", "OBSERVATION_CLAIM_VERSION", "ObservationClassification", "ObservationElement",
    "SideObservation", "classify_pair", "classify_side",
]

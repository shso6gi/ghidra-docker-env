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

* **E-b, callers' demanded bits.**  For a value class, the *E-b fact* holds
  when the record is a complete scan (``SCANNED``) and

  - C-b1: a direct call to the entry is followed by straight-line code (C-b6)
    whose sinks demand bits of that class's register (C-b3: exact or
    under-approximating transfers);
  - C-b2: the callee's own flow from its entry writes that register (not a
    call inside it, not code Ghidra's function body merely contains);
  - C-b7: exactly one function / label symbol names the entry (identical
    code folding puts several functions at one entry; a stripped entry cannot
    be checked).

  What the fact shows: a caller reads the register after the call, and the
  callee clobbers it on its own path, so under interprocedural register
  allocation the caller cannot be relying on the register being preserved;
  a compiled call reads a register the callee clobbers only as the call's
  result.  Hence **O1 is verified**: the function returns a value.  This holds
  whatever convention the compiler chose for the call -- no translation turns
  a function without a result into one with a result -- and it rests only on
  the method's premise that the caller's code is a compiled, well-defined
  call of this function (the premise of E-b itself, v2 §6).

  **O2 is not verified by E-b** without C-b5 (the call follows the standard
  calling convention, which Ghidra's convention name does not reveal): the
  register the caller reads as the result need not hold the value itself.
  A memory-returned aggregate returns its address in the result register on
  some ABIs (MIPS n64), and an internal convention may return a narrowed
  value (a dead-member elimination keeps the function's name).  The classes
  the callers read are recorded as diagnostic evidence of an ``ASSUMED`` O2.

  **O3 is not verified by E-b** without C-b5 and H3 (the caller relies on no
  interprocedural knowledge of the callee beyond the ABI: a value range or an
  extension); its demanded width is diagnostic evidence of an ``ASSUMED`` O3.

  A later producer that confirms C-b5 (and H3) passes them in
  ``confirmed``; nothing in production confirms them today.
* **E-e, the executed format**: the run reports the format of the scalar
  floating-point instruction that produced the compared bits.  With O2
  verified it verifies O4, and O3 of a floating-point value follows from O4.
  (O2 is never verified today, so neither is O4.)
* **E-a, the static return-width provenance** (``SMT_PARITY``) is never a
  verifying method: it agrees with the recovered prototype's width whenever
  both exist and inherits the prototype's errors (#327 PoC).  It is an evidence
  level of an assumed element only.
* **E-d, a write of the register** alone shows nothing (a void function may use
  the register as scratch); it is only C-b2.

``CONFLICT`` is a positive contradiction, never a lack of evidence.  It is
produced for O2 only when the E-b fact holds for the *other* class and not
for the compared one, on an ABI whose return values occupy registers of one
class only (``single_class_return``: AAPCS64).  The contradiction itself rests
on the standard convention (C-b5, named on the element); a refusal only gives
up the difference, so it may rest on it, while verification may not.  On an
ABI not known to return each value in one class (MIPS n64: its small-aggregate
rules are not modelled) the same evidence is not a contradiction and is
recorded as diagnostic.  The E-b fact holding
for both classes on a single-class ABI is inconsistent evidence: E-b is then
not used at all (recorded as diagnostic).  No evidence, an incomplete scan,
callers that read nothing, or a failed producer leave elements ``ASSUMED``.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from enum import Enum
from typing import Any, FrozenSet, Mapping, Optional, Tuple

OBSERVATION_CLAIM_VERSION = "return-observation-claim-v2"

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

    #: the call follows the standard calling convention (not confirmable from the binary today): the
    #: result register holds the value itself (not a memory-returned aggregate's address, not a value an
    #: internal convention narrowed), at the ABI's bit positions
    STANDARD_CALLING_CONVENTION = "C-b5_standard_calling_convention"
    #: the caller relies on no interprocedural knowledge of the callee beyond the ABI
    NO_INTERPROCEDURAL_RELIANCE = "H3_no_interprocedural_reliance"
    #: the callee's own flow from its entry writes the register (C-b2) -- failed
    CALLEE_WRITES_REGISTER = "C-b2_callee_writes_register"
    #: exactly one function / label symbol names the entry (C-b7) -- failed or not checkable
    ENTRY_UNSHARED = "C-b7_entry_unshared"
    #: the E-b fact does not hold for both classes on a single-class ABI -- failed
    CONSISTENT_CLASS_EVIDENCE = "E-b_consistent_class_evidence"
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
    #: the value classes whose E-b fact held (diagnostic evidence of O2; never verification by itself)
    diagnostic_classes: Tuple[str, ...] = ()

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
            "diagnostic_classes": list(self.diagnostic_classes),
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
            "diagnostic_classes": self.diagnostic_classes,
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

def _caller_demand(evidence: Optional[Mapping[str, Any]]) -> Optional[Mapping[str, Any]]:
    """Per value class ``{"demanded": mask, "own_write": bool}`` and whether the
    entry is unshared (C-b7), from a ``ReturnUseEvidence.to_json()`` record;
    ``None`` when the record is missing or not a complete scan."""
    if not isinstance(evidence, Mapping) or evidence.get("status") != "SCANNED":
        return None
    own = evidence.get("own_writes") or {}
    classes = {}
    for value_class in VALUE_CLASSES:
        mask = 0
        for site in evidence.get("callsites") or ():
            demand = (site.get("demand") or {}).get(value_class, 0)
            if type(demand) is int and demand > 0:
                mask |= demand
        classes[value_class] = {"demanded": mask, "own_write": own.get(value_class) is True}
    count = evidence.get("entry_symbol_count")
    return {"classes": classes, "entry_unshared": type(count) is int and count == 1}


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
    single_class_return: bool = False,
    confirmed: FrozenSet[Condition] = frozenset(),
) -> SideObservation:
    """Classify the four elements of one side (see the module docstring).

    ``single_class_return``: the ABI returns every value in registers of one
    class (from the ABI table).  ``confirmed``: conditions a producer confirmed
    from the binary (none in production today)."""
    if value_class not in VALUE_CLASSES:
        raise ValueError(f"unknown value class: {value_class}")
    parity = parity_status is EvidenceStatus.CONSULTED and isinstance(smt_parity, Mapping) and smt_parity.get("complete") is True
    level = EvidenceLevel.SMT_PARITY if parity else EvidenceLevel.PROTOTYPE
    record = _caller_demand(caller_demand) if caller_demand_status is EvidenceStatus.CONSULTED else None
    classes = (record or {}).get("classes") or {}
    demanded = {c for c, d in classes.items() if d["demanded"]}
    written = {c for c in demanded if classes[c]["own_write"]}
    unshared = bool(record and record["entry_unshared"])
    # the E-b fact per class: C-b1/C-b3/C-b6 (demand from the producer's regions), C-b2 (own write), C-b7
    holds = written if unshared else set()
    other = "FP" if value_class == "INT" else "INT"
    inconsistent = single_class_return and holds == set(VALUE_CLASSES)
    diag_classes = tuple(sorted(holds))
    if inconsistent:
        holds = set()

    # O1: some class's E-b fact holds
    if holds:
        o1 = ElementClaim(ObservationElement.O1_EXISTS, ElementState.VERIFIED, methods=(Method.CALLER_DEMAND,))
    else:
        failed = []
        if demanded - written:
            failed.append(Condition.CALLEE_WRITES_REGISTER)
        if written and not unshared:
            failed.append(Condition.ENTRY_UNSHARED)
        if inconsistent:
            failed.append(Condition.CONSISTENT_CLASS_EVIDENCE)
        o1 = ElementClaim(ObservationElement.O1_EXISTS, ElementState.ASSUMED, level, assumed=True,
                          unconfirmed=tuple(failed), diagnostic_classes=diag_classes if inconsistent else ())

    # O2: verified only with C-b5 confirmed; a contradiction only on a single-class ABI
    standard = Condition.STANDARD_CALLING_CONVENTION in confirmed
    if holds == {value_class} and standard:
        o2 = ElementClaim(ObservationElement.O2_CLASS, ElementState.VERIFIED, methods=(Method.CALLER_DEMAND,),
                          diagnostic_classes=diag_classes)
    elif holds == {other} and single_class_return:
        o2 = ElementClaim(ObservationElement.O2_CLASS, ElementState.CONFLICT, methods=(Method.CALLER_DEMAND,),
                          assumed=value_class, diagnostic_classes=diag_classes,
                          unconfirmed=() if standard else (Condition.STANDARD_CALLING_CONVENTION,))
    else:
        o2 = ElementClaim(ObservationElement.O2_CLASS, ElementState.ASSUMED, level, assumed=value_class,
                          methods=(Method.CALLER_DEMAND,) if holds else (), diagnostic_classes=diag_classes,
                          unconfirmed=(Condition.STANDARD_CALLING_CONVENTION,) if holds and not standard else ())

    if value_class == "INT":
        o4 = ElementClaim(ObservationElement.O4_FP_FORMAT, ElementState.NOT_APPLICABLE)
        diag = _prefix(classes["INT"]["demanded"]) if "INT" in holds else None
        missing = tuple(c for c in (Condition.STANDARD_CALLING_CONVENTION, Condition.NO_INTERPROCEDURAL_RELIANCE)
                        if c not in confirmed)
        if diag and o2.state is ElementState.VERIFIED and not missing:
            o3 = ElementClaim(ObservationElement.O3_VALID_BITS, ElementState.VERIFIED,
                              methods=(Method.CALLER_DEMAND,), bound_bits=diag)
        else:
            o3 = ElementClaim(
                ObservationElement.O3_VALID_BITS, ElementState.ASSUMED, level,
                methods=(Method.CALLER_DEMAND,) if diag else (),
                assumed=prototype_width_bits,
                diagnostic_bits=diag,
                unconfirmed=missing if diag else (),
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


def relied_methods(side: SideObservation) -> FrozenSet[Method]:
    """The methods whose evidence decided an element of ``side`` (a ``VERIFIED``
    or ``CONFLICT`` state).  Evidence that only annotates an assumed element
    (its level, a diagnostic) decides nothing and is not relied on."""
    return frozenset(
        method for claim in side.elements
        if claim.state in (ElementState.VERIFIED, ElementState.CONFLICT) for method in claim.methods
    )


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
    "SideObservation", "classify_pair", "classify_side", "relied_methods",
]

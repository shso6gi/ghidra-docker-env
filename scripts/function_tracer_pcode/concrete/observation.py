# -*- coding: utf-8 -*-
"""The observation surface: what is compared after two concrete runs.

Today the surface has one component, the value in the ABI return register.
Memory written through pointer arguments or to globals, and other side
effects, are not observed: a ``ReturnObservationPlan`` says nothing about
them, and a difference claimed from it is a difference of the return value
only.  Further components are added next to ``ReturnObservationPlan``; nothing
in this module reads or replaces the symbolic memory/effect analysis.

An observation is a read.  A run reports, with the value of the return
register, how many of its low-order bytes are *defined* at return (bound at
entry or written by the run); bytes that are not defined are never compared.

Integer class.  The values are compared on the low ``k`` bytes, ``k`` being
the smallest of the two recovered widths and the two defined widths.  A
difference there is a difference of the returned value under every width
reading; equality there is only equality of that part and proves nothing.

Floating-point class.  Two bit patterns can only be compared as values of one
known format: binary32 1.0 (``0x3F800000``) and binary64 1.0
(``0x3FF0000000000000``) are different bits and the same number, and which
bytes of the register are the value at all depends on the format.  The format
is not inferred from the shape of the value.  It is *evidence from the run*:
the executor reports, with the register, the format of the scalar
floating-point write that produced its value (``ObservedRegister.value_format``),
and reports nothing when the value was not produced by such a write (a vector
operation, an aggregate, a copy of bytes of unknown meaning).  Then:

* each side must carry that evidence, and the two formats must be equal;
* the evidence must agree with the recovered storage width (4 bytes is
  binary32, 8 bytes is binary64; a 16-byte location -- AArch64 reports the
  whole 128-bit register for many functions that return a ``double`` --
  accepts either);
* the bytes of the format must be defined, and on a 16-byte location every
  defined byte above the format must be zero (a scalar write clears them; a
  non-zero byte there means the register holds something wider);
* a NaN on either side refuses the comparison: the executor's arithmetic is
  not guaranteed to preserve NaN payloads or signalling state;
* otherwise the bits of the format are compared.

What this module cannot see.  Different bits of one format are different
values, but they are not always a difference *between the functions*: a C
compiler may contract ``a * b + c`` into one fused operation, and two builds
of the same source then return results that differ in the last place
(measured on the target machine: one source, ``gcc -O0`` against ``gcc -O2``,
two of fourteen inputs).  That is a property of the run, not of the returned
bits, and it applies to an integer computed from floating-point values just
as well.  The executor's monitors (``concrete.value_monitor``) follow it, and
the same for undefined integer operations: a run reports, per observed
register, how many low-order bytes are free of such doubt
(``ObservedRegister.reliable_low_bytes``), and only those are compared; a
doubt that reached the run's control flow is a hazard of the whole run.  A
value whose only doubt is the build's rounding choice carries every value a
conforming build may hold (``ObservedRegister.rounding_values``); it differs
from the other side's value only when the two sets of possible values are
disjoint and hold no NaN -- exact sets, no tolerance.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Optional, Tuple, Union

from scripts.function_tracer_pcode.concrete.abi import AbiModel, ArgClass
from scripts.function_tracer_pcode.concrete.storage import StorageLocation


class ObservationRefusal(str, Enum):
    """Why a return location or a comparison was not accepted."""

    RETURN_VOID = "RETURN_VOID"
    # The recovered prototype returns a pointer: its value is an address whose
    # placement two binaries do not share (#18).
    RETURN_TYPE_POINTER = "RETURN_TYPE_POINTER"
    RETURN_NOT_IN_REGISTER = "RETURN_NOT_IN_REGISTER"
    RETURN_NOT_SINGLE_LOCATION = "RETURN_NOT_SINGLE_LOCATION"
    RETURN_REGISTER_NOT_A_RETURN_REGISTER = "RETURN_REGISTER_NOT_A_RETURN_REGISTER"
    RETURN_NOT_LOW_PART_OF_REGISTER = "RETURN_NOT_LOW_PART_OF_REGISTER"
    RETURN_WIDTH_UNSUPPORTED = "RETURN_WIDTH_UNSUPPORTED"
    RETURN_CLASS_MISMATCH = "RETURN_CLASS_MISMATCH"
    RETURN_VALUE_NOT_DEFINED = "RETURN_VALUE_NOT_DEFINED"
    FP_FORMAT_UNRESOLVED = "FP_FORMAT_UNRESOLVED"
    NAN_OBSERVED = "NAN_OBSERVED"
    # The compared bytes are not known to be what every conforming build
    # computes on this input (a signed overflow, a rounding choice, a NaN, ...;
    # ``ObservedRegister.unreliable`` says which), or the run did not report it.
    VALUE_NOT_RELIABLE = "VALUE_NOT_RELIABLE"


class ObservationRelation(str, Enum):
    DIFFERENT = "DIFFERENT"
    NOT_DIFFERENT_ON_OBSERVED_PART = "NOT_DIFFERENT_ON_OBSERVED_PART"


class FpFormat(str, Enum):
    BINARY32 = "BINARY32"
    BINARY64 = "BINARY64"


_INT_WIDTHS = (1, 2, 4, 8)
_FP_WIDTHS = (4, 8, 16)


@dataclass(frozen=True)
class ReturnStorage:
    """Where a function's recovered return value lives (binary storage facts).

    ``is_void`` is the recovered prototype saying nothing is returned;
    ``locations`` are the storage pieces of the return value; ``is_pointer``
    is the recovered prototype saying the value is a pointer.
    """

    is_void: bool
    locations: Tuple[StorageLocation, ...]
    is_pointer: bool = False


@dataclass(frozen=True)
class ReturnLocation:
    arg_class: ArgClass
    register: str
    register_bytes: int
    width_bytes: int


def return_location(
    abi: AbiModel, storage: ReturnStorage
) -> Union[ReturnLocation, ObservationRefusal]:
    if storage.is_void:
        return ObservationRefusal.RETURN_VOID
    if storage.is_pointer:
        return ObservationRefusal.RETURN_TYPE_POINTER
    if len(storage.locations) != 1:
        return ObservationRefusal.RETURN_NOT_SINGLE_LOCATION
    location = storage.locations[0]
    if not location.is_register or not location.base_register_name:
        return ObservationRefusal.RETURN_NOT_IN_REGISTER
    arg_class = abi.return_class_of(location.base_register_name)
    if arg_class is None:
        return ObservationRefusal.RETURN_REGISTER_NOT_A_RETURN_REGISTER
    register_bytes = (
        abi.register_bytes if arg_class is ArgClass.INT else abi.fp_return_register_bytes
    )
    widths = _INT_WIDTHS if arg_class is ArgClass.INT else _FP_WIDTHS
    if location.size_bytes not in widths or location.size_bytes > register_bytes:
        return ObservationRefusal.RETURN_WIDTH_UNSUPPORTED
    if not location.is_low_order_part(abi.big_endian):
        return ObservationRefusal.RETURN_NOT_LOW_PART_OF_REGISTER
    return ReturnLocation(
        arg_class, location.base_register_name, register_bytes, location.size_bytes
    )


@dataclass(frozen=True)
class ReturnObservationPlan:
    """Which two return registers are compared, and with which recovered widths.

    ``narrowed`` records that the two locations reported different widths.
    """

    arg_class: ArgClass
    locations: Tuple[ReturnLocation, ReturnLocation]
    narrowed: bool


def plan_return_observation(
    left: ReturnLocation, right: ReturnLocation
) -> Union[ReturnObservationPlan, ObservationRefusal]:
    if left.arg_class is not right.arg_class:
        return ObservationRefusal.RETURN_CLASS_MISMATCH
    return ReturnObservationPlan(
        left.arg_class, (left, right), left.width_bytes != right.width_bytes
    )


@dataclass(frozen=True)
class ObservedRegister:
    """The value of a register at return and how much of it is defined.

    ``defined_low_bytes`` counts the contiguous low-order bytes that were bound
    at entry or written by the run.

    ``value_format`` is the format of the scalar floating-point write that
    produced the value, as the executor established it from the run (through
    whole-register copies of that value); ``None`` when the value was not
    produced by such a write or the executor did not establish it.

    ``reliable_low_bytes`` counts the low-order bytes whose value does not
    depend on an undefined operation or on a rounding choice of the build;
    only those are compared.
    """

    value: int
    defined_low_bytes: int
    value_format: Optional[FpFormat] = None
    # Low-order bytes free of every monitor's doubt (``concrete.value_monitor``);
    # ``None`` = not reported, and then nothing of the value is compared.
    reliable_low_bytes: Optional[int] = None
    # Why the bytes above ``reliable_low_bytes`` are in doubt (``HazardKind``
    # values), for diagnosis.
    unreliable: Tuple[str, ...] = ()
    # When the only doubt is the build's rounding choice
    # (``FP_ROUNDING_SENSITIVE``): every value a conforming build may hold in
    # the low ``rounding_bytes`` bytes, the machine's among them; else empty.
    rounding_values: Tuple[int, ...] = ()
    rounding_bytes: int = 0

    def reliable_for(self, byte_count: int) -> bool:
        return self.reliable_low_bytes is not None and self.reliable_low_bytes >= byte_count

    def possible_values(self, byte_count: int) -> Optional[Tuple[int, ...]]:
        """The values the low ``byte_count`` bytes may have in a conforming
        build of the same source, or ``None`` when that is not known."""
        if self.reliable_for(byte_count):
            return (_low(self.value, byte_count),)
        if (self.rounding_bytes == byte_count and self.rounding_values
                and self.unreliable == ("FP_ROUNDING_SENSITIVE",)
                and _low(self.value, byte_count) in self.rounding_values):
            return self.rounding_values
        return None


def _low(value: int, byte_count: int) -> int:
    return value & ((1 << (byte_count * 8)) - 1)


def _is_nan(bits: int, fmt: FpFormat) -> bool:
    if fmt is FpFormat.BINARY32:
        bits = _low(bits, 4)
        return (bits & 0x7F800000) == 0x7F800000 and (bits & 0x007FFFFF) != 0
    bits = _low(bits, 8)
    return (bits & 0x7FF0000000000000) == 0x7FF0000000000000 and (
        bits & 0x000FFFFFFFFFFFFF
    ) != 0


_FORMAT_BYTES = {FpFormat.BINARY32: 4, FpFormat.BINARY64: 8}
# Formats a recovered storage width is compatible with.
_WIDTH_FORMATS = {
    4: (FpFormat.BINARY32,),
    8: (FpFormat.BINARY64,),
    16: (FpFormat.BINARY32, FpFormat.BINARY64),
}


def _fp_value(
    location: ReturnLocation, observed: ObservedRegister
) -> Union[Tuple[FpFormat, int], ObservationRefusal]:
    """The format and the bits of one side's floating-point return value."""
    fmt = observed.value_format
    if fmt is None or fmt not in _WIDTH_FORMATS[location.width_bytes]:
        return ObservationRefusal.FP_FORMAT_UNRESOLVED
    format_bytes = _FORMAT_BYTES[fmt]
    defined = min(observed.defined_low_bytes, location.width_bytes)
    if defined < format_bytes:
        return ObservationRefusal.RETURN_VALUE_NOT_DEFINED
    if _low(observed.value, defined) >> (format_bytes * 8):
        # Defined bytes above the scalar: the register holds something wider.
        return ObservationRefusal.FP_FORMAT_UNRESOLVED
    return fmt, _low(observed.value, format_bytes)


def compare_return_values(
    plan: ReturnObservationPlan, left: ObservedRegister, right: ObservedRegister
) -> Union[ObservationRelation, ObservationRefusal]:
    """Compare the two return registers under ``plan``."""
    observed = (left, right)
    if plan.arg_class is ArgClass.INT:
        compare_bytes = min(
            min(location.width_bytes, value.defined_low_bytes)
            for location, value in zip(plan.locations, observed)
        )
        if compare_bytes <= 0:
            return ObservationRefusal.RETURN_VALUE_NOT_DEFINED
        if not all(value.reliable_for(compare_bytes) for value in observed):
            return ObservationRefusal.VALUE_NOT_RELIABLE
    else:
        sides = []
        for location, value in zip(plan.locations, observed):
            side = _fp_value(location, value)
            if isinstance(side, ObservationRefusal):
                return side
            sides.append(side)
        if sides[0][0] is not sides[1][0]:
            return ObservationRefusal.FP_FORMAT_UNRESOLVED
        fmt = sides[0][0]
        if any(_is_nan(bits, fmt) for _, bits in sides):
            return ObservationRefusal.NAN_OBSERVED
        compare_bytes = _FORMAT_BYTES[fmt]
        if not all(value.reliable_for(compare_bytes) for value in observed):
            # A rounding-sensitive value is compared by its whole set of
            # possible values: different only if no value of one side is a
            # value of the other (exact sets, no tolerance).
            possible = [value.possible_values(compare_bytes) for value in observed]
            if any(p is None for p in possible):
                return ObservationRefusal.VALUE_NOT_RELIABLE
            if any(_is_nan(bits, fmt) for p in possible for bits in p):
                return ObservationRefusal.VALUE_NOT_RELIABLE
            if set(possible[0]).isdisjoint(possible[1]):
                return ObservationRelation.DIFFERENT
            return ObservationRefusal.VALUE_NOT_RELIABLE
    if _low(left.value, compare_bytes) != _low(right.value, compare_bytes):
        return ObservationRelation.DIFFERENT
    return ObservationRelation.NOT_DIFFERENT_ON_OBSERVED_PART

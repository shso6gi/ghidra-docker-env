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

Floating-point class.  A difference of bits is evidence only if neither value
can be a NaN, because the executor's floating-point arithmetic is not
guaranteed to preserve NaN payloads or signalling state; and whether a bit
pattern is a NaN depends on its format.  Each side's *admissible formats* are
derived from its recovered width, its defined bytes and its value:

* width 4: binary32;
* width 8: binary64;
* width 16 (AArch64 reports the whole 128-bit register for many functions
  that return a ``double``): the upper 8 bytes, when defined, must be zero --
  otherwise the value is a binary128 or a vector and is not compared.  Then
  binary64 is admissible, and binary32 as well when bits 32..63 are zero (an
  AArch64 single-precision write clears every higher bit of the register, so
  a binary32 result always has that shape, and a value of that shape may be
  one); with fewer than 8 defined bytes only binary32 is.

The two sides must share a format.  A value that is a NaN under *any* of its
own admissible formats refuses the comparison.  The bits are compared on 8
bytes when binary64 is shared and on 4 bytes otherwise; when both formats are
shared, bits 32..63 are zero on both sides and the two comparisons agree.

Limit: a vector or homogeneous aggregate returned in the FP register is read
as one of the scalar formats above, so a NaN in a lane is not recognised here.
A run whose floating-point operations touched a NaN is to be excluded by the
executor's hazards, which do not depend on the format.
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
    RETURN_NOT_IN_REGISTER = "RETURN_NOT_IN_REGISTER"
    RETURN_NOT_SINGLE_LOCATION = "RETURN_NOT_SINGLE_LOCATION"
    RETURN_REGISTER_NOT_A_RETURN_REGISTER = "RETURN_REGISTER_NOT_A_RETURN_REGISTER"
    RETURN_NOT_LOW_PART_OF_REGISTER = "RETURN_NOT_LOW_PART_OF_REGISTER"
    RETURN_WIDTH_UNSUPPORTED = "RETURN_WIDTH_UNSUPPORTED"
    RETURN_CLASS_MISMATCH = "RETURN_CLASS_MISMATCH"
    RETURN_VALUE_NOT_DEFINED = "RETURN_VALUE_NOT_DEFINED"
    FP_FORMAT_UNRESOLVED = "FP_FORMAT_UNRESOLVED"
    NAN_OBSERVED = "NAN_OBSERVED"


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
    ``locations`` are the storage pieces of the return value.
    """

    is_void: bool
    locations: Tuple[StorageLocation, ...]


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
    """

    value: int
    defined_low_bytes: int


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


def _admissible_fp_formats(
    location: ReturnLocation, observed: ObservedRegister
) -> Union[Tuple[FpFormat, ...], ObservationRefusal]:
    defined = min(observed.defined_low_bytes, location.width_bytes)
    if location.width_bytes == 4:
        return (FpFormat.BINARY32,) if defined >= 4 else ObservationRefusal.RETURN_VALUE_NOT_DEFINED
    if location.width_bytes == 8:
        return (FpFormat.BINARY64,) if defined >= 8 else ObservationRefusal.RETURN_VALUE_NOT_DEFINED
    # 16-byte location.
    if defined < 4:
        return ObservationRefusal.RETURN_VALUE_NOT_DEFINED
    if defined < 8:
        return (FpFormat.BINARY32,)
    if _low(observed.value, defined) >> 64:
        return ObservationRefusal.FP_FORMAT_UNRESOLVED
    if (_low(observed.value, 8) >> 32) == 0:
        return (FpFormat.BINARY64, FpFormat.BINARY32)
    return (FpFormat.BINARY64,)


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
    else:
        formats = []
        for location, value in zip(plan.locations, observed):
            admissible = _admissible_fp_formats(location, value)
            if isinstance(admissible, ObservationRefusal):
                return admissible
            formats.append(admissible)
        shared = [fmt for fmt in formats[0] if fmt in formats[1]]
        if not shared:
            return ObservationRefusal.FP_FORMAT_UNRESOLVED
        for admissible, value in zip(formats, observed):
            if any(_is_nan(value.value, fmt) for fmt in admissible):
                return ObservationRefusal.NAN_OBSERVED
        compare_bytes = 8 if FpFormat.BINARY64 in shared else 4
    if _low(left.value, compare_bytes) != _low(right.value, compare_bytes):
        return ObservationRelation.DIFFERENT
    return ObservationRelation.NOT_DIFFERENT_ON_OBSERVED_PART

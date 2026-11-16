# -*- coding: utf-8 -*-
"""The observation surface: what is compared after two concrete runs.

Today the surface has one component, the value in the ABI return register.
Memory written through pointer arguments or to globals, and other side
effects, are not observed: a ``ReturnObservationPlan`` says nothing about
them, and a difference claimed from it is a difference of the return value
only.  Further components are added next to ``ReturnObservationPlan``; nothing
in this module reads or replaces the symbolic memory/effect analysis.

Rules (all from the ABI and from the recovered storage of the binary):

* the two return locations must be of the same class (integer / FP);
* integer class: the values are compared on the low ``min(width)`` bytes.  A
  difference there is a difference under every width reading; equality there
  is only equality of that part and proves nothing;
* floating-point class: the two widths must name one IEEE format.  A 16-byte
  location is read as binary64 only when the upper 8 bytes of *both* observed
  values are zero (a binary64 result written to the register clears them, and
  a zero upper half cannot be a binary128 NaN);
* a NaN on either side is not comparable: the executor's floating-point
  arithmetic is not guaranteed to preserve NaN payloads or signalling state.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Optional, Union

from scripts.function_tracer_pcode.concrete.abi import AbiModel, ArgClass


class ObservationRefusal(str, Enum):
    """Why a return location or a comparison was not accepted."""

    RETURN_VOID = "RETURN_VOID"
    RETURN_NOT_IN_REGISTER = "RETURN_NOT_IN_REGISTER"
    RETURN_NOT_SINGLE_LOCATION = "RETURN_NOT_SINGLE_LOCATION"
    RETURN_REGISTER_NOT_A_RETURN_REGISTER = "RETURN_REGISTER_NOT_A_RETURN_REGISTER"
    RETURN_NOT_LOW_PART_OF_REGISTER = "RETURN_NOT_LOW_PART_OF_REGISTER"
    RETURN_WIDTH_UNSUPPORTED = "RETURN_WIDTH_UNSUPPORTED"
    RETURN_CLASS_MISMATCH = "RETURN_CLASS_MISMATCH"
    FP_FORMAT_UNRESOLVED = "FP_FORMAT_UNRESOLVED"
    NAN_OBSERVED = "NAN_OBSERVED"


class ObservationRelation(str, Enum):
    DIFFERENT = "DIFFERENT"
    NOT_DIFFERENT_ON_OBSERVED_PART = "NOT_DIFFERENT_ON_OBSERVED_PART"


_INT_WIDTHS = (1, 2, 4, 8)
_FP_WIDTHS = (4, 8, 16)


@dataclass(frozen=True)
class ReturnStorage:
    """Where a function's recovered return value lives (binary storage facts).

    ``location_count`` is the number of storage pieces; ``is_void`` is the
    recovered prototype saying nothing is returned.  ``bit_offset_in_base``
    follows ``core.storage.StorageInfo`` (address-based).
    """

    is_void: bool
    location_count: int
    is_register: bool
    base_register_name: Optional[str]
    base_register_bits: int
    bit_offset_in_base: int
    size_bytes: int


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
    if storage.location_count != 1:
        return ObservationRefusal.RETURN_NOT_SINGLE_LOCATION
    if not storage.is_register or not storage.base_register_name:
        return ObservationRefusal.RETURN_NOT_IN_REGISTER
    arg_class = abi.return_class_of(storage.base_register_name)
    if arg_class is None:
        return ObservationRefusal.RETURN_REGISTER_NOT_A_RETURN_REGISTER
    register_bytes = (
        abi.register_bytes if arg_class is ArgClass.INT else abi.fp_return_register_bytes
    )
    widths = _INT_WIDTHS if arg_class is ArgClass.INT else _FP_WIDTHS
    if storage.size_bytes not in widths or storage.size_bytes > register_bytes:
        return ObservationRefusal.RETURN_WIDTH_UNSUPPORTED
    bits = storage.size_bytes * 8
    low = (
        storage.bit_offset_in_base + bits == storage.base_register_bits
        if abi.big_endian
        else storage.bit_offset_in_base == 0
    )
    if not low:
        return ObservationRefusal.RETURN_NOT_LOW_PART_OF_REGISTER
    return ReturnLocation(arg_class, storage.base_register_name, register_bytes, storage.size_bytes)


@dataclass(frozen=True)
class ReturnObservationPlan:
    """How the two return registers are compared.

    ``narrowed`` records that the two locations reported different widths and
    the comparison uses the smaller one.
    """

    arg_class: ArgClass
    locations: tuple
    compare_bytes: int
    narrowed: bool


def plan_return_observation(
    left: ReturnLocation, right: ReturnLocation
) -> Union[ReturnObservationPlan, ObservationRefusal]:
    if left.arg_class is not right.arg_class:
        return ObservationRefusal.RETURN_CLASS_MISMATCH
    widths = {left.width_bytes, right.width_bytes}
    if left.arg_class is ArgClass.FP and 4 in widths and len(widths) > 1:
        # binary32 against a wider format: the format is not determined.
        return ObservationRefusal.FP_FORMAT_UNRESOLVED
    return ReturnObservationPlan(
        left.arg_class,
        (left, right),
        min(widths),
        len(widths) > 1,
    )


def _is_nan(bits: int, width_bytes: int) -> bool:
    if width_bytes == 4:
        return (bits & 0x7F800000) == 0x7F800000 and (bits & 0x007FFFFF) != 0
    return (bits & 0x7FF0000000000000) == 0x7FF0000000000000 and (
        bits & 0x000FFFFFFFFFFFFF
    ) != 0


def compare_return_values(
    plan: ReturnObservationPlan, left_register_value: int, right_register_value: int
) -> Union[ObservationRelation, ObservationRefusal]:
    """Compare the full values of the two return registers under ``plan``."""
    values = (left_register_value, right_register_value)
    compare_bytes = plan.compare_bytes
    if plan.arg_class is ArgClass.FP:
        for location, value in zip(plan.locations, values):
            if location.width_bytes == 16 and value >> 64:
                return ObservationRefusal.FP_FORMAT_UNRESOLVED
        compare_bytes = min(compare_bytes, 8)
    mask = (1 << (compare_bytes * 8)) - 1
    observed = tuple(value & mask for value in values)
    if plan.arg_class is ArgClass.FP and any(_is_nan(v, compare_bytes) for v in observed):
        return ObservationRefusal.NAN_OBSERVED
    if observed[0] != observed[1]:
        return ObservationRelation.DIFFERENT
    return ObservationRelation.NOT_DIFFERENT_ON_OBSERVED_PART

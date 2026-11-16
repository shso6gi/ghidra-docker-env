# -*- coding: utf-8 -*-
"""The input surface of a function and the correspondence of two of them.

A *side surface* says which ABI argument slots a function reads and how many
bytes of each slot's register the function's recovered signature covers.  It
is built from storage facts of the binary (base register, bit position, size);
no source prototype is involved.

An *input correspondence* pairs the slots of two side surfaces into abstract
arguments, by ABI rules alone:

* same ABI: a register is the same argument on both sides;
* different ABIs: the parameter list is read off the side whose ABI numbers
  arguments positionally, and re-assigned under the other side's ABI.

The width a signature gives to a slot is evidence, not truth, and the two
sides may disagree.  Every width either side reports is kept as a *reading*
of the abstract argument, and a concrete value is admitted only when its
register image is a conforming, equal-valued argument under every reading.

Whatever cannot be established is returned as an ``InputSurfaceRefusal``; a
refusal never becomes a guess.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Iterable, Optional, Sequence, Tuple, Union

from scripts.function_tracer_pcode.concrete.abi import (
    AbiModel,
    ArgClass,
    ArgumentSlot,
    SlotNumbering,
)
from scripts.function_tracer_pcode.concrete.storage import StorageLocation


class InputSurfaceRefusal(str, Enum):
    """Why an input surface, a correspondence or a value was not accepted."""

    PARAMETER_NOT_IN_REGISTER = "PARAMETER_NOT_IN_REGISTER"
    PARAMETER_REGISTER_NOT_AN_ARGUMENT_SLOT = "PARAMETER_REGISTER_NOT_AN_ARGUMENT_SLOT"
    PARAMETER_NOT_LOW_PART_OF_REGISTER = "PARAMETER_NOT_LOW_PART_OF_REGISTER"
    PARAMETER_WIDTH_UNSUPPORTED = "PARAMETER_WIDTH_UNSUPPORTED"
    DUPLICATE_ARGUMENT_SLOT = "DUPLICATE_ARGUMENT_SLOT"
    CROSS_ABI_NUMBERING_UNSUPPORTED = "CROSS_ABI_NUMBERING_UNSUPPORTED"
    CROSS_ABI_POSITIONS_NOT_CONTIGUOUS = "CROSS_ABI_POSITIONS_NOT_CONTIGUOUS"
    CROSS_ABI_SLOTS_DISAGREE = "CROSS_ABI_SLOTS_DISAGREE"
    VALUE_NOT_CONFORMING_UNDER_EVERY_READING = "VALUE_NOT_CONFORMING_UNDER_EVERY_READING"
    VALUE_WIDER_THAN_REGISTER = "VALUE_WIDER_THAN_REGISTER"


_INT_WIDTHS = (1, 2, 4, 8)
_FP_WIDTHS = (4, 8, 16)


@dataclass(frozen=True)
class SlotReading:
    """One argument slot a function reads, with the width its signature gives."""

    slot: ArgumentSlot
    width_bytes: int


@dataclass(frozen=True)
class SideInputSurface:
    abi: AbiModel
    readings: Tuple[SlotReading, ...]

    def reading_of(self, slot: ArgumentSlot) -> Optional[SlotReading]:
        for reading in self.readings:
            if reading.slot == slot:
                return reading
        return None


def side_input_surface(
    abi: AbiModel, parameters: Iterable[StorageLocation]
) -> Union[SideInputSurface, InputSurfaceRefusal]:
    """The input surface of one function from its recovered parameter storage."""
    readings = []
    seen = set()
    for parameter in parameters:
        if not parameter.is_register or not parameter.base_register_name:
            return InputSurfaceRefusal.PARAMETER_NOT_IN_REGISTER
        slot = abi.argument_slot_of(parameter.base_register_name)
        if slot is None:
            return InputSurfaceRefusal.PARAMETER_REGISTER_NOT_AN_ARGUMENT_SLOT
        widths = _INT_WIDTHS if slot.arg_class is ArgClass.INT else _FP_WIDTHS
        if (
            parameter.size_bytes not in widths
            or parameter.size_bytes > abi.argument_register_bytes(slot.arg_class)
        ):
            return InputSurfaceRefusal.PARAMETER_WIDTH_UNSUPPORTED
        if not parameter.is_low_order_part(abi.big_endian):
            return InputSurfaceRefusal.PARAMETER_NOT_LOW_PART_OF_REGISTER
        if slot in seen:
            return InputSurfaceRefusal.DUPLICATE_ARGUMENT_SLOT
        seen.add(slot)
        readings.append(SlotReading(slot, parameter.size_bytes))
    readings.sort(key=lambda reading: (reading.slot.arg_class.value, reading.slot.index))
    return SideInputSurface(abi, tuple(readings))


@dataclass(frozen=True)
class AbstractArgument:
    """One argument of the pair: its class, its slot on each side, its readings.

    ``slots[k]`` is the slot on side ``k``; it is present on both sides even
    when only one side's signature reads it (binding a register the other
    function never reads cannot change that function's behaviour).
    ``readings`` is every width either signature reports, ascending.
    """

    arg_class: ArgClass
    slots: Tuple[ArgumentSlot, ArgumentSlot]
    readings: Tuple[int, ...]


@dataclass(frozen=True)
class InputCorrespondence:
    abis: Tuple[AbiModel, AbiModel]
    arguments: Tuple[AbstractArgument, ...]


def _readings(*candidates: Optional[SlotReading]) -> Tuple[int, ...]:
    return tuple(sorted({c.width_bytes for c in candidates if c is not None}))


def correspond_inputs(
    left: SideInputSurface, right: SideInputSurface
) -> Union[InputCorrespondence, InputSurfaceRefusal]:
    """Pair the argument slots of two functions by ABI rules alone."""
    if left.abi.abi_id is right.abi.abi_id:
        slots = sorted(
            {r.slot for r in left.readings} | {r.slot for r in right.readings},
            key=lambda slot: (slot.arg_class.value, slot.index),
        )
        return InputCorrespondence(
            (left.abi, right.abi),
            tuple(
                AbstractArgument(
                    slot.arg_class,
                    (slot, slot),
                    _readings(left.reading_of(slot), right.reading_of(slot)),
                )
                for slot in slots
            ),
        )

    sides = (left, right)
    positional = [
        index for index, side in enumerate(sides)
        if side.abi.slot_numbering is SlotNumbering.POSITIONAL
    ]
    if len(positional) != 1:
        # Two different per-class ABIs (or two different positional ones) do not
        # determine a common parameter order from register facts.
        return InputSurfaceRefusal.CROSS_ABI_NUMBERING_UNSUPPORTED
    p_index = positional[0]
    o_index = 1 - p_index
    p_side, o_side = sides[p_index], sides[o_index]

    ordered = sorted(p_side.readings, key=lambda reading: reading.slot.index)
    if [reading.slot.index for reading in ordered] != list(range(len(ordered))):
        # A gap is a parameter whose class the positional side does not show.
        return InputSurfaceRefusal.CROSS_ABI_POSITIONS_NOT_CONTIGUOUS
    classes = tuple(reading.slot.arg_class for reading in ordered)
    other_slots = o_side.abi.assign_slots(classes)
    if other_slots is None or set(other_slots) != {r.slot for r in o_side.readings}:
        return InputSurfaceRefusal.CROSS_ABI_SLOTS_DISAGREE

    arguments = []
    for p_reading, o_slot in zip(ordered, other_slots):
        pair = [None, None]
        pair[p_index] = p_reading.slot
        pair[o_index] = o_slot
        arguments.append(
            AbstractArgument(
                p_reading.slot.arg_class,
                (pair[0], pair[1]),
                _readings(p_reading, o_side.reading_of(o_slot)),
            )
        )
    return InputCorrespondence((left.abi, right.abi), tuple(arguments))


@dataclass(frozen=True)
class RegisterImage:
    """The value written to one full argument register at entry."""

    register: str
    register_bytes: int
    value: int


def _sign_extend(value: int, from_bytes: int, to_bytes: int) -> int:
    bits = from_bytes * 8
    value &= (1 << bits) - 1
    if value >> (bits - 1):
        value -= 1 << bits
    return value & ((1 << (to_bytes * 8)) - 1)


def argument_register_images(
    correspondence: InputCorrespondence, argument: AbstractArgument, value: int
) -> Union[Tuple[RegisterImage, RegisterImage], InputSurfaceRefusal]:
    """Register images of ``value`` for one abstract argument, one per side.

    ``value`` is a non-negative bit pattern of the argument's widest reading
    (at most 8 bytes).

    Integer class.  The same 64-bit image is written on both sides, and it is
    admitted only in *canonical narrow form* under every reading narrower than
    the register: for a 4-byte reading the image is the sign extension of its
    low 32 bits (what MIPS n64 requires, and one of the images AAPCS64
    allows); for a 1- or 2-byte reading the value's top bit is clear as well,
    so the sign- and zero-extended promotions agree.  Such an image is the
    same argument value whichever reading is the true one, on either ABI.

    Floating-point class.  Every bit pattern is a conforming register value;
    the pattern is written to the low bytes and the rest of the register is
    zero.
    """
    widest = max(argument.readings) if argument.readings else 8
    width = min(widest, 8)
    if value < 0 or value >> (width * 8):
        return InputSurfaceRefusal.VALUE_WIDER_THAN_REGISTER

    images = []
    for abi, slot in zip(correspondence.abis, argument.slots):
        register = abi.argument_register(slot)
        register_bytes = abi.argument_register_bytes(argument.arg_class)
        if argument.arg_class is ArgClass.INT:
            image = _sign_extend(value, width, register_bytes)
            for reading in argument.readings:
                if reading >= register_bytes:
                    continue
                if image != _sign_extend(image, reading, register_bytes):
                    return InputSurfaceRefusal.VALUE_NOT_CONFORMING_UNDER_EVERY_READING
                if reading < 4 and (image >> (reading * 8 - 1)) & 1:
                    return InputSurfaceRefusal.VALUE_NOT_CONFORMING_UNDER_EVERY_READING
        else:
            image = value
        images.append(RegisterImage(register, register_bytes, image))
    return images[0], images[1]


def bind_arguments(
    correspondence: InputCorrespondence, values: Sequence[int]
) -> Union[Tuple[Tuple[RegisterImage, ...], Tuple[RegisterImage, ...]], InputSurfaceRefusal]:
    """Register images of a whole argument vector, as (left images, right images)."""
    if len(values) != len(correspondence.arguments):
        raise ValueError("one value per abstract argument is required")
    left, right = [], []
    for argument, value in zip(correspondence.arguments, values):
        images = argument_register_images(correspondence, argument, value)
        if isinstance(images, InputSurfaceRefusal):
            return images
        left.append(images[0])
        right.append(images[1])
    return tuple(left), tuple(right)

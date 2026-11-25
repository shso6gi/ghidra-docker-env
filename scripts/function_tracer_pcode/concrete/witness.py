# -*- coding: utf-8 -*-
"""Turning a witness of a formula into corresponding concrete inputs (#18).

A satisfying assignment of the symbolic analysis (a *witness*) gives a value
to each input variable of the formula: one variable per recovered parameter
of each side.  To run the two functions on it, the values must become one
value per *abstract argument* of the pair -- the ABI correspondence of
``concrete.input_surface`` -- and then register images.  Everything the
formula says about a parameter is evidence, not truth:

* the variable of a parameter is found by the parameter's storage, never by
  its name or position: the abstract argument is the ABI slot of that
  storage on each side;
* when both sides have a variable for one abstract argument, the two values
  must be the same argument (an integer: the same value sign-extended from
  each variable's width; a floating-point bit pattern: the same width and
  bits).  The formula may relate the two variables differently (a zero
  extension, another pairing of the parameters); then the witness does not
  name one input and is refused;
* the width of each variable joins the widths of the storage as a further
  *reading* of the argument, so a value is admitted only when it is the same
  integer under every width either binary or the formula gives it;
* a variable the witness does not assign is refused, not defaulted.

Nothing here makes the formula's witness *true*.  The runs decide what the
witness shows; this module only refuses a witness that does not name one
input of the pair.  It sees storage facts and the formula's variable names,
widths and values -- no source, no types beyond the storage, no verdict.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from enum import Enum
from typing import Dict, List, Mapping, Optional, Sequence, Tuple, Union

from scripts.function_tracer_pcode.concrete.abi import AbiModel, ArgClass, ArgumentSlot
from scripts.function_tracer_pcode.concrete.input_surface import (
    InputCorrespondence,
    InputSurfaceRefusal,
    SideInputSurface,
    side_input_surface,
)
from scripts.function_tracer_pcode.concrete.storage import StorageLocation


class WitnessRefusal(str, Enum):
    """Why a witness does not name one input of the pair."""

    # The formula's input variable has a width the registers cannot hold.
    VARIABLE_WIDTH_UNSUPPORTED = "VARIABLE_WIDTH_UNSUPPORTED"
    # A parameter's storage is not an argument slot of the pair's correspondence.
    VARIABLE_NOT_AN_ARGUMENT = "VARIABLE_NOT_AN_ARGUMENT"
    # The witness assigns no value to an input variable.
    VALUE_MISSING = "VALUE_MISSING"
    # The value is not a bit pattern of the variable's width (a Boolean, a
    # negative number, too many bits).
    VALUE_NOT_A_BIT_PATTERN = "VALUE_NOT_A_BIT_PATTERN"
    # Two variables of one abstract argument hold different arguments.
    SIDES_DISAGREE = "SIDES_DISAGREE"


@dataclass(frozen=True)
class FormulaInput:
    """One input variable of the formula: its name, width and storage."""

    variable: str
    bit_width: int
    location: StorageLocation


def formula_surface(
    abi: AbiModel, inputs: Sequence[FormulaInput]
) -> Union[SideInputSurface, InputSurfaceRefusal]:
    """The input surface of one side read off the formula's inputs."""
    return side_input_surface(abi, [item.location for item in inputs])


@dataclass(frozen=True)
class WitnessInput:
    """The abstract argument values a witness names, under a correspondence
    whose readings include the formula's widths."""

    correspondence: InputCorrespondence
    values: Tuple[int, ...]
    # Formula variables per abstract argument, (left, right); None where the
    # side's formula has no variable for that argument.
    variables: Tuple[Tuple[Optional[str], Optional[str]], ...]


def _sign_extend(value: int, bits: int) -> int:
    value &= (1 << bits) - 1
    if value >> (bits - 1):
        value -= 1 << bits
    return value & ((1 << 64) - 1)


def witness_input(
    correspondence: InputCorrespondence,
    sides: Tuple[Sequence[FormulaInput], Sequence[FormulaInput]],
    witness: Mapping[str, object],
) -> Union[WitnessInput, WitnessRefusal]:
    """The input of the pair a witness names, or why it names none."""
    found: List[Dict[ArgumentSlot, FormulaInput]] = [{}, {}]
    for side, (abi, inputs) in enumerate(zip(correspondence.abis, sides)):
        for item in inputs:
            if item.bit_width <= 0 or item.bit_width % 8 or item.bit_width > 64:
                return WitnessRefusal.VARIABLE_WIDTH_UNSUPPORTED
            slot = (
                abi.argument_slot_of(item.location.base_register_name)
                if item.location.is_register and item.location.base_register_name else None
            )
            if slot is None or slot not in {a.slots[side] for a in correspondence.arguments}:
                return WitnessRefusal.VARIABLE_NOT_AN_ARGUMENT
            found[side][slot] = item

    arguments, values, variables = [], [], []
    for argument in correspondence.arguments:
        present = [found[side].get(argument.slots[side]) for side in (0, 1)]
        readings = set(argument.readings)
        candidates = []
        for item in present:
            if item is None:
                continue
            raw = witness.get(item.variable)
            if raw is None:
                return WitnessRefusal.VALUE_MISSING
            if type(raw) is not int or raw < 0 or raw >> item.bit_width:
                return WitnessRefusal.VALUE_NOT_A_BIT_PATTERN
            width = item.bit_width // 8
            if argument.arg_class is ArgClass.INT:
                readings.add(width)
                candidates.append(_sign_extend(raw, item.bit_width))
            else:
                candidates.append((width, raw))
        if not candidates:
            return WitnessRefusal.VALUE_MISSING
        if any(candidate != candidates[0] for candidate in candidates):
            return WitnessRefusal.SIDES_DISAGREE
        if argument.arg_class is ArgClass.INT:
            widest = max(readings)
            value = candidates[0] & ((1 << (8 * min(widest, 8))) - 1)
        else:
            value = candidates[0][1]
        arguments.append(replace(argument, readings=tuple(sorted(readings))))
        values.append(value)
        variables.append(tuple(None if item is None else item.variable for item in present))
    return WitnessInput(
        InputCorrespondence(correspondence.abis, tuple(arguments)),
        tuple(values),
        tuple(variables),
    )

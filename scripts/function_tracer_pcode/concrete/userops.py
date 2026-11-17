# -*- coding: utf-8 -*-
"""P-code user operations (``CALLOTHER``) whose meaning is established.

A SLEIGH specification names an instruction's effect it does not spell out in
P-code as a *user operation*; the emulator does not know what it does.  The
concrete executor therefore runs a user operation only when this module
states its meaning, and stops the run (``UNSUPPORTED_OPERATION``) for every
other one.  An entry is admitted only from the processor manual and the SLEIGH
definition that calls it, and only for the operand shapes checked here; any
other shape of the same name is unsupported.

The user operations observed in the 964 AArch64 / MIPS64 validation binaries: ``trap`` (MIPS ``teq``
and friends, reached only when the trap condition holds), ``NEON_fminnm``
(AArch64 scalar ``fminnm``) and ``NEON_ext`` (AArch64 ``ext``).

* ``trap`` (MIPS ``mips32Instructions.sinc``: ``teq``/``tge``/... call it
  when the condition holds): the machine raises a trap exception and the
  process is signalled -- the call does not complete (``Termination.FAULT``).
* ``NEON_fminnm(Rn, Rm)`` (``AARCH64neon.sinc``, scalar ``FMINNM``; the
  vector forms carry a third element-size operand and are not admitted):
  ``FPMinNum`` of the Arm ARM -- a single quiet NaN loses to a number, a
  signalling NaN propagates, ``min(+0, -0) = -0``.
* ``NEON_ext(Rn, Rm, imm4, 1)`` (``ext Vd.16B / Vd.8B``): the bytes
  ``imm4 .. imm4 + size - 1`` of the concatenation ``Rm:Rn`` (``Rn`` the low
  half), ``imm4 < size``.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Optional, Sequence, Tuple

from scripts.function_tracer_pcode.concrete import ieee


class UseropEffect(str, Enum):
    VALUE = "VALUE"            # writes ``value`` to the operation's output
    TRAP = "TRAP"              # the machine traps: the call does not complete
    UNSUPPORTED = "UNSUPPORTED"


@dataclass(frozen=True)
class UseropOutcome:
    effect: UseropEffect
    value: Optional[int] = None
    # The output is a floating-point value of this many bytes (format evidence
    # and the floating-point monitor treat it as a scalar FP operation).
    fp_size: Optional[int] = None
    # The output is a NaN (its payload is not established).
    nan: bool = False
    detail: str = ""


# (processor, user operation name) pairs this module knows.  ``processor`` is
# Ghidra's processor name (``Language.getProcessor()``).
KNOWN_USEROPS = frozenset({
    ("MIPS", "trap"),
    ("AARCH64", "NEON_fminnm"),
    ("AARCH64", "NEON_ext"),
})


def _unsupported(detail: str) -> UseropOutcome:
    return UseropOutcome(UseropEffect.UNSUPPORTED, detail=detail)


def evaluate_userop(
    processor: str,
    name: Optional[str],
    input_sizes: Sequence[int],
    input_constant: Sequence[bool],
    output_size: Optional[int],
    values: Optional[Sequence[int]],
) -> UseropOutcome:
    """What the user operation does with these operands (values as unsigned ints).

    ``input_sizes`` / ``input_constant`` / ``values`` describe the operands
    after the user operation index (the first ``CALLOTHER`` input).
    ``values`` is ``None`` when the operand values are not known; then only
    the effect is decided.
    """
    key = (processor, name)
    if key not in KNOWN_USEROPS:
        return _unsupported(f"user operation {name!r} of {processor} has no established meaning")
    if name == "trap":
        return UseropOutcome(UseropEffect.TRAP, detail="trap")
    if name == "NEON_fminnm":
        if len(input_sizes) != 2 or any(input_constant) or output_size not in (4, 8) or \
                tuple(input_sizes) != (output_size, output_size):
            return _unsupported("NEON_fminnm: not the scalar form")
        if values is None:
            return UseropOutcome(UseropEffect.VALUE, fp_size=output_size)
        fmt = ieee.FORMAT_OF_SIZE[output_size]
        result = ieee.min_number(values[0], values[1], fmt)
        if result is None:
            # A NaN result: which NaN is not established; the monitor taints it.
            return UseropOutcome(UseropEffect.VALUE, value=values[0], fp_size=output_size, nan=True)
        return UseropOutcome(UseropEffect.VALUE, value=result, fp_size=output_size)
    if name == "NEON_ext":
        if len(input_sizes) != 4 or tuple(input_constant) != (False, False, True, True) or \
                output_size not in (8, 16) or tuple(input_sizes[:2]) != (output_size, output_size):
            return _unsupported("NEON_ext: unexpected operands")
        if values is None:
            return UseropOutcome(UseropEffect.VALUE)
        low, high, index, flag = values
        if flag != 1 or not 0 <= index < output_size:
            return _unsupported(f"NEON_ext: index {index} for {output_size} bytes")
        concatenated = (high << (8 * output_size)) | low
        value = (concatenated >> (8 * index)) & ((1 << (8 * output_size)) - 1)
        return UseropOutcome(UseropEffect.VALUE, value=value)
    return _unsupported(f"user operation {name!r}")  # pragma: no cover - KNOWN_USEROPS guards


def userop_effect_without_values(
    processor: str, name: Optional[str], input_sizes: Sequence[int],
    input_constant: Sequence[bool], output_size: Optional[int],
) -> UseropEffect:
    return evaluate_userop(processor, name, input_sizes, input_constant, output_size, None).effect


def operand_shape(inputs) -> Tuple[Tuple[int, ...], Tuple[bool, ...]]:
    """(sizes, is-constant) of a CALLOTHER's operands after the index."""
    rest = tuple(inputs[1:])
    return tuple(v.size for v in rest), tuple(v.space == "const" for v in rest)

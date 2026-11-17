# -*- coding: utf-8 -*-
"""IEEE 754 binary32 / binary64 arithmetic on bit patterns, exactly.

The floating-point monitor (``concrete.value_monitor``) needs to know, for an
operation the emulator executed, what a conforming machine computes -- to check
the emulator's own result, to know whether a product was rounded, and to
compute the result another build would get by fusing a multiplication into
the following addition (``fma``).  Every function here takes and returns bit
patterns; results are rounded once, to nearest with ties to even (the default
mode of both modelled ABIs), from the exact value (``fractions.Fraction``).

A NaN result is reported as ``NAN`` without a payload: which NaN a machine
produces is not modelled (the monitor treats every NaN as an uncertain value).
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction
from typing import Optional, Tuple, Union

from scripts.function_tracer_pcode.concrete.observation import FpFormat


@dataclass(frozen=True)
class _Layout:
    total_bits: int
    exponent_bits: int
    fraction_bits: int

    @property
    def bias(self) -> int:
        return (1 << (self.exponent_bits - 1)) - 1

    @property
    def max_exponent_field(self) -> int:
        return (1 << self.exponent_bits) - 1


LAYOUTS = {
    FpFormat.BINARY32: _Layout(32, 8, 23),
    FpFormat.BINARY64: _Layout(64, 11, 52),
}
FORMAT_OF_SIZE = {4: FpFormat.BINARY32, 8: FpFormat.BINARY64}


class _Nan:
    """A NaN result (payload not modelled)."""

    def __repr__(self) -> str:
        return "NAN"


NAN = _Nan()
# A decoded value: a Fraction (finite, with a separate sign for zeros),
# +-infinity, or NaN.
Number = Union[Fraction, float, _Nan]


@dataclass(frozen=True)
class Decoded:
    kind: str          # "finite", "inf", "nan"
    negative: bool
    value: Fraction    # magnitude-signed exact value for "finite" (0 for zeros)
    quiet: bool = True  # for NaNs


def bits_mask(fmt: FpFormat) -> int:
    return (1 << LAYOUTS[fmt].total_bits) - 1


def decode(bits: int, fmt: FpFormat) -> Decoded:
    layout = LAYOUTS[fmt]
    bits &= bits_mask(fmt)
    negative = bool(bits >> (layout.total_bits - 1))
    exponent = (bits >> layout.fraction_bits) & layout.max_exponent_field
    fraction = bits & ((1 << layout.fraction_bits) - 1)
    if exponent == layout.max_exponent_field:
        if fraction == 0:
            return Decoded("inf", negative, Fraction(0))
        quiet = bool(fraction >> (layout.fraction_bits - 1))
        return Decoded("nan", negative, Fraction(0), quiet)
    if exponent == 0:
        magnitude = Fraction(fraction, 1 << (layout.fraction_bits + layout.bias - 1))
    else:
        magnitude = Fraction((1 << layout.fraction_bits) | fraction) * Fraction(2) ** (
            exponent - layout.bias - layout.fraction_bits
        )
    return Decoded("finite", negative, -magnitude if negative else magnitude)


def is_nan(bits: int, fmt: FpFormat) -> bool:
    return decode(bits, fmt).kind == "nan"


def _inf_bits(negative: bool, fmt: FpFormat) -> int:
    layout = LAYOUTS[fmt]
    return (int(negative) << (layout.total_bits - 1)) | (layout.max_exponent_field << layout.fraction_bits)


def _zero_bits(negative: bool, fmt: FpFormat) -> int:
    return int(negative) << (LAYOUTS[fmt].total_bits - 1)


def round_exact(value: Fraction, fmt: FpFormat, negative_zero: bool = False) -> int:
    """The bits of ``value`` rounded to nearest, ties to even."""
    layout = LAYOUTS[fmt]
    if value == 0:
        return _zero_bits(negative_zero, fmt)
    negative = value < 0
    magnitude = -value if negative else value
    p = layout.fraction_bits + 1
    emin = 1 - layout.bias
    # exponent e with 2**e <= magnitude < 2**(e+1)
    e = magnitude.numerator.bit_length() - magnitude.denominator.bit_length()
    if Fraction(2) ** e > magnitude:
        e -= 1
    elif Fraction(2) ** (e + 1) <= magnitude:
        e += 1
    quantum_exponent = max(e, emin) - (p - 1)
    scaled = magnitude / (Fraction(2) ** quantum_exponent)
    integer = scaled.numerator // scaled.denominator
    remainder = scaled - integer
    if remainder > Fraction(1, 2) or (remainder == Fraction(1, 2) and integer & 1):
        integer += 1
    # integer * 2**quantum_exponent, possibly carried to the next binade
    if integer >= (1 << p):
        integer >>= 1
        quantum_exponent += 1
    if integer == 0:
        return _zero_bits(negative, fmt)
    if integer < (1 << (p - 1)):
        # subnormal
        exponent_field = 0
        fraction = integer
    else:
        exponent_field = quantum_exponent + (p - 1) + layout.bias
        if exponent_field >= layout.max_exponent_field:
            return _inf_bits(negative, fmt)
        fraction = integer - (1 << (p - 1))
    return (int(negative) << (layout.total_bits - 1)) | (exponent_field << layout.fraction_bits) | fraction


def to_number(bits: int, fmt: FpFormat) -> Number:
    d = decode(bits, fmt)
    if d.kind == "nan":
        return NAN
    if d.kind == "inf":
        return -math.inf if d.negative else math.inf
    return d.value


def _from_number(value: Number, fmt: FpFormat, negative_zero: bool = False) -> Optional[int]:
    """Bits of an exact or special result; ``None`` for NaN."""
    if value is NAN:
        return None
    if isinstance(value, float):
        return _inf_bits(value < 0, fmt)
    return round_exact(value, fmt, negative_zero)


Result = Optional[int]   # bits, or None for a NaN result


def _sign(bits: int, fmt: FpFormat) -> bool:
    return decode(bits, fmt).negative


def _add_exact(a: int, b: int, fmt: FpFormat, negate_b: bool = False) -> Result:
    da, db = decode(a, fmt), decode(b, fmt)
    b_negative = db.negative != negate_b
    if "nan" in (da.kind, db.kind):
        return None
    if da.kind == "inf" or db.kind == "inf":
        if da.kind == "inf" and db.kind == "inf" and da.negative != b_negative:
            return None
        negative = da.negative if da.kind == "inf" else b_negative
        return _inf_bits(negative, fmt)
    vb = -db.value if negate_b else db.value
    total = da.value + vb
    if total == 0:
        # exact zero: -0 only when both addends are -0 (round to nearest)
        return _zero_bits(da.negative and b_negative, fmt)
    return round_exact(total, fmt)


def add(a: int, b: int, fmt: FpFormat) -> Result:
    return _add_exact(a, b, fmt)


def sub(a: int, b: int, fmt: FpFormat) -> Result:
    return _add_exact(a, b, fmt, negate_b=True)


def _mul_special(da: Decoded, db: Decoded, fmt: FpFormat) -> Tuple[bool, Result]:
    """(handled, result) for products with a NaN, an infinity."""
    if "nan" in (da.kind, db.kind):
        return True, None
    negative = da.negative != db.negative
    if da.kind == "inf" or db.kind == "inf":
        other = db if da.kind == "inf" else da
        if other.kind == "finite" and other.value == 0:
            return True, None
        return True, _inf_bits(negative, fmt)
    return False, None


def exact_product(a: int, b: int, fmt: FpFormat) -> Optional[Fraction]:
    """The exact product of two finite values, ``None`` otherwise."""
    da, db = decode(a, fmt), decode(b, fmt)
    if da.kind != "finite" or db.kind != "finite":
        return None
    return da.value * db.value


def mul(a: int, b: int, fmt: FpFormat) -> Result:
    da, db = decode(a, fmt), decode(b, fmt)
    handled, result = _mul_special(da, db, fmt)
    if handled:
        return result
    product = da.value * db.value
    return round_exact(product, fmt, negative_zero=da.negative != db.negative)


def product_is_exact(a: int, b: int, fmt: FpFormat) -> bool:
    """True when ``a * b`` needs no rounding (so fusing it changes nothing)."""
    da, db = decode(a, fmt), decode(b, fmt)
    if da.kind != "finite" or db.kind != "finite":
        return True   # inf / NaN products are the same fused or not
    product = da.value * db.value
    bits = round_exact(product, fmt, negative_zero=da.negative != db.negative)
    rounded = decode(bits, fmt)
    return rounded.kind == "finite" and rounded.value == product


def fma(a: int, b: int, c: int, fmt: FpFormat, negate_product: bool = False, negate_c: bool = False) -> Result:
    """``(+-a*b) + (+-c)`` rounded once."""
    da, db, dc = decode(a, fmt), decode(b, fmt), decode(c, fmt)
    product_negative = (da.negative != db.negative) != negate_product
    c_negative = dc.negative != negate_c
    if "nan" in (da.kind, db.kind, dc.kind):
        return None
    if da.kind == "inf" or db.kind == "inf":
        other = db if da.kind == "inf" else da
        if other.kind == "finite" and other.value == 0:
            return None
        if dc.kind == "inf" and c_negative != product_negative:
            return None
        return _inf_bits(product_negative, fmt)
    if dc.kind == "inf":
        return _inf_bits(c_negative, fmt)
    product = da.value * db.value
    if negate_product:
        product = -product
    vc = -dc.value if negate_c else dc.value
    total = product + vc
    if total == 0:
        return _zero_bits(product_negative and c_negative, fmt)
    return round_exact(total, fmt)


def div(a: int, b: int, fmt: FpFormat) -> Result:
    da, db = decode(a, fmt), decode(b, fmt)
    if "nan" in (da.kind, db.kind):
        return None
    negative = da.negative != db.negative
    if da.kind == "inf":
        return None if db.kind == "inf" else _inf_bits(negative, fmt)
    if db.kind == "inf":
        return _zero_bits(negative, fmt)
    if db.value == 0:
        return None if da.value == 0 else _inf_bits(negative, fmt)
    return round_exact(da.value / db.value, fmt, negative_zero=negative)


def neg(a: int, fmt: FpFormat) -> Result:
    if is_nan(a, fmt):
        return None
    return a ^ (1 << (LAYOUTS[fmt].total_bits - 1))


def fabs(a: int, fmt: FpFormat) -> Result:
    if is_nan(a, fmt):
        return None
    return a & ~(1 << (LAYOUTS[fmt].total_bits - 1)) & bits_mask(fmt)


def sqrt(a: int, fmt: FpFormat) -> Result:
    d = decode(a, fmt)
    if d.kind == "nan":
        return None
    if d.kind == "inf":
        return None if d.negative else a
    if d.value == 0:
        return a
    if d.value < 0:
        return None
    # Correctly rounded: integer square root at ample precision, then round.
    layout = LAYOUTS[fmt]
    shift = 2 * (layout.fraction_bits + 8) + max(0, d.value.denominator.bit_length())
    scaled = d.value * (Fraction(4) ** shift)
    root = math.isqrt(scaled.numerator // scaled.denominator)
    exact = Fraction(root * root) == scaled
    approx = Fraction(root, 2 ** shift)
    if not exact:
        # nudge below/above the halfway points: root < true root < root + 1
        approx += Fraction(1, 2 ** (shift + 1))
    return round_exact(approx, fmt)


def convert(a: int, source: FpFormat, target: FpFormat) -> Result:
    d = decode(a, source)
    if d.kind == "nan":
        return None
    if d.kind == "inf":
        return _inf_bits(d.negative, target)
    return round_exact(d.value, target, negative_zero=d.negative)


def from_int(value: int, fmt: FpFormat) -> int:
    return round_exact(Fraction(value), fmt)


def to_int_truncated(a: int, fmt: FpFormat, size: int) -> Optional[int]:
    """Truncation toward zero to a signed ``size``-byte integer.

    ``None`` when C leaves the conversion undefined: a NaN, an infinity or a
    value outside the target range (C11 6.3.1.4).
    """
    d = decode(a, fmt)
    if d.kind != "finite":
        return None
    value = d.value
    integer = int(value)   # toward zero
    if not -(1 << (8 * size - 1)) <= integer < (1 << (8 * size - 1)):
        return None
    return integer


def round_integral(a: int, fmt: FpFormat, mode: str) -> Result:
    d = decode(a, fmt)
    if d.kind == "nan":
        return None
    if d.kind == "inf":
        return a
    value = d.value
    if mode == "ceil":
        integer = -((-value.numerator) // value.denominator)
    else:
        integer = value.numerator // value.denominator
    return round_exact(Fraction(integer), fmt, negative_zero=d.negative)


def compare(op: str, a: int, b: int, fmt: FpFormat) -> bool:
    """FLOAT_EQUAL / NOTEQUAL / LESS / LESSEQUAL (an unordered pair is unequal)."""
    na, nb = to_number(a, fmt), to_number(b, fmt)
    if na is NAN or nb is NAN:
        return op == "FLOAT_NOTEQUAL"
    if op == "FLOAT_EQUAL":
        return na == nb
    if op == "FLOAT_NOTEQUAL":
        return na != nb
    if op == "FLOAT_LESS":
        return na < nb
    if op == "FLOAT_LESSEQUAL":
        return na <= nb
    raise ValueError(op)


def min_number(a: int, b: int, fmt: FpFormat) -> Result:
    """AArch64 ``FMINNM`` (FPMinNum): a single quiet NaN loses to a number."""
    da, db = decode(a, fmt), decode(b, fmt)
    if da.kind == "nan" and db.kind == "nan":
        return None
    if da.kind == "nan" or db.kind == "nan":
        nan_side = da if da.kind == "nan" else db
        if not nan_side.quiet:
            return None        # a signalling NaN is propagated (quietened)
        return b if da.kind == "nan" else a
    na, nb = to_number(a, fmt), to_number(b, fmt)
    if na == nb == 0:
        # min(+0, -0) is -0
        return _zero_bits(da.negative or db.negative, fmt)
    return a if na < nb else b

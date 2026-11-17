# -*- coding: utf-8 -*-
"""The integer-UB and floating-point monitors of a concrete run (#314, #317).

Two builds of one C source may compute different results on an input where
the source has undefined behaviour (a signed overflow, a division by zero, a
shift by the width or more, a floating-point value converted to an integer
it does not fit), and they may round floating-point arithmetic differently
(a compiler may contract ``a * b + c`` into one fused operation).  A
difference between two runs is a difference between the *functions* only
when it does not come from one of those.  This module follows every value of
a run and says which of them are not guaranteed to be what every conforming
build of the same source computes on the same input.

It sees the binary only: the executed P-code operations and the values of
their operands (``RunObserver`` asks the executor for the operand values of
the operations it names in ``value_request``).  Nothing here reads source,
types, build options or labels.

Shadow state.  Every byte of a register, temporary or memory location may
carry *taints* -- the ``HazardKind`` s its value depends on -- and a value may
carry one *fact*:

``WrapFact(width, exact)``
    The low ``width`` bytes are a two's-complement integer computed by an
    operation whose signed result did not fit (an overflow), and ``exact`` is
    the mathematical value under the signed reading.  The bits are what the
    machine computed; a build that relies on "signed overflow does not
    happen" may hold ``exact`` instead.
``FlagFact``
    A condition flag of an AArch64 flag-setting subtraction or addition whose
    result overflowed (``NG`` = the sign of the wrapped result, ``OV`` = the
    overflow bit), so that ``NG != OV`` -- the machine's signed comparison --
    is recognised as the exact comparison it is.
``FpFact(elements)``
    The floating-point value is one of several bit patterns depending on how a
    build rounds (each element is a possible value, the machine's among
    them), or it is the rounded result of a multiplication that another build
    may fuse into a following addition (the element keeps the operands).

Integer rule (signed overflow).  The binary does not say whether an
operation was a C signed operation, whose overflow is undefined, or an
unsigned one, whose wrap-around C defines.  A run on an input where the
source may have had undefined behaviour is no evidence that two builds
compute different functions, so:

* an ``INT_ADD``/``SUB``/``MULT``/``2COMP``/``LEFT`` whose signed result does
  not fit is an *overflow site* (``IntegerOverflow``), its result carries a
  ``WrapFact``;
* an operation narrower than the ABI's C ``int`` may compute the low bits
  of ``int`` arithmetic on promoted operands of either signedness
  (``unsigned short`` times ``unsigned short`` overflows ``int``; a
  vectorised 16-bit lane), and its own wrap may be the only trace of that
  overflow: it is a site when it wraps under the signed *or* the unsigned
  reading of its operands (0xFFFF * 0xFFFF does not overflow as -1 * -1).
  Its true ``int`` value is then unknown, so any use is refused like an
  ``int`` overflow -- conservative: ``(unsigned short)(a + b)`` that wraps
  at 16 bits is refused although ``a + b`` fits ``int``;
* moves (``COPY``, ``INT_ZEXT``, ``INT_SEXT`` -- the register write of a
  32-bit operation on both ISAs) keep the result's identity, and the
  condition flags its own instruction takes from it (AArch64 ``NG``, ``ZR``
  of a ``cmp``/``subs``) are not uses: a comparison has no overflow, and
  ``NG != OV`` is recognised as the exact comparison it is (``FlagFact``);
* any other use -- an operand of any operation, a store, an address, a
  branch -- makes the site ``VALUE_USED`` and the run hazardous
  (``SIGNED_OVERFLOW``).  What used it is recorded (``IntegerOverflow.uses``)
  but no use clears it: an unsigned use is also what compilers emit for
  signed values they assume not to overflow, and an unsigned comparison
  alone is both the compiled form of the range test ``lo <= x <= hi``
  (``(unsigned)(x - lo) <= hi - lo``, no overflow in the source) and of a
  source that converts an overflowed difference;
* a result that is still unused in an observed register at return makes
  that register unreliable (``VALUE_RETURNED``).

The modular facts of the values computed after a use are still followed:
two's-complement arithmetic is a ring homomorphism, so ``+``, ``-``,
``*``, negation, the bitwise operations and left shifts agree with the
exact computation on the low bytes, and a use that depends on more than
the low bytes (a signed comparison, a signed division, a branch, an
address) is evaluated on both.  This says whether the observed value would
agree with a build that holds the exact value (``reliable_low_bytes``), kept
apart from the occurrence of the overflow for later stages.

Floating-point rule.  Under the default ``FP_CONTRACT``, the only freedom a
conforming compiler has on these targets is to fuse a multiplication with
the addition or subtraction that consumes it (C11 6.5p8, ``fma``).  A product
that is exact fuses to the same result, so the monitor computes, for every
``FLOAT_ADD``/``SUB`` whose operand is an inexact product, both the unfused
and the fused result, and propagates the set of possible values through the
following floating-point operations (``FpFact``).  This also covers the
emulator itself: Ghidra's AArch64 ``fmadd`` is two P-code operations (two
roundings, the hardware rounds once).  A comparison or conversion whose
result is the same for every possible value is clean; otherwise the result
is tainted ``FP_ROUNDING_SENSITIVE``.  No tolerance (ULP, relative, absolute)
is applied anywhere.

NaN rule.  The emulator does not preserve NaN payloads or signalling state,
and NaNs produced by an operation differ between machines.  A floating-point
operation that produces a value and consumes or produces a NaN taints its
output ``FP_NAN_OPERAND``.  Comparisons and ``FLOAT_NAN`` give the same
result for every NaN and are clean.

Other undefined operations, from the operand values:

* ``INT_SDIV``/``INT_SREM`` of the most negative value by ``-1`` and an
  integer division whose divisor is zero (AArch64 ``sdiv``/``udiv`` test the
  divisor in the instruction and return 0) taint the instruction's outputs
  ``INTEGER_DIVISION_UNDEFINED``;
* a shift amount that the shift instruction itself reduces modulo the width
  (``INT_AND`` with ``width - 1`` feeding the shift in the same instruction)
  and that was not already in range taints ``SHIFT_COUNT_OUT_OF_RANGE``;
* a floating-point to integer conversion (``TRUNC``) of a NaN, an infinity or
  an out-of-range value taints ``FP_TO_INTEGER_OUT_OF_RANGE``;
* a floating-point result of the emulator that differs from the IEEE 754
  result of the same operands taints ``FP_EMULATION_MISMATCH``.

Sinks.  A taint or a divergent fact that reaches a branch condition, a
computed branch target or a load/store address is a hazard of the run (the
path itself depends on it).  At return, ``observe`` reports how many low
bytes of a register are free of taints and divergent facts.

Guarantees and limits.  A run is reported as monitored only when every
operation the monitor needed values for had them.  What the integer monitor
catches is a signed overflow *executed* by this binary at the width of the
operation; a build that never executes the overflowing operation (it was
optimised away, or computes a 32-bit ``int`` in a 64-bit register without
overflowing it) is caught only through the other side's run
(``compare_runs`` refuses when either side is affected).  Signedness is not
known from the binary: every overflow of the signed reading (and, below
``int`` width, of the unsigned reading) is treated as possibly undefined, including unsigned
arithmetic (hashes) -- a lost witness, never a wrong one.  A source
subtraction whose only use is its sign or zero test, compiled to a
flag-setting compare, is indistinguishable from a comparison; the machine's
flags then are the exact comparison.  A left shift of a negative value
that does not overflow, pointer-arithmetic overflow beyond the address width
and a truncating conversion of an out-of-range integer (implementation
defined in C) are not reported.  Reassociation and other ``-ffast-math``
transformations are not modelled.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, FrozenSet, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.concrete import ieee
from scripts.function_tracer_pcode.concrete.executor import HazardKind, IntegerOverflow, OverflowDisposition
from scripts.function_tracer_pcode.concrete.userops import UseropEffect, UseropOutcome, evaluate_userop

CONST_SPACE = "const"

MODULAR = frozenset({
    "INT_ADD", "INT_SUB", "INT_MULT", "INT_2COMP", "INT_NEGATE", "INT_AND", "INT_OR",
    "INT_XOR", "INT_LEFT",
})
WRAPPING = frozenset({"INT_ADD", "INT_SUB", "INT_MULT", "INT_2COMP", "INT_LEFT"})
SIGNED_USES = frozenset({"INT_EQUAL", "INT_NOTEQUAL", "INT_SLESS", "INT_SLESSEQUAL"})
UNSIGNED_USES = frozenset({"INT_LESS", "INT_LESSEQUAL", "INT_CARRY", "INT_DIV", "INT_REM", "INT_RIGHT"})
SIGNED_VALUE_USES = frozenset({"INT_SDIV", "INT_SREM", "INT_SRIGHT"})
DIVISIONS = frozenset({"INT_DIV", "INT_SDIV", "INT_REM", "INT_SREM"})
SHIFTS = frozenset({"INT_LEFT", "INT_RIGHT", "INT_SRIGHT"})
FLAG_OPS = frozenset({"INT_SBORROW", "INT_SCARRY"})
# Operations whose operands the integer monitor needs whatever the shadow.
INTEGER_VALUE_OPS = WRAPPING | frozenset({"INT_SDIV", "INT_SREM"}) | FLAG_OPS

FP_VALUE_OPS = frozenset({
    "FLOAT_ADD", "FLOAT_SUB", "FLOAT_MULT", "FLOAT_DIV", "FLOAT_NEG", "FLOAT_ABS",
    "FLOAT_SQRT", "INT2FLOAT", "FLOAT2FLOAT", "CEIL", "FLOOR", "ROUND",
})
FP_COMPARES = frozenset({"FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL"})
FP_OPS = FP_VALUE_OPS | FP_COMPARES | frozenset({"FLOAT_NAN", "TRUNC"})
# Byte j of the output depends on input byte j only.
BYTEWISE = frozenset({
    "COPY", "INT_AND", "INT_OR", "INT_XOR", "INT_NEGATE", "BOOL_AND", "BOOL_OR",
    "BOOL_XOR", "BOOL_NEGATE",
})
# Byte j of the output depends on input bytes 0..j.
CARRYING = frozenset({"INT_ADD", "INT_SUB", "INT_MULT", "INT_2COMP"})
MAX_FP_ELEMENTS = 16
MAX_EXACT_BITS = 4096

SIGNED_OVERFLOW = HazardKind.SIGNED_OVERFLOW
NO_TAINT: FrozenSet[HazardKind] = frozenset()


@dataclass(frozen=True)
class WrapFact:
    width: int
    exact: int
    # (step, operation, left value, right value, size) of the INT_ADD / INT_SUB
    # that produced the value, for pairing with its overflow flag.
    origin: Optional[tuple] = None
    # index of the overflowing operation in ``ValueMonitor._sites`` while the
    # value is still the operation's result (moved, not computed with)
    site: Optional[int] = None


@dataclass
class _Site:
    address: int
    operation: str
    width: int
    disposition: OverflowDisposition
    count: int = 1
    uses: set = None


# Operations that move a value without computing with it: an overflowed
# result keeps its identity through them (the register write of a 32-bit
# operation is an INT_ZEXT / INT_SEXT on both ISAs).
MOVES = frozenset({"COPY", "INT_ZEXT", "INT_SEXT"})
# Condition flags an instruction derives from its own result (AArch64 NG, ZR).
FLAG_TESTS = frozenset({"INT_SLESS", "INT_EQUAL", "INT_NOTEQUAL"})


@dataclass(frozen=True)
class FlagFact:
    kind: str            # "sign" or "overflow"
    key: tuple
    exact: int           # the exact value of the bit (sign: exact result < 0)
    divergent: bool = False


@dataclass(frozen=True)
class FpElement:
    bits: int
    # (a, b, negated) when the value is the rounded product a*b (negated) and
    # the product was inexact: another build may fuse it into an addition.
    product: Optional[Tuple[int, int, bool]] = None


@dataclass(frozen=True)
class FpFact:
    size: int
    elements: FrozenSet[FpElement]

    @property
    def certain(self) -> bool:
        return len({e.bits for e in self.elements}) == 1


def _signed(value: int, size: int) -> int:
    bits = 8 * size
    value &= (1 << bits) - 1
    return value - (1 << bits) if value >> (bits - 1) else value


def _mask(value: int, size: int) -> int:
    return value & ((1 << (8 * size)) - 1)


def evaluate_int(mnemonic: str, values: Sequence[int], sizes: Sequence[int], out_size: int) -> Optional[int]:
    """The P-code result (unsigned, ``out_size`` bytes) of an integer operation."""
    a = values[0] if values else 0
    sa = _signed(a, sizes[0]) if sizes else 0
    b = values[1] if len(values) > 1 else 0
    sb = _signed(b, sizes[1]) if len(sizes) > 1 else 0
    if mnemonic == "COPY":
        r = a
    elif mnemonic == "INT_ADD":
        r = a + b
    elif mnemonic == "INT_SUB":
        r = a - b
    elif mnemonic == "INT_MULT":
        r = a * b
    elif mnemonic == "INT_2COMP":
        r = -a
    elif mnemonic == "INT_NEGATE":
        r = ~a
    elif mnemonic == "INT_AND":
        r = a & b
    elif mnemonic == "INT_OR":
        r = a | b
    elif mnemonic == "INT_XOR":
        r = a ^ b
    elif mnemonic == "INT_LEFT":
        r = 0 if b >= 8 * sizes[0] else a << b
    elif mnemonic == "INT_RIGHT":
        r = 0 if b >= 8 * sizes[0] else a >> b
    elif mnemonic == "INT_SRIGHT":
        r = (-1 if sa < 0 else 0) if b >= 8 * sizes[0] else sa >> b
    elif mnemonic == "INT_EQUAL":
        r = int(a == b)
    elif mnemonic == "INT_NOTEQUAL":
        r = int(a != b)
    elif mnemonic == "INT_LESS":
        r = int(a < b)
    elif mnemonic == "INT_LESSEQUAL":
        r = int(a <= b)
    elif mnemonic == "INT_SLESS":
        r = int(sa < sb)
    elif mnemonic == "INT_SLESSEQUAL":
        r = int(sa <= sb)
    elif mnemonic == "INT_ZEXT":
        r = a
    elif mnemonic == "INT_SEXT":
        r = sa
    elif mnemonic == "INT_CARRY":
        r = int(a + b >= (1 << (8 * sizes[0])))
    elif mnemonic == "INT_SCARRY":
        r = int(not -(1 << (8 * sizes[0] - 1)) <= sa + sb < (1 << (8 * sizes[0] - 1)))
    elif mnemonic == "INT_SBORROW":
        r = int(not -(1 << (8 * sizes[0] - 1)) <= sa - sb < (1 << (8 * sizes[0] - 1)))
    elif mnemonic in ("INT_DIV", "INT_REM", "INT_SDIV", "INT_SREM"):
        if b == 0:
            return None
        if mnemonic == "INT_DIV":
            r = a // b
        elif mnemonic == "INT_REM":
            r = a % b
        else:
            q = abs(sa) // abs(sb)
            q = q if (sa < 0) == (sb < 0) else -q
            r = q if mnemonic == "INT_SDIV" else sa - q * sb
    elif mnemonic == "SUBPIECE":
        r = a >> (8 * b)
    elif mnemonic == "PIECE":
        r = (a << (8 * sizes[1])) | b
    elif mnemonic in ("BOOL_AND", "BOOL_OR", "BOOL_XOR", "BOOL_NEGATE"):
        x, y = a & 1, b & 1
        r = {"BOOL_AND": x & y, "BOOL_OR": x | y, "BOOL_XOR": x ^ y, "BOOL_NEGATE": 1 - x}[mnemonic]
    else:
        return None
    return _mask(r, out_size)


def _exact_signed_compare(mnemonic: str, x: int, y: int) -> int:
    return {
        "INT_EQUAL": int(x == y),
        "INT_NOTEQUAL": int(x != y),
        "INT_SLESS": int(x < y),
        "INT_SLESSEQUAL": int(x <= y),
    }[mnemonic]


@dataclass(frozen=True)
class _InstructionShape:
    # op index -> the shift width (bits) when the op is an INT_AND that
    # reduces a shift amount of a shift in the same instruction.
    shift_masks: Tuple[Tuple[int, int], ...]
    # op indices of INT_EQUAL ops that test a divisor of the instruction for 0.
    division_guards: FrozenSet[int]


def _instruction_shape(ops) -> _InstructionShape:
    masks = {}
    for index, op in enumerate(ops):
        if op.mnemonic != "INT_AND" or op.output is None or len(op.inputs) != 2:
            continue
        mask = op.inputs[1]
        if mask.space != CONST_SPACE:
            continue
        limit = mask.offset + 1
        if limit & (limit - 1):
            continue
        # follow exact copies / zero extensions of the output to a shift amount
        carriers = {(op.output.space, op.output.offset, op.output.size)}
        for later in ops[index + 1:]:
            if later.mnemonic in ("COPY", "INT_ZEXT") and later.inputs and later.output is not None:
                source = later.inputs[0]
                if (source.space, source.offset, source.size) in carriers:
                    carriers.add((later.output.space, later.output.offset, later.output.size))
            if later.mnemonic in SHIFTS and len(later.inputs) == 2:
                amount = later.inputs[1]
                if (amount.space, amount.offset, amount.size) in carriers and 8 * later.inputs[0].size == limit:
                    masks[index] = limit
    guards = set()
    divisors = {
        (op.inputs[1].space, op.inputs[1].offset, op.inputs[1].size)
        for op in ops if op.mnemonic in DIVISIONS and len(op.inputs) == 2 and op.inputs[1].space != CONST_SPACE
    }
    for index, op in enumerate(ops):
        if op.mnemonic == "INT_EQUAL" and len(op.inputs) == 2:
            a, b = op.inputs
            key_a, key_b = (a.space, a.offset, a.size), (b.space, b.offset, b.size)
            if (key_a in divisors and b.space == CONST_SPACE and b.offset == 0) or \
                    (key_b in divisors and a.space == CONST_SPACE and a.offset == 0):
                guards.add(index)
    return _InstructionShape(tuple(sorted(masks.items())), frozenset(guards))


@dataclass(frozen=True)
class ValueRequest:
    inputs: bool = False
    output: bool = False


NO_REQUEST = ValueRequest()


class ValueMonitor:
    """Shadow state of one run.  Driven by ``RunObserver``."""

    def __init__(self, big_endian: bool, processor: str, c_int_bytes: int = 0):
        self._big_endian = big_endian
        self._processor = processor
        # operations narrower than this are checked under both readings
        self._narrow_below = c_int_bytes if c_int_bytes > 0 else 1 << 30
        self._sites: List[_Site] = []
        self._site_of: Dict[Tuple[int, str], int] = {}
        self._address = 0
        self._taint: Dict[Tuple[str, int], FrozenSet[HazardKind]] = {}
        self._facts: Dict[Tuple[str, int, int], object] = {}
        self._fact_at: Dict[Tuple[str, int], Tuple[str, int, int]] = {}
        self._shapes: Dict[int, _InstructionShape] = {}
        self._shape = _InstructionShape((), frozenset())
        self._step = 0
        self._instruction_taint: FrozenSet[HazardKind] = NO_TAINT
        self._next_instruction_taint: FrozenSet[HazardKind] = NO_TAINT
        self.hazards: List[Tuple[HazardKind, str]] = []
        self.integer_complete = True
        self.fp_complete = True
        self._expected_output: Optional[Tuple[object, int, Optional[int]]] = None
        # counts for the measurements (diagnosis only)
        self.counters: Dict[str, int] = {}

    # ----------------------------------------------------------- locations

    def _byte(self, space: str, offset: int, size: int, significance: int) -> Tuple[str, int]:
        if self._big_endian:
            return (space, offset + size - 1 - significance)
        return (space, offset + significance)

    def _byte_keys(self, vn) -> List[Tuple[str, int]]:
        return [self._byte(vn.space, vn.offset, vn.size, k) for k in range(vn.size)]

    def _count(self, name: str) -> None:
        self.counters[name] = self.counters.get(name, 0) + 1

    def _taints(self, vn) -> List[FrozenSet[HazardKind]]:
        if vn.space == CONST_SPACE or not self._taint:
            return [NO_TAINT] * vn.size
        return [self._taint.get(key, NO_TAINT) for key in self._byte_keys(vn)]

    def _low_aligned(self, vn, key) -> bool:
        space, offset, size = key
        if self._big_endian:
            return vn.offset + vn.size == offset + size
        return vn.offset == offset

    def _read_fact(self, vn):
        """(fact, unresolved taint) for the value of ``vn``."""
        if vn.space == CONST_SPACE or not self._fact_at:
            return None, NO_TAINT
        keys = {self._fact_at.get(k) for k in self._byte_keys(vn)}
        keys.discard(None)
        if not keys:
            return None, NO_TAINT
        if len(keys) > 1:
            kinds = frozenset(self._fact_kind(self._facts[k]) for k in keys) - {None}
            return None, frozenset(kinds)
        key = keys.pop()
        fact = self._facts[key]
        if key == (vn.space, vn.offset, vn.size):
            return fact, NO_TAINT
        inside = vn.offset >= key[1] and vn.offset + vn.size <= key[1] + key[2]
        if isinstance(fact, WrapFact) and inside and self._low_aligned(vn, key):
            if vn.size < fact.width:
                return None, NO_TAINT          # a truncation: modular
            return WrapFact(fact.width, fact.exact, None, fact.site), NO_TAINT
        if isinstance(fact, FpFact) and fact.certain:
            return None, NO_TAINT
        if isinstance(fact, FlagFact) and not fact.divergent and fact.kind == "overflow":
            return None, NO_TAINT
        kind = self._fact_kind(fact)
        return None, frozenset({kind}) if kind else NO_TAINT

    @staticmethod
    def _fact_kind(fact) -> Optional[HazardKind]:
        if isinstance(fact, (WrapFact, FlagFact)):
            return SIGNED_OVERFLOW
        if isinstance(fact, FpFact) and not fact.certain:
            return HazardKind.FP_ROUNDING_SENSITIVE
        return None

    def _write(self, vn, taints: Sequence[FrozenSet[HazardKind]], fact=None) -> None:
        if vn is None or vn.space == CONST_SPACE:
            return
        keys = self._byte_keys(vn)
        if self._fact_at:
            stale = {self._fact_at.get(k) for k in keys}
            stale.discard(None)
            written = set(keys)
            for old in stale:
                old_fact = self._facts.pop(old)
                kind = self._fact_kind(old_fact)
                for k in range(old[2]):
                    byte = self._byte(old[0], old[1], old[2], k)
                    self._fact_at.pop(byte, None)
                    if kind is not None and byte not in written:
                        # the rest of a partly overwritten value
                        self._taint[byte] = self._taint.get(byte, NO_TAINT) | {kind}
                        if isinstance(old_fact, WrapFact) and old_fact.site is not None and old[0] != "unique":
                            # its remaining bytes stay readable as program state
                            self._use(old_fact.site, "PARTIAL_OVERWRITE", "")
        extra = self._instruction_taint
        for key, taint in zip(keys, taints):
            taint = taint | extra if extra else taint
            if taint:
                self._taint[key] = taint
            elif self._taint:
                self._taint.pop(key, None)
        if fact is not None:
            location = (vn.space, vn.offset, vn.size)
            self._facts[location] = fact
            for key in keys:
                self._fact_at[key] = location

    # ---------------------------------------------------------- instructions

    def begin_instruction(self, step: int, address: int, ops) -> None:
        self._step = step
        self._address = address
        self._instruction_taint = NO_TAINT
        self._next_instruction_taint = NO_TAINT
        shape = self._shapes.get(address)
        if shape is None:
            shape = _instruction_shape(ops)
            self._shapes[address] = shape
        self._shape = shape

    def value_request(self, index: int, op) -> ValueRequest:
        m = op.mnemonic
        if m in FP_OPS:
            return ValueRequest(True, m != "FLOAT_NAN")
        if m == "CALLOTHER":
            return ValueRequest(True, False)
        if m in INTEGER_VALUE_OPS or index in self._shape.division_guards:
            return ValueRequest(True, False)
        if any(i == index for i, _ in self._shape.shift_masks):
            return ValueRequest(True, False)
        if self._fact_at and m not in ("LOAD", "STORE"):
            for vn in op.inputs:
                if vn.space != CONST_SPACE and any(self._fact_at.get(k) for k in self._byte_keys(vn)):
                    return ValueRequest(True, False)
        return NO_REQUEST

    def _hazard(self, kinds, detail: str) -> None:
        for kind in sorted(kinds, key=lambda k: k.value):
            self.hazards.append((kind, detail))

    # ------------------------------------------------------ overflow sites

    def _site(self, mnemonic: str, width: int, disposition: OverflowDisposition) -> int:
        key = (self._address, mnemonic)
        index = self._site_of.get(key)
        if index is None:
            index = len(self._sites)
            self._site_of[key] = index
            self._sites.append(_Site(self._address, mnemonic, width, disposition, 0, set()))
        self._sites[index].count += 1
        return index

    def _use(self, index: int, use: str, where: str) -> None:
        """The result of an overflowing operation was used (``use``: the
        operation, ``STORE``, ``ADDRESS``): the run may have executed a C
        signed overflow."""
        site = self._sites[index]
        site.uses.add(use)
        if site.disposition is OverflowDisposition.VALUE_USED:
            return
        site.disposition = OverflowDisposition.VALUE_USED
        self._count("signed_overflow_used")
        self._hazard({SIGNED_OVERFLOW}, f"overflow of {site.operation} at {site.address:#x} used by {use}{where}")

    def _sites_in(self, vn) -> List[int]:
        if vn.space == CONST_SPACE or not self._fact_at:
            return []
        found = []
        for key in self._byte_keys(vn):
            location = self._fact_at.get(key)
            if location is None:
                continue
            fact = self._facts[location]
            if isinstance(fact, WrapFact) and fact.site is not None and fact.site not in found:
                found.append(fact.site)
        return found

    def _consume(self, vn, use: str, where: str) -> None:
        for index in self._sites_in(vn):
            self._use(index, use, where)

    def _consume_inputs(self, op, facts, where: str) -> None:
        """Mark the overflowed results ``op`` uses (moves and the instruction's
        own condition flags are not uses)."""
        m = op.mnemonic
        for k, vn in enumerate(op.inputs):
            if vn.space == CONST_SPACE:
                continue
            fact = facts[k]
            carried = isinstance(fact, WrapFact) and fact.site is not None
            if m in MOVES and carried:
                continue
            if (m in FLAG_TESTS and k == 0 and carried and fact.origin is not None
                    and fact.origin[0] == self._step and len(op.inputs) == 2
                    and op.inputs[1].space == CONST_SPACE and op.inputs[1].offset == 0):
                continue
            self._consume(vn, m, where)

    def overflows(self) -> Tuple[IntegerOverflow, ...]:
        return tuple(
            IntegerOverflow(s.address, s.operation, s.width, s.disposition, s.count, tuple(sorted(s.uses)))
            for s in sorted(self._sites, key=lambda s: (s.address, s.operation))
        )

    # ------------------------------------------------------------ operations

    def execute(self, index: int, op, values: Optional[Sequence[int]], where: str) -> Optional[UseropOutcome]:
        """Apply ``op`` to the shadow.  ``values`` are the operand values when supplied."""
        self._expected_output = None
        request = self.value_request(index, op)
        if request.inputs and values is None:
            if op.mnemonic in FP_OPS or op.mnemonic == "CALLOTHER":
                self.fp_complete = False
            if op.mnemonic not in FP_OPS:
                self.integer_complete = False
        m = op.mnemonic
        inputs = op.inputs
        taints = [self._taints(vn) for vn in inputs]
        facts = []
        for k, vn in enumerate(inputs):
            fact, unresolved = self._read_fact(vn)
            facts.append(fact)
            if unresolved:
                taints[k] = [t | unresolved for t in taints[k]]
        union = frozenset().union(*[frozenset().union(*t) for t in taints]) if taints else NO_TAINT
        if self._fact_at and m not in ("LOAD", "STORE"):
            self._consume_inputs(op, facts, where)

        # sinks
        if m == "CBRANCH" and len(inputs) == 2:
            self._sink(union_of(taints[1]), facts[1], values[1] if values else None, inputs[1].size, where, "branch condition")
            return None
        if m in ("BRANCHIND", "CALLIND", "RETURN") and inputs:
            self._sink(union_of(taints[0]), facts[0], values[0] if values else None, inputs[0].size, where, "branch target")
            return None
        if m in ("LOAD", "STORE"):
            return None   # handled by load() / store()
        if m == "CALLOTHER":
            return self._userop(op, values, taints, facts, where)
        out = op.output
        if out is None:
            return None

        if m in FP_OPS:
            self._fp(op, values, taints, facts, union)
            return None
        if m != "COPY" and any(isinstance(f, FpFact) and not f.certain for f in facts):
            # a floating-point value with several possible values used as bits
            union = union | {HazardKind.FP_ROUNDING_SENSITIVE}
            taints = [[t | {HazardKind.FP_ROUNDING_SENSITIVE} for t in ts] for ts in taints]
            facts = [None if isinstance(f, FpFact) else f for f in facts]
        out_taints = self._propagate(m, op, taints, union)
        if m == "COPY" and inputs[0].size == out.size and facts[0] is not None:
            # an exact copy keeps what is known of the value
            self._write(out, out_taints, facts[0])
            return None
        fact, extra = self._integer(index, op, values, facts)
        if extra:
            out_taints = [t | extra for t in out_taints]
        self._write(out, out_taints, fact)
        if self._next_instruction_taint:
            # the instruction's own guard fired: what it writes from now on
            self._instruction_taint = self._instruction_taint | self._next_instruction_taint
            self._next_instruction_taint = NO_TAINT
        return None

    def _propagate(self, m: str, op, taints, union) -> List[FrozenSet[HazardKind]]:
        out = op.output
        if not union:
            return [NO_TAINT] * out.size
        if m in BYTEWISE:
            return [
                frozenset().union(*[ts[k] for ts in taints if k < len(ts)]) for k in range(out.size)
            ]
        if m in CARRYING or (m == "INT_LEFT" and op.inputs[1].space == CONST_SPACE):
            sources = taints[:1] if m == "INT_LEFT" else taints
            result, acc = [], NO_TAINT
            for k in range(out.size):
                for ts in sources:
                    if k < len(ts):
                        acc = acc | ts[k]
                result.append(acc)
            return result
        if m in ("INT_ZEXT", "INT_SEXT"):
            low = taints[0]
            # zero extension writes constant zeros above; sign extension copies the sign
            above = union_of(low) if m == "INT_SEXT" else NO_TAINT
            return [low[k] if k < len(low) else above for k in range(out.size)]
        if m == "SUBPIECE" and len(op.inputs) == 2 and op.inputs[1].space == CONST_SPACE:
            shift, source = op.inputs[1].offset, taints[0]
            return [source[shift + k] if shift + k < len(source) else NO_TAINT for k in range(out.size)]
        if m == "PIECE" and len(op.inputs) == 2:
            high, low = taints
            return [low[k] if k < len(low) else high[k - len(low)] for k in range(out.size)]
        if m in ("FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL", "FLOAT_NAN"):
            return [union - {HazardKind.FP_NAN_OPERAND}] * out.size
        return [union] * out.size

    def _sink(self, kinds, fact, value, size, where, what) -> None:
        if fact is not None:
            divergent = False
            if isinstance(fact, WrapFact):
                if value is None:
                    divergent = True
                elif what == "branch condition":
                    divergent = int(fact.exact != 0) != int(value != 0)
                else:
                    # an address or a target: the exact value must be the address itself
                    divergent = fact.exact != value
            elif isinstance(fact, FlagFact):
                divergent = fact.divergent or value is None or (fact.kind == "sign" and fact.exact != (value & 1))
            elif isinstance(fact, FpFact) and not fact.certain:
                kinds = kinds | {HazardKind.FP_ROUNDING_SENSITIVE}
            if divergent:
                kinds = kinds | {SIGNED_OVERFLOW}
        if kinds:
            self._hazard(kinds, f"{what}{where}")

    # ----------------------------------------------------- integer monitor

    def _integer(self, index: int, op, values, facts):
        """(fact for the output, extra taints for the output)."""
        m = op.mnemonic
        out = op.output
        sizes = [vn.size for vn in op.inputs]
        has_fact = any(f is not None for f in facts)
        extra = NO_TAINT
        if values is None:
            if has_fact:
                return None, frozenset({SIGNED_OVERFLOW})
            return None, NO_TAINT
        # shift amounts the shift instruction reduces itself
        for mask_index, limit in self._shape.shift_masks:
            if mask_index == index and _mask(values[0], sizes[0]) >= limit:
                self._count("shift_count_out_of_range")
                extra = extra | {HazardKind.SHIFT_COUNT_OUT_OF_RANGE}
        if index in self._shape.division_guards:
            divisor = values[0] if op.inputs[1].space == CONST_SPACE else values[1]
            if divisor == 0:
                self._count("division_by_zero")
                self._next_instruction_taint = frozenset({HazardKind.INTEGER_DIVISION_UNDEFINED})
        if m in ("INT_SDIV", "INT_SREM") and not has_fact:
            if _signed(values[0], sizes[0]) == -(1 << (8 * sizes[0] - 1)) and _signed(values[1], sizes[1]) == -1:
                self._count("division_overflow")
                extra = extra | {HazardKind.INTEGER_DIVISION_UNDEFINED}
        actual = evaluate_int(m, values, sizes, out.size)
        if m in FLAG_OPS:
            return self._flag(m, values, sizes, facts, actual), extra
        if not has_fact:
            if m in WRAPPING and actual is not None:
                exact = self._exact(m, [_signed(v, s) for v, s in zip(values, sizes)], values)
                if (exact is None or exact == _signed(actual, out.size)) and out.size < self._narrow_below:
                    # promoted operands may be unsigned: the zero-extended reading
                    unsigned = self._exact(m, [_mask(v, s) for v, s in zip(values, sizes)], values)
                    if unsigned is not None and unsigned != _mask(actual, out.size):
                        exact = unsigned
                if exact is not None and exact != _signed(actual, out.size):
                    self._count("signed_overflow_" + m)
                    origin = (self._step, m, values[0], values[1], sizes[0]) if m in ("INT_ADD", "INT_SUB") else None
                    site = self._site(m, out.size, OverflowDisposition.VALUE_NOT_USED)
                    return WrapFact(out.size, exact, origin, site), extra
            return None, extra
        # an input carries a fact
        flag = [f for f in facts if isinstance(f, FlagFact)]
        if flag and m in ("INT_NOTEQUAL", "INT_EQUAL", "BOOL_XOR", "INT_XOR") and len(facts) == 2 and actual is not None:
            kinds = {f.kind for f in flag}
            if len(flag) == 2 and kinds == {"sign", "overflow"} and flag[0].key == flag[1].key:
                sign = next(f for f in flag if f.kind == "sign")
                exact = sign.exact if m != "INT_EQUAL" else 1 - sign.exact
                if exact == actual:
                    return None, extra
                return None, extra | {SIGNED_OVERFLOW}
        exact_inputs = []
        for f, v, s in zip(facts, values, sizes):
            if isinstance(f, WrapFact):
                exact_inputs.append(f.exact)
            elif isinstance(f, FlagFact):
                if f.divergent:
                    return None, extra | {SIGNED_OVERFLOW}
                exact_inputs.append(f.exact)
            else:
                exact_inputs.append(_signed(v, s))
        if actual is None:
            return None, extra | {SIGNED_OVERFLOW}
        if m in MODULAR:
            if m == "INT_LEFT" and facts[1] is not None:
                return None, extra | {SIGNED_OVERFLOW}
            exact = self._exact(m, exact_inputs, values)
            if exact is None:
                return None, extra | {SIGNED_OVERFLOW}
            if exact == _signed(actual, out.size):
                return None, extra
            origin = (self._step, m, values[0], values[1], sizes[0]) if m in ("INT_ADD", "INT_SUB") else None
            return WrapFact(out.size, exact, origin), extra
        if m in MOVES:
            f = facts[0]
            if isinstance(f, WrapFact):
                return WrapFact(f.width, f.exact, None, f.site), extra
            if isinstance(f, FlagFact):
                if m == "COPY":
                    return f, extra
                if f.exact == (values[0] & 1):
                    return None, extra
                return WrapFact(1, f.exact), extra
            return None, extra
        if m == "SUBPIECE":
            f = facts[0]
            shift = values[1]
            if isinstance(f, WrapFact) and shift == 0:
                return (None, extra) if out.size < f.width else (WrapFact(f.width, f.exact), extra)
            exact_part = exact_inputs[0] >> (8 * shift)
            if _mask(exact_part, out.size) == actual and exact_part == _signed(actual, out.size):
                return None, extra
            return None, extra | {SIGNED_OVERFLOW}
        if m in UNSIGNED_USES:
            if facts[1] is not None and m in ("INT_RIGHT",):
                return None, extra | {SIGNED_OVERFLOW}
            self._count("unsigned_use_of_wrapped")
            return None, extra
        if m == "INT_SLESS" and isinstance(facts[0], WrapFact) and facts[0].origin is not None \
                and facts[1] is None and op.inputs[1].space == CONST_SPACE and values[1] == 0:
            sign = int(facts[0].exact < 0)
            return FlagFact("sign", facts[0].origin, sign), extra
        if m in SIGNED_USES:
            exact = _exact_signed_compare(m, exact_inputs[0], exact_inputs[1])
            if exact == actual:
                return None, extra
            self._count("signed_use_diverged")
            return None, extra | {SIGNED_OVERFLOW}
        if m in SIGNED_VALUE_USES:
            x, y = exact_inputs
            if m == "INT_SRIGHT":
                if facts[1] is not None:
                    return None, extra | {SIGNED_OVERFLOW}
                exact = x >> values[1] if values[1] < 8 * sizes[0] else (-1 if x < 0 else 0)
            else:
                if y == 0:
                    return None, extra | {SIGNED_OVERFLOW}
                q = abs(x) // abs(y)
                q = q if (x < 0) == (y < 0) else -q
                exact = q if m == "INT_SDIV" else x - q * y
            if exact == _signed(actual, out.size):
                return None, extra
            self._count("signed_use_diverged")
            return None, extra | {SIGNED_OVERFLOW}
        return None, extra | {SIGNED_OVERFLOW}

    def _exact(self, m: str, x: Sequence[int], values: Sequence[int]) -> Optional[int]:
        a = x[0]
        b = x[1] if len(x) > 1 else 0
        if m == "INT_ADD":
            r = a + b
        elif m == "INT_SUB":
            r = a - b
        elif m == "INT_MULT":
            r = a * b
        elif m == "INT_2COMP":
            r = -a
        elif m == "INT_NEGATE":
            r = ~a
        elif m == "INT_AND":
            r = a & b
        elif m == "INT_OR":
            r = a | b
        elif m == "INT_XOR":
            r = a ^ b
        elif m == "INT_LEFT":
            amount = values[1]
            if amount >= MAX_EXACT_BITS:
                return None
            r = a << amount
        else:
            return None
        if r.bit_length() > MAX_EXACT_BITS:
            return None
        return r

    def _flag(self, m, values, sizes, facts, actual):
        kind = "INT_SUB" if m == "INT_SBORROW" else "INT_ADD"
        key = (self._step, kind, values[0], values[1], sizes[0])
        if any(f is not None for f in facts):
            # the comparison of a wrapped value: pair it, never use alone
            return FlagFact("overflow", key, actual or 0, divergent=True)
        if actual:
            return FlagFact("overflow", key, actual)
        return None

    # ------------------------------------------------- floating-point monitor

    def _fp(self, op, values, taints, facts, union) -> None:
        m = op.mnemonic
        out = op.output
        out_taint = union
        if m in ("FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL", "FLOAT_NAN"):
            out_taint = union - {HazardKind.FP_NAN_OPERAND}
        if values is None:
            self._write(out, [out_taint] * out.size)
            return
        if any(isinstance(f, (WrapFact, FlagFact)) for f in facts) and m != "INT2FLOAT":
            self._write(out, [out_taint | {SIGNED_OVERFLOW}] * out.size)
            return
        try:
            fact, extra, expected = self._fp_evaluate(op, values, facts)
        except _NotModelled:
            self._count("fp_not_modelled_" + m)
            self._write(out, [out_taint | {HazardKind.FP_ROUNDING_SENSITIVE}] * out.size)
            return
        self._write(out, [out_taint | extra] * out.size, fact)
        self._expected_output = (out, out.size, expected)

    def _elements(self, vn, value, fact) -> List[FpElement]:
        if isinstance(fact, FpFact) and fact.size == vn.size:
            return list(fact.elements)
        return [FpElement(_mask(value, vn.size))]

    def _fp_evaluate(self, op, values, facts):
        """(fact, extra taints, the emulator's expected result bits or None)."""
        m = op.mnemonic
        out = op.output
        inputs = op.inputs
        if m == "INT2FLOAT":
            fmt = ieee.FORMAT_OF_SIZE.get(out.size)
            if fmt is None:
                raise _NotModelled()
            actual = ieee.from_int(_signed(values[0], inputs[0].size), fmt)
            f = facts[0]
            if isinstance(f, WrapFact):
                exact = ieee.from_int(f.exact, fmt) if abs(f.exact).bit_length() < 2000 else None
                if exact != actual:
                    return None, frozenset({SIGNED_OVERFLOW}), actual
            elif f is not None:
                return None, frozenset({SIGNED_OVERFLOW}), actual
            return None, NO_TAINT, actual
        fmt = ieee.FORMAT_OF_SIZE.get(inputs[0].size)
        if fmt is None:
            raise _NotModelled()
        operands = [self._elements(vn, v, f) for vn, v, f in zip(inputs, values, facts)]
        combos = [[]]
        for choices in operands:
            combos = [c + [e] for c in combos for e in choices]
            if len(combos) > MAX_FP_ELEMENTS * 4:
                return None, frozenset({HazardKind.FP_ROUNDING_SENSITIVE}), None
        machine = [FpElement(_mask(v, vn.size)) for vn, v in zip(inputs, values)]
        if m in ("FLOAT_EQUAL", "FLOAT_NOTEQUAL", "FLOAT_LESS", "FLOAT_LESSEQUAL", "FLOAT_NAN"):
            def boolean(c):
                if m == "FLOAT_NAN":
                    return int(ieee.is_nan(c[0].bits, fmt))
                return int(ieee.compare(m, c[0].bits, c[1].bits, fmt))
            results = {boolean(c) for c in combos}
            expected = boolean(machine)
            extra = NO_TAINT if len(results) == 1 else frozenset({HazardKind.FP_ROUNDING_SENSITIVE})
            return None, extra, expected
        if m == "TRUNC":
            results = {ieee.to_int_truncated(c[0].bits, fmt, out.size) for c in combos}
            if None in results:
                self._count("fp_to_integer_out_of_range")
                return None, frozenset({HazardKind.FP_TO_INTEGER_OUT_OF_RANGE}), None
            expected = ieee.to_int_truncated(machine[0].bits, fmt, out.size)
            extra = NO_TAINT if len(results) == 1 else frozenset({HazardKind.FP_ROUNDING_SENSITIVE})
            return None, extra, None if expected is None else _mask(expected, out.size)
        if m == "ROUND":
            # Ghidra's FLOAT_ROUND stands for several instructions with different
            # tie rules; its result is not established.
            raise _NotModelled()
        out_fmt = ieee.FORMAT_OF_SIZE.get(out.size)
        if out_fmt is None:
            raise _NotModelled()
        nan_seen = any(ieee.is_nan(e.bits, fmt) for choices in operands for e in choices)
        results = set()
        for c in combos:
            for element in self._fp_results(m, c, fmt, out_fmt):
                if element is None:
                    nan_seen = True
                else:
                    results.add(element)
        expected_elements = self._fp_results(m, machine, fmt, out_fmt, fused=False)
        expected = expected_elements[0].bits if expected_elements and expected_elements[0] is not None else None
        if nan_seen:
            self._count("fp_nan")
            return None, frozenset({HazardKind.FP_NAN_OPERAND}), None
        if len(results) > MAX_FP_ELEMENTS:
            return None, frozenset({HazardKind.FP_ROUNDING_SENSITIVE}), expected
        fact = FpFact(out.size, frozenset(results))
        if fact.certain and all(e.product is None for e in results):
            fact = None
        elif not fact.certain:
            self._count("fp_rounding_alternatives")
        return fact, NO_TAINT, expected

    def _fp_results(self, m, c, fmt, out_fmt, fused: bool = True) -> List[Optional[FpElement]]:
        a = c[0]
        b = c[1] if len(c) > 1 else None
        if m == "FLOAT_MULT":
            r = ieee.mul(a.bits, b.bits, fmt)
            if r is None:
                return [None]
            product = None if ieee.product_is_exact(a.bits, b.bits, fmt) else (a.bits, b.bits, False)
            return [FpElement(r, product)]
        if m in ("FLOAT_ADD", "FLOAT_SUB"):
            subtract = m == "FLOAT_SUB"
            r = (ieee.sub if subtract else ieee.add)(a.bits, b.bits, fmt)
            results = [None if r is None else FpElement(r)]
            if not fused:
                return results
            if a.product is not None or b.product is not None:
                self._count("fp_contraction_site")
            if a.product is not None:
                pa, pb, negated = a.product
                f = ieee.fma(pa, pb, b.bits, fmt, negate_product=negated, negate_c=subtract)
                results.append(None if f is None else FpElement(f))
            if b.product is not None:
                pa, pb, negated = b.product
                f = ieee.fma(pa, pb, a.bits, fmt, negate_product=negated != subtract)
                results.append(None if f is None else FpElement(f))
            return results
        if m == "FLOAT_NEG":
            r = ieee.neg(a.bits, fmt)
            if r is None:
                return [None]
            product = None if a.product is None else (a.product[0], a.product[1], not a.product[2])
            return [FpElement(r, product)]
        if m == "FLOAT_ABS":
            r = ieee.fabs(a.bits, fmt)
        elif m == "FLOAT_DIV":
            r = ieee.div(a.bits, b.bits, fmt)
        elif m == "FLOAT_SQRT":
            r = ieee.sqrt(a.bits, fmt)
        elif m == "FLOAT2FLOAT":
            r = ieee.convert(a.bits, fmt, out_fmt)
        elif m == "CEIL":
            r = ieee.round_integral(a.bits, fmt, "ceil")
        elif m == "FLOOR":
            r = ieee.round_integral(a.bits, fmt, "floor")
        else:
            raise _NotModelled()
        return [None if r is None else FpElement(r)]

    def output(self, value: int) -> None:
        """The emulator's result of the last operation (checked against IEEE 754)."""
        expected = self._expected_output
        self._expected_output = None
        if expected is None:
            return
        out, size, bits = expected
        if bits is None:
            return
        value = _mask(value, size)
        fmt = ieee.FORMAT_OF_SIZE.get(size)
        if value != _mask(bits, size) and not (fmt is not None and ieee.is_nan(value, fmt) and ieee.is_nan(bits, fmt)):
            self._count("fp_emulation_mismatch")
            taints = [t | {HazardKind.FP_EMULATION_MISMATCH} for t in self._taints(out)]
            self._write(out, taints)

    # ------------------------------------------------------------- userops

    def _userop(self, op, values, taints, facts, where) -> UseropOutcome:
        from scripts.function_tracer_pcode.concrete.userops import operand_shape

        sizes, constant = operand_shape(op.inputs)
        out = op.output
        operand_values = None if values is None else list(values[1:])
        outcome = evaluate_userop(
            self._processor, op.userop, sizes, constant, None if out is None else out.size, operand_values
        )
        if outcome.effect is not UseropEffect.VALUE or out is None:
            return outcome
        if values is None:
            self.fp_complete = False
            self.integer_complete = False
            self._write(out, [frozenset().union(*[frozenset().union(*t) for t in taints[1:]])] * out.size)
            return outcome
        union = frozenset().union(*[frozenset().union(*t) for t in taints[1:]]) if len(taints) > 1 else NO_TAINT
        if outcome.fp_size is not None:
            fmt = ieee.FORMAT_OF_SIZE[outcome.fp_size]
            operands = [self._elements(vn, v, f) for vn, v, f in zip(op.inputs[1:], values[1:], facts[1:])]
            if any(isinstance(f, (WrapFact, FlagFact)) for f in facts[1:]):
                union = union | {SIGNED_OVERFLOW}
            results, nan = set(), outcome.nan
            for a in operands[0]:
                for b in operands[1]:
                    r = ieee.min_number(a.bits, b.bits, fmt)
                    if r is None:
                        nan = True
                    else:
                        results.add(FpElement(r))
            if nan:
                self._write(out, [union | {HazardKind.FP_NAN_OPERAND}] * out.size)
            elif len({e.bits for e in results}) > 1:
                self._write(out, [union] * out.size, FpFact(out.size, frozenset(results)))
            else:
                self._write(out, [union] * out.size)
            return outcome
        if any(f is not None for f in facts[1:]):
            kinds = frozenset(k for k in (self._fact_kind(f) for f in facts[1:] if f is not None) if k)
            union = union | kinds
        self._write(out, [union] * out.size)
        return outcome

    # ------------------------------------------------------- memory traffic

    def address(self, op, where: str, actual_address: int) -> None:
        """Check the address operand of a LOAD / STORE."""
        vn = op.inputs[1]
        self._consume(vn, "ADDRESS", where)
        taint = union_of(self._taints(vn))
        fact, unresolved = self._read_fact(vn)
        self._sink(taint | unresolved, fact, actual_address, vn.size, where, "address")

    def load(self, op, space: str, address: int, size: int) -> None:
        source = _Vn(space, address, size)
        fact, unresolved = self._read_fact(source)
        taints = self._taints(source)
        if unresolved:
            taints = [t | unresolved for t in taints]
        self._write(op.output, taints, fact)

    def store(self, op, space: str, address: int, size: int, where: str = "") -> None:
        value = op.inputs[2]
        self._consume(value, "STORE", where)
        fact, unresolved = self._read_fact(value)
        taints = self._taints(value)
        if unresolved:
            taints = [t | unresolved for t in taints]
        self._write(_Vn(space, address, size), taints, fact)

    # --------------------------------------------------------------- return

    def observe(self, offset: int, size: int, space: str = "register", where: str = "") -> Tuple[int, Tuple[HazardKind, ...]]:
        """(low bytes free of taints and divergent facts, kinds found) of a register.

        The unused result of an overflowing operation in the register makes
        the whole register unreliable (``VALUE_RETURNED``): it is the
        function's return value when the caller compares this register.
        """
        vn = _Vn(space, offset, size)
        reliable = size
        kinds = set()
        for index in self._sites_in(vn):
            site = self._sites[index]
            if site.disposition is OverflowDisposition.VALUE_NOT_USED:
                site.disposition = OverflowDisposition.VALUE_RETURNED
            kinds.add(SIGNED_OVERFLOW)
            reliable = 0
        for k, taint in enumerate(self._taints(vn)):
            if taint:
                kinds |= taint
                reliable = min(reliable, k)
        seen = set()
        for k in range(size):
            location = self._fact_at.get(self._byte(space, offset, size, k))
            if location is None or location in seen:
                continue
            seen.add(location)
            fact = self._facts[location]
            if isinstance(fact, FpFact) and fact.certain:
                continue
            if isinstance(fact, FlagFact) and fact.kind == "overflow" and not fact.divergent:
                continue
            # k is the significance of the first byte of the fact in the register
            limit = fact.width if isinstance(fact, WrapFact) and k == 0 else k
            kind = self._fact_kind(fact)
            if kind is not None and limit < size:
                kinds.add(kind)
            reliable = min(reliable, limit)
        return reliable, tuple(sorted(kinds, key=lambda x: x.value))

    def rounding_values(self, offset: int, size: int, space: str = "register") -> Tuple[int, Tuple[int, ...]]:
        """(bytes, values) when the only doubt on the low bytes of a register is
        the build's rounding choice: the floating-point value starting at its
        lowest byte has several possible values (``FpFact``) and nothing else
        is in doubt below its size.  ``(0, ())`` otherwise."""
        location = self._fact_at.get(self._byte(space, offset, size, 0)) if self._fact_at else None
        if location is None:
            return 0, ()
        fact = self._facts[location]
        if not isinstance(fact, FpFact) or fact.certain or fact.size > size:
            return 0, ()
        vn = _Vn(space, offset, size)
        if not self._low_aligned(vn, location) or location[2] != fact.size:
            return 0, ()
        taints = self._taints(vn)
        if any(taints[k] for k in range(fact.size)):
            return 0, ()
        if any(self._fact_at.get(self._byte(space, offset, size, k)) != location for k in range(fact.size)):
            return 0, ()
        return fact.size, tuple(sorted({e.bits for e in fact.elements}))


class _NotModelled(Exception):
    """An operation of a format or kind the floating-point monitor does not model."""


@dataclass(frozen=True)
class _Vn:
    space: str
    offset: int
    size: int


def union_of(taints: Sequence[FrozenSet[HazardKind]]) -> FrozenSet[HazardKind]:
    return frozenset().union(*taints) if taints else NO_TAINT

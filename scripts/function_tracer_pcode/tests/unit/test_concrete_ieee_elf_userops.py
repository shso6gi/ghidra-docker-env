# -*- coding: utf-8 -*-
"""The IEEE 754 model, the ELF zero-initialisation rule and the user operations (C3).

The IEEE model is checked against the host's binary64 arithmetic (correctly
rounded, round to nearest even) on random and special operands, and against
exact rational arithmetic for binary32 and fused multiply-add.  Pure Python.
"""
import math
import random
import struct
from fractions import Fraction

import pytest

from scripts.function_tracer_pcode.concrete import ieee
from scripts.function_tracer_pcode.concrete.elf_sections import (
    ET_REL,
    SHF_ALLOC,
    SHF_TLS,
    SHF_WRITE,
    SHT_NOBITS,
    ElfSection,
    ElfSectionTable,
    MemoryBlockFact,
    parse_section_table,
    zero_initialized_blocks,
)
from scripts.function_tracer_pcode.concrete.observation import FpFormat
from scripts.function_tracer_pcode.concrete.userops import UseropEffect, evaluate_userop

B32, B64 = FpFormat.BINARY32, FpFormat.BINARY64


def d2b(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def b2d(b):
    return struct.unpack("<d", struct.pack("<Q", b))[0]


def f2b(x):
    return struct.unpack("<I", struct.pack("<f", x))[0]


def _doubles(seed, n):
    rng = random.Random(seed)
    specials = [0.0, -0.0, 1.0, -1.0, 0.1, 1e308, -1e308, 5e-324, -5e-324, 2.2250738585072014e-308,
                math.inf, -math.inf, 1.7976931348623157e308, 3.0, 1 / 3]
    values = [d2b(x) for x in specials]
    values += [rng.getrandbits(64) for _ in range(n)]
    values += [d2b(rng.uniform(-10, 10)) for _ in range(n)]
    return [v for v in values if not ieee.is_nan(v, B64)]


@pytest.mark.parametrize("name, fn, py", [
    ("add", ieee.add, lambda a, b: a + b),
    ("sub", ieee.sub, lambda a, b: a - b),
    ("mul", ieee.mul, lambda a, b: a * b),
])
def test_binary64_arithmetic_matches_the_host(name, fn, py):
    values = _doubles(1, 60)
    for a in values:
        for b in values[::7]:
            expected = py(b2d(a), b2d(b))
            got = fn(a, b, B64)
            if math.isnan(expected):
                assert got is None
            else:
                assert got == d2b(expected), (name, hex(a), hex(b))


def test_binary64_division_and_square_root_match_the_host():
    values = _doubles(2, 80)
    for a in values:
        for b in values[::9]:
            x, y = b2d(a), b2d(b)
            try:
                expected = x / y
            except ZeroDivisionError:
                expected = math.nan if x == 0 or math.isnan(x) else math.copysign(math.inf, x) * math.copysign(1, y)
            got = ieee.div(a, b, B64)
            assert (got is None) if math.isnan(expected) else got == d2b(expected), (hex(a), hex(b))
        x = b2d(a)
        if x < 0 and x != 0:
            assert ieee.sqrt(a, B64) is None
        else:
            assert ieee.sqrt(a, B64) == d2b(math.sqrt(x)), hex(a)


def test_binary32_results_are_the_exact_result_rounded_once():
    rng = random.Random(3)
    for _ in range(300):
        a, b = rng.getrandbits(32), rng.getrandbits(32)
        if ieee.is_nan(a, B32) or ieee.is_nan(b, B32):
            continue
        da, db = ieee.decode(a, B32), ieee.decode(b, B32)
        if da.kind == db.kind == "finite":
            exact = da.value * db.value
            assert ieee.mul(a, b, B32) == ieee.round_exact(exact, B32, da.negative != db.negative)
            # double rounding through binary64 is innocuous for one operation
            expected = struct.unpack("<f", struct.pack("<f", b2d(ieee.convert(a, B32, B64)) + b2d(ieee.convert(b, B32, B64))))[0] \
                if abs(float(da.value + db.value)) < 3e38 else None
            if expected is not None:
                assert ieee.add(a, b, B32) == f2b(expected)


def test_rounding_handles_ties_subnormals_and_overflow():
    assert ieee.round_exact(Fraction(1) + Fraction(1, 2 ** 53), B64) == d2b(1.0)          # tie to even
    assert ieee.round_exact(Fraction(1) + Fraction(3, 2 ** 53), B64) == d2b(1.0 + 2 ** -51)
    assert ieee.round_exact(Fraction(1, 2 ** 1075), B64) == 0                            # tie to even 0
    assert ieee.round_exact(Fraction(3, 2 ** 1076), B64) == 1                            # nearest subnormal
    assert ieee.round_exact(Fraction(2) ** 1024, B64) == d2b(math.inf)
    assert ieee.round_exact(-Fraction(2) ** 1024, B32) == f2b(-math.inf)


def test_fused_multiply_add_rounds_once():
    a, b, c = d2b(0.1), d2b(10.0), d2b(-1.0)
    assert ieee.add(ieee.mul(a, b, B64), c, B64) == d2b(0.0)
    fused = ieee.fma(a, b, c, B64)
    assert b2d(fused) == float(Fraction(0.1) * 10 - 1) and fused != d2b(0.0)
    assert not ieee.product_is_exact(a, b, B64) and ieee.product_is_exact(d2b(1.5), d2b(4.0), B64)
    assert ieee.fma(a, b, d2b(1.0), B64, negate_product=True) == d2b(float(1 - Fraction(0.1) * 10))
    assert ieee.fma(d2b(math.inf), d2b(0.0), c, B64) is None


def test_conversions_and_comparisons():
    assert ieee.to_int_truncated(d2b(-2.9), B64, 4) == -2
    assert ieee.to_int_truncated(d2b(2.0 ** 31), B64, 4) is None
    assert ieee.to_int_truncated(d2b(math.nan), B64, 4) is None
    assert ieee.to_int_truncated(d2b(math.inf), B64, 8) is None
    assert ieee.convert(d2b(0.1), B64, B32) == f2b(0.1)
    assert ieee.from_int(2 ** 53 + 1, B64) == d2b(2.0 ** 53)
    assert ieee.round_integral(d2b(-0.5), B64, "ceil") == d2b(-0.0)
    assert ieee.round_integral(d2b(-0.5), B64, "floor") == d2b(-1.0)
    nan = 0x7FF8000000000000
    assert not ieee.compare("FLOAT_LESS", nan, d2b(1.0), B64)
    assert ieee.compare("FLOAT_NOTEQUAL", nan, nan, B64)
    assert ieee.compare("FLOAT_EQUAL", d2b(0.0), d2b(-0.0), B64)


def test_min_number_follows_fpminnum():
    one, two = d2b(1.0), d2b(2.0)
    assert ieee.min_number(two, one, B64) == one
    assert ieee.min_number(0x7FF8000000000000, one, B64) == one          # a quiet NaN loses
    assert ieee.min_number(0x7FF0000000000001, one, B64) is None         # a signalling NaN propagates
    assert ieee.min_number(d2b(0.0), d2b(-0.0), B64) == d2b(-0.0)


# ------------------------------------------------------------------ ELF

def _elf(sections, big_endian=False, e_type=ET_REL):
    """A minimal ELF64 image: header, section names, section header table."""
    order = ">" if big_endian else "<"
    names = b"\x00" + b"".join(s.name.encode() + b"\x00" for s in sections) + b".shstrtab\x00"
    name_offsets, offset = [], 1
    for s in sections:
        name_offsets.append(offset)
        offset += len(s.name) + 1
    shstr_name = offset
    strtab_offset = 64
    shoff = strtab_offset + len(names)
    shoff += (-shoff) % 8
    entries = [b"\x00" * 64]
    for s, n in zip(sections, name_offsets):
        entries.append(struct.pack(order + "IIQQQQIIQQ", n, s.sh_type, s.flags, s.address, 0, s.size, 0, 0, 1, 0))
    entries.append(struct.pack(order + "IIQQQQIIQQ", shstr_name, 3, 0, 0, strtab_offset, len(names), 0, 0, 1, 0))
    header = b"\x7fELF" + bytes([2, 2 if big_endian else 1, 1]) + b"\x00" * 9
    header += struct.pack(order + "HHIQQQIHHHHHH", e_type, 183, 1, 0, 0, shoff, 0, 64, 0, 0, 64,
                          len(entries), len(entries) - 1)
    data = header + names
    data += b"\x00" * (shoff - len(data)) + b"".join(entries)
    return data


def _reader(data):
    return lambda offset, count: data[offset:offset + count]


BSS = ElfSection(".bss", SHT_NOBITS, SHF_ALLOC | SHF_WRITE, 0, 0x40)


@pytest.mark.parametrize("big_endian", [False, True])
def test_the_section_table_is_read_from_the_file(big_endian):
    data = _elf([BSS, ElfSection(".data", 1, SHF_ALLOC | SHF_WRITE, 0, 8)], big_endian)
    table = parse_section_table(_reader(data), len(data))
    assert table.big_endian is big_endian and table.file_type == ET_REL
    assert [(s.name, s.sh_type, s.size) for s in table.sections[1:3]] == [(".bss", SHT_NOBITS, 0x40), (".data", 1, 8)]
    assert parse_section_table(_reader(data[:40]), 40) is None
    assert parse_section_table(_reader(b"\x7fELF" + b"\x01" * 60), 64) is None   # ELF32


def test_only_an_allocated_nobits_section_that_is_the_block_is_zero():
    table = ElfSectionTable(False, ET_REL, (
        BSS,
        ElfSection(".tbss", SHT_NOBITS, SHF_ALLOC | SHF_WRITE | SHF_TLS, 0, 0x10),
        ElfSection(".data", 1, SHF_ALLOC | SHF_WRITE, 0, 0x10),
    ))
    blocks = [
        MemoryBlockFact(".bss", 0x200000, 0x40, False),
        MemoryBlockFact(".tbss", 0x300000, 0x10, False),
        MemoryBlockFact("EXTERNAL", 0x400000, 0x100, False),
        MemoryBlockFact(".data", 0x500000, 0x10, True),
    ]
    zero = zero_initialized_blocks(table, blocks)
    assert zero.ranges == ((0x200000, 0x200040),)
    assert {name for name, _ in zero.left_undefined} == {".tbss", "EXTERNAL"}
    # a size that is not the section's
    assert zero_initialized_blocks(table, [MemoryBlockFact(".bss", 0x200000, 0x80, False)]).ranges == ()
    # no table: nothing is zero
    assert zero_initialized_blocks(None, blocks[:1]).ranges == ()


def test_a_linked_file_s_section_must_also_be_at_the_block_s_address():
    table = ElfSectionTable(False, 2, (ElfSection(".bss", SHT_NOBITS, SHF_ALLOC | SHF_WRITE, 0x411000, 0x40),))
    assert zero_initialized_blocks(table, [MemoryBlockFact(".bss", 0x411000, 0x40, False)]).ranges == \
        ((0x411000, 0x411040),)
    assert zero_initialized_blocks(table, [MemoryBlockFact(".bss", 0x412000, 0x40, False)]).ranges == ()


# ------------------------------------------------------------- user operations

def test_user_operations_are_admitted_only_in_their_checked_shapes():
    assert evaluate_userop("MIPS", "trap", (2,), (True,), None, [7]).effect is UseropEffect.TRAP
    assert evaluate_userop("AARCH64", "trap", (2,), (True,), None, [7]).effect is UseropEffect.UNSUPPORTED
    vector = evaluate_userop("AARCH64", "NEON_fminnm", (16, 16, 1), (False, False, True), 16, [0, 0, 8])
    assert vector.effect is UseropEffect.UNSUPPORTED
    scalar = evaluate_userop("AARCH64", "NEON_fminnm", (8, 8), (False, False), 8, [d2b(3.0), d2b(-2.0)])
    assert scalar.effect is UseropEffect.VALUE and scalar.value == d2b(-2.0) and scalar.fp_size == 8
    ext8 = evaluate_userop("AARCH64", "NEON_ext", (8, 8, 1, 1), (False, False, True, True), 8,
                           [0x0706050403020100, 0x0F0E0D0C0B0A0908, 3, 1])
    assert ext8.value == 0x0A09080706050403
    assert evaluate_userop("AARCH64", "NEON_ext", (8, 8, 1, 1), (False, False, True, True), 8,
                           [0, 0, 9, 1]).effect is UseropEffect.UNSUPPORTED
    assert evaluate_userop("AARCH64", None, (), (), None, []).effect is UseropEffect.UNSUPPORTED

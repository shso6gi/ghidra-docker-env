# -*- coding: utf-8 -*-
"""Which program memory an ELF file defines as zero at program start.

The System V gABI defines a section of type ``SHT_NOBITS`` with the
``SHF_ALLOC`` flag as memory that occupies space in the process image but
none in the file; ``.bss`` is the reserved name of such a section and "the
system initializes the data with zeros when the program begins to run"
(gABI, *Special Sections*).  A thread-local section (``SHF_TLS``, ``.tbss``)
is a per-thread template, not process memory, and is excluded.

Ghidra loads such a section as an *uninitialized* memory block.  The concrete
executor zero-fills a block only when this module finds, in the file's own
section header table, exactly one ``SHT_NOBITS`` + ``SHF_ALLOC`` section that
is the block (same name and size, and for a linked file the same address).
Every other uninitialized block -- the ``EXTERNAL`` block, a block without a
section, a section that does not match -- stays undefined: a read of it is a
hazard, never a zero.

Only ELF64 files are read (the two modelled ABIs are 64-bit).
"""

from __future__ import annotations

import struct
from dataclasses import dataclass
from typing import Iterable, List, Optional, Sequence, Tuple

SHT_NOBITS = 8
SHF_WRITE = 0x1
SHF_ALLOC = 0x2
SHF_TLS = 0x400
ET_REL = 1
_ELFCLASS64 = 2


@dataclass(frozen=True)
class ElfSection:
    name: str
    sh_type: int
    flags: int
    address: int
    size: int


@dataclass(frozen=True)
class ElfSectionTable:
    big_endian: bool
    file_type: int
    sections: Tuple[ElfSection, ...]


@dataclass(frozen=True)
class MemoryBlockFact:
    """One memory block of the loaded program (Ghidra's view)."""

    name: str
    start: int
    size: int
    initialized: bool


@dataclass(frozen=True)
class ZeroInitialization:
    ranges: Tuple[Tuple[int, int], ...]          # (start, end) exclusive
    # Uninitialized blocks left undefined, with why (diagnosis).
    left_undefined: Tuple[Tuple[str, str], ...]


def parse_section_table(read, length: int) -> Optional[ElfSectionTable]:
    """The section header table of an ELF64 file, from ``read(offset, count) -> bytes``.

    ``None`` when the bytes are not a well-formed ELF64 header and table.
    """
    if length < 64:
        return None
    ident = read(0, 16)
    if len(ident) != 16 or ident[:4] != b"\x7fELF" or ident[4] != _ELFCLASS64 or ident[5] not in (1, 2):
        return None
    big_endian = ident[5] == 2
    order = ">" if big_endian else "<"
    header = read(16, 48)
    if len(header) != 48:
        return None
    e_type = struct.unpack(order + "H", header[0:2])[0]
    e_shoff = struct.unpack(order + "Q", header[24:32])[0]
    e_shentsize, e_shnum, e_shstrndx = struct.unpack(order + "HHH", header[42:48])
    if e_shoff == 0 or e_shentsize < 64 or e_shnum == 0 or e_shstrndx >= e_shnum:
        return None
    if e_shoff + e_shentsize * e_shnum > length:
        return None
    raw = []
    for index in range(e_shnum):
        entry = read(e_shoff + index * e_shentsize, 64)
        if len(entry) != 64:
            return None
        name, sh_type, flags, address, offset, size = struct.unpack(order + "IIQQQQ", entry[:40])
        raw.append((name, sh_type, flags, address, offset, size))
    strtab = raw[e_shstrndx]
    if strtab[4] + strtab[5] > length:
        return None
    names = read(strtab[4], strtab[5])
    sections = []
    for name_offset, sh_type, flags, address, _offset, size in raw:
        end = names.find(b"\x00", name_offset)
        if name_offset >= len(names) or end < 0:
            return None
        sections.append(ElfSection(names[name_offset:end].decode("ascii", "replace"), sh_type, flags, address, size))
    return ElfSectionTable(big_endian, e_type, tuple(sections))


def zero_initialized_blocks(
    table: Optional[ElfSectionTable], blocks: Sequence[MemoryBlockFact]
) -> ZeroInitialization:
    """The uninitialized blocks the ELF file defines as zero at program start."""
    uninitialized = [b for b in blocks if not b.initialized]
    if table is None:
        return ZeroInitialization((), tuple((b.name, "no ELF64 section table") for b in uninitialized))
    zero_sections = [
        s for s in table.sections
        if s.sh_type == SHT_NOBITS and s.flags & SHF_ALLOC and not s.flags & SHF_TLS
    ]
    ranges: List[Tuple[int, int]] = []
    left: List[Tuple[str, str]] = []
    for block in uninitialized:
        candidates = [
            s for s in zero_sections
            if s.name == block.name and s.size == block.size
            and (table.file_type == ET_REL or s.address == block.start)
        ]
        same_name = [s for s in table.sections if s.name == block.name]
        if len(candidates) == 1 and len(same_name) == 1:
            if block.size:
                ranges.append((block.start, block.start + block.size))
            continue
        if not same_name:
            why = "no ELF section of this name"
        elif len(same_name) > 1:
            why = "several ELF sections of this name"
        else:
            section = same_name[0]
            why = (
                f"section type {section.sh_type} flags {section.flags:#x} "
                f"address {section.address:#x} size {section.size}"
            )
        left.append((block.name, why))
    return ZeroInitialization(tuple(sorted(ranges)), tuple(left))


def ranges_to_json(ranges: Iterable[Tuple[int, int]]) -> list:
    return [list(r) for r in ranges]

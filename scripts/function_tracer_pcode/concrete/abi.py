# -*- coding: utf-8 -*-
"""Calling-convention models for concrete execution.

An ``AbiModel`` is public-specification data: which registers carry
arguments and return values, which registers a callee must preserve, and how a
value narrower than its register is held.  It is the only source of ABI facts
for the concrete layer -- nothing here is derived from source code, from a
decompiled prototype, or from an expected verdict.

Registers are named by the *base* (full-width) register name the Ghidra
processor module uses, which is what ``core.storage.StorageInfo`` records as
``base_register_name``.  The tables are written out per ABI; register names
are never parsed.

Supported today: AArch64 AAPCS64 and MIPS n64, each for exactly one
combination of language, compiler specification and executable format (see
``select_abi``).  Any other program has no model, and every consumer treats
"no model" as a refusal.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Mapping, Optional, Tuple


class AbiId(str, Enum):
    AARCH64_AAPCS64 = "AARCH64_AAPCS64"
    MIPS_N64 = "MIPS_N64"


class ArgClass(str, Enum):
    """The register class an argument or a return value is passed in."""

    INT = "INT"
    FP = "FP"


class SlotNumbering(str, Enum):
    """How an ABI assigns argument registers to a parameter list.

    ``PER_CLASS``: each class counts on its own (AAPCS64: the k-th integer
    argument is in ``x<k>``, the k-th floating-point argument in ``v<k>``).

    ``POSITIONAL``: one counter for all arguments (MIPS n64: the i-th argument
    is in ``a<i>`` or ``f<12+i>`` depending on its class).
    """

    PER_CLASS = "PER_CLASS"
    POSITIONAL = "POSITIONAL"


class NarrowIntRule(str, Enum):
    """What an ABI says about the register bits above a narrow integer.

    ``SIGN_EXTENDED_REQUIRED``: a 32-bit value is held sign-extended in its
    64-bit register whatever its signedness (MIPS n64).

    ``UPPER_BITS_UNSPECIFIED``: the bits above the value are not defined and a
    conforming callee does not depend on them (AAPCS64).
    """

    SIGN_EXTENDED_REQUIRED = "SIGN_EXTENDED_REQUIRED"
    UPPER_BITS_UNSPECIFIED = "UPPER_BITS_UNSPECIFIED"


class NarrowIntImage(str, Enum):
    """How the concrete layer fills the register bits above a narrow integer.

    The image must be one the ABI admits (``NarrowIntRule``) and the one the
    program's compiler specification declares for its integer parameters
    (``extension="sign"`` / ``"zero"``), so that the entry state conforms to
    both.  ``concrete.abi_conformance`` checks the second at run time.

    AAPCS64 leaves the bits unspecified and Ghidra's AArch64 specification
    declares zero extension -- which is also what a caller's 32-bit register
    write produces -- so the AArch64 image is zero-extended.  MIPS n64 requires
    sign extension and its specification declares nothing.
    """

    SIGN_EXTENDED = "SIGN_EXTENDED"
    ZERO_EXTENDED = "ZERO_EXTENDED"


@dataclass(frozen=True)
class ArgumentSlot:
    """One register argument position of an ABI.

    ``index`` is the position within ``arg_class`` for ``PER_CLASS`` ABIs and
    the position in the whole parameter list for ``POSITIONAL`` ABIs.
    """

    arg_class: ArgClass
    index: int


@dataclass(frozen=True)
class AbiModel:
    abi_id: AbiId
    big_endian: bool
    register_bytes: int
    slot_numbering: SlotNumbering
    narrow_int_rule: NarrowIntRule
    narrow_int_image: NarrowIntImage
    int_argument_registers: Tuple[str, ...]
    fp_argument_registers: Tuple[str, ...]
    fp_argument_register_bytes: int
    int_return_register: str
    fp_return_register: str
    fp_return_register_bytes: int
    indirect_result_register: Optional[str]
    stack_pointer: str
    return_address_register: str
    # Holds the callee's own entry address at entry (position-independent MIPS code).
    entry_address_register: Optional[str]
    callee_saved_registers: Tuple[str, ...]
    # Control registers the ABI defines at entry, with their entry value.
    control_register_defaults: Tuple[Tuple[str, int], ...]
    # Bytes of the C ``int`` type of the ABI's data model.  Operands narrower
    # than ``int`` are promoted to ``int`` (C11 6.3.1.1), signed or unsigned,
    # so an operation narrower than ``int`` may stand for ``int`` arithmetic
    # on either extension of its operands.
    c_int_bytes: int = 0

    def argument_register(self, slot: ArgumentSlot) -> Optional[str]:
        table = (
            self.int_argument_registers
            if slot.arg_class is ArgClass.INT
            else self.fp_argument_registers
        )
        if slot.index < 0 or slot.index >= len(table):
            return None
        return table[slot.index]

    def argument_slot_of(self, base_register_name: str) -> Optional[ArgumentSlot]:
        """The argument slot a base register carries, or ``None``."""
        if base_register_name in self.int_argument_registers:
            return ArgumentSlot(
                ArgClass.INT, self.int_argument_registers.index(base_register_name)
            )
        if base_register_name in self.fp_argument_registers:
            return ArgumentSlot(
                ArgClass.FP, self.fp_argument_registers.index(base_register_name)
            )
        return None

    def return_class_of(self, base_register_name: str) -> Optional[ArgClass]:
        if base_register_name == self.int_return_register:
            return ArgClass.INT
        if base_register_name == self.fp_return_register:
            return ArgClass.FP
        return None

    def return_register(self, arg_class: ArgClass) -> str:
        return (
            self.int_return_register
            if arg_class is ArgClass.INT
            else self.fp_return_register
        )

    def argument_register_bytes(self, arg_class: ArgClass) -> int:
        return (
            self.register_bytes
            if arg_class is ArgClass.INT
            else self.fp_argument_register_bytes
        )

    def assign_slots(self, classes: Tuple[ArgClass, ...]) -> Optional[Tuple[ArgumentSlot, ...]]:
        """Slots of a register-only parameter list with these classes, in order.

        ``None`` when the list does not fit in the argument registers (the
        rest would be passed on the stack, which this model does not cover).
        """
        slots = []
        counters = {ArgClass.INT: 0, ArgClass.FP: 0}
        for position, arg_class in enumerate(classes):
            index = (
                position
                if self.slot_numbering is SlotNumbering.POSITIONAL
                else counters[arg_class]
            )
            counters[arg_class] += 1
            slot = ArgumentSlot(arg_class, index)
            if self.argument_register(slot) is None:
                return None
            slots.append(slot)
        return tuple(slots)


_AARCH64 = AbiModel(
    abi_id=AbiId.AARCH64_AAPCS64,
    big_endian=False,
    register_bytes=8,
    slot_numbering=SlotNumbering.PER_CLASS,
    narrow_int_rule=NarrowIntRule.UPPER_BITS_UNSPECIFIED,
    narrow_int_image=NarrowIntImage.ZERO_EXTENDED,
    int_argument_registers=("x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"),
    # Ghidra's AArch64 module makes z<n> the base of v<n>/q<n>/d<n>/s<n>.
    fp_argument_registers=("z0", "z1", "z2", "z3", "z4", "z5", "z6", "z7"),
    fp_argument_register_bytes=16,
    int_return_register="x0",
    fp_return_register="z0",
    fp_return_register_bytes=16,
    indirect_result_register="x8",
    stack_pointer="sp",
    return_address_register="x30",
    entry_address_register=None,
    callee_saved_registers=(
        "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29",
        # AAPCS64 preserves the low 64 bits of v8-v15.
        "d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15",
    ),
    control_register_defaults=(("fpcr", 0),),
    c_int_bytes=4,       # LP64 (AAPCS64 data model)
)

_MIPS_N64 = AbiModel(
    abi_id=AbiId.MIPS_N64,
    big_endian=True,
    register_bytes=8,
    slot_numbering=SlotNumbering.POSITIONAL,
    narrow_int_rule=NarrowIntRule.SIGN_EXTENDED_REQUIRED,
    narrow_int_image=NarrowIntImage.SIGN_EXTENDED,
    # n64 passes eight integer arguments in $4-$11.  Ghidra's MIPS module keeps
    # the o32 names for $8-$11, so the fifth to eighth are t0-t3 there.
    int_argument_registers=("a0", "a1", "a2", "a3", "t0", "t1", "t2", "t3"),
    fp_argument_registers=("f12", "f13", "f14", "f15", "f16", "f17", "f18", "f19"),
    fp_argument_register_bytes=8,
    int_return_register="v0",
    fp_return_register="f0",
    fp_return_register_bytes=8,
    indirect_result_register=None,
    stack_pointer="sp",
    return_address_register="ra",
    entry_address_register="t9",
    callee_saved_registers=(
        "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "gp",
        "f24", "f25", "f26", "f27", "f28", "f29", "f30", "f31",
    ),
    control_register_defaults=(("fcsr", 0),),
    c_int_bytes=4,       # LP64 (n64 data model)
)

_MODELS: Mapping[AbiId, AbiModel] = {
    _AARCH64.abi_id: _AARCH64,
    _MIPS_N64.abi_id: _MIPS_N64,
}


def abi_model(abi_id: AbiId) -> AbiModel:
    return _MODELS[AbiId(abi_id)]


ELF_FORMAT = "Executable and Linking Format (ELF)"

# (language id, compiler specification id, executable format) -> model.
#
# The key is exact on purpose.  The same processor runs other conventions that
# the tables above do not describe: for AArch64 the Windows, Go and Apple
# conventions (other compiler specifications, or the AppleSilicon language
# variant loaded from Mach-O); for 64-bit MIPS the o32/n32/o64 conventions
# (the ``64-32addr`` languages), the little-endian variants and the microMIPS
# and R6 instruction sets, none of which has been checked against a binary.
# An ELF64 big-endian MIPS program under the default specification is n64.
_SELECTION: Mapping[Tuple[str, str, str], AbiModel] = {
    ("AARCH64:LE:64:v8A", "default", ELF_FORMAT): _AARCH64,
    ("MIPS:BE:64:default", "default", ELF_FORMAT): _MIPS_N64,
}

# The name of the default prototype in the compiler specification of each
# selected program (checked at run time by ``concrete.abi_conformance``).
SPECIFICATION_PROTOTYPE_NAMES: Mapping[AbiId, str] = {
    AbiId.AARCH64_AAPCS64: "__cdecl",
    AbiId.MIPS_N64: "__stdcall",
}

# Calling-convention names of a function that mean "the program's default
# convention": no explicit convention, or the default prototype model itself.
_DEFAULT_CONVENTION_NAMES: Mapping[AbiId, Tuple[str, ...]] = {
    abi_id: ("unknown", "default", name)
    for abi_id, name in SPECIFICATION_PROTOTYPE_NAMES.items()
}


def select_abi(
    language_id: str,
    compiler_spec_id: str,
    executable_format: str,
    calling_convention: Optional[str] = None,
) -> Optional[AbiModel]:
    """The ABI model of a function, from facts of the binary.

    ``language_id`` / ``compiler_spec_id`` / ``executable_format`` identify the
    program; ``calling_convention`` is the convention name recorded for the
    function, when one is known.  ``None`` means the concrete layer has no
    model -- the program is not one of the exact combinations it describes, or
    the function is marked with a convention other than the program's default
    -- and callers treat that as a refusal.
    """
    model = _SELECTION.get((str(language_id), str(compiler_spec_id), str(executable_format)))
    if model is None:
        return None
    if calling_convention is not None and (
        str(calling_convention) not in _DEFAULT_CONVENTION_NAMES[model.abi_id]
    ):
        return None
    return model

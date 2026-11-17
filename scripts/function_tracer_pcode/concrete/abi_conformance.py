# -*- coding: utf-8 -*-
"""Run-time check of an ABI model against the program's compiler specification.

``concrete.abi`` writes the calling conventions out as tables from the public
ABI documents and selects one by the program's exact language, compiler
specification and executable format.  That selection says which document
applies; it does not show that the tables say what the program's own compiler
specification says.  Before anything runs, the executor reads the program's
default prototype (``CompilerSpecFacts``, extracted by the Ghidra boundary)
and ``check_abi_conformance`` compares every fact both sides state:

* integer and floating-point argument registers, in order, and that the
  argument after them is not in a register;
* how a mixed parameter list is numbered (per class / positional);
* where a narrow argument sits in its register (low-order part);
* the return register and position of each return class and width;
* the registers a callee preserves (the specification's "unaffected" list),
  apart from the stack pointer and the return-address register, which the
  model holds in their own roles;
* the stack pointer;
* how a narrow integer argument is extended (``pentry extension``) against
  the image the model writes (``AbiModel.narrow_int_image``).

Facts the compiler specification does not state -- the return-address
register (its prototypes declare none), the MIPS entry-address register, the
control-register defaults -- are not checked here.  The run checks the first
itself: a call only counts as returned when control reaches the return
address the entry state put in that register.

Any disagreement is a refusal of the program.  Nothing here reads source
code, a decompiled prototype or an expected verdict.
"""

from __future__ import annotations

import xml.etree.ElementTree as ElementTree
from dataclasses import dataclass
from enum import Enum
from typing import Optional, Tuple

from scripts.function_tracer_pcode.concrete.abi import (
    SPECIFICATION_PROTOTYPE_NAMES,
    AbiModel,
    ArgClass,
    NarrowIntImage,
    NarrowIntRule,
)
from scripts.function_tracer_pcode.concrete.storage import StorageLocation


class ReturnProbe(str, Enum):
    """The return types whose storage the facts record."""

    INT64 = "INT64"
    INT32 = "INT32"
    INT8 = "INT8"
    BINARY64 = "BINARY64"
    BINARY32 = "BINARY32"


# The mixed parameter list whose storage shows the numbering and the narrow
# positions: (int32, binary64, int32, binary32, int32).
MIXED_PROBE: Tuple[Tuple[ArgClass, int], ...] = (
    (ArgClass.INT, 4),
    (ArgClass.FP, 8),
    (ArgClass.INT, 4),
    (ArgClass.FP, 4),
    (ArgClass.INT, 4),
)

_RETURN_PROBES = {
    ReturnProbe.INT64: (ArgClass.INT, 8),
    ReturnProbe.INT32: (ArgClass.INT, 4),
    ReturnProbe.INT8: (ArgClass.INT, 1),
    ReturnProbe.BINARY64: (ArgClass.FP, 8),
    ReturnProbe.BINARY32: (ArgClass.FP, 4),
}


@dataclass(frozen=True)
class CompilerSpecFacts:
    """What the program's compiler specification states, read at run time.

    ``int_arguments`` / ``fp_arguments`` are the storage of a list of 8-byte
    integers / binary64 values one longer than the model's argument
    registers; ``mixed_arguments`` that of ``MIXED_PROBE``.  ``unaffected`` is
    the default prototype's unaffected list, each varnode named by the
    language register it is.  ``default_prototype_xml`` is the default
    prototype as the specification encodes it (the source of the extension
    attributes).
    """

    language_id: str
    compiler_spec_id: str
    executable_format: str
    default_prototype: str
    stack_pointer: str
    int_arguments: Tuple[StorageLocation, ...]
    fp_arguments: Tuple[StorageLocation, ...]
    mixed_arguments: Tuple[StorageLocation, ...]
    returns: Tuple[Tuple[ReturnProbe, StorageLocation], ...]
    unaffected: Tuple[StorageLocation, ...]
    default_prototype_xml: str


class ConformanceItem(str, Enum):
    DEFAULT_PROTOTYPE = "DEFAULT_PROTOTYPE"
    INT_ARGUMENT_REGISTERS = "INT_ARGUMENT_REGISTERS"
    FP_ARGUMENT_REGISTERS = "FP_ARGUMENT_REGISTERS"
    ARGUMENT_NUMBERING = "ARGUMENT_NUMBERING"
    NARROW_ARGUMENT_POSITION = "NARROW_ARGUMENT_POSITION"
    RETURN_LOCATION = "RETURN_LOCATION"
    CALLEE_SAVED_REGISTERS = "CALLEE_SAVED_REGISTERS"
    STACK_POINTER = "STACK_POINTER"
    NARROW_INT_EXTENSION = "NARROW_INT_EXTENSION"
    FACTS_INCOMPLETE = "FACTS_INCOMPLETE"


@dataclass(frozen=True)
class ConformanceMismatch:
    item: ConformanceItem
    expected: str
    found: str


@dataclass(frozen=True)
class AbiConformance:
    """The result of the check; ``conforms`` only when nothing disagrees."""

    mismatches: Tuple[ConformanceMismatch, ...]

    @property
    def conforms(self) -> bool:
        return not self.mismatches


def _describe(locations) -> str:
    return ", ".join(
        f"{loc.base_register_name}+{loc.byte_offset_in_base}:{loc.size_bytes}"
        if loc.is_register
        else f"stack:{loc.size_bytes}"
        for loc in locations
    )


def _is_low_part(location: StorageLocation, base: str, size: int, big_endian: bool) -> bool:
    return (
        location.is_register
        and location.base_register_name == base
        and location.size_bytes == size
        and location.is_low_order_part(big_endian)
    )


def integer_parameter_extensions(prototype_xml: str) -> Tuple[str, ...]:
    """The ``extension`` attribute of each integer register input entry.

    Reads the prototype as Ghidra encodes it (``storage="float"``,
    ``<addr space="register" .../>``) and, equally, as a specification file
    writes it (``metatype="float"``, ``<register name=.../>``).  ``"none"``
    stands for an entry without the attribute.  Floating-point entries, the
    hidden return-pointer entry and stack entries are skipped.
    """
    root = ElementTree.fromstring(prototype_xml)
    found = []
    for section in root.iter("input"):
        for entry in section.iter("pentry"):
            kind = entry.get("storage") or entry.get("metatype") or ""
            if kind in ("float", "hiddenret"):
                continue
            address = entry.find("addr")
            in_register = entry.find("register") is not None or (
                address is not None and address.get("space") == "register"
            )
            if not in_register:
                continue
            found.append(entry.get("extension", "none"))
    return tuple(found)


def _check_registers(model, facts, mismatches):
    for item, table, located, size in (
        (ConformanceItem.INT_ARGUMENT_REGISTERS, model.int_argument_registers, facts.int_arguments, 8),
        (ConformanceItem.FP_ARGUMENT_REGISTERS, model.fp_argument_registers, facts.fp_arguments, 8),
    ):
        expected = tuple(table)
        if len(located) != len(expected) + 1:
            mismatches.append(ConformanceMismatch(
                ConformanceItem.FACTS_INCOMPLETE, f"{len(expected) + 1} locations", str(len(located))
            ))
            continue
        good = all(
            _is_low_part(loc, name, size, model.big_endian)
            for loc, name in zip(located, expected)
        ) and not located[-1].is_register
        if not good:
            mismatches.append(ConformanceMismatch(
                item,
                ", ".join(f"{name}:{size}" for name in expected) + ", stack",
                _describe(located),
            ))


def _check_mixed(model, facts, mismatches):
    classes = tuple(arg_class for arg_class, _ in MIXED_PROBE)
    slots = model.assign_slots(classes)
    if slots is None or len(facts.mixed_arguments) != len(MIXED_PROBE):
        mismatches.append(ConformanceMismatch(
            ConformanceItem.FACTS_INCOMPLETE, f"{len(MIXED_PROBE)} locations", str(len(facts.mixed_arguments))
        ))
        return
    expected = tuple(model.argument_register(slot) for slot in slots)
    found = tuple(loc.base_register_name if loc.is_register else None for loc in facts.mixed_arguments)
    if found != expected:
        mismatches.append(ConformanceMismatch(
            ConformanceItem.ARGUMENT_NUMBERING, ", ".join(expected), _describe(facts.mixed_arguments)
        ))
        return
    for (arg_class, size), loc, name in zip(MIXED_PROBE, facts.mixed_arguments, expected):
        if not _is_low_part(loc, name, size, model.big_endian):
            mismatches.append(ConformanceMismatch(
                ConformanceItem.NARROW_ARGUMENT_POSITION,
                f"{name} low {size} bytes",
                _describe((loc,)),
            ))


def _check_returns(model, facts, mismatches):
    returns = dict(facts.returns)
    for probe, (arg_class, size) in _RETURN_PROBES.items():
        loc = returns.get(probe)
        name = model.return_register(arg_class)
        if loc is None:
            mismatches.append(ConformanceMismatch(ConformanceItem.FACTS_INCOMPLETE, probe.value, "missing"))
        elif not _is_low_part(loc, name, size, model.big_endian):
            mismatches.append(ConformanceMismatch(
                ConformanceItem.RETURN_LOCATION,
                f"{probe.value}: {name} low {size} bytes",
                _describe((loc,)),
            ))


def _check_callee_saved(model, facts, mismatches):
    roles = {model.stack_pointer, model.return_address_register}
    unaffected = set()
    unnamed = []
    for loc in facts.unaffected:
        if not loc.is_register or not loc.register_name:
            unnamed.append(loc)
        else:
            unaffected.add(loc.register_name)
    expected = set(model.callee_saved_registers)
    found = unaffected - roles
    if unnamed or found != expected:
        mismatches.append(ConformanceMismatch(
            ConformanceItem.CALLEE_SAVED_REGISTERS,
            ", ".join(sorted(expected)),
            ", ".join(sorted(found)) + (f" (+{len(unnamed)} unnamed)" if unnamed else ""),
        ))


def _check_extension(model, facts, mismatches):
    if (
        model.narrow_int_rule is NarrowIntRule.SIGN_EXTENDED_REQUIRED
        and model.narrow_int_image is not NarrowIntImage.SIGN_EXTENDED
    ):
        mismatches.append(ConformanceMismatch(
            ConformanceItem.NARROW_INT_EXTENSION,
            "an image the ABI admits",
            f"{model.narrow_int_image.value} under {model.narrow_int_rule.value}",
        ))
        return
    try:
        extensions = set(integer_parameter_extensions(facts.default_prototype_xml))
    except ElementTree.ParseError as error:
        mismatches.append(ConformanceMismatch(ConformanceItem.FACTS_INCOMPLETE, "prototype XML", str(error)))
        return
    if not extensions:
        mismatches.append(ConformanceMismatch(
            ConformanceItem.FACTS_INCOMPLETE, "integer parameter entries", "none"
        ))
        return
    declared = {"zero": NarrowIntImage.ZERO_EXTENDED, "sign": NarrowIntImage.SIGN_EXTENDED}
    if len(extensions) != 1:
        mismatches.append(ConformanceMismatch(
            ConformanceItem.NARROW_INT_EXTENSION, "one extension for every entry", ", ".join(sorted(extensions))
        ))
        return
    (extension,) = extensions
    image: Optional[NarrowIntImage] = declared.get(extension)
    if extension != "none" and image is None:
        mismatches.append(ConformanceMismatch(
            ConformanceItem.NARROW_INT_EXTENSION, "zero / sign / none", extension
        ))
    elif image is not None and image is not model.narrow_int_image:
        mismatches.append(ConformanceMismatch(
            ConformanceItem.NARROW_INT_EXTENSION, model.narrow_int_image.value, extension
        ))


def check_abi_conformance(model: AbiModel, facts: CompilerSpecFacts) -> AbiConformance:
    """Compare ``model`` with what the program's compiler specification states."""
    mismatches = []
    if facts.default_prototype != SPECIFICATION_PROTOTYPE_NAMES[model.abi_id]:
        mismatches.append(ConformanceMismatch(
            ConformanceItem.DEFAULT_PROTOTYPE,
            SPECIFICATION_PROTOTYPE_NAMES[model.abi_id],
            facts.default_prototype,
        ))
    if facts.stack_pointer != model.stack_pointer:
        mismatches.append(ConformanceMismatch(
            ConformanceItem.STACK_POINTER, model.stack_pointer, facts.stack_pointer
        ))
    _check_registers(model, facts, mismatches)
    _check_mixed(model, facts, mismatches)
    _check_returns(model, facts, mismatches)
    _check_callee_saved(model, facts, mismatches)
    _check_extension(model, facts, mismatches)
    return AbiConformance(tuple(mismatches))


# ------------------------------------------------------------ recording

def _location_to_json(loc: StorageLocation) -> list:
    return [
        loc.is_register, loc.register_name, loc.base_register_name,
        loc.base_register_bytes, loc.byte_offset_in_base, loc.size_bytes,
    ]


def _location_from_json(raw) -> StorageLocation:
    return StorageLocation(
        bool(raw[0]),
        None if raw[1] is None else str(raw[1]),
        None if raw[2] is None else str(raw[2]),
        int(raw[3]), int(raw[4]), int(raw[5]),
    )


def facts_to_json(facts: CompilerSpecFacts) -> dict:
    return {
        "language_id": facts.language_id,
        "compiler_spec_id": facts.compiler_spec_id,
        "executable_format": facts.executable_format,
        "default_prototype": facts.default_prototype,
        "stack_pointer": facts.stack_pointer,
        "int_arguments": [_location_to_json(x) for x in facts.int_arguments],
        "fp_arguments": [_location_to_json(x) for x in facts.fp_arguments],
        "mixed_arguments": [_location_to_json(x) for x in facts.mixed_arguments],
        "returns": [[probe.value, _location_to_json(loc)] for probe, loc in facts.returns],
        "unaffected": [_location_to_json(x) for x in facts.unaffected],
        "default_prototype_xml": facts.default_prototype_xml,
    }


def facts_from_json(raw) -> CompilerSpecFacts:
    return CompilerSpecFacts(
        language_id=str(raw["language_id"]),
        compiler_spec_id=str(raw["compiler_spec_id"]),
        executable_format=str(raw["executable_format"]),
        default_prototype=str(raw["default_prototype"]),
        stack_pointer=str(raw["stack_pointer"]),
        int_arguments=tuple(_location_from_json(x) for x in raw["int_arguments"]),
        fp_arguments=tuple(_location_from_json(x) for x in raw["fp_arguments"]),
        mixed_arguments=tuple(_location_from_json(x) for x in raw["mixed_arguments"]),
        returns=tuple((ReturnProbe(p), _location_from_json(loc)) for p, loc in raw["returns"]),
        unaffected=tuple(_location_from_json(x) for x in raw["unaffected"]),
        default_prototype_xml=str(raw["default_prototype_xml"]),
    )

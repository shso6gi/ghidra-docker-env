# -*- coding: utf-8 -*-
"""Run-time check of the ABI tables against the program's compiler specification.

The facts are recorded from real EqBench binaries (``tests/fixtures/concrete/
facts_*.json``, recorded by ``tests/tools/record_concrete_fixture.py``); each
test then breaks one fact and expects exactly that disagreement.  Ghidra is not
needed.
"""
import dataclasses
import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.concrete.abi import (
    ELF_FORMAT,
    AbiId,
    NarrowIntImage,
    abi_model,
    select_abi,
)
from scripts.function_tracer_pcode.concrete.abi_conformance import (
    ConformanceItem,
    ReturnProbe,
    check_abi_conformance,
    facts_from_json,
    facts_to_json,
    integer_parameter_extensions,
)
from scripts.function_tracer_pcode.concrete.storage import StorageLocation

FIXTURES = Path(__file__).resolve().parents[1] / "fixtures" / "concrete"
ARM = abi_model(AbiId.AARCH64_AAPCS64)
MIPS = abi_model(AbiId.MIPS_N64)


def _facts(name):
    raw = json.loads((FIXTURES / f"{name}.json").read_text())
    assert raw["schema"] == "concrete-compiler-spec-facts-v1" and raw["refusal"] is None
    return facts_from_json(raw["facts"])


@pytest.fixture(params=[("facts_aarch64_elf", ARM), ("facts_mips64_elf", MIPS)], ids=["aarch64", "mips64"])
def recorded(request):
    name, model = request.param
    return _facts(name), model


def _items(model, facts):
    return {m.item for m in check_abi_conformance(model, facts).mismatches}


def test_the_recorded_specifications_select_and_conform_to_their_models(recorded):
    facts, model = recorded
    assert select_abi(facts.language_id, facts.compiler_spec_id, facts.executable_format) is model
    assert facts.executable_format == ELF_FORMAT
    result = check_abi_conformance(model, facts)
    assert result.conforms, result.mismatches
    assert facts_from_json(facts_to_json(facts)) == facts


def test_a_model_is_not_checked_against_another_abis_specification():
    assert _items(MIPS, _facts("facts_aarch64_elf")) >= {
        ConformanceItem.DEFAULT_PROTOTYPE,
        ConformanceItem.INT_ARGUMENT_REGISTERS,
        ConformanceItem.FP_ARGUMENT_REGISTERS,
        ConformanceItem.RETURN_LOCATION,
        ConformanceItem.CALLEE_SAVED_REGISTERS,
        ConformanceItem.NARROW_INT_EXTENSION,
    }


def test_the_extension_of_narrow_integer_parameters_is_read_from_the_specification():
    # Measured: Ghidra's AArch64 specification declares zero extension and the
    # MIPS64 one declares none (n64 sign extension is the ABI's rule).
    assert set(integer_parameter_extensions(_facts("facts_aarch64_elf").default_prototype_xml)) == {"zero"}
    assert set(integer_parameter_extensions(_facts("facts_mips64_elf").default_prototype_xml)) == {"none"}
    # The specification-file spelling is read the same way.
    xml = (
        '<prototype name="p"><input>'
        '<pentry minsize="1" maxsize="8" metatype="float"><register name="d0"/></pentry>'
        '<pentry minsize="1" maxsize="8" extension="sign"><register name="x0"/></pentry>'
        '<pentry minsize="1" maxsize="500" align="8"><addr offset="0" space="stack"/></pentry>'
        "</input></prototype>"
    )
    assert integer_parameter_extensions(xml) == ("sign",)


def _replace_xml(facts, old, new):
    assert old in facts.default_prototype_xml
    return dataclasses.replace(facts, default_prototype_xml=facts.default_prototype_xml.replace(old, new))


def test_an_extension_that_differs_from_the_models_image_is_a_mismatch():
    arm = _facts("facts_aarch64_elf")
    assert _items(ARM, _replace_xml(arm, 'extension="zero"', 'extension="sign"')) == {
        ConformanceItem.NARROW_INT_EXTENSION
    }
    # Undeclared: AAPCS64 leaves the bits unspecified, any image conforms.
    assert _items(ARM, _replace_xml(arm, ' extension="zero"', "")) == set()
    mips = _facts("facts_mips64_elf")
    first = mips.default_prototype_xml.index('<pentry minsize="1" maxsize="8">')
    zero = dataclasses.replace(
        mips,
        default_prototype_xml=(
            mips.default_prototype_xml[:first]
            + '<pentry minsize="1" maxsize="8" extension="zero">'
            + mips.default_prototype_xml[first + len('<pentry minsize="1" maxsize="8">'):]
        ),
    )
    assert _items(MIPS, zero) == {ConformanceItem.NARROW_INT_EXTENSION}   # mixed and not sign
    # A model whose image its own ABI rule does not admit is refused as well.
    broken = dataclasses.replace(MIPS, narrow_int_image=NarrowIntImage.ZERO_EXTENDED)
    assert _items(broken, mips) == {ConformanceItem.NARROW_INT_EXTENSION}


def _moved(location, **changes):
    return dataclasses.replace(location, **changes)


def test_each_disagreeing_fact_is_reported(recorded):
    facts, model = recorded
    cases = [
        (dataclasses.replace(facts, default_prototype="__other"), ConformanceItem.DEFAULT_PROTOTYPE),
        (dataclasses.replace(facts, stack_pointer="x29"), ConformanceItem.STACK_POINTER),
        (
            dataclasses.replace(facts, int_arguments=facts.int_arguments[1:] + facts.int_arguments[:1]),
            ConformanceItem.INT_ARGUMENT_REGISTERS,
        ),
        (
            # A ninth integer argument in a register: the table is too short.
            dataclasses.replace(facts, int_arguments=facts.int_arguments[:8] + facts.int_arguments[:1]),
            ConformanceItem.INT_ARGUMENT_REGISTERS,
        ),
        (
            dataclasses.replace(facts, fp_arguments=tuple(reversed(facts.fp_arguments[:8])) + facts.fp_arguments[8:]),
            ConformanceItem.FP_ARGUMENT_REGISTERS,
        ),
        (
            dataclasses.replace(facts, unaffected=facts.unaffected[1:]),
            ConformanceItem.CALLEE_SAVED_REGISTERS,
        ),
        (
            dataclasses.replace(
                facts,
                unaffected=facts.unaffected + (StorageLocation(True, "x9" if model is ARM else "t4", "x9", 8, 0, 8),),
            ),
            ConformanceItem.CALLEE_SAVED_REGISTERS,
        ),
    ]
    for broken, item in cases:
        assert _items(model, broken) == {item}, item


def test_numbering_and_narrow_positions_come_from_the_mixed_list(recorded):
    facts, model = recorded
    mixed = list(facts.mixed_arguments)
    # (int, double, int, float, int): swap the second integer into the third slot.
    other = facts.int_arguments[3]
    renumbered = mixed[:2] + [_moved(mixed[2], base_register_name=other.base_register_name)] + mixed[3:]
    assert _items(model, dataclasses.replace(facts, mixed_arguments=tuple(renumbered))) == {
        ConformanceItem.ARGUMENT_NUMBERING
    }
    high = _moved(mixed[0], register_name=None, byte_offset_in_base=0 if model.big_endian else 4)
    assert _items(model, dataclasses.replace(facts, mixed_arguments=(high,) + tuple(mixed[1:]))) == {
        ConformanceItem.NARROW_ARGUMENT_POSITION
    }


def test_return_locations_are_checked_per_class_and_width(recorded):
    facts, model = recorded
    returns = dict(facts.returns)
    swapped = dict(returns)
    swapped[ReturnProbe.BINARY64] = returns[ReturnProbe.INT64]
    assert _items(model, dataclasses.replace(facts, returns=tuple(swapped.items()))) == {
        ConformanceItem.RETURN_LOCATION
    }
    narrow = dict(returns)
    narrow[ReturnProbe.INT8] = _moved(
        returns[ReturnProbe.INT8], register_name=None, byte_offset_in_base=0 if model.big_endian else 7
    )
    assert _items(model, dataclasses.replace(facts, returns=tuple(narrow.items()))) == {
        ConformanceItem.RETURN_LOCATION
    }
    missing = tuple((p, loc) for p, loc in facts.returns if p is not ReturnProbe.BINARY32)
    assert _items(model, dataclasses.replace(facts, returns=missing)) == {ConformanceItem.FACTS_INCOMPLETE}

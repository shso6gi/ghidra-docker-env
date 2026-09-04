"""Phase 5: RegionFacts is the first collaborator extracted from ReturnAnalyzer.
It owns only the program; the facade delegates to it and keeps the old names."""
from types import SimpleNamespace

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.region_facts import (
    RegionFacts,
    input_is_nondata_operand,
    parameter_index_for_location,
)


class _Address:
    def __init__(self, space, offset):
        self._space = SimpleNamespace(getName=lambda: space)
        self._offset = offset

    def getAddressSpace(self):
        return self._space

    def getOffset(self):
        return self._offset


class _Varnode:
    def __init__(self, space, offset, size, *, constant=False, defined=False):
        self._address = _Address(space, offset)
        self._size = size
        self._constant = constant
        self._defined = defined

    def isConstant(self):
        return self._constant

    def getDef(self):
        return object() if self._defined else None

    def getAddress(self):
        return self._address

    def getSize(self):
        return self._size


class _CodeProgram:
    """Every address is inside a function."""

    def getFunctionManager(self):
        return SimpleNamespace(getFunctionContaining=lambda address: object())


def test_pure_predicates():
    assert input_is_nondata_operand("LOAD", 0) and not input_is_nondata_operand("LOAD", 1)
    assert input_is_nondata_operand("CALL", 0) and not input_is_nondata_operand("INT_ADD", 0)
    params = [{"index": 3, "storage": {"space_name": "register", "offset": 0x20, "size": 8}}]
    assert parameter_index_for_location(("register", 0x20, 8), params) == 3
    assert parameter_index_for_location(("register", 0x28, 8), params) is None
    assert parameter_index_for_location(("stack", 8, 8), [{"no": "storage"}]) is None


def test_live_in_key_classification():
    facts = RegionFacts(program=None)
    params = [{"index": 0, "storage": {"space_name": "register", "offset": 0x20, "size": 8}}]
    assert facts.live_in_key(_Varnode("register", 0x20, 8), mnemonic="CALL", input_index=0, parameters=params) == (None, "excluded_nondata_operand")
    assert facts.live_in_key(_Varnode("register", 0x20, 8, constant=True), mnemonic="INT_ADD", input_index=0, parameters=params) == (None, "excluded_not_live_in")
    assert facts.live_in_key(_Varnode("register", 0x20, 8, defined=True), mnemonic="INT_ADD", input_index=0, parameters=params) == (None, "excluded_not_live_in")
    assert facts.live_in_key(_Varnode("register", 0x20, 8), mnemonic="INT_ADD", input_index=0, parameters=params) == (("parameter_input", 0, ("register", 0x20, 8)), "included")
    assert facts.live_in_key(_Varnode("register", 0x28, 8), mnemonic="INT_ADD", input_index=0, parameters=params) == (("register_input", ("register", 0x28, 8)), "included")
    assert facts.live_in_key(_Varnode("stack", -8, 4), mnemonic="INT_ADD", input_index=0, parameters=params) == (("memory_input", ("stack", -8, 4)), "included")
    assert facts.live_in_key(_Varnode("unique", 0x100, 4), mnemonic="INT_ADD", input_index=0, parameters=params) == (None, "incomplete")
    assert facts.live_in_key(object(), mnemonic="INT_ADD", input_index=0, parameters=params) == (None, "incomplete")
    # a ram address that the program knows as code is an artifact, not data
    code_facts = RegionFacts(program=_CodeProgram())
    assert not RegionFacts(program=None).address_is_code(_Address("ram", 0x1000))
    assert code_facts.address_is_code(_Address("ram", 0x1000))
    assert code_facts.live_in_key(_Varnode("ram", 0x1000, 8), mnemonic="INT_ADD", input_index=0, parameters=()) == (None, "excluded_artifact_code_address")
    assert facts.live_in_key(_Varnode("ram", 0x1000, 8), mnemonic="INT_ADD", input_index=0, parameters=()) == (("memory_input", ("ram", 0x1000, 8)), "included")


def test_facade_delegates_and_keeps_the_old_names():
    analyzer = ReturnAnalyzer(program=None)
    assert isinstance(analyzer._region_facts, RegionFacts)
    assert analyzer._region_facts.program is analyzer.program
    varnode = _Varnode("register", 0x20, 8)
    params = [{"index": 0, "storage": {"space_name": "register", "offset": 0x20, "size": 8}}]
    assert analyzer._region_live_in_key(varnode, mnemonic="INT_ADD", input_index=0, parameters=params) == analyzer._region_facts.live_in_key(varnode, mnemonic="INT_ADD", input_index=0, parameters=params)
    assert ReturnAnalyzer._region_input_is_nondata_operand("STORE", 0) is True
    assert ReturnAnalyzer._region_parameter_index_for_location(("register", 0x20, 8), params) == 0
    assert analyzer._region_address_is_code(None) is False

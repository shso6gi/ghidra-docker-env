# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.model.call_target import CallTargetRef
from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixer


class _FakeFunction:
    def __init__(self, name: str):
        self._name = name

    def getName(self):
        return self._name


class _FakeFunctionManager:
    def __init__(self, functions):
        self._functions = list(functions)
        self._by_address = {}

    def getFunctions(self, _forward):
        return list(self._functions)

    def map_address(self, address, function):
        self._by_address[address] = function

    def getFunctionAt(self, address):
        return self._by_address.get(address)


class _FakeAddressSpace:
    def getAddress(self, offset):
        return ("addr", offset)


class _FakeAddressFactory:
    def getDefaultAddressSpace(self):
        return _FakeAddressSpace()


class _FakeProgram:
    def __init__(self, functions):
        self._manager = _FakeFunctionManager(functions)

    def getFunctionManager(self):
        return self._manager

    def getAddressFactory(self):
        return _FakeAddressFactory()


def test_analyze_function_by_name_reports_simple_not_found_message():
    analyzer = ReturnAnalyzer(_FakeProgram([_FakeFunction("fc_add")]), debug=False)

    analysis = analyzer.analyze_function_by_name("lr_loop_with_side_effect")

    assert analysis is None
    assert analyzer.get_last_function_lookup_error() == "Function 'lr_loop_with_side_effect' not found"


def test_return_analyzer_find_function_by_name_uses_exact_getfunctions_match():
    target = _FakeFunction("lr_loop_with_side_effect")
    analyzer = ReturnAnalyzer(_FakeProgram([target, _FakeFunction("lr_loop_with_side_effect_alt")]), debug=False)

    resolved = analyzer._find_function_by_name("lr_loop_with_side_effect")

    assert resolved is target


def test_type_fixer_find_function_by_name_uses_exact_getfunctions_match():
    target = _FakeFunction("lr_loop_with_side_effect")
    fixer = TypeFixer(_FakeProgram([target, _FakeFunction("lr_loop_with_side_effect_alt")]), debug=False)

    resolved = fixer._find_function_by_name("lr_loop_with_side_effect")

    assert resolved is target


def test_return_analyzer_resolve_target_function_uses_entry_offset_lookup():
    target = _FakeFunction("callee")
    program = _FakeProgram([target])
    program.getFunctionManager().map_address(("addr", 0x401000), target)
    analyzer = ReturnAnalyzer(program, debug=False)

    resolved = analyzer._resolve_target_function(CallTargetRef.from_name("callee", entry_offset=0x401000))

    assert resolved is target

# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.analysis.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixer


class _FakeFunction:
    def __init__(self, name: str):
        self._name = name

    def getName(self):
        return self._name


class _FakeFunctionManager:
    def __init__(self, functions):
        self._functions = list(functions)

    def getFunctions(self, _forward):
        return list(self._functions)


class _FakeProgram:
    def __init__(self, functions):
        self._manager = _FakeFunctionManager(functions)

    def getFunctionManager(self):
        return self._manager


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

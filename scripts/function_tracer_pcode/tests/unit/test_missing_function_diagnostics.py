# -*- coding: utf-8 -*-

import pytest

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.failure import (
    ANALYSIS_STATUS_ANALYSIS_EXCEPTION,
    ANALYSIS_STATUS_DECOMPILATION_FAILED,
    ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS,
    ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
)
from scripts.function_tracer_pcode.core import Expression, FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.checker.phases.handler import PhaseContext
from scripts.function_tracer_pcode.checker.result_factory import create_context_unknown_result
from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixer
from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixResult
from scripts.function_tracer_pcode.checker.unknown_reason import UnknownReasonClass, UnknownReasonId
from scripts.function_tracer_pcode.reporting.unknown_reason_summary import (
    summarize_validation_unknowns,
)


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


class _FakeDecompilerResult:
    def __init__(self, completed=True, high_function=object()):
        self._completed = completed
        self._high_function = high_function

    def decompileCompleted(self):
        return self._completed

    def getHighFunction(self):
        return self._high_function


class _FakeDecompiler:
    def __init__(self, result):
        self._result = result

    def decompileFunction(self, *_args):
        return self._result


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
    failure = analyzer.get_last_analysis_failure()
    assert failure is not None
    assert failure.status == ANALYSIS_STATUS_FUNCTION_LOOKUP_MISS


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


def test_return_analyzer_records_decompilation_failed_status(monkeypatch):
    function = _FakeFunction("target")
    analyzer = ReturnAnalyzer(_FakeProgram([function]), debug=False)
    monkeypatch.setattr(
        analyzer,
        "_get_decompiler",
        lambda: _FakeDecompiler(_FakeDecompilerResult(completed=False)),
    )

    analysis = analyzer.analyze_function_by_name("target")

    assert analysis is None
    failure = analyzer.get_last_analysis_failure()
    assert failure is not None
    assert failure.status == ANALYSIS_STATUS_DECOMPILATION_FAILED


def test_return_analyzer_records_high_function_missing_status(monkeypatch):
    function = _FakeFunction("target")
    analyzer = ReturnAnalyzer(_FakeProgram([function]), debug=False)
    monkeypatch.setattr(
        analyzer,
        "_get_decompiler",
        lambda: _FakeDecompiler(_FakeDecompilerResult(completed=True, high_function=None)),
    )

    analysis = analyzer.analyze_function_by_name("target")

    assert analysis is None
    failure = analyzer.get_last_analysis_failure()
    assert failure is not None
    assert failure.status == ANALYSIS_STATUS_HIGH_FUNCTION_MISSING


def test_return_analyzer_records_analysis_exception_without_swallowing(monkeypatch):
    function = _FakeFunction("target")
    analyzer = ReturnAnalyzer(_FakeProgram([function]), debug=False)

    def _boom(*_args, **_kwargs):
        raise RuntimeError("implementation bug")

    monkeypatch.setattr(analyzer, "analyze_function", _boom)

    with pytest.raises(RuntimeError, match="implementation bug"):
        analyzer.analyze_function_by_name("target")

    failure = analyzer.get_last_analysis_failure()
    assert failure is not None
    assert failure.status == ANALYSIS_STATUS_ANALYSIS_EXCEPTION


def test_refresh_structural_recurrence_summary_accepts_analysis_return(monkeypatch):
    function = _FakeFunction("target")
    analyzer = ReturnAnalyzer(_FakeProgram([function]), debug=False)
    seed = FunctionReturnAnalysis(
        "target",
        "0x1000",
        [],
        [ReturnInfo("0x1000", Expression.constant(1, 4))],
    )
    refreshed = FunctionReturnAnalysis(
        "target",
        "0x1000",
        [],
        [ReturnInfo("0x1004", Expression.constant(2, 4))],
    )

    monkeypatch.setattr(analyzer, "_find_function_by_name", lambda _name: function)
    monkeypatch.setattr(
        analyzer,
        "_get_decompiler",
        lambda: _FakeDecompiler(_FakeDecompilerResult(completed=True, high_function=object())),
    )
    monkeypatch.setattr(analyzer, "_make_tracer", lambda _high_function: object())
    monkeypatch.setattr(
        analyzer,
        "_apply_structural_recurrence_summary",
        lambda *_args, **_kwargs: refreshed,
    )
    monkeypatch.setattr(analyzer, "_normalize_return_partition", lambda _analysis: None)
    monkeypatch.setattr(analyzer, "_mark_incomplete_control_flow", lambda _analysis: None)

    result = analyzer.refresh_structural_recurrence_summary(seed)

    assert result is refreshed


@pytest.mark.parametrize(
    ("failure_status", "expected_reason_id"),
    [
        (
            ANALYSIS_STATUS_DECOMPILATION_FAILED,
            UnknownReasonId.DECOMPILATION_FAILED.value,
        ),
        (
            ANALYSIS_STATUS_HIGH_FUNCTION_MISSING,
            UnknownReasonId.HIGH_FUNCTION_MISSING.value,
        ),
    ],
)
def test_context_unknown_result_synthesizes_operational_unknown_reason(
    failure_status,
    expected_reason_id,
):
    ctx = PhaseContext(
        program1=object(),
        program2=object(),
        function_name1="snippet",
        function_name2="snippet",
        binary1_name="B14",
        binary2_name="B16",
        decompile_timeout=30,
        save_formula=False,
        type_fix_result=TypeFixResult(),
        original_signature1=None,
        original_signature2=None,
    )

    result = create_context_unknown_result(
        ctx=ctx,
        failure_status=failure_status,
        message=f"{failure_status} for snippet",
        start_time=0.0,
        retry_count=0,
    )
    payload = result.to_dict()
    summary = summarize_validation_unknowns([payload])

    assert payload["error_message"] is None
    assert payload["failure_status"] == failure_status
    assert payload["unknown_reasons"][0]["reason_id"] == expected_reason_id
    assert summary.unknown_by_reason == {
        expected_reason_id: 1,
    }
    assert summary.operational_unknown_by_reason == {
        expected_reason_id: 1,
    }
    assert summary.operational_unknown_by_class == {
        UnknownReasonClass.OPERATIONAL_GAP.value: 1,
    }

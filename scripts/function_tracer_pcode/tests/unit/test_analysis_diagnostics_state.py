"""Phase 6a-4: AnalysisDiagnosticsState が診断 2 フィールドを所有し、更新タイミングの契約が変わらないことの回帰テスト。"""

import dataclasses
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.diagnostics_state import AnalysisDiagnosticsState
from scripts.function_tracer_pcode.analysis.failure import AnalysisFailure
from scripts.function_tracer_pcode.analysis.returns._shared import ANALYSIS_STATUS_DECOMPILATION_FAILED, ANALYSIS_STATUS_HIGH_FUNCTION_MISSING
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer

FIELDS = [f.name for f in dataclasses.fields(AnalysisDiagnosticsState)]


def _analyzer():
    return ReturnAnalyzer(program=Mock(), debug=False)


def _stale(analyzer):
    analyzer._last_function_lookup_error = "stale-lookup"
    analyzer._last_analysis_failure = AnalysisFailure(status="stale", message="stale", function_name="old")


def test_diagnostics_state_has_exactly_the_two_fields():
    assert set(FIELDS) == {"last_function_lookup_error", "last_analysis_failure"}


def test_facade_reads_and_writes_go_through_the_owner():
    analyzer = _analyzer()
    assert isinstance(analyzer._diagnostics, AnalysisDiagnosticsState)
    assert analyzer._last_function_lookup_error is None and analyzer._last_analysis_failure is None
    assert not ({"_last_function_lookup_error", "_last_analysis_failure"} & set(vars(analyzer)))
    failure = AnalysisFailure(status="x", message="m", function_name="f")
    analyzer._last_analysis_failure = failure
    analyzer._last_function_lookup_error = "err"
    assert analyzer._diagnostics.last_analysis_failure is failure and analyzer._diagnostics.last_function_lookup_error == "err"
    assert analyzer.get_last_analysis_failure() is failure
    assert analyzer.get_last_function_lookup_error() == "err"
    assert analyzer.get_last_analysis_failure_status() == "x"


def test_analyze_function_by_name_resets_both_fields_on_entry_and_records_a_lookup_miss():
    analyzer = _analyzer()
    _stale(analyzer)
    with patch.object(analyzer._program_access, "find_function_by_name", return_value=None):
        assert analyzer.analyze_function_by_name("missing") is None
    assert analyzer.get_last_function_lookup_error() == "Function 'missing' not found"
    failure = analyzer.get_last_analysis_failure()
    assert failure is not None and failure.function_name == "missing" and failure.message == "Function 'missing' not found"


def test_analyze_function_by_name_clears_both_fields_on_a_successful_lookup_and_analysis():
    analyzer = _analyzer()
    _stale(analyzer)
    sentinel = object()
    with patch.object(analyzer._program_access, "find_function_by_name", return_value=Mock()), \
         patch.object(ReturnAnalyzer, "analyze_function", return_value=sentinel):
        assert analyzer.analyze_function_by_name("f") is sentinel
    assert analyzer.get_last_function_lookup_error() is None
    assert analyzer.get_last_analysis_failure() is None


def test_analyze_function_by_name_records_an_exception_raised_by_analyze_function():
    """契約: 例外は記録した上で re-raise される（握りつぶさない）。"""
    import pytest
    analyzer = _analyzer()
    with patch.object(analyzer._program_access, "find_function_by_name", return_value=Mock()), \
         patch.object(ReturnAnalyzer, "analyze_function", side_effect=RuntimeError("boom")):
        with pytest.raises(RuntimeError):
            analyzer.analyze_function_by_name("f")
    failure = analyzer.get_last_analysis_failure()
    assert failure is not None and "boom" in str(failure.message)
    assert analyzer.get_last_function_lookup_error() is None  # 例外経路では lookup error は None のまま


class _AlwaysHit(dict):
    """`analyze_function` の cached-analysis 早期 return 経路を確実に踏ませる call_analysis_cache。"""

    def __init__(self, hit):
        super().__init__()
        self._hit = hit

    def get(self, key, default=None):
        return self._hit


def _function_mock(name="f"):
    fn = Mock()
    fn.getName.return_value = name
    fn.getEntryPoint.return_value = "0x1000"
    return fn


def test_direct_analyze_function_does_not_reset_a_stale_failure_on_entry():
    """契約: analyze_function 自体は入口で診断状態を reset しない（reset は analyze_function_by_name の責務）。

    診断を一切書かない cached-analysis 早期 return 経路を踏み、stale な 2 フィールドが同一のまま残ることを固定する。
    """
    analyzer = _analyzer()
    _stale(analyzer)
    stale_failure = analyzer.get_last_analysis_failure()
    cached = object()
    analyzer._call_analysis_cache = _AlwaysHit(cached)   # property setter 経由の直接代入 seam
    assert analyzer.analyze_function(_function_mock(), timeout=1) is cached
    assert analyzer.get_last_analysis_failure() is stale_failure
    assert analyzer.get_last_function_lookup_error() == "stale-lookup"


def _run_decompile_failure(analyzer, results):
    analyzer._call_analysis_cache = {}
    with patch("scripts.function_tracer_pcode.ghidra.decompilation_broker.decompile_function", return_value=results) as broker:
        result = analyzer.analyze_function(_function_mock("target"), timeout=1)
    assert broker.call_args.args[0] is analyzer   # top-level broker は facade を第 1 引数に取る（analyze_function 内の局所 import を source module で patch）
    return result


def test_direct_analyze_function_overwrites_the_failure_only_when_decompilation_fails():
    analyzer = _analyzer()
    _stale(analyzer)
    results = Mock()
    results.decompileCompleted.return_value = False
    assert _run_decompile_failure(analyzer, results) is None
    failure = analyzer.get_last_analysis_failure()
    assert failure.message == "Decompilation failed!" and failure.status == ANALYSIS_STATUS_DECOMPILATION_FAILED
    assert failure.function_name == "target"
    assert analyzer.get_last_function_lookup_error() == "stale-lookup"   # analyze_function は lookup error に触れない


def test_direct_analyze_function_records_missing_high_function():
    analyzer = _analyzer()
    _stale(analyzer)
    results = Mock()
    results.decompileCompleted.return_value = True
    results.getHighFunction.return_value = None
    assert _run_decompile_failure(analyzer, results) is None
    failure = analyzer.get_last_analysis_failure()
    assert failure.message == "HighFunction is None!" and failure.status == ANALYSIS_STATUS_HIGH_FUNCTION_MISSING
    assert failure.function_name == "target"
    assert analyzer.get_last_function_lookup_error() == "stale-lookup"

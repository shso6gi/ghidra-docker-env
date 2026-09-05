"""Phase 6a-4: AnalysisDiagnosticsState が診断 2 フィールドを所有し、更新タイミングの契約が変わらないことの回帰テスト。"""

import dataclasses
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.diagnostics_state import AnalysisDiagnosticsState
from scripts.function_tracer_pcode.analysis.returns._shared import AnalysisFailure
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


def test_direct_analyze_function_does_not_reset_a_stale_failure_on_entry():
    """契約: analyze_function 自体は入口で診断状態を reset しない（reset は analyze_function_by_name の責務）。"""
    analyzer = _analyzer()
    _stale(analyzer)
    stale = analyzer.get_last_analysis_failure()
    results = Mock()
    results.decompileCompleted.return_value = True
    results.getHighFunction.return_value = None  # "HighFunction is None!" 経路で上書きされる
    with patch.object(analyzer._program_access, "decompile_function", return_value=results), \
         patch.object(analyzer._program_access, "get_decompiler", return_value=Mock(decompileFunction=Mock(return_value=results))), \
         patch.object(ReturnAnalyzer, "_collect_parameters", return_value=[]):
        try:
            analyzer.analyze_function(Mock(getName=Mock(return_value="f"), getEntryPoint=Mock(return_value="0x1")), timeout=1)
        except Exception:
            pass
    after = analyzer.get_last_analysis_failure()
    # stale は入口では消えず、失敗経路に到達した場合のみ新しい failure で上書きされる
    assert after is not None
    assert after is stale or after.message in ("HighFunction is None!", "Decompilation failed!")
    assert analyzer.get_last_function_lookup_error() == "stale-lookup"  # analyze_function は lookup error に触れない

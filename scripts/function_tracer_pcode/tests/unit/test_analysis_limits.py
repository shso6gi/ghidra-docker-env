"""Phase 6a-3: AnalysisLimits が bounded-call 設定を所有し、facade 属性 seam が維持されることの回帰テスト。"""

import dataclasses
import inspect
from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.limits import AnalysisLimits
from scripts.function_tracer_pcode.analysis.returns import analyzer as analyzer_module
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.config.settings import (
    BOUNDED_CALL_MAX_CASES,
    BOUNDED_CALL_REFINEMENT_ENABLED,
    BOUNDED_CALL_UNROLL_LIMIT,
)

FIELDS = [f.name for f in dataclasses.fields(AnalysisLimits)]


def _analyzer():
    return ReturnAnalyzer(program=Mock(), debug=False)


def test_limits_has_exactly_the_three_bounded_call_fields():
    assert set(FIELDS) == {"bounded_call_refinement_enabled", "bounded_call_unroll_limit", "bounded_call_max_cases"}


def test_from_settings_applies_the_same_conversions_as_the_old_constructor():
    limits = AnalysisLimits.from_settings()
    assert limits.bounded_call_refinement_enabled is bool(BOUNDED_CALL_REFINEMENT_ENABLED)
    assert limits.bounded_call_unroll_limit == int(BOUNDED_CALL_UNROLL_LIMIT) and type(limits.bounded_call_unroll_limit) is int
    assert limits.bounded_call_max_cases == int(BOUNDED_CALL_MAX_CASES) and type(limits.bounded_call_max_cases) is int


def test_facade_reads_come_from_the_owner_and_are_not_raw_attributes():
    analyzer = _analyzer()
    assert isinstance(analyzer._limits, AnalysisLimits)
    for f in FIELDS:
        assert getattr(analyzer, "_" + f) == getattr(analyzer._limits, f), f
    assert not ({"_" + f for f in FIELDS} & set(vars(analyzer)))
    assert analyzer._bounded_call_max_cases == int(BOUNDED_CALL_MAX_CASES)


def test_direct_assignment_updates_the_owner_without_coercion():
    """既存 seam: analyzer._bounded_call_* への直接代入。旧属性と同じく値はそのまま格納される。"""
    analyzer = _analyzer()
    analyzer._bounded_call_max_cases = 3
    analyzer._bounded_call_unroll_limit = 0
    analyzer._bounded_call_refinement_enabled = False
    assert analyzer._limits.bounded_call_max_cases == 3 and analyzer._bounded_call_max_cases == 3
    assert analyzer._limits.bounded_call_unroll_limit == 0
    assert analyzer._limits.bounded_call_refinement_enabled is False
    analyzer._bounded_call_max_cases = "7"  # 旧属性は型変換しなかった: setter も coercion しない
    assert analyzer._limits.bounded_call_max_cases == "7"


def test_owners_are_created_before_any_state_dependent_collaborator_in_the_constructor():
    """#84 レビュー指摘: runtime state / limits の所有者は collaborator 構築より前に作る（temporal coupling の解消）。"""
    src = inspect.getsource(ReturnAnalyzer.__init__)
    lines = src.splitlines()
    idx = {k: next(i for i, l in enumerate(lines) if k in l) for k in ("self._analysis_session = AnalysisSession()", "self._runtime_state = AnalysisRuntimeState()", "self._limits = AnalysisLimits.from_settings()", "self._diagnostics = AnalysisDiagnosticsState()")}
    first_collab = next(i for i, l in enumerate(lines) if "= ExpressionCaseService(" in l or "= ConstantValueService(" in l)
    assert max(idx.values()) < first_collab
    # DebugReporter / LocalValueResolver / ProgramAccessService はそれより前に作られるが、runtime state / limits を受け取らない
    assert "_runtime_state" not in "".join(lines[: idx["self._runtime_state = AnalysisRuntimeState()"]])


def test_analyzer_no_longer_imports_the_bounded_call_settings_directly():
    for name in ("BOUNDED_CALL_REFINEMENT_ENABLED", "BOUNDED_CALL_UNROLL_LIMIT", "BOUNDED_CALL_MAX_CASES"):
        assert not hasattr(analyzer_module, name), name

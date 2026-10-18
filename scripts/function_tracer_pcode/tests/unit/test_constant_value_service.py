"""ConstantValueService collaborator（Phase 5 #6、plan v4 PR-C で stack protector の条件除去を撤去）の回帰テスト。"""

import inspect
from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.constant_values import ConstantValueService
from scripts.function_tracer_pcode.core.expression import Expression


def _analyzer(debug=False):
    return ReturnAnalyzer(program=Mock(), debug=debug)


def test_collaborator_holds_no_state():
    assert vars(_analyzer()._constant_values) == {}


def test_the_only_method_is_constant_int_value():
    """条件を形だけで canary と認める helper（照合・除去・probe）は撤去した（plan v4 PR-C）。"""
    names = [n for n, _ in inspect.getmembers(ConstantValueService, predicate=inspect.isfunction)]
    assert names == ["constant_int_value"]
    for removed in (
        "_strip_stack_protector_only_conditions",
        "_condition_looks_like_stack_protector_guard",
        "_extract_stack_protector_compare_pair",
        "_reads_share_stack_protector_probe",
        "_extract_stack_protector_memory_probe",
        "_extract_indirect_probe",
        "_extract_difference_pair",
        "_is_zero_constant",
    ):
        assert not hasattr(ReturnAnalyzer, removed), removed


def test_constant_int_value_matches_facade_result():
    analyzer = _analyzer()
    assert analyzer._constant_int_value(Expression.constant(9, 4)) == 9
    assert analyzer._constant_values.constant_int_value(Expression.constant(9, 4)) == 9
    assert analyzer._constant_values.constant_int_value(Expression.variable("param_1", 4)) is None
    assert analyzer._constant_values.constant_int_value(None) is None


def test_dependency_graph_uses_the_collaborator_directly():
    """#67 / #68 の facade callback を直接依存に置き換えたこと。"""
    analyzer = _analyzer()
    assert analyzer._condition_logic.constant_values is analyzer._constant_values
    assert analyzer._placeholder_algebra.constant_values is analyzer._constant_values
    assert not hasattr(analyzer._condition_logic, "constant_int_value")
    assert not hasattr(analyzer._placeholder_algebra, "constant_int_value")

"""ConditionLogicService collaborator（Phase 5 #4）の回帰テスト。"""

import inspect
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.condition_logic import ConditionLogicService
from scripts.function_tracer_pcode.analysis.returns.constant_values import ConstantValueService
from scripts.function_tracer_pcode.core.expression import Condition, Expression


def _analyzer():
    return ReturnAnalyzer(program=Mock(), debug=False)


def _service(**overrides):
    kwargs = dict(
        constant_values=Mock(spec=ConstantValueService),
        fold_constant_expression=lambda expr, **kw: expr,
    )
    kwargs.update(overrides)
    return ConditionLogicService(**kwargs)


def test_collaborator_holds_no_facade_state():
    service = _service()
    assert set(vars(service)) == {
        "constant_values",
        "fold_constant_expression",
    }


def test_every_delegator_forwards_to_the_collaborator():
    analyzer = _analyzer()
    names = [n for n, _ in inspect.getmembers(ConditionLogicService, predicate=inspect.isfunction) if n != "__init__"]
    assert len(names) == 36
    static = {"constant_expression_value", "expression_has_param"}
    for name in names:
        sentinel = object()
        facade = inspect.getattr_static(ReturnAnalyzer, "_" + name)
        assert isinstance(facade, staticmethod) == (name in static), name
        target = ConditionLogicService if name in static else analyzer._condition_logic
        with patch.object(target, name, return_value=sentinel) as mocked:
            sig = inspect.signature(getattr(ReturnAnalyzer, "_" + name))
            params = list(sig.parameters.values())
            if name not in static:
                params = params[1:]
            args, kwargs = [], {}
            for param in params:
                if param.kind is inspect.Parameter.KEYWORD_ONLY:
                    kwargs[param.name] = Mock()
                else:
                    args.append(Mock())
            assert getattr(analyzer, "_" + name)(*args, **kwargs) is sentinel
            mocked.assert_called_once_with(*args, **kwargs)


def test_static_helpers_are_callable_on_the_class_without_an_instance():
    expr = Expression.constant(5, 4)
    assert ReturnAnalyzer._constant_expression_value(expr) == 5
    assert ConditionLogicService.constant_expression_value(expr) == 5
    assert ReturnAnalyzer._expression_has_param(expr, "param_1") is False


def test_injected_helpers_dispatch_through_the_facade_at_call_time():
    """facade の class-level patch が collaborator 内の helper 呼び出しにも効くこと。"""
    analyzer = _analyzer()
    with patch.object(ReturnAnalyzer, "_fold_constant_expression", return_value="folded") as mocked:
        fallback = Expression.constant(9, 4)
        assert analyzer._condition_logic.fold_constant_expression(Mock(), fallback_expr=fallback) == "folded"
        mocked.assert_called_once()
        assert mocked.call_args.kwargs == {"fallback_expr": fallback}


def test_constant_int_value_is_a_direct_constant_values_dependency():
    """定数値抽出は facade を経由せず ConstantValueService を直接呼ぶ。"""
    analyzer = _analyzer()
    assert analyzer._condition_logic.constant_values is analyzer._constant_values
    p = Expression.variable("param_1", 4)
    zero = Expression.constant(0, 4)
    cond = Condition(Expression.binary_op("INT_SLESS", zero, p), True)
    with patch.object(analyzer._constant_values, "constant_int_value", wraps=analyzer._constant_values.constant_int_value) as direct, \
         patch.object(ReturnAnalyzer, "_constant_int_value", side_effect=AssertionError("facade must not be used")):
        analyzer._condition_logic.condition_is_signed_nonpositive_of_param(cond, p)
        direct.assert_called_once_with(zero)


def test_decompose_comparison_condition_is_the_pure_lifecycle_function():
    from scripts.function_tracer_pcode.analysis.returns import condition_logic, lifecycle
    assert condition_logic.decompose_comparison_condition is lifecycle.decompose_comparison_condition
    p = Expression.variable("param_1", 4)
    cond = Condition(Expression.binary_op("INT_SLESS", Expression.constant(0, 4), p), True)
    assert lifecycle.decompose_comparison_condition(cond) == ReturnAnalyzer._decompose_comparison_condition(_analyzer(), cond)


def test_conditions_imply_matches_facade_result():
    analyzer = _analyzer()
    p = Expression.variable("param_1", 4)
    zero = Expression.constant(0, 4)
    cond = Condition(Expression.binary_op("INT_EQUAL", p, zero), False)
    assert analyzer._conditions_imply([cond], [cond]) is True
    assert analyzer._condition_logic.conditions_imply([cond], [cond]) is True

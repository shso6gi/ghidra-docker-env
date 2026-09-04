"""PlaceholderAlgebraService collaborator（Phase 5 #5）の回帰テスト。"""

import inspect
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.condition_logic import ConditionLogicService
from scripts.function_tracer_pcode.analysis.returns.placeholder_algebra import PlaceholderAlgebraService
from scripts.function_tracer_pcode.core.expression import Condition, Expression


def _analyzer():
    return ReturnAnalyzer(program=Mock(), debug=False)


def test_collaborator_holds_only_its_dependencies():
    analyzer = _analyzer()
    service = analyzer._placeholder_algebra
    assert set(vars(service)) == {
        "condition_logic",
        "stack_protector",
        "current_parameters",
        "condition_identity_key",
        "branch_guarded_expression_is_param_minus_one",
    }
    assert service.condition_logic is analyzer._condition_logic
    assert isinstance(service.condition_logic, ConditionLogicService)
    assert service.stack_protector is analyzer._stack_protector


def test_every_delegator_forwards_to_the_collaborator():
    analyzer = _analyzer()
    names = [n for n, _ in inspect.getmembers(PlaceholderAlgebraService, predicate=inspect.isfunction) if n != "__init__"]
    assert len(names) == 18
    static = {"strip_transparent_unary"}
    for name in names:
        sentinel = object()
        facade = inspect.getattr_static(ReturnAnalyzer, "_" + name)
        assert isinstance(facade, staticmethod) == (name in static), name
        target = PlaceholderAlgebraService if name in static else analyzer._placeholder_algebra
        with patch.object(target, name, return_value=sentinel) as mocked:
            params = list(inspect.signature(getattr(ReturnAnalyzer, "_" + name)).parameters.values())
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


def test_condition_logic_is_a_direct_dependency_not_a_facade_callback():
    """条件論理 6 名称は facade を経由せず ConditionLogicService を直接呼ぶ。"""
    analyzer = _analyzer()
    p = Expression.variable("param_1", 4)
    q = Expression.variable("param_2", 4)
    expr = Expression.binary_op("INT_ADD", q, Expression.constant(0, 4))
    with patch.object(analyzer._condition_logic, "expressions_same_key", return_value=True) as direct, \
         patch.object(ReturnAnalyzer, "_expressions_same_key", side_effect=AssertionError("facade must not be used")):
        assert analyzer._placeholder_algebra.expression_is_placeholder_plus_zero_under_conditions(expr, p, ()) is True
        direct.assert_called_once_with(q, p)


def test_unextracted_helpers_dispatch_through_the_facade_at_call_time():
    analyzer = _analyzer()
    with patch.object(ReturnAnalyzer, "_condition_identity_key", return_value=("k",)) as mocked:
        assert analyzer._placeholder_algebra.condition_identity_key(Mock()) == ("k",)
        mocked.assert_called_once()
    with patch.object(ReturnAnalyzer, "_branch_guarded_expression_is_param_minus_one", return_value=True) as mocked:
        assert analyzer._placeholder_algebra.branch_guarded_expression_is_param_minus_one(Mock(), Mock(), Mock()) is True
        mocked.assert_called_once()


def test_current_parameters_supplier_reads_analyzer_state_at_call_time():
    """旧コードの getattr(self, "_current_parameters", ()) 読み取りが supplier 経由で保たれること。"""
    analyzer = _analyzer()
    analyzer._current_parameters = [{"name": "param_1", "size": 4}]
    assert analyzer._placeholder_algebra.current_parameters() is analyzer._current_parameters
    p = Expression.variable("param_1", 4)
    expected = Expression.binary_op("INT_ADD", p, Expression.constant(1, 4))
    with patch.object(analyzer._condition_logic, "expressions_equal_under_conditions_smt", return_value=False) as smt:
        analyzer._placeholder_algebra.expression_is_placeholder_plus_one_under_conditions(Mock(operator=None, operands=[]), p, ())
    assert smt.call_args.args[3] is analyzer._current_parameters


def test_constant_int_value_is_a_direct_stack_protector_dependency():
    analyzer = _analyzer()
    p = Expression.variable("param_1", 4)
    expr = Expression.binary_op("INT_SUB", p, Expression.constant(1, 4))
    with patch.object(analyzer._stack_protector, "constant_int_value", wraps=analyzer._stack_protector.constant_int_value) as direct, \
         patch.object(ReturnAnalyzer, "_constant_int_value", side_effect=AssertionError("facade must not be used")):
        assert analyzer._placeholder_algebra.expression_is_placeholder_minus_one(expr, p) is True
        direct.assert_called()


def test_static_helper_is_callable_on_the_class_without_an_instance():
    inner = Expression.constant(3, 4)
    wrapped = Expression.unary_op("COPY", inner)
    assert ReturnAnalyzer._strip_transparent_unary(wrapped) is PlaceholderAlgebraService.strip_transparent_unary(wrapped)


def test_placeholder_minus_one_matches_facade_result():
    analyzer = _analyzer()
    p = Expression.variable("param_1", 4)
    expr = Expression.binary_op("INT_SUB", p, Expression.constant(1, 4))
    assert analyzer._expression_is_placeholder_minus_one(expr, p) is True
    assert analyzer._placeholder_algebra.expression_is_placeholder_minus_one(expr, p) is True
    assert analyzer._expression_is_placeholder_minus_one(p, p) is False

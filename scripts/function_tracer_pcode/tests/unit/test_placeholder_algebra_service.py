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
        "session",
        "branch_guarded_expression_is_param_minus_one",
    }
    assert service.condition_logic is analyzer._condition_logic
    assert isinstance(service.condition_logic, ConditionLogicService)
    assert service.stack_protector is analyzer._stack_protector


def test_every_delegator_forwards_to_the_collaborator():
    analyzer = _analyzer()
    names = [n for n, _ in inspect.getmembers(PlaceholderAlgebraService, predicate=inspect.isfunction) if n != "__init__"]
    assert len(names) == 22
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
    with patch.object(ReturnAnalyzer, "_branch_guarded_expression_is_param_minus_one", return_value=True) as mocked:
        assert analyzer._placeholder_algebra.branch_guarded_expression_is_param_minus_one(Mock(), Mock(), Mock()) is True
        mocked.assert_called_once()


def test_current_parameters_supplier_reads_analyzer_state_at_call_time():
    """旧コードの getattr(self, "_current_parameters", ()) 読み取りが supplier 経由で保たれること。"""
    analyzer = _analyzer()
    analyzer._current_parameters = [{"name": "param_1", "size": 4}]
    assert analyzer._placeholder_algebra.session().parameters is analyzer._current_parameters
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


def test_condition_identity_key_is_the_pure_module_function_from_divergence_proofs():
    """#68 の facade callback condition_identity_key を純関数 import に置き換えたこと。"""
    from scripts.function_tracer_pcode.analysis.returns import divergence_proofs, placeholder_algebra
    analyzer = _analyzer()
    assert not hasattr(analyzer._placeholder_algebra, "condition_identity_key")
    assert placeholder_algebra.condition_identity_key is divergence_proofs.condition_identity_key
    p = Expression.variable("param_1", 4)
    cond = Condition(Expression.binary_op("INT_SLESS", Expression.constant(0, 4), p), True)
    assert divergence_proofs.condition_identity_key(cond) == ReturnAnalyzer._condition_identity_key(cond)
    assert divergence_proofs.condition_identity_key(cond) is not None


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


def _unnamable_condition():
    """厳密な identity を組めない条件。

    Ghidra 由来の object が値に入っていると `identity_complete` が偽になる。
    深さではなく **値の性質**なので、通常の入力で起きる。
    """
    from scripts.function_tracer_pcode.analysis.returns.proof_identity import (
        proof_condition_identity,
    )
    from scripts.function_tracer_pcode.core.expression import ExpressionType

    class _GhidraObject:
        def __repr__(self):
            return "<ghidra object>"

    opaque = Expression(ExpressionType.CONSTANT, value=_GhidraObject(), size=4)
    condition = Condition(Expression.binary_op("INT_LESS", opaque, Expression.constant(1, size=4)))
    assert proof_condition_identity(condition) is None
    return condition


def test_recognition_does_not_depend_on_whether_the_condition_can_be_named():
    """照合（recognition）が identity の可否に引きずられないこと。

    「この式が置換子 ± 単位条件の形か」は SMT 裏付けの照合で決まり、条件に
    どれだけ細かい名前を付けられるかとは無関係。一方、証明鍵に載せるには厳密な
    名前が要る（無ければ出さない）。

    1 つの関数で両方を返していたときは、名前を付けられない条件で **照合そのもの
    が失敗したことになり**、解析が別の式を組み立てていた（固定 subset の 1 pair
    で `node_count` が 44→36 に動いたのがこれ）。照合と命名を分けたので、照合は
    名前の可否に依らない。
    """
    analyzer = _analyzer()
    service = analyzer._placeholder_algebra
    condition = _unnamable_condition()
    flag = Expression.parameter("flag", 1, size=4)

    with patch.object(service, "expression_is_one_under_conditions", return_value=True):
        # 照合は成功する（名前を付けられなくても）
        assert service.unit_condition_for_expression(flag, [condition]) is condition
        # 証明鍵は出ない（fail-closed）
        assert service.unit_condition_key_for_expression(flag, [condition]) is None

    placeholder = Expression.parameter("p", 0, size=4)
    expr = Expression.binary_op("INT_ADD", placeholder, flag)
    with patch.object(service, "expression_is_one_under_conditions", return_value=True):
        with patch.object(service.condition_logic, "expressions_same_key",
                          side_effect=lambda left, right: left is placeholder):
            # 認識の gate は True のまま（以前はここが False に化けていた）
            assert service.expression_is_placeholder_plus_unit_condition(
                expr, placeholder, [condition]
            )
            assert service.placeholder_plus_unit_condition(expr, placeholder, [condition]) is condition
            # 証明鍵だけが出ない
            assert service.placeholder_plus_unit_condition_guard_key(
                expr, placeholder, [condition]
            ) is None


def test_a_namable_condition_still_produces_a_guard_key():
    """fail-closed が「常に鍵を出さない」へ退化していないこと。"""
    analyzer = _analyzer()
    service = analyzer._placeholder_algebra
    condition = Condition(
        Expression.binary_op(
            "INT_LESS", Expression.parameter("a", 0, size=4), Expression.constant(1, size=4)
        )
    )
    flag = Expression.parameter("flag", 1, size=4)
    with patch.object(service, "expression_is_one_under_conditions", return_value=True):
        assert service.unit_condition_for_expression(flag, [condition]) is condition
        assert service.unit_condition_key_for_expression(flag, [condition]) is not None

"""PhiOriginService collaborator（Phase 5 #7）の回帰テスト。"""

import ast
import inspect
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns import phi_origins as po_module
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.phi_origins import PhiOriginService
from scripts.function_tracer_pcode.core.expression import Condition, Expression, ExpressionType


def _analyzer(debug=False):
    return ReturnAnalyzer(program=Mock(), debug=debug)


def test_collaborator_holds_only_its_dependencies():
    analyzer = _analyzer()
    service = analyzer._phi_origins
    assert set(vars(service)) == {
        "condition_logic",
        "stack_protector",
        "pcode_sites",
        "return_normalization",
        "debug_reporter",
        "debug_flag",
    }
    assert service.condition_logic is analyzer._condition_logic
    assert service.stack_protector is analyzer._stack_protector
    assert service.pcode_sites is analyzer._pcode_sites
    assert service.return_normalization is analyzer._return_normalization


def test_every_delegator_forwards_to_the_collaborator():
    analyzer = _analyzer()
    names = [n for n, _ in inspect.getmembers(PhiOriginService, predicate=inspect.isfunction) if n != "__init__"]
    assert len(names) == 14
    for name in names:
        sentinel = object()
        assert not isinstance(inspect.getattr_static(ReturnAnalyzer, "_" + name), staticmethod), name
        with patch.object(analyzer._phi_origins, name, return_value=sentinel) as mocked:
            params = list(inspect.signature(getattr(ReturnAnalyzer, "_" + name)).parameters.values())[1:]
            args, kwargs = [], {}
            for param in params:
                if param.kind is inspect.Parameter.KEYWORD_ONLY:
                    kwargs[param.name] = Mock()
                else:
                    args.append(Mock())
            assert getattr(analyzer, "_" + name)(*args, **kwargs) is sentinel
            mocked.assert_called_once_with(*args, **kwargs)


def test_condition_logic_and_stack_protector_are_direct_dependencies():
    """collaborator 本体は conditions_are_unsat / constant_int_value を直接依存経由でのみ呼ぶ。"""
    tree = ast.parse(inspect.getsource(po_module))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "PhiOriginService")
    routed, direct_on_self = set(), set()
    for node in ast.walk(cls):
        if isinstance(node, ast.Attribute) and node.attr in {"conditions_are_unsat", "constant_int_value"}:
            base = node.value
            if isinstance(base, ast.Attribute) and isinstance(base.value, ast.Name) and base.value.id == "self":
                routed.add((base.attr, node.attr))
            elif isinstance(base, ast.Name) and base.id == "self":
                direct_on_self.add(node.attr)
    assert routed == {("condition_logic", "conditions_are_unsat"), ("stack_protector", "constant_int_value")}
    assert direct_on_self == set()
    # 実行時にも facade を経由しないこと
    analyzer = _analyzer()
    p = Expression.variable("param_1", 4)
    cond = Condition(Expression.binary_op("INT_EQUAL", p, Expression.constant(3, 4)), False)
    with patch.object(ReturnAnalyzer, "_conditions_are_unsat", side_effect=AssertionError("facade must not be used")), \
         patch.object(ReturnAnalyzer, "_constant_int_value", side_effect=AssertionError("facade must not be used")):
        analyzer._phi_origins.split_small_finite_parameter_reachability_conditions([cond])
        analyzer._phi_origins.parameter_equals_condition(p, 3)


def test_no_facade_callbacks_remain_after_lifecycle_split():
    """lifecycle 分割により debug_print も直接依存になり、facade 経由 callback は無い。"""
    analyzer = _analyzer()
    service = analyzer._phi_origins
    assert service.debug_reporter is analyzer._debug_reporter
    lambdas = {k for k, v in vars(service).items() if getattr(v, "__name__", "") == "<lambda>"}
    assert lambdas == {"debug_flag"}  # 残る lambda は supplier のみ


def test_pcode_op_stable_key_is_a_direct_pcode_sites_dependency():
    """#70 で facade callback だった pcode_op_stable_key を直接依存に置き換えたこと。"""
    analyzer = _analyzer()
    assert not hasattr(analyzer._phi_origins, "pcode_op_stable_key")
    tree = ast.parse(inspect.getsource(po_module))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "PhiOriginService")
    bases = set()
    for node in ast.walk(cls):
        if isinstance(node, ast.Attribute) and node.attr == "pcode_op_stable_key":
            base = node.value
            bases.add(base.attr if isinstance(base, ast.Attribute) else getattr(base, "id", None))
    assert bases == {"pcode_sites"}


def test_normalize_expanded_return_value_is_a_direct_return_normalization_dependency():
    """#71 まで facade callback だった normalize_expanded_return_value を直接依存に置き換えたこと。"""
    analyzer = _analyzer()
    assert not hasattr(analyzer._phi_origins, "normalize_expanded_return_value")
    tree = ast.parse(inspect.getsource(po_module))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "PhiOriginService")
    bases = set()
    for node in ast.walk(cls):
        if isinstance(node, ast.Attribute) and node.attr == "normalize_expanded_return_value":
            base = node.value
            bases.add(base.attr if isinstance(base, ast.Attribute) else getattr(base, "id", None))
    assert bases == {"return_normalization"}


def test_expression_contains_phi_is_a_pure_module_function():
    phi = Expression(ExpressionType.PHI, value=[(None, Expression.constant(1, 4))], size=4)
    assert po_module.expression_contains_phi(phi) is True
    assert po_module.expression_contains_phi(Expression.constant(1, 4)) is False
    assert po_module.expression_contains_phi(None) is False
    service = _analyzer()._phi_origins
    assert service.expression_contains_phi(phi) is po_module.expression_contains_phi(phi)


def test_debug_flag_supplier_reads_analyzer_state_at_call_time():
    analyzer = _analyzer(debug=False)
    assert analyzer._phi_origins.debug_flag() is False
    analyzer.debug = True
    assert analyzer._phi_origins.debug_flag() is True


def test_expression_contains_phi_matches_facade_result():
    analyzer = _analyzer()
    phi = Expression(ExpressionType.PHI, value=[(None, Expression.constant(1, 4))], size=4)
    wrapped = Expression.binary_op("INT_ADD", phi, Expression.constant(2, 4))
    assert analyzer._expression_contains_phi(wrapped) is True
    assert analyzer._phi_origins.expression_contains_phi(wrapped) is True
    assert analyzer._phi_origins.expression_contains_phi(Expression.constant(1, 4)) is False

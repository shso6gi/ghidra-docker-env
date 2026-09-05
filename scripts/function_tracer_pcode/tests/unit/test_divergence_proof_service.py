"""DivergenceProofService collaborator（Phase 5 #10）の回帰テスト。"""

import ast
import inspect
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns import divergence_proofs as dp_module
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.divergence_proofs import DivergenceProofService, condition_identity_key
from scripts.function_tracer_pcode.core.expression import Condition, Expression

DIRECT = {
    "condition_logic": {
        "condition_is_signed_positive_of_param", "expressions_same_key", "conditions_equivalent",
        "signed_positive_condition", "conditions_are_unsat", "condition_is_signed_nonpositive_of_param",
    },
    "placeholder_algebra": {"expression_is_placeholder_minus_one_under_conditions", "expression_is_one_under_conditions"},
    "stack_protector": {"constant_int_value"},
}
FACADE_CALLBACKS = ()
SUPPLIERS = ("program_value", "direct_call_graph_value", "direct_call_graph_complete_nodes_value")
STATIC = {"condition_identity_key", "field_value_from_structural_proof", "tuple_field_from_structural_proof"}


def _analyzer():
    return ReturnAnalyzer(program=Mock(), debug=False)


def test_collaborator_holds_only_its_dependencies():
    analyzer = _analyzer()
    service = analyzer._divergence_proofs
    assert set(vars(service)) == set(DIRECT) | set(FACADE_CALLBACKS) | set(SUPPLIERS) | {"debug_reporter", "program_access", "block_graph"}
    for attr in DIRECT:
        assert getattr(service, attr) is getattr(analyzer, "_" + attr)
    assert service.debug_reporter is analyzer._debug_reporter
    assert service.program_access is analyzer._program_access
    assert service.block_graph is analyzer._block_graph


def test_every_delegator_forwards_to_the_collaborator():
    analyzer = _analyzer()
    names = [n for n, _ in inspect.getmembers(DivergenceProofService, predicate=inspect.isfunction) if n != "__init__"]
    assert len(names) == 21
    for name in names:
        sentinel = object()
        facade = inspect.getattr_static(ReturnAnalyzer, "_" + name)
        assert isinstance(facade, staticmethod) == (name in STATIC), name
        assert not isinstance(facade, classmethod), name
        target = DivergenceProofService if name in STATIC else analyzer._divergence_proofs
        with patch.object(target, name, return_value=sentinel) as mocked:
            params = list(inspect.signature(getattr(ReturnAnalyzer, "_" + name)).parameters.values())
            if name not in STATIC:
                params = params[1:]
            args, kwargs = [], {}
            for param in params:
                if param.kind is inspect.Parameter.KEYWORD_ONLY:
                    kwargs[param.name] = Mock()
                else:
                    args.append(Mock())
            assert getattr(analyzer, "_" + name)(*args, **kwargs) is sentinel
            mocked.assert_called_once_with(*args, **kwargs)


def test_collaborator_owned_names_are_called_only_through_direct_dependencies():
    tree = ast.parse(inspect.getsource(dp_module))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "DivergenceProofService")
    owned = {name: dep for dep, names in DIRECT.items() for name in names}
    seen = {}
    for node in ast.walk(cls):
        if isinstance(node, ast.Attribute) and node.attr in owned:
            base = node.value
            assert isinstance(base, ast.Attribute) and isinstance(base.value, ast.Name) and base.value.id == "self", node.attr
            seen.setdefault(node.attr, set()).add(base.attr)
    assert set(seen) == set(owned)
    assert all(v == {owned[k]} for k, v in seen.items())


def test_condition_identity_key_is_one_pure_module_function():
    p = Expression.variable("param_1", 4)
    cond = Condition(Expression.binary_op("INT_EQUAL", p, Expression.constant(0, 4)), False)
    key = condition_identity_key(cond)
    assert key[0] == "condition" and key[2] is False
    assert DivergenceProofService.condition_identity_key(cond) == key
    assert ReturnAnalyzer._condition_identity_key(cond) == key
    assert condition_identity_key(Condition(cond.expression, True))[2] is True


def test_suppliers_read_analyzer_state_at_call_time():
    analyzer = _analyzer()
    service = analyzer._divergence_proofs
    assert service.program_value() is analyzer.program
    assert service.direct_call_graph_value() is analyzer._direct_call_graph
    assert service.direct_call_graph_complete_nodes_value() is analyzer._direct_call_graph_complete_nodes
    analyzer._direct_call_graph[("f",)] = {("g",)}
    assert service.direct_call_graph_value() == {("f",): {("g",)}}


def test_unextracted_helpers_dispatch_through_the_facade_at_call_time():
    """block 走査 helper が BlockGraphService 直接依存になり、facade 経由 callback は残っていない。"""
    analyzer = _analyzer()
    assert FACADE_CALLBACKS == ()
    lambdas = {k for k, v in vars(analyzer._divergence_proofs).items() if getattr(v, "__name__", "") == "<lambda>"}
    assert lambdas == set(SUPPLIERS)
    for attr in FACADE_CALLBACKS:
        sentinel = object()
        with patch.object(ReturnAnalyzer, "_" + attr, return_value=sentinel) as mocked:
            assert getattr(analyzer._divergence_proofs, attr)(Mock(), key=1) is sentinel
            mocked.assert_called_once()


def test_high_function_has_cfg_cycle_matches_facade_result():
    analyzer = _analyzer()
    hf = Mock()
    with patch.object(analyzer._block_graph, "iter_high_basic_blocks", return_value=[]):
        assert analyzer._high_function_has_cfg_cycle(hf) == analyzer._divergence_proofs.high_function_has_cfg_cycle(hf)

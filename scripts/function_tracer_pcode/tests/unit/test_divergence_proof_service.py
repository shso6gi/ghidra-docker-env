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
SUPPLIERS = ("program_value",)
STATIC = {"condition_identity_key", "field_value_from_structural_proof", "tuple_field_from_structural_proof"}


def _analyzer():
    return ReturnAnalyzer(program=Mock(), debug=False)


def test_collaborator_holds_only_its_dependencies():
    analyzer = _analyzer()
    service = analyzer._divergence_proofs
    assert set(vars(service)) == set(DIRECT) | set(FACADE_CALLBACKS) | set(SUPPLIERS) | {"debug_reporter", "program_access", "block_graph", "runtime_state"}
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
    # 鍵の中身の並びではなく契約を見る: 同じ 1 つの関数が答え、向きを区別し、
    # 組めない条件には鍵を与えない（`core/structural.condition_identity`）。
    assert key is not None
    assert DivergenceProofService.condition_identity_key(cond) == key
    assert ReturnAnalyzer._condition_identity_key(cond) == key
    negated = condition_identity_key(Condition(cond.expression, True))
    assert negated is not None and negated != key


def test_suppliers_read_analyzer_state_at_call_time():
    analyzer = _analyzer()
    service = analyzer._divergence_proofs
    assert service.program_value() is analyzer.program
    assert service.runtime_state is analyzer._runtime_state
    assert service.runtime_state.direct_call_graph is analyzer._direct_call_graph
    assert service.runtime_state.direct_call_graph_complete_nodes is analyzer._direct_call_graph_complete_nodes
    analyzer._direct_call_graph[("f",)] = {("g",)}
    assert service.runtime_state.direct_call_graph == {("f",): {("g",)}}


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


def test_conditional_progress_guard_key_survives_the_proof_it_is_stored_in():
    """guard key が structural proof に入れて読み戻しても使えること。

    **この proof の寿命は process 内**（`branch_guarded_structural_proof_from_return`
    で組み、同じ解析の中で `validate_…` と `…_from_structural_proof` が読む）。
    直列化されるのは `summary_candidate_source_key` の中の evidence としてだけで、
    JSON から読み戻して照合することは無い（tuple は list になるので、そもそも
    そういう契約ではない）。だから確かめるのは

    * 保存形式が plain data であること（= 直列化できる）
    * 同じ process 内で読み戻して、元の条件を引けること

    の 2 つ。読み手は tuple しか受けないので、鍵の側が plain data でなくなると
    黙って全部捨てられる（proof が必ず落ちる）。そこを固定しておく。
    """
    import json
    from unittest.mock import patch

    from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
    from scripts.function_tracer_pcode.core.expression import Expression

    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    service = analyzer._placeholder_algebra
    divergence = analyzer._divergence_proofs

    placeholder = Expression.parameter("p", 0, size=4)
    flag = Expression.parameter("flag", 1, size=4)
    expr = Expression.binary_op("INT_ADD", placeholder, flag)
    condition = Condition(
        Expression.binary_op(
            "INT_LESS", Expression.parameter("a", 0, size=4), Expression.constant(1, size=4)
        )
    )

    with patch.object(service, "expression_is_one_under_conditions", return_value=True), patch.object(
        service.condition_logic, "expressions_same_key", side_effect=lambda l, r: l is placeholder
    ):
        guard_key = service.placeholder_plus_unit_condition_guard_key(
            expr, placeholder, [condition]
        )

    assert guard_key is not None and isinstance(guard_key, tuple)

    proof = (
        "branch_guarded_affine_unit_count_structural_proof",
        ("conditional_progress_guard_keys", tuple(sorted({3: guard_key}.items(), key=repr))),
    )

    # evidence として直列化できる（wrapper object が混ざっていない）
    marker = "<not-plain-data>"
    assert marker not in json.dumps(proof, default=lambda o: marker)

    # 同じ process 内で読み戻して照合できる
    restored = divergence.conditional_progress_guard_keys_from_structural_proof(proof)
    assert restored == {3: guard_key}
    assert divergence.condition_for_identity_key(restored[3], [condition]) is condition

    # その鍵で validate が通る
    with patch.object(
        divergence, "condition_for_identity_key", return_value=condition
    ), patch(
        "scripts.function_tracer_pcode.analysis.returns.divergence_proofs.ConditionSMTOracle.conjunction_is_unsat",
        return_value=True,
    ):
        assert divergence.conditional_progress_guards_contradict_invariant(
            restored, target_conditions=(condition,), invariant_conditions=(condition,)
        ) is True



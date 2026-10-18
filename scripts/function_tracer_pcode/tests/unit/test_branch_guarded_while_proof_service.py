"""BranchGuardedWhileProofService collaborator（control_recovery 分割 2/n）の回帰テスト。"""

import ast
import inspect
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns import control_recovery as cr_module
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.control_recovery import BranchGuardedWhileProofService

DIRECT = ("condition_logic", "placeholder_algebra", "divergence_proofs", "block_graph", "constant_values",
          "debug_reporter", "expression_cases", "phi_origins", "program_access", "parameters", "pcode_sites",
          "return_paths")
NAMES = {
    "try_apply_branch_guarded_while_outcomes", "infer_branch_guarded_while_role_parameters",
    "prove_branch_guarded_structural_nonprogress_must_diverge", "branch_guarded_structural_proof_from_return",
    "find_branch_guarded_structural_proof_tuple", "validate_branch_guarded_structural_proof",
    "find_branch_guarded_while_return_partition", "synthesize_branch_guarded_affine_initial_count_return",
    "branch_guarded_artifact_is_imprecise_zero_seed", "branch_guarded_artifact_is_structural_accumulator_seed_projection",
    "prove_branch_guarded_affine_unit_count_recurrence", "branch_guarded_affine_ignored_artifacts_are_shadowed",
    "branch_guarded_affine_phi_step", "branch_guarded_affine_singleton_base_anchor_matches",
    "branch_guarded_expression_is_param_minus_one", "prove_branch_guarded_while_nonprogress_must_diverge",
}
FACADE_CALLBACKS = ("acc_phi_flows_to_return_origin_phi", "return_conditions_cover_region",
                    "return_info_candidate_phi_origin_keys", "return_info_return_phi_origin_keys",
                    "return_info_summary_identity_key", "return_site_key")
SUPPLIERS = ("debug_flag", "enable_completed_recovery_proofs_value", "program_value", "session")


def _analyzer():
    return ReturnAnalyzer(program=Mock(), debug=False)


def test_collaborator_holds_only_its_dependencies():
    analyzer = _analyzer()
    service = analyzer._branch_guarded_while
    assert set(vars(service)) == set(DIRECT) | set(FACADE_CALLBACKS) | set(SUPPLIERS)
    for attr in DIRECT:
        assert getattr(service, attr) is getattr(analyzer, "_" + attr), attr


def test_every_delegator_forwards_to_the_collaborator():
    analyzer = _analyzer()
    names = {n for n, _ in inspect.getmembers(BranchGuardedWhileProofService, predicate=inspect.isfunction)} - {"__init__"}
    assert names == NAMES  # #79 レビュー: 件数だけでなく名簿で固定
    for name in sorted(names):
        sentinel = object()
        assert not isinstance(inspect.getattr_static(ReturnAnalyzer, "_" + name), (staticmethod, classmethod)), name
        with patch.object(analyzer._branch_guarded_while, name, return_value=sentinel) as mocked:
            params = list(inspect.signature(getattr(ReturnAnalyzer, "_" + name)).parameters.values())[1:]
            args, kwargs = [], {}
            for param in params:
                if param.kind is inspect.Parameter.KEYWORD_ONLY:
                    kwargs[param.name] = Mock()
                else:
                    args.append(Mock())
            assert getattr(analyzer, "_" + name)(*args, **kwargs) is sentinel
            mocked.assert_called_once_with(*args, **kwargs)


def test_collaborator_owned_names_go_through_direct_dependencies_and_self_is_never_passed():
    tree = ast.parse(inspect.getsource(cr_module))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "BranchGuardedWhileProofService")
    own = {n.name for n in cls.body if isinstance(n, ast.FunctionDef)}
    for node in ast.walk(cls):
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and node.value.id == "self":
            assert node.attr in own | set(DIRECT) | set(FACADE_CALLBACKS) | set(SUPPLIERS), node.attr
            assert not node.attr.startswith("_"), node.attr
    assert not [n for n in ast.walk(cls) if isinstance(n, ast.Call)
                and any(isinstance(a, ast.Name) and a.id == "self" for a in list(n.args) + [k.value for k in n.keywords])]
    # 旧 module 関数 _current_cfg_applicability_surface は BlockGraphService へ移設され、module には残らない
    assert not hasattr(cr_module, "_current_cfg_applicability_surface")


def test_suppliers_read_analyzer_state_at_call_time():
    analyzer = _analyzer()
    service = analyzer._branch_guarded_while
    analyzer._current_parameters = [{"name": "param_1"}]
    assert service.session().parameters is analyzer._current_parameters
    assert service.program_value() is analyzer.program
    assert service.enable_completed_recovery_proofs_value() == analyzer.enable_completed_recovery_proofs
    analyzer.debug = True
    assert service.debug_flag() is True


def test_unextracted_helpers_dispatch_through_the_facade_at_call_time():
    analyzer = _analyzer()
    for attr in FACADE_CALLBACKS:
        sentinel = object()
        with patch.object(ReturnAnalyzer, "_" + attr, return_value=sentinel) as mocked:
            assert getattr(analyzer._branch_guarded_while, attr)(Mock(), key=1) is sentinel
            mocked.assert_called_once()


def test_placeholder_algebra_callback_still_reaches_the_collaborator_via_the_facade():
    """PlaceholderAlgebraService は生成順の都合で facade callback を保つが、facade delegator は本 collaborator へ届く。"""
    analyzer = _analyzer()
    with patch.object(analyzer._branch_guarded_while, "branch_guarded_expression_is_param_minus_one", return_value=True) as direct:
        assert analyzer._placeholder_algebra.branch_guarded_expression_is_param_minus_one(Mock(), Mock(), ()) is True
        direct.assert_called_once()

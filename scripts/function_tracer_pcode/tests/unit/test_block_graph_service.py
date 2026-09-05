"""BlockGraphService collaborator（control_recovery 分割 1/n: 純 block 走査 helper）の回帰テスト。"""

import ast
import inspect
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns import control_recovery as cr_module
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.control_recovery import BlockGraphService

NAMES = {
    "block_successors", "block_predecessor_count", "block_has_return_op", "block_writes_outcome_guard_state",
    "direct_cbranch_successor_relation", "block_start_address_keys", "block_start_address_spaces",
    "first_high_block_cbranch", "same_high_block", "block_debug_key", "block_reaches", "high_function_cbranch_count",
    "iter_high_basic_blocks", "iter_high_block_ops", "coerce_block_path_entries", "find_block_index_on_path",
    "blocks_match", "get_block_start_address", "cfg_applicability_surface",
}


def _analyzer():
    return ReturnAnalyzer(program=Mock(), debug=False)


def test_collaborator_holds_only_its_dependencies():
    analyzer = _analyzer()
    service = analyzer._block_graph
    assert set(vars(service)) == {"pcode_sites", "cbranch_direct_target_keys"}
    assert service.pcode_sites is analyzer._pcode_sites


def test_every_delegator_forwards_to_the_collaborator():
    analyzer = _analyzer()
    names = {n for n, _ in inspect.getmembers(BlockGraphService, predicate=inspect.isfunction)} - {"__init__"}
    assert names == NAMES
    for name in sorted(names - {"cfg_applicability_surface"}):  # 旧 module 関数の移設で facade delegator は無い
        sentinel = object()
        assert not isinstance(inspect.getattr_static(ReturnAnalyzer, "_" + name), (staticmethod, classmethod)), name
        with patch.object(analyzer._block_graph, name, return_value=sentinel) as mocked:
            params = list(inspect.signature(getattr(ReturnAnalyzer, "_" + name)).parameters.values())[1:]
            args, kwargs = [], {}
            for param in params:
                if param.kind is inspect.Parameter.KEYWORD_ONLY:
                    kwargs[param.name] = Mock()
                else:
                    args.append(Mock())
            assert getattr(analyzer, "_" + name)(*args, **kwargs) is sentinel
            mocked.assert_called_once_with(*args, **kwargs)


def test_collaborator_reads_no_facade_state_and_never_passes_itself():
    tree = ast.parse(inspect.getsource(cr_module))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "BlockGraphService")
    self_attrs = {n.attr for n in ast.walk(cls) if isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name) and n.value.id == "self"}
    assert self_attrs <= NAMES | {"pcode_sites", "cbranch_direct_target_keys"}
    assert not [n for n in ast.walk(cls) if isinstance(n, ast.Call)
                and any(isinstance(a, ast.Name) and a.id == "self" for a in list(n.args) + [k.value for k in n.keywords])]


def test_block_predecessor_count_and_successors_match_facade():
    analyzer = _analyzer()
    succ = [Mock(), Mock()]
    block = Mock()
    block.getOutSize.return_value = 2
    block.getOut.side_effect = lambda i: succ[i]
    block.getInSize.return_value = 3
    assert analyzer._block_successors(block) == analyzer._block_graph.block_successors(block)
    assert analyzer._block_predecessor_count(block) == analyzer._block_graph.block_predecessor_count(block)


def test_cbranch_direct_target_keys_dispatches_through_the_facade_at_call_time():
    analyzer = _analyzer()
    sentinel = object()
    with patch.object(ReturnAnalyzer, "_cbranch_direct_target_keys", return_value=sentinel) as mocked:
        assert analyzer._block_graph.cbranch_direct_target_keys(Mock(), Mock()) is sentinel
        mocked.assert_called_once()


def test_cfg_applicability_surface_is_built_from_the_block_graph_itself():
    analyzer = _analyzer()
    bg = analyzer._block_graph
    a, b = Mock(name="A"), Mock(name="B")
    with patch.object(bg, "iter_high_basic_blocks", return_value=[a, b]), \
         patch.object(bg, "block_debug_key", side_effect=lambda blk: blk._mock_name), \
         patch.object(bg, "block_successors", side_effect=lambda blk: [b] if blk is a else []):
        assert bg.cfg_applicability_surface(Mock()) == (("A", "B"), (("A", "B"),))


def test_direct_dependants_share_the_single_block_graph():
    analyzer = _analyzer()
    assert analyzer._divergence_proofs.block_graph is analyzer._block_graph
    assert not any(k in vars(analyzer._divergence_proofs) for k in NAMES)

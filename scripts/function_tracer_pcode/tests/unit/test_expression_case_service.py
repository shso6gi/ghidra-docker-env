"""ExpressionCaseService collaborator（Phase 5 #3）の回帰テスト。

主眼は class-level patch seam ``ReturnAnalyzer._contains_multiequal`` が
collaborator 抽出後も保持されることの確認。
"""

import ast
import inspect
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns import expression_cases as ec_module
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.expression_cases import ExpressionCaseService
from scripts.function_tracer_pcode.core.expression import Expression


def _analyzer():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    return analyzer


def _varnode_chain(mnemonics):
    """mnemonics[0] を def とする varnode を返す。各 def は 1 入力で次の varnode へ繋がる。"""
    vn = None
    for mnemonic in reversed(mnemonics):
        op = Mock()
        op.getMnemonic.return_value = mnemonic
        op.getNumInputs.return_value = 0 if vn is None else 1
        op.getInput.return_value = vn
        cur = Mock()
        cur.getDef.return_value = op
        vn = cur
    return vn


def test_contains_multiequal_class_level_patch_seam_is_preserved():
    analyzer = _analyzer()
    varnode = _varnode_chain(["INT_ADD", "MULTIEQUAL"])
    assert analyzer._contains_multiequal(varnode) is True
    with patch.object(ReturnAnalyzer, "_contains_multiequal", return_value=False):
        assert analyzer._contains_multiequal(varnode) is False
    with patch.object(ReturnAnalyzer, "_contains_multiequal", return_value=True):
        assert analyzer._contains_multiequal(_varnode_chain(["INT_ADD"])) is True
    # patch 解除後は collaborator の実装へ戻る
    assert analyzer._contains_multiequal(_varnode_chain(["INT_ADD"])) is False


def test_contains_multiequal_has_no_internal_caller_that_bypasses_the_seam():
    """collaborator 内で contains_multiequal を呼ぶのは自身の再帰だけであること。

    他のメソッドが collaborator 経由で呼ぶと facade の class-level patch を素通りするため、
    seam が保持できなくなる。これを静的に固定する。
    """
    tree = ast.parse(inspect.getsource(ec_module))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "ExpressionCaseService")
    callers = set()
    for fn in (n for n in cls.body if isinstance(n, ast.FunctionDef)):
        for node in ast.walk(fn):
            if (
                isinstance(node, ast.Attribute)
                and node.attr in {"contains_multiequal", "_contains_multiequal"}
            ):
                callers.add(fn.name)
    assert callers == {"contains_multiequal"}


def test_every_delegator_forwards_to_the_collaborator():
    """facade の各 delegator が同名 collaborator メソッドへ引数をそのまま転送すること。"""
    analyzer = _analyzer()
    names = [
        n for n, _ in inspect.getmembers(ExpressionCaseService, predicate=inspect.isfunction)
        if n != "__init__"
    ]
    assert len(names) == 25
    for name in names:
        sentinel = object()
        with patch.object(analyzer._expression_cases, name, return_value=sentinel) as mocked:
            sig = inspect.signature(getattr(ReturnAnalyzer, "_" + name))
            args, kwargs = [], {}
            for param in list(sig.parameters.values())[1:]:
                if param.kind is inspect.Parameter.KEYWORD_ONLY:
                    kwargs[param.name] = Mock()
                else:
                    args.append(Mock())
            assert getattr(analyzer, "_" + name)(*args, **kwargs) is sentinel
            mocked.assert_called_once_with(*args, **kwargs)


def test_current_parameters_supplier_reads_analyzer_state_at_call_time():
    seen = []

    class _Probe(ExpressionCaseService):
        def snapshot(self):
            seen.append(list(self._current_parameters()))

    holder = {"params": [{"name": "a"}]}
    service = _Probe(current_parameters=lambda: holder["params"])
    service.snapshot()
    holder["params"] = [{"name": "b"}]
    service.snapshot()
    assert seen == [[{"name": "a"}], [{"name": "b"}]]


def test_analyzer_current_parameters_are_visible_through_the_collaborator():
    analyzer = _analyzer()
    analyzer._current_parameters = [{"name": "param_1", "size": 4}]
    assert analyzer._expression_cases._current_parameters() is analyzer._current_parameters


def test_clone_expression_delegator_matches_module_function():
    analyzer = _analyzer()
    expr = Expression.binary_op("INT_ADD", Expression.constant(1, 4), Expression.constant(2, 4))
    cloned = analyzer._clone_expression(expr)
    assert cloned is not expr
    assert cloned.to_string() == expr.to_string()
    assert cloned.to_string() == ec_module.clone_expression(expr).to_string()

"""DebugReporter collaborator（lifecycle 分割 1/3）の回帰テスト。"""

import inspect
from unittest.mock import Mock, patch

from scripts.function_tracer_pcode.analysis.returns import lifecycle
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.debug_reporter import DebugReporter
from scripts.function_tracer_pcode.core.expression import Expression


def _analyzer(debug=False):
    return ReturnAnalyzer(program=Mock(), debug=debug)


def test_reporter_holds_only_the_debug_flag_supplier():
    analyzer = _analyzer()
    assert set(vars(analyzer._debug_reporter)) == {"debug_flag"}
    assert analyzer._debug_reporter.debug_flag() is False
    analyzer.debug = True
    assert analyzer._debug_reporter.debug_flag() is True


def test_every_delegator_forwards_to_the_reporter():
    analyzer = _analyzer()
    names = [n for n, _ in inspect.getmembers(DebugReporter, predicate=inspect.isfunction) if n != "__init__"]
    assert set(names) == {
        "debug_available",
        "debug_print",
        "debug_expr_summary",
        "debug_expr_identity_summary",
    }
    for name in names:
        sentinel = object()
        with patch.object(analyzer._debug_reporter, name, return_value=sentinel) as mocked:
            params = list(inspect.signature(getattr(ReturnAnalyzer, "_" + name)).parameters.values())[1:]
            args = [Mock() for _ in params]
            assert getattr(analyzer, "_" + name)(*args) is sentinel
            mocked.assert_called_once_with(*args)


def test_debug_print_respects_the_flag_at_call_time(capsys):
    analyzer = _analyzer(debug=False)
    analyzer._debug_print("hidden")
    analyzer.debug = True
    analyzer._debug_print("shown", indent=1)
    out = capsys.readouterr().out
    assert "hidden" not in out and "  [ReturnAnalyzer] shown" in out


def test_debug_expr_identity_summary_discriminates_a_real_expression():
    """#76 レビュー指摘: debug 行が式を識別できる情報を持ち続けること。

    旧実装では ``expression_key_safe`` の import 漏れが try/except に握り潰され、
    ``structural=None`` が出続けても compileall / import / unit / subset のどれにも
    現れなかった。今の debug 行は判定用の structural key を作らない（走査量が
    node 予算だけでは抑えられないため）ので、代わりに有界 preview が構造を
    名乗っていること、および**構造の違う式が違う行になる**ことを固定する。
    """
    analyzer = _analyzer()
    expr = Expression.binary_op("INT_ADD", Expression.variable("param_1", 4), Expression.constant(2, 4))

    text = analyzer._debug_expr_identity_summary(expr)

    assert "structural_preview=[BINARY_OP:INT_ADD:size=4," in text
    assert "VARIABLE:param_1:size=4" in text
    assert "CONSTANT:size=4:value=2" in text
    assert "<unavailable>" not in text and "structural_preview=[]" not in text

    other = Expression.binary_op("INT_SUB", Expression.variable("param_1", 4), Expression.constant(2, 4))
    assert analyzer._debug_expr_identity_summary(other) != text
    assert analyzer._debug_expr_identity_summary(None) == "None"


def test_every_collaborator_shares_the_single_reporter():
    analyzer = _analyzer()
    holders = [
        v for v in vars(analyzer).values()
        if type(v).__module__.startswith("scripts.function_tracer_pcode.analysis.returns.") and "debug_reporter" in vars(v)
    ]
    assert len(holders) >= 6
    assert all(h.debug_reporter is analyzer._debug_reporter for h in holders)
    assert not any("debug_print" in vars(h) for h in holders)


def test_no_collaborator_local_shadows_an_imported_module_function():
    """`x = x(...)` 形の shadowing（UnboundLocalError）を returns package 全体で禁止する。

    対象は Assign / AnnAssign / AugAssign の直接ターゲットのみ（for / with ... as / except ... as /
    walrus は対象外）。今回の回帰の再発防止に必要十分な範囲に限定している。

    lifecycle の純関数 function_cache_key を import した effect_integration で、同名のローカル変数が
    import を隠して実行時に UnboundLocalError になる欠陥を検出したことに由来する回帰ガード。
    """
    import ast
    import glob
    import os
    pkg = os.path.dirname(inspect.getsourcefile(lifecycle))
    offenders = []
    for path in sorted(glob.glob(os.path.join(pkg, "*.py"))):
        tree = ast.parse(open(path).read())
        imported = {a.asname or a.name for n in tree.body if isinstance(n, ast.ImportFrom) for a in n.names}
        for fn in (n for n in ast.walk(tree) if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))):
            def _direct_targets(node):
                targets = [node.target] if hasattr(node, "target") else list(node.targets)
                out = []
                for t in targets:
                    if isinstance(t, ast.Name):
                        out.append(t.id)
                    elif isinstance(t, (ast.Tuple, ast.List)):
                        out.extend(e.id for e in t.elts if isinstance(e, ast.Name))
                return out  # Attribute / Subscript への代入（x.attr = ...）は名前を束縛しない
            assigned = {name for n in ast.walk(fn) if isinstance(n, (ast.Assign, ast.AnnAssign, ast.AugAssign))
                        for name in _direct_targets(n)}
            params = {a.arg for a in fn.args.args + fn.args.kwonlyargs}
            for name in (assigned - params) & imported:
                offenders.append((os.path.basename(path), fn.name, name))
    assert offenders == []


def test_promoted_pure_helpers_are_module_functions_shared_by_facade():
    fn = Mock()
    fn.getEntryPoint.return_value = "0x1000"
    assert lifecycle.function_cache_key(fn) == ("0x1000",) == ReturnAnalyzer._function_cache_key(_analyzer(), fn)
    assert lifecycle.function_cache_key(None) is None
    assert lifecycle.function_entry_address(fn) == ReturnAnalyzer._function_entry_address(fn)
    assert lifecycle.collect_java_or_python_iterable([1, 2]) == ReturnAnalyzer._collect_java_or_python_iterable([1, 2])
    assert lifecycle.collect_java_or_python_iterable(None) == ReturnAnalyzer._collect_java_or_python_iterable(None)

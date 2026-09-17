# -*- coding: utf-8 -*-
"""debug 出力のための eager rendering を静的に禁止する guard（Issue #22 PR-22-A）。

`Expression.to_string()` / `to_smt()` / `repr()` は DAG を木として展開するので、
巨大式では debug の有無に関わらず解析時間を食う。debug message のために
これらを呼ぶと、``--debug`` を付けていなくても引数が先に評価される（helper が
関数の中で flag を見ても遅い）。本 test は AST 走査でその形を 0 件に固定する。

固定する 4 つの契約:

* **R1** debug guard の中で `to_string()` / `to_smt()` / `repr()` / `getattr(x, "to_string")()`
  を呼ばない。guard の中は debug 専用なので、そこにある full render は
  「debug のためだけに式を展開している」ことを意味する。
* **R2** debug sink（`print` と名前に ``debug`` を含む呼び出し）の引数に
  full render を含めない。guard の有無に関わらず禁止（debug ON でも展開しない）。
* **R3** debug sink の引数で bounded summary（``summarize_expression`` 等）を
  使うときは debug guard の中で行う。summary は有界だが、message の f-string
  組み立て自体を debug OFF 時に走らせないため。
* **R4** ``__repr__`` / ``__str__`` が full render を呼ばない。``repr()`` は
  logging・例外・デバッガから暗黙に呼ばれるので、full render を持つと
  「debug OFF なら安全」が成立しない。

debug guard の判定は「test に ``debug`` を含む名前が出てくる ``if``」という
構文的な近似で、コメントや変数の意味からは推定しない。早期 return 型の
guard 節（``if not self.debug: return``）も guard として扱う。
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from typing import FrozenSet, Iterator, List, Sequence, Tuple

import pytest

from scripts.function_tracer_pcode.analysis.debug import render as debug_render
from scripts.function_tracer_pcode.analysis.phi_resolver import ExpandedBranch
from scripts.function_tracer_pcode.analysis.recurrence import counted_loop
from scripts.function_tracer_pcode.analysis.recurrence.models import StateTransitionLoopModel
from scripts.function_tracer_pcode.analysis.recurrence.summarizer import (
    StructuralRecurrenceSummarizer,
)
from scripts.function_tracer_pcode.core.analysis import ReturnInfo
from scripts.function_tracer_pcode.core.condition import Condition
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.semantics.transform.expander_support import ExpandedValue
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis
from scripts.function_tracer_pcode.tests.unit._recurrence_fixtures import (
    _FakeFunction,
    _FakeTracer,
    _build_branch_while_state_cfg,
    _cond,
    _const,
    _param,
)


PACKAGE_ROOT = Path(__file__).resolve().parents[2]

#: 走査しない package 直下のディレクトリ（テスト自身は対象外）。
EXCLUDED_TOP_LEVEL_DIRS = frozenset({"tests"})

# 契約の語彙は production 側の owner（analysis.debug.render）が持つ。ここで
# 名前を再定義すると二重管理になり、新しい renderer を足すたびに test も直す
# ことになるので、import して使う。
#
#: DAG を木として展開する rendering method。
RENDER_METHODS = debug_render.UNBOUNDED_RENDER_CALLS

#: owner が所有する bounded renderer。family 側の wrapper はここへ委譲するだけ
#: なので列挙しない（:func:`bounded_renderer_names` が委譲を辿って足す）。
OWNED_SUMMARY_FUNCTIONS = debug_render.BOUNDED_DEBUG_RENDERERS

#: 名前に ``debug`` を含むが sink ではない述語（呼んでも何も出力しない）。
DEBUG_PREDICATES = debug_render.DEBUG_AVAILABILITY_PREDICATES

#: full render を持ってはいけない dunder。
RENDER_FREE_DUNDERS = frozenset({"__repr__", "__str__"})


@dataclass
class EagerDebugRenderingViolations:
    """4 契約それぞれの違反。すべて空なら PASS。"""

    render_in_debug_guard: List[Tuple[str, int, str]] = field(default_factory=list)
    render_in_debug_sink: List[Tuple[str, int, str]] = field(default_factory=list)
    unguarded_summary_in_debug_sink: List[Tuple[str, int, str]] = field(default_factory=list)
    render_in_dunder: List[Tuple[str, int, str]] = field(default_factory=list)

    def __bool__(self) -> bool:
        return bool(
            self.render_in_debug_guard
            or self.render_in_debug_sink
            or self.unguarded_summary_in_debug_sink
            or self.render_in_dunder
        )

    def describe(self) -> str:
        lines: List[str] = []
        for module, lineno, detail in self.render_in_debug_guard:
            lines.append(
                f"R1 {module}:{lineno}: {detail} runs inside a debug guard; "
                "use summarize_expression()/summarize_conditions() instead"
            )
        for module, lineno, detail in self.render_in_debug_sink:
            lines.append(
                f"R2 {module}:{lineno}: {detail} is evaluated to build a debug message; "
                "use summarize_expression()/summarize_conditions() instead"
            )
        for module, lineno, detail in self.unguarded_summary_in_debug_sink:
            lines.append(
                f"R3 {module}:{lineno}: {detail} builds a debug message outside a debug guard; "
                "wrap the call site in `if <debug available>:`"
            )
        for module, lineno, detail in self.render_in_dunder:
            lines.append(
                f"R4 {module}:{lineno}: {detail} is reachable from repr()/str(); "
                "use summarize_expression(max_depth=4) instead"
            )
        return "\n".join(lines)


def _called_name(node: ast.Call) -> str:
    func = node.func
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        return func.attr
    return ""


def _render_call_label(node: ast.AST) -> str:
    """`node` が full render の呼び出しならその名前、そうでなければ空文字。"""

    if not isinstance(node, ast.Call):
        return ""
    func = node.func
    if isinstance(func, ast.Attribute) and func.attr in RENDER_METHODS:
        return f"{func.attr}()"
    if isinstance(func, ast.Name) and func.id == "repr":
        return "repr()"
    # `getattr(expr, "to_string", ...)()`: 呼び出し対象が getattr でも full render。
    if isinstance(func, ast.Call) and _called_name(func) == "getattr":
        arguments = func.args
        if len(arguments) >= 2 and isinstance(arguments[1], ast.Constant):
            attribute = arguments[1].value
            if isinstance(attribute, str) and attribute in RENDER_METHODS:
                return f'getattr(..., "{attribute}")()'
    return ""


def _summary_call_label(node: ast.AST, renderers: FrozenSet[str]) -> str:
    if isinstance(node, ast.Call) and _called_name(node) in renderers:
        return f"{_called_name(node)}()"
    return ""


def _is_debug_sink(node: ast.Call, renderers: FrozenSet[str]) -> bool:
    name = _called_name(node)
    if not name or name in renderers or name in DEBUG_PREDICATES:
        return False
    return name == "print" or "debug" in name.lower()


def _delegates_to_a_bounded_renderer(
    node: ast.FunctionDef | ast.AsyncFunctionDef,
    known: FrozenSet[str],
) -> bool:
    """`node` が既知の bounded renderer へ **委譲するだけ** の wrapper か。

    family 側の ``_debug_expr_summary`` などを名前で数え上げずに拾うための規則。
    委譲だけ = (a) 呼び出しは既知 renderer か debug 述語しか無い、(b) 返り値は
    定数文字列か既知 renderer の呼び出しだけ、(c) 入れ子の関数定義が無い。
    ここから外れる helper（自分で走査するもの）は renderer と見なさないので、
    その呼び出しは「guard が要る任意の呼び出し」として扱われる。
    """

    returns: List[ast.AST] = []
    for sub in ast.walk(node):
        if sub is not node and isinstance(
            sub, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
        ):
            return False
        if isinstance(sub, ast.Return):
            returns.append(sub.value)
        elif isinstance(sub, ast.Call):
            name = _called_name(sub)
            if name not in known and name not in DEBUG_PREDICATES:
                return False
    delegations = [
        value
        for value in returns
        if isinstance(value, ast.Call) and _called_name(value) in known
    ]
    if not delegations:
        # 定数しか返さない関数は renderer ではない（委譲が 1 つも無い）。
        return False
    for value in returns:
        if isinstance(value, ast.Constant) and isinstance(value.value, str):
            continue  # `return "<debug-suppressed>"` のような guard 節の戻り値
        if value in delegations:
            continue
        return False
    return True


@lru_cache(maxsize=None)
def bounded_renderer_names(root: Path = PACKAGE_ROOT) -> FrozenSet[str]:
    """owner の宣言 + そこへ委譲する family wrapper の名前を返す。

    owner（``analysis.debug.render``）が宣言した名前を種にして、委譲するだけの
    wrapper を不動点まで足す。新しい bounded renderer を足すときに触るのは
    owner だけでよく、この test も家族側の module も変えなくてよい。
    """

    definitions = [
        node
        for path in _iter_source_files(Path(root))
        for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"), filename=str(path)))
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    ]
    known = set(OWNED_SUMMARY_FUNCTIONS)
    while True:
        discovered = {
            node.name
            for node in definitions
            if node.name not in known
            and _delegates_to_a_bounded_renderer(node, frozenset(known))
        }
        if not discovered:
            return frozenset(known)
        known |= discovered


def _mentions_debug(node: ast.AST) -> bool:
    for sub in ast.walk(node):
        if isinstance(sub, ast.Name) and "debug" in sub.id.lower():
            return True
        if isinstance(sub, ast.Attribute) and "debug" in sub.attr.lower():
            return True
    return False


def _is_negated(test: ast.AST) -> bool:
    return isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not)


def _always_exits(body: Sequence[ast.stmt]) -> bool:
    return bool(body) and isinstance(body[-1], (ast.Return, ast.Raise, ast.Continue, ast.Break))


class _EagerDebugRenderingScanner:
    """1 module 分の AST を走査して 4 契約の違反を集める。"""

    def __init__(
        self,
        module: str,
        violations: EagerDebugRenderingViolations,
        renderers: FrozenSet[str] = OWNED_SUMMARY_FUNCTIONS,
    ) -> None:
        self.module = module
        self.violations = violations
        self.renderers = renderers

    # -- entry ---------------------------------------------------------------
    def scan(self, tree: ast.Module) -> None:
        self._walk_body(tree.body, guarded=False)
        self._scan_dunders(tree)

    # -- R4 ------------------------------------------------------------------
    def _scan_dunders(self, tree: ast.Module) -> None:
        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            if node.name not in RENDER_FREE_DUNDERS:
                continue
            for sub in ast.walk(node):
                label = _render_call_label(sub)
                if label:
                    self.violations.render_in_dunder.append(
                        (self.module, sub.lineno, f"{node.name} calls {label}")
                    )

    # -- statement walk ------------------------------------------------------
    def _walk_body(self, body: Sequence[ast.stmt], *, guarded: bool) -> None:
        for statement in body:
            if isinstance(statement, ast.If) and _mentions_debug(statement.test):
                self._visit_expression(statement.test, guarded=guarded)
                if _is_negated(statement.test):
                    # `if not <debug>: return` 型の guard 節。以降は debug 専用。
                    self._walk_body(statement.body, guarded=False)
                    self._walk_body(statement.orelse, guarded=True)
                    if not statement.orelse and _always_exits(statement.body):
                        guarded = True
                else:
                    self._walk_body(statement.body, guarded=True)
                    self._walk_body(statement.orelse, guarded=guarded)
                continue
            self._walk_statement(statement, guarded=guarded)

    def _walk_statement(self, statement: ast.stmt, *, guarded: bool) -> None:
        if isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef)):
            # 別の呼び出し文脈で実行されるので guard を引き継がない。
            for decorator in statement.decorator_list:
                self._visit_expression(decorator, guarded=guarded)
            self._walk_body(statement.body, guarded=False)
            return
        if isinstance(statement, ast.ClassDef):
            self._walk_body(statement.body, guarded=False)
            return
        for name, value in ast.iter_fields(statement):
            if name in {"body", "orelse", "finalbody"}:
                self._walk_body(value, guarded=guarded)
                continue
            if name == "handlers":
                for handler in value:
                    self._walk_body(handler.body, guarded=guarded)
                continue
            if isinstance(value, list):
                for item in value:
                    if isinstance(item, ast.stmt):
                        self._walk_statement(item, guarded=guarded)
                    elif isinstance(item, ast.AST):
                        self._visit_expression(item, guarded=guarded)
            elif isinstance(value, ast.AST):
                if isinstance(value, ast.stmt):
                    self._walk_statement(value, guarded=guarded)
                else:
                    self._visit_expression(value, guarded=guarded)

    # -- expression walk -----------------------------------------------------
    def _visit_expression(self, node: ast.AST, *, guarded: bool) -> None:
        for sub in ast.walk(node):
            if isinstance(sub, ast.Lambda):
                continue
            label = _render_call_label(sub)
            if label and guarded:
                self.violations.render_in_debug_guard.append((self.module, sub.lineno, label))
            if not isinstance(sub, ast.Call) or not _is_debug_sink(sub, self.renderers):
                continue
            arguments: List[ast.AST] = list(sub.args) + [kw.value for kw in sub.keywords]
            for argument in arguments:
                for inner in ast.walk(argument):
                    render = _render_call_label(inner)
                    if render:
                        self.violations.render_in_debug_sink.append(
                            (self.module, sub.lineno, f"{_called_name(sub)}(... {render} ...)")
                        )
                    summary = _summary_call_label(inner, self.renderers)
                    if summary and not guarded:
                        self.violations.unguarded_summary_in_debug_sink.append(
                            (self.module, sub.lineno, f"{_called_name(sub)}(... {summary} ...)")
                        )


def scan_source(
    module: str,
    source: str,
    renderers: FrozenSet[str] = OWNED_SUMMARY_FUNCTIONS,
) -> EagerDebugRenderingViolations:
    """1 module 分のソース文字列を走査する（self-test 用の入口でもある）。"""

    violations = EagerDebugRenderingViolations()
    _EagerDebugRenderingScanner(module, violations, renderers).scan(
        ast.parse(source, filename=module)
    )
    return violations


def _iter_source_files(root: Path) -> Iterator[Path]:
    for path in sorted(root.rglob("*.py")):
        if path.relative_to(root).parts[0] in EXCLUDED_TOP_LEVEL_DIRS:
            continue
        yield path


def _module_name(root: Path, path: Path) -> str:
    parts = list(path.relative_to(root).parts)
    if parts[-1] == "__init__.py":
        parts.pop()
    else:
        parts[-1] = parts[-1][: -len(".py")]
    return ".".join(parts)


def scan_package(root: Path = PACKAGE_ROOT) -> EagerDebugRenderingViolations:
    renderers = bounded_renderer_names(root)
    violations = EagerDebugRenderingViolations()
    for path in _iter_source_files(Path(root)):
        module = _module_name(Path(root), path)
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        _EagerDebugRenderingScanner(module, violations, renderers).scan(tree)
    return violations


# --------------------------------------------------------------------- 契約


def test_no_full_render_inside_debug_guards():
    violations = scan_package()
    assert not violations.render_in_debug_guard, violations.describe()


def test_no_full_render_in_debug_sink_arguments():
    violations = scan_package()
    assert not violations.render_in_debug_sink, violations.describe()


def test_debug_messages_with_summaries_are_guarded():
    violations = scan_package()
    assert not violations.unguarded_summary_in_debug_sink, violations.describe()


def test_repr_and_str_do_not_full_render():
    violations = scan_package()
    assert not violations.render_in_dunder, violations.describe()


# --------------------------------------------- 契約 owner と wrapper の導出


def test_owned_renderer_names_exist_in_the_owner_module():
    """宣言した名前が owner module に実在すること（宣言と実装のずれを防ぐ）。"""

    for name in OWNED_SUMMARY_FUNCTIONS:
        assert callable(getattr(debug_render, name, None)), name


def test_family_wrappers_are_derived_from_the_owner_contract():
    """family の wrapper は名前を並べずに委譲から導かれる。

    ここが壊れると、wrapper 経由の debug message が guard 無しで書かれても
    R3 が気付かなくなる。
    """

    derived = bounded_renderer_names()

    assert OWNED_SUMMARY_FUNCTIONS <= derived
    assert {
        "_debug_expr_summary",
        "_debug_condition_summary",
        "debug_expr_summary",
        "debug_expr_identity_summary",
        "_debug_expr_identity_summary",
    } <= derived
    # 定数しか返さない関数は renderer ではない。
    assert "reason_id" not in derived


def test_a_new_owner_renderer_needs_no_change_here():
    """owner に renderer を 1 つ足すだけで、wrapper も呼び出し側も追随する。"""

    renderers = OWNED_SUMMARY_FUNCTIONS | {"summarize_widget"}
    violations = scan_source(
        "sample",
        "def f(self, widget):\n"
        "    self._debug_print(f'w={summarize_widget(widget)}')\n",
        renderers,
    )
    assert [entry[2] for entry in violations.unguarded_summary_in_debug_sink] == [
        "_debug_print(... summarize_widget() ...)"
    ]


def test_scanner_treats_a_delegating_wrapper_as_a_bounded_renderer():
    source = (
        "class Host:\n"
        "    def _debug_widget_summary(self, widget):\n"
        "        if not self._debug_available():\n"
        "            return '<debug-suppressed>'\n"
        "        return summarize_widget(widget)\n"
        "    def _reason(self):\n"
        "        return 'constant'\n"
    )
    tree = ast.parse(source)
    known = frozenset({"summarize_widget"})
    wrappers = {
        node.name
        for node in ast.walk(tree)
        if isinstance(node, ast.FunctionDef)
        and _delegates_to_a_bounded_renderer(node, known)
    }
    assert wrappers == {"_debug_widget_summary"}


# ------------------------------------------------------------- scanner 自体


def test_scanner_detects_render_inside_a_debug_guard():
    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    if self.debug:\n"
        "        rendered = expr.to_string()\n"
        "        self._debug_print(rendered)\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_guard] == ["to_string()"]


def test_scanner_detects_render_in_sink_arguments_without_a_guard():
    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    self._debug_print(f'value={expr.to_string()}')\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_sink] == [
        "_debug_print(... to_string() ...)"
    ]


def test_scanner_detects_render_behind_getattr():
    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    self._debug_print(f\"{getattr(expr, 'to_string', lambda: expr)()}\")\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_sink] == [
        '_debug_print(... getattr(..., "to_string")() ...)'
    ]


def test_scanner_detects_unguarded_summary_in_a_debug_message():
    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    self._debug_print(f'value={summarize_expression(expr)}')\n",
    )
    assert [entry[2] for entry in violations.unguarded_summary_in_debug_sink] == [
        "_debug_print(... summarize_expression() ...)"
    ]


def test_scanner_accepts_a_guarded_summary_message():
    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    if self._debug_available():\n"
        "        self._debug_print(f'value={summarize_expression(expr)}')\n",
    )
    assert not violations, violations.describe()


def test_scanner_accepts_an_early_return_debug_guard():
    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    if not self._debug_available():\n"
        "        return\n"
        "    self._debug_print(f'value={summarize_expression(expr)}')\n",
    )
    assert not violations, violations.describe()


def test_scanner_detects_full_render_in_repr():
    violations = scan_source(
        "sample",
        "class Sample:\n"
        "    def __repr__(self):\n"
        "        return self.value.to_string()\n",
    )
    assert [entry[2] for entry in violations.render_in_dunder] == ["__repr__ calls to_string()"]


def test_scanner_ignores_non_debug_rendering():
    violations = scan_source(
        "sample",
        "def render(expr):\n"
        "    return expr.to_string()\n",
    )
    assert not violations, violations.describe()


# ----------------------------------------------------- 実行時（AC A3）: boom


def _boom(*args, **kwargs):
    raise AssertionError("full rendering must not run during analysis")


def _summarize_branch_while_state(debug: bool):
    analysis = create_mock_analysis(
        "branch_while_state",
        return_type="int",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}
        ],
        returns=[
            ReturnInfo(address="0x1000", value=_const(0), conditions=[]),
            ReturnInfo(
                address="0x1004",
                value=Expression.binary_op("INT_ADD", Expression.unknown("phi_circular"), _const(1)),
                conditions=[_cond("INT_SLESS", _const(0), _param("param_1"))],
            ),
        ],
    )
    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=debug)
    return summarizer.try_summarize_function(
        _FakeFunction("branch_while_state"),
        _build_branch_while_state_cfg(),
        analysis,
    )


def _state_transition_model():
    """state guard が signed-positive でない（= 要約を断る）loop model。"""

    state = Expression.variable("__loop_state", size=4)
    accumulator = Expression.variable("__loop_acc", size=4)
    return StateTransitionLoopModel(
        None, None, None, None, None, _const(0), state,
        Expression.binary_op("INT_SLESS", state, _param()),
        Expression.binary_op("INT_ADD", state, _const(1)),
        None, None, _const(0),
        Expression.binary_op("INT_ADD", state, _const(1)),
        accumulator, True, (),
    )


@pytest.mark.parametrize("debug", [False, True], ids=["debug-off", "debug-on"])
def test_declined_recurrence_summary_does_not_render(monkeypatch, debug):
    """要約を断る経路の debug message が full render を経由しない（AC A3）。

    ここは本 PR の前は guard の無い ``self._debug(f"...{expr.to_string()}")``
    だったので、debug OFF でも引数が評価されていた。
    """

    summarizer = StructuralRecurrenceSummarizer(_FakeTracer("unused", _const(0)), debug=debug)
    model = _state_transition_model()

    monkeypatch.setattr(Expression, "to_string", _boom)
    monkeypatch.setattr(Condition, "to_string", _boom)

    declined = counted_loop._impl__build_state_decrement_accumulator_sum_value(
        summarizer,
        model=model,
        result_size=4,
    )

    assert declined is None


@pytest.mark.parametrize("debug", [False, True], ids=["debug-off", "debug-on"])
def test_analysis_runs_with_full_rendering_disabled(monkeypatch, debug):
    """``to_string`` を boom にしても解析が同じ結果まで走る（AC A3）。

    debug OFF が本命（``--debug`` なしの解析が rendering に一切触れない）。
    debug ON も通すことで、debug message 側も有界サマリーだけを使うことを
    実行時に確認する。
    """

    expected = _summarize_branch_while_state(debug=False)
    assert expected is not None

    monkeypatch.setattr(Expression, "to_string", _boom)
    monkeypatch.setattr(Condition, "to_string", _boom)

    summary = _summarize_branch_while_state(debug=debug)

    assert summary is not None
    summarized_returns, note = summary
    assert note == expected[1]
    assert len(summarized_returns) == len(expected[0])


def test_repr_works_with_full_rendering_disabled(monkeypatch):
    """``repr()`` は full render を経由しない（AC A3 / R4 の実行時確認）。"""

    value = Expression.binary_op("INT_ADD", _param("param_1"), _const(1))
    conditions = [_cond("INT_SLESS", _const(0), _param("param_1"))]

    monkeypatch.setattr(Expression, "to_string", _boom)
    monkeypatch.setattr(Condition, "to_string", _boom)

    assert "ExpandedValue(" in repr(ExpandedValue(value, list(conditions)))
    assert "ExpandedBranch(" in repr(ExpandedBranch(list(conditions), value))

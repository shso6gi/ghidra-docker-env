# -*- coding: utf-8 -*-
"""debug 出力のための eager rendering を静的に禁止する guard（Issue #22 PR-22-A）。

`Expression.to_string()` / `to_smt()` / `repr()` は DAG を木として展開するので、
巨大式では debug の有無に関わらず解析時間を食う。debug message のために
これらを呼ぶと、``--debug`` を付けていなくても引数が先に評価される（helper が
関数の中で flag を見ても遅い）。本 test は AST 走査でその形を 0 件に固定する。

固定する 5 つの契約:

* **R1** debug guard の中で禁止呼び出し（``analysis.debug.render`` の
  :data:`UNBOUNDED_RENDER_CALLS` と :data:`HEAVY_DIAGNOSTIC_CALLS`、および
  ``repr()`` / ``getattr(x, "to_string")()``）を呼ばない。guard の中は debug
  専用なので、そこにある full render や重い診断 helper は「debug のためだけに
  入力を辿っている」ことを意味する。
* **R2** debug sink（``print`` と名前に ``debug`` を含む呼び出し）の引数に
  禁止呼び出しを含めない。guard の有無に関わらず禁止（debug ON でも辿らない）。
  引数に直接書いた場合だけでなく、**同じ関数で一度変数へ入れてから渡す形**も
  見る（代入 1 段。production も使う値は対象外）。
* **R3** debug sink の引数で bounded renderer（``summarize_expression`` 等）を
  使うときは debug guard の中で行う。renderer は有界だが、message の f-string
  組み立て自体を debug OFF 時に走らせないため。
* **R4** ``__repr__`` / ``__str__`` が full render を呼ばない。``repr()`` は
  logging・例外・デバッガから暗黙に呼ばれるので、full render を持つと
  「debug OFF なら安全」が成立しない。
* **R5** debug message の前準備（:data:`BOUNDED_DEBUG_PREPARATION` =
  ``bounded_items`` / ``bounded_enumerate``）も debug guard の中で呼ぶ。有界
  とはいえ列を先読みするので、debug OFF で走ってよい仕事ではない。

契約語彙（禁止呼び出し・renderer・前準備・述語・flag）は production 側の owner
``analysis/debug/render.py`` が単独所有し、本 test は import して使う。ここで
名前を並べ直さない。

**guard の判定は 2 つの別契約**（見ている性質が違う）:

* :func:`branch_implies_debug_enabled` — 「この branch に入ったら debug は必ず
  有効か」。R1 / R3 / R5 の到達条件。``and`` は 1 項が debug 可否なら認める
  （全項が真でないと入らない）。``or`` / 比較 / 無関係な名前 / 呼んでいない
  method object は認めない。
* :func:`is_pure_debug_availability_test` — 「guard 自体が debug 可否の確認
  しかしていないか」。wrapper 導出が使う。``and`` も認めない
  （``if not (expensive() and self.debug): return`` は debug OFF でも
  ``expensive()`` を走らせる）。

どちらも fail-closed で、認識できない形はすべて「guard ではない」に倒す。
名前の部分一致では判定しない。
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
#: debug 表示から呼んではいけない呼び出し。DAG を木として展開する描画と、
#: 1 要素ごとに構造キー生成を起動する重い診断 helper。
RENDER_METHODS = debug_render.UNBOUNDED_RENDER_CALLS | debug_render.HEAVY_DIAGNOSTIC_CALLS

#: owner が所有する bounded renderer。family 側の wrapper はここへ委譲するだけ
#: なので列挙しない（:func:`bounded_renderer_names` が委譲を辿って足す）。
OWNED_SUMMARY_FUNCTIONS = debug_render.BOUNDED_DEBUG_RENDERERS

#: 名前に ``debug`` を含むが sink ではない述語（呼んでも何も出力しない）。
DEBUG_PREDICATES = debug_render.DEBUG_AVAILABILITY_PREDICATES

#: debug message の前準備 helper。描画はしないが列を先読みするので、guard の
#: 中でだけ呼んでよい（R5）。renderer とは別契約。
PREPARATION_FUNCTIONS = debug_render.BOUNDED_DEBUG_PREPARATION

#: 契約語彙そのものを持つ owner。ここでの定義・呼び出しは R5 の対象外。
CONTRACT_OWNER_MODULE = "analysis.debug.render"

#: 出力可否を表す属性名（``self.debug`` 等）。guard 節の形の判定に使う。
DEBUG_FLAGS = debug_render.DEBUG_AVAILABILITY_FLAGS

#: full render を持ってはいけない dunder。
RENDER_FREE_DUNDERS = frozenset({"__repr__", "__str__"})


@dataclass
class EagerDebugRenderingViolations:
    """4 契約それぞれの違反。すべて空なら PASS。"""

    render_in_debug_guard: List[Tuple[str, int, str]] = field(default_factory=list)
    render_in_debug_sink: List[Tuple[str, int, str]] = field(default_factory=list)
    unguarded_summary_in_debug_sink: List[Tuple[str, int, str]] = field(default_factory=list)
    render_in_dunder: List[Tuple[str, int, str]] = field(default_factory=list)
    unguarded_debug_preparation: List[Tuple[str, int, str]] = field(default_factory=list)

    def __bool__(self) -> bool:
        return bool(
            self.render_in_debug_guard
            or self.render_in_debug_sink
            or self.unguarded_summary_in_debug_sink
            or self.render_in_dunder
            or self.unguarded_debug_preparation
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
        for module, lineno, detail in self.unguarded_debug_preparation:
            lines.append(
                f"R5 {module}:{lineno}: {detail} reads the head of a sequence outside a "
                "debug guard; wrap the call site in `if <debug available>:`"
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


def _is_simple_argument(node: ast.AST) -> bool:
    """委譲呼び出しの引数として認める形（評価が明らかに軽い式だけ）。

    ``*items`` / ``**mapping`` は拒否する: 展開の時点で任意 iterable / mapping を
    読むので、「guard の外で入力に触らない」という wrapper の前提を壊す。
    """

    if isinstance(node, (ast.Name, ast.Constant)):
        return True
    if isinstance(node, ast.Attribute):
        return _is_simple_argument(node.value)
    return False


def _render_bearing_locals(
    function: ast.FunctionDef | ast.AsyncFunctionDef,
    renderers: FrozenSet[str],
) -> dict:
    """**debug のためだけに**禁止された呼び出しを受けた局所名 → その呼び出し名。

    ``rendered = ConditionNormalizer.get_simplified_string(cond)`` のように
    一度変数へ入れてから debug message に渡す形を捕まえるための、**代入 1 段**
    だけの追跡。汎用 data-flow は要らない。

    production が同じ値を使っている場合（``smt = expr.to_smt()`` を制約に使い、
    ついでに debug にも出す）は対象外。その仕事は debug の有無に関わらず起きる
    ので、debug 側の問題ではない。判定は「その名前の読み出しが **すべて**
    debug sink の引数の中か」で行う。
    """

    labels: dict = {}
    for node in ast.walk(function):
        targets: List[ast.AST] = []
        if isinstance(node, ast.Assign):
            targets = list(node.targets)
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
            targets = [node.target]
        else:
            continue
        if node.value is None:
            continue
        label = next(
            (
                found
                for found in (_render_call_label(inner) for inner in ast.walk(node.value))
                if found
            ),
            "",
        )
        if not label:
            continue
        for target in targets:
            if isinstance(target, ast.Name):
                labels[target.id] = label
    if not labels:
        return labels

    in_sink = {
        id(name)
        for call in ast.walk(function)
        if isinstance(call, ast.Call) and _is_debug_sink(call, renderers)
        for argument in list(call.args) + [keyword.value for keyword in call.keywords]
        for name in ast.walk(argument)
        if isinstance(name, ast.Name)
    }
    reads: dict = {}
    for node in ast.walk(function):
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load) and node.id in labels:
            reads.setdefault(node.id, []).append(id(node) in in_sink)
    return {
        name: label
        for name, label in labels.items()
        if reads.get(name) and all(reads[name])
    }


def _is_debug_guard_clause(statement: ast.stmt) -> bool:
    """``if not self._debug_available(): return "<debug-suppressed>"`` 型の前置き。

    test は :func:`is_pure_debug_availability_test` の否定だけ。``and`` / ``or``
    や他の条件を混ぜた形は認めない（``not (expensive() and self.debug)`` は
    debug OFF でも ``expensive()`` を走らせる）。本体は定数文字列を返すか、
    そのまま return するだけ。
    """

    if not isinstance(statement, ast.If) or statement.orelse:
        return False
    if not _is_negated(statement.test):
        return False
    if not is_pure_debug_availability_test(statement.test.operand):
        return False
    if len(statement.body) != 1 or not isinstance(statement.body[0], ast.Return):
        return False
    value = statement.body[0].value
    return value is None or (isinstance(value, ast.Constant) and isinstance(value.value, str))


def _delegates_to_a_bounded_renderer(
    node: ast.FunctionDef | ast.AsyncFunctionDef,
    known: FrozenSet[str],
) -> bool:
    """`node` が既知の bounded renderer へ **委譲するだけ** の wrapper か。

    family 側の ``_debug_expr_summary`` などを名前で数え上げずに拾うための規則。
    判定は fail-closed で、認めるのは次の形だけ:

        [docstring]
        [debug 述語だけの guard 節（定数を返す）]*
        return <既知 renderer>(<単純な引数>)

    ループ・内包表記・``try``・``with``・代入・入れ子定義・複雑な引数のどれか
    があれば wrapper と認めない。自分で走査する helper を「有界」と誤認すると、
    その呼び出しが guard 無しで debug message に入っても R3 が気付かなくなる。
    """

    body = list(node.body)
    if body and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant):
        body = body[1:]  # docstring
    if not body:
        return False
    *guards, last = body
    if not all(_is_debug_guard_clause(statement) for statement in guards):
        return False
    if not isinstance(last, ast.Return) or not isinstance(last.value, ast.Call):
        return False
    call = last.value
    if _called_name(call) not in known:
        return False
    if any(isinstance(argument, ast.Starred) for argument in call.args):
        return False  # ``*items``
    if any(keyword.arg is None for keyword in call.keywords):
        return False  # ``**mapping``
    arguments = list(call.args) + [keyword.value for keyword in call.keywords]
    return all(_is_simple_argument(argument) for argument in arguments)


@lru_cache(maxsize=None)
def bounded_renderer_names(root: Path = PACKAGE_ROOT) -> FrozenSet[str]:
    """owner の宣言 + そこへ委譲する family wrapper の名前を返す。

    owner（``analysis.debug.render``）が宣言した名前を種にして、委譲するだけの
    wrapper を不動点まで足す。新しい bounded renderer を足すときに触るのは
    owner だけでよく、この test も家族側の module も変えなくてよい。
    """

    definitions: dict[str, List[ast.AST]] = {}
    for path in _iter_source_files(Path(root)):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                definitions.setdefault(node.name, []).append(node)
    known = set(OWNED_SUMMARY_FUNCTIONS)
    while True:
        frozen = frozenset(known)
        discovered = {
            name
            for name, nodes in definitions.items()
            if name not in known
            # 同名の定義が複数あるなら、**全部**が単純委譲のときだけ認める
            # （1 つでも違えば、どの定義を指しているか判断できないので拒否）。
            and all(_delegates_to_a_bounded_renderer(node, frozen) for node in nodes)
        }
        if not discovered:
            return frozenset(known)
        known |= discovered


def is_pure_debug_availability_test(node: ast.AST) -> bool:
    """**debug 可否の確認そのもの**か（他の仕事を一切しない形）。

    認めるのは 2 つだけ:

    * 引数なしの述語呼び出し（``self._debug_available()`` / ``self.debug_flag()``）
    * flag そのもの（``self.debug`` / ``debug``）

    呼び出しは Call のときだけ述語と認める（``self._debug_available`` という
    method object を flag 扱いしない）。flag は Name / Attribute のときだけ。
    ``and`` / ``or`` / 比較 / 添字 / その他の式はすべて拒否する。

    wrapper 導出（:func:`_is_debug_guard_clause`）が使う contract。wrapper の
    guard 節は「debug 可否を見るだけ」でなければならない: ``if not
    (expensive_check() and self.debug): return`` は debug が偽でも
    ``expensive_check()`` を走らせるので、bounded wrapper とは呼べない。
    """

    if isinstance(node, ast.Call):
        if _called_name(node) == "getattr":
            # ``getattr(self, "debug", False)`` だけを flag 読み出しとして認める。
            # receiver も default も、評価が軽いと構文で言える形に限る。
            if node.keywords or not (2 <= len(node.args) <= 3):
                return False
            receiver, attribute, *default = node.args
            if not _is_simple_argument(receiver):
                return False
            if not isinstance(attribute, ast.Constant) or type(attribute.value) is not str:
                return False
            if default and not isinstance(default[0], ast.Constant):
                return False
            return attribute.value in DEBUG_FLAGS
        if node.args or node.keywords:
            return False
        return _called_name(node) in DEBUG_PREDICATES
    if isinstance(node, ast.Attribute):
        return node.attr in DEBUG_FLAGS
    if isinstance(node, ast.Name):
        return node.id in DEBUG_FLAGS
    return False


def branch_implies_debug_enabled(node: ast.AST) -> bool:
    """**この式が真なら debug が有効**と構文的に言えるか。

    scanner（R1 / R3）が使う contract。body に入った時点で debug が有効だと
    保証できればよいので、``and`` は 1 項が debug 可否なら認める（全項が真で
    ないと入らないため）。``or`` は debug が偽でも入るので認めない。

    :func:`is_pure_debug_availability_test` より緩いのは意図的で、見ている
    性質が違う（到達条件 vs guard 自体の純粋さ）。
    """

    if isinstance(node, ast.BoolOp):
        return isinstance(node.op, ast.And) and any(
            branch_implies_debug_enabled(value) for value in node.values
        )
    return is_pure_debug_availability_test(node)


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
        #: 現在の関数で「禁止された呼び出しの結果」を束ねている局所名。
        self.assigned_render_labels: dict[str, str] = {}

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
            if isinstance(statement, ast.If) and branch_implies_debug_enabled(statement.test):
                # `if <debug available>:` — body に入るなら debug は必ず有効。
                self._visit_expression(statement.test, guarded=guarded)
                self._walk_body(statement.body, guarded=True)
                self._walk_body(statement.orelse, guarded=guarded)
                continue
            if (
                isinstance(statement, ast.If)
                and _is_negated(statement.test)
                and branch_implies_debug_enabled(statement.test.operand)
            ):
                # `if not <debug available>: return` — 抜けた先は debug 専用。
                self._visit_expression(statement.test, guarded=guarded)
                self._walk_body(statement.body, guarded=False)
                self._walk_body(statement.orelse, guarded=True)
                if not statement.orelse and _always_exits(statement.body):
                    guarded = True
                continue
            self._walk_statement(statement, guarded=guarded)

    def _walk_statement(self, statement: ast.stmt, *, guarded: bool) -> None:
        if isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef)):
            # 別の呼び出し文脈で実行されるので guard を引き継がない。
            for decorator in statement.decorator_list:
                self._visit_expression(decorator, guarded=guarded)
            outer = self.assigned_render_labels
            self.assigned_render_labels = _render_bearing_locals(statement, self.renderers)
            try:
                self._walk_body(statement.body, guarded=False)
            finally:
                self.assigned_render_labels = outer
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
            if (
                isinstance(sub, ast.Call)
                and not guarded
                and self.module != CONTRACT_OWNER_MODULE
                and _called_name(sub) in PREPARATION_FUNCTIONS
            ):
                self.violations.unguarded_debug_preparation.append(
                    (self.module, sub.lineno, f"{_called_name(sub)}()")
                )
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
                    if isinstance(inner, ast.Name) and isinstance(inner.ctx, ast.Load):
                        indirect = self.assigned_render_labels.get(inner.id)
                        if indirect:
                            self.violations.render_in_debug_sink.append(
                                (
                                    self.module,
                                    sub.lineno,
                                    f"{_called_name(sub)}(... {inner.id} = {indirect} ...)",
                                )
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

def test_no_unguarded_debug_preparation():
    violations = scan_package()
    assert not violations.unguarded_debug_preparation, violations.describe()


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
        "debug_expr_details_summary",
        "_debug_expr_details_summary",
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


def _wrappers_in(source: str, known=frozenset({"summarize_widget"})):
    tree = ast.parse(source)
    return {
        node.name
        for node in ast.walk(tree)
        if isinstance(node, ast.FunctionDef)
        and _delegates_to_a_bounded_renderer(node, known)
    }


def test_scanner_treats_a_delegating_wrapper_as_a_bounded_renderer():
    assert _wrappers_in(
        "class Host:\n"
        "    def _debug_widget_summary(self, widget):\n"
        '        "docstring"\n'
        "        if not self._debug_available():\n"
        "            return '<debug-suppressed>'\n"
        "        return summarize_widget(widget)\n"
        "    def _reason(self):\n"
        "        return 'constant'\n"
    ) == {"_debug_widget_summary"}


@pytest.mark.parametrize(
    "body, label",
    [
        (
            "        parts = [summarize_widget(w) for w in widget]\n"
            "        return summarize_widget(parts)\n",
            "comprehension",
        ),
        (
            "        for part in widget:\n"
            "            pass\n"
            "        return summarize_widget(widget)\n",
            "for-loop",
        ),
        (
            "        while widget:\n"
            "            break\n"
            "        return summarize_widget(widget)\n",
            "while-loop",
        ),
        (
            "        try:\n"
            "            pass\n"
            "        except ValueError:\n"
            "            pass\n"
            "        return summarize_widget(widget)\n",
            "try",
        ),
        (
            "        return summarize_widget(sorted(widget))\n",
            "argument that walks the input",
        ),
        (
            "        return summarize_widget(w for w in widget)\n",
            "generator argument",
        ),
        (
            "        if len(widget) > 1000:\n"
            "            return 'big'\n"
            "        return summarize_widget(widget)\n",
            "guard clause that walks the input",
        ),
    ],
)
def test_scanner_refuses_a_wrapper_that_does_its_own_work(body, label):
    """自分で走査する helper を bounded renderer と誤認しない（fail-closed）。

    どれも「owner renderer へ委譲している」点では以前の規則を満たすので、
    修正前は bounded renderer として通っていた。
    """

    source = "class Host:\n    def _debug_widget_summary(self, widget):\n" + body
    assert _wrappers_in(source) == set(), label


@pytest.mark.parametrize(
    "guard, label",
    [
        ("        if not self._debug_available():\n            return '<suppressed>'\n", "predicate call"),
        ("        if not self.debug:\n            return '<suppressed>'\n", "debug flag"),
        ("        if not self.debug_flag():\n            return ''\n", "flag accessor"),
    ],
)
def test_scanner_accepts_only_a_debug_availability_guard(guard, label):
    source = (
        "class Host:\n"
        "    def _debug_widget_summary(self, widget):\n"
        + guard
        + "        return summarize_widget(widget)\n"
    )
    assert _wrappers_in(source) == {"_debug_widget_summary"}, label


@pytest.mark.parametrize(
    "guard, label",
    [
        ("        if widget:\n            return '<suppressed>'\n", "unrelated name"),
        ("        if self.some_flag:\n            return '<suppressed>'\n", "unrelated attribute"),
        ("        if self.debug or widget:\n            return '<suppressed>'\n", "or-ed condition"),
        ("        if self.debug == False:\n            return '<suppressed>'\n", "comparison"),
        ("        if not (self.debug and widget):\n            return '<suppressed>'\n", "and: guard が debug 可否以外も見る"),
        ("        if self._debug_available:\n            return '<suppressed>'\n", "predicate as a method object"),
        ("        if not self._debug_available(widget):\n            return '<suppressed>'\n", "predicate with an argument"),
        ("        if widget is None:\n            return 'None'\n", "value test"),
    ],
)
def test_scanner_refuses_a_guard_that_is_not_about_debug(guard, label):
    """guard は「debug 可否そのもの」の否定だけ。他の条件を混ぜた形は認めない。"""

    source = (
        "class Host:\n"
        "    def _debug_widget_summary(self, widget):\n"
        + guard
        + "        return summarize_widget(widget)\n"
    )
    assert _wrappers_in(source) == set(), label


def test_scanner_refuses_an_ambiguous_wrapper_name():
    """同名の定義が混在するなら、どちらを指すか決められないので認めない。"""

    source = (
        "class Good:\n"
        "    def _debug_widget_summary(self, widget):\n"
        "        return summarize_widget(widget)\n"
        "class Bad:\n"
        "    def _debug_widget_summary(self, widget):\n"
        "        joined = [summarize_widget(w) for w in widget]\n"
        "        return summarize_widget(joined)\n"
    )
    definitions = [
        node for node in ast.walk(ast.parse(source)) if isinstance(node, ast.FunctionDef)
    ]
    known = frozenset({"summarize_widget"})
    assert not all(_delegates_to_a_bounded_renderer(node, known) for node in definitions)


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


@pytest.mark.parametrize(
    "test_source, guarded, label",
    [
        ("if self.debug:", True, "flag attribute"),
        ("if debug:", True, "flag name"),
        ("if self._debug_available():", True, "predicate call"),
        ("if self.debug and force:", True, "and: 入った時点で debug は有効"),
        ("if self.debug or force:", False, "or: debug が偽でも入る"),
        ("if debug_payload:", False, "名前に debug を含むだけの値"),
        ("if self.debug == False:", False, "比較"),
        ("if self._debug_available:", False, "呼んでいない method object"),
        ("if self.some_flag:", False, "無関係な flag"),
    ],
)
def test_scanner_decides_a_guard_by_shape_not_by_name(test_source, guarded, label):
    """R1 / R3 の guard 判定は「入ったら debug は必ず有効」と言える形だけ。

    名前の部分一致で guarded に倒すと、``if self.debug or force:`` のような
    形で先行評価が素通りする。
    """

    violations = scan_source(
        "sample",
        "def f(self, expr, force, debug, debug_payload):\n"
        f"    {test_source}\n"
        "        self._debug_print(f'v={summarize_expression(expr)}')\n",
    )
    assert bool(violations.unguarded_summary_in_debug_sink) is not guarded, label


def test_scanner_treats_an_early_return_guard_clause_by_shape():
    guarded = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    if not self._debug_available():\n"
        "        return\n"
        "    self._debug_print(f'v={summarize_expression(expr)}')\n",
    )
    assert not guarded, guarded.describe()

    unguarded = scan_source(
        "sample",
        "def f(self, expr, force):\n"
        "    if not force:\n"
        "        return\n"
        "    self._debug_print(f'v={summarize_expression(expr)}')\n",
    )
    assert unguarded.unguarded_summary_in_debug_sink


def test_scanner_refuses_a_heavy_diagnostic_helper_in_debug_output():
    """既知の重い helper は debug 表示から呼べない（owner が名前を所有する）。

    ``get_simplified_condition_string`` は条件ごとに正規化と構造キー生成を
    起動するので、``[f(c) for c in conditions]`` の形で使うと件数 × 走査コスト
    になる。guard の中でも sink の引数でも許さない。
    """

    assert "get_simplified_condition_string" in debug_render.HEAVY_DIAGNOSTIC_CALLS

    in_guard = scan_source(
        "sample",
        "def f(self, conditions):\n"
        "    if self.debug:\n"
        "        dump = [ConditionSimplifier.get_simplified_condition_string(c) for c in conditions]\n"
        "        self._debug_print(f'conds={dump}')\n",
    )
    assert [entry[2] for entry in in_guard.render_in_debug_guard] == [
        "get_simplified_condition_string()"
    ]

    in_arguments = scan_source(
        "sample",
        "def f(self, cond):\n"
        "    self._debug_print(f'c={ConditionSimplifier.get_simplified_condition_string(cond)}')\n",
    )
    assert in_arguments.render_in_debug_sink


@pytest.mark.parametrize(
    "name",
    sorted(debug_render.HEAVY_DIAGNOSTIC_CALLS),
)
def test_every_declared_heavy_helper_is_refused_in_debug_output(name):
    violations = scan_source(
        "sample",
        "def f(self, value):\n"
        "    if self.debug:\n"
        f"        self._debug_print(f'v={{owner.{name}(value)}}')\n",
    )
    assert violations.render_in_debug_guard and violations.render_in_debug_sink


@pytest.mark.parametrize(
    "test_source, scanner_guarded, wrapper_accepted, label",
    [
        ("self.debug", True, True, "flag"),
        ("self._debug_available()", True, True, "predicate call"),
        ("self.debug and force", True, False, "and: 到達条件は満たすが guard は純粋でない"),
        ("self.debug or force", False, False, "or"),
        ("expensive_check() and self.debug", True, False, "debug 判定の前に仕事をする"),
        ("force", False, False, "無関係"),
    ],
)
def test_the_two_guard_contracts_are_separate(
    test_source, scanner_guarded, wrapper_accepted, label
):
    """scanner と wrapper 導出は別の性質を見る。

    * scanner: 「この branch に入ったら debug は有効か」（到達条件）
    * wrapper: 「guard 自体が debug 可否の確認しかしていないか」（純粋さ）

    ``if not (expensive_check() and self.debug): return`` は前者を満たすが
    後者を満たさない（debug OFF でも ``expensive_check()`` が走る）。
    """

    assert branch_implies_debug_enabled(ast.parse(test_source, mode="eval").body) is scanner_guarded, label

    source = (
        "class Host:\n"
        "    def _debug_widget_summary(self, widget, force):\n"
        f"        if not ({test_source}):\n"
        "            return '<suppressed>'\n"
        "        return summarize_widget(widget)\n"
    )
    assert bool(_wrappers_in(source)) is wrapper_accepted, label


def test_scanner_follows_one_assignment_into_a_debug_message():
    """一度変数へ入れてから渡す形も見逃さない（代入 1 段）。"""

    violations = scan_source(
        "sample",
        "def f(self, cond):\n"
        "    rendered = ConditionNormalizer.get_simplified_string(cond)\n"
        "    self._debug_print(f'{rendered}')\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_sink] == [
        "_debug_print(... rendered = get_simplified_string() ...)"
    ]


def test_scanner_follows_an_assignment_of_a_full_render_too():
    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    text = expr.to_smt()\n"
        "    self._debug_print(f'smt={text}')\n",
    )
    assert violations.render_in_debug_sink


def test_scanner_leaves_a_value_production_also_uses():
    """production が使う値のついでに debug へ出す形は debug の問題ではない。"""

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    smt = expr.to_smt()\n"
        "    constraint = build(smt)\n"
        "    self._debug_print(f'smt={smt}')\n"
        "    return constraint\n",
    )
    assert not violations.render_in_debug_sink


def test_scanner_requires_a_guard_for_bounded_preparation():
    """``bounded_items`` は描画しないが列を先読みするので guard の中だけ。"""

    assert "bounded_items" in debug_render.BOUNDED_DEBUG_PREPARATION

    unguarded = scan_source(
        "sample",
        "def f(self, items):\n"
        "    for item in bounded_items(items):\n"
        "        self._debug_print(f'{item}')\n",
    )
    assert [entry[2] for entry in unguarded.unguarded_debug_preparation] == ["bounded_items()"]

    guarded = scan_source(
        "sample",
        "def f(self, items):\n"
        "    if self.debug:\n"
        "        for item in bounded_items(items):\n"
        "            self._debug_print(f'{item}')\n",
    )
    assert not guarded.unguarded_debug_preparation


@pytest.mark.parametrize(
    "name",
    sorted(debug_render.BOUNDED_DEBUG_PREPARATION),
)
def test_every_declared_preparation_helper_needs_a_guard(name):
    violations = scan_source(
        "sample",
        "def f(self, items):\n"
        f"    for item in {name}(items):\n"
        "        self._debug_print(f'{item}')\n",
    )
    assert violations.unguarded_debug_preparation


@pytest.mark.parametrize(
    "call, accepted, label",
    [
        ("summarize_widget(widget)", True, "name"),
        ("summarize_widget(widget, max_depth=depth)", True, "keyword name"),
        ("summarize_widget(self.widget)", True, "attribute"),
        ("summarize_widget(*items)", False, "*args は iterable を展開する"),
        ("summarize_widget(**mapping)", False, "**kwargs は mapping を展開する"),
        ("summarize_widget(sorted(widget))", False, "引数が入力を走査する"),
    ],
)
def test_wrapper_arguments_must_be_cheap(call, accepted, label):
    source = (
        "class Host:\n"
        "    def _debug_widget_summary(self, widget, items, mapping, depth):\n"
        f"        return {call}\n"
    )
    assert bool(_wrappers_in(source)) is accepted, label


@pytest.mark.parametrize(
    "test_source, pure, label",
    [
        ('getattr(self, "debug", False)', True, "flag 読み出し"),
        ('getattr(self, "debug")', True, "default 無し"),
        ('getattr(factory(), "debug", False)', False, "receiver が任意式"),
        ('getattr(self, "debug", expensive_default())', False, "default が任意式"),
        ('getattr(self, name, False)', False, "属性名が定数でない"),
        ('getattr(self, "some_flag", False)', False, "debug flag ではない"),
        ('getattr(self, "debug", False, True)', False, "引数が多い"),
    ],
)
def test_getattr_is_only_a_flag_read_in_an_exact_shape(test_source, pure, label):
    node = ast.parse(test_source, mode="eval").body
    assert is_pure_debug_availability_test(node) is pure, label


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

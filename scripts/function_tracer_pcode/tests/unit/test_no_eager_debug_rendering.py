# -*- coding: utf-8 -*-
"""debug 出力のための eager rendering を静的に禁止する guard（Issue #22 PR-22-A）。

`Expression.to_string()` / `to_smt()` / `repr()` は DAG を木として展開するので、
巨大式では debug の有無に関わらず解析時間を食う。debug message のために
これらを呼ぶと、``--debug`` を付けていなくても引数が先に評価される（helper が
関数の中で flag を見ても遅い）。本 test は AST 走査でその形を 0 件に固定する。

固定する 6 つの契約:

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

* **R6** debug guard の **条件式**で bounded renderer を呼ばない。``and`` の
  後続 conjunct は debug が有効なときだけ評価されるので body と同じ扱いだが、
  条件式は「出すかどうかを決める」場所なので、描画は message 側へ置く。

契約語彙（禁止呼び出し・renderer・前準備・guard の形・描画の呼び出し対象）は
production 側の owner ``analysis/debug/render.py`` が単独所有し、本 test は
import して使う。ここで名前を並べ直さない。

owner が持つのは **設計判断**（何を guard と認めるか / どの対象で呼んだ描画を
有界と認めるか）だけ。「名前は debug だが guard ではない構文が **いま** どれだけ
あるか」は repository の観測結果で変更軸が違うので、static test 側の
:mod:`_debug_guard_baseline` が所有する（production の診断 helper が test の
都合で太らないように）。

**guard の形は exact shape で持つ**。受け手 / flag 名 / 述語名を別々の allow
list にして組み合わせると、production に無い ``self.DEBUG`` / ``cls.debug`` /
``strategy.debug_flag()`` / ``self.debug_reporter.debug_flag()`` まで guard と
して通ってしまう。そこで owner は :data:`DEBUG_GUARD_SHAPES` に
``("attr", ("self",), "debug")`` のような **canonical descriptor**
（:func:`guard_descriptor`）を並べ、判定は完全一致だけで行う。名前は debug でも
guard ではない形（``self._debug_suppressed`` 等）は
:data:`DEBUG_SHAPED_NON_GUARDS` に明示する。

宣言が実測とずれないよう、:func:`observed_guard_shapes` は **recognizer を
通さずに** production の AST から候補を集め、
:func:`test_the_declared_guard_shapes_are_exactly_the_ones_the_package_has` が
両方向のずれ（未宣言 / stale）を FAIL にする。descriptor 文法に落とせない形
（``self.debug is True`` / ``debug_available(config)``）も
:func:`unsupported_guard_descriptor` が ``ast.dump`` の正規形で残すので、
**文法の外側でも fail-closed**（``x is True`` と ``x is False`` のように意味が
違えば別 descriptor になり、未知形が baseline に紛れない）。

**scope と評価のタイミングは別の話**なので、走査の境界を 2 つ用意し、実装は
:func:`_walk_bounded` 1 つを共有する:

* :func:`walk_lexical_scope` — 名前の束縛。入れ子の ``def`` / ``lambda`` /
  ``class`` / comprehension には降りないが、header（default 引数・annotation・
  decorator・base class）は定義側で評価されるので辿る。関数の追跡は
  :func:`function_body_nodes`（**本体だけ**）から始める。
* :func:`walk_evaluated_now` — いまこの場で評価される部分。``lambda`` / ``def``
  の本体は後で走るので含めない（``thunk = lambda: expr.to_string()`` を R1 に
  するのは誤検出）。無視ではなく別 scope として改めて解析する。comprehension と
  class 本体はその場で走るのでそのまま辿る。

代入 1 段の追跡は **読み出し node の id** を鍵にする。名前でまとめると、同じ名前
への複数代入（``key = a.stable_key()`` … ``key = b.stable_key()`` は本 package に
67 関数ある）で「前の代入が production に読まれている」だけで後の debug 専用代入
まで免除されてしまう。読み出しは source 順で直前の代入に割り当てる。CFG は作らず、
割り当て先が決まらない読み出しは免除側に倒す。

**renderer / 前準備を呼んでよい対象も exact shape**（:data:`DEBUG_RENDER_CALL_TARGETS`）。
任意の Attribute chain を pure とみなすと ``self.expensive_property.summarize_expression(x)``
のように property / descriptor 経由で任意処理が起動する形まで「有界な描画」に
なってしまう。実在するのは素の関数呼び出しと ``self`` / ``cls`` 束縛 method、
reporter 1 段だけ。契約の外で呼んだ renderer は **``unsafe_renderer``** として、
guard の中でも、局所変数を挟んでも拒否する（:func:`_summary_call`）。
renderer 認識・wrapper 導出・代入追跡はこの 1 つの判定を共有する。

**guard の判定は 2 つの別契約**（見ている性質が違う）:

* :func:`branch_implies_debug_enabled` — 「この branch に入ったら debug は必ず
  有効か」。R1 / R3 / R5 / R6 の到達条件。``and`` は **先頭項が** debug 可否の
  ときだけ認める（短絡評価により、後続の項は debug が有効なときしか評価され
  ない）。``or`` / 比較 / 無関係な名前 / 呼んでいない method object は認めない。
  後続 conjunct は :func:`debug_only_conjuncts` が debug 専用経路として
  body と同じ規則で検査する。
* :func:`is_pure_debug_availability_test` — 「guard 自体が debug 可否の確認
  しかしていないか」。wrapper 導出が使う。``and`` は認めない
  （``if not (expensive() and self.debug): return`` は debug OFF でも
  ``expensive()`` を走らせる）。

どちらも fail-closed で、認識できない形はすべて「guard ではない」に倒す。名前の
部分一致では判定しない。
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
from contextlib import contextmanager
from functools import lru_cache
from pathlib import Path
from typing import Callable, Dict, FrozenSet, Iterator, List, Optional, Sequence, Tuple

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
from scripts.function_tracer_pcode.tests.unit import _debug_guard_baseline
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

#: **debug 可否の確認そのもの**として認める形（exact descriptor の集合）。
#: 受け手 / flag 名 / 述語名を別々に持って組み合わせると production に無い形まで
#: 通るので、owner は実在する形そのものを宣言する。
DEBUG_GUARD_SHAPES = debug_render.DEBUG_GUARD_SHAPES

#: 名前は debug でも guard ではない、**この repository の現状**の一覧。
#: production の契約ではなく static test 側の観測 baseline なので owner は持たない
#: （:mod:`_debug_guard_baseline` の docstring に責務分離の理由）。
DEBUG_SHAPED_NON_GUARDS = _debug_guard_baseline.DEBUG_SHAPED_NON_GUARDS

#: bounded renderer / 前準備 helper を呼んでよい対象の形。任意の Attribute
#: chain を許すと property / descriptor 経由の任意処理が通るので、実在する
#: 形だけを owner が宣言する。
DEBUG_RENDER_CALL_TARGETS = debug_render.DEBUG_RENDER_CALL_TARGETS

#: 名前に ``debug`` を含むが sink ではない述語（呼んでも何も出力しない）。
#: 契約から導出するので、ここで名前を並べ直さない。
DEBUG_PREDICATES = frozenset(
    shape[2] for shape in DEBUG_GUARD_SHAPES if shape[0] == "call"
)

#: debug message の前準備 helper。描画はしないが列を先読みするので、guard の
#: 中でだけ呼んでよい（R5）。renderer とは別契約。
PREPARATION_FUNCTIONS = debug_render.BOUNDED_DEBUG_PREPARATION

#: 契約語彙そのものを持つ owner。ここでの定義・呼び出しは R5 の対象外。
CONTRACT_OWNER_MODULE = "analysis.debug.render"

#: 名前で辿れない受け手を潰す印（宣言には現れないので fail-closed）。
COMPUTED_RECEIVER: Tuple[str, ...] = ("<computed>",)

#: ``getattr`` の引数が静的に読めないときに使う印。
UNREADABLE = "<expr>"

#: full render を持ってはいけない dunder。
RENDER_FREE_DUNDERS = frozenset({"__repr__", "__str__"})


@dataclass
class EagerDebugRenderingViolations:
    """6 契約（R1〜R6）それぞれの違反。すべて空なら PASS。"""

    render_in_debug_guard: List[Tuple[str, int, str]] = field(default_factory=list)
    render_in_debug_sink: List[Tuple[str, int, str]] = field(default_factory=list)
    unguarded_summary_in_debug_sink: List[Tuple[str, int, str]] = field(default_factory=list)
    render_in_dunder: List[Tuple[str, int, str]] = field(default_factory=list)
    unguarded_debug_preparation: List[Tuple[str, int, str]] = field(default_factory=list)
    renderer_in_guard_condition: List[Tuple[str, int, str]] = field(default_factory=list)

    def __bool__(self) -> bool:
        return bool(
            self.render_in_debug_guard
            or self.render_in_debug_sink
            or self.unguarded_summary_in_debug_sink
            or self.render_in_dunder
            or self.unguarded_debug_preparation
            or self.renderer_in_guard_condition
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
        for module, lineno, detail in self.renderer_in_guard_condition:
            lines.append(
                f"R6 {module}:{lineno}: {detail} runs in the guard condition itself; "
                "a guard only decides whether to emit -- move the call into the message"
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
    """`node` が禁止された呼び出しならその名前、そうでなければ空文字。

    判定は **呼び出しの綴り方に依らない**: ``obj.get_simplified_string(c)`` も
    ``from ... import get_simplified_string`` 後の ``get_simplified_string(c)``
    も同じ contract（owner の :data:`RENDER_METHODS`）で見る。import の形で
    guard を回避できないようにするため。
    """

    if not isinstance(node, ast.Call):
        return ""
    func = node.func
    if isinstance(func, ast.Attribute) and func.attr in RENDER_METHODS:
        return f"{func.attr}()"
    if isinstance(func, ast.Name):
        if func.id in RENDER_METHODS:
            return f"{func.id}()"
        if func.id == "repr":
            return "repr()"
    # `getattr(expr, "to_string", ...)()`: 呼び出し対象が getattr でも full render。
    if isinstance(func, ast.Call) and _called_name(func) == "getattr":
        arguments = func.args
        if len(arguments) >= 2 and isinstance(arguments[1], ast.Constant):
            attribute = arguments[1].value
            if isinstance(attribute, str) and attribute in RENDER_METHODS:
                return f'getattr(..., "{attribute}")()'
    return ""


def _summary_call(node: ast.AST, renderers: FrozenSet[str]) -> Tuple[str, str]:
    """renderer 呼び出しを **種別つき**で返す（``(種別, 表示)``）。

    * ``("renderer", "summarize_expression()")`` — 宣言された対象で呼んでいる。
      有界なので debug guard の中でなら使ってよい（R3）。
    * ``("unsafe_renderer", "<computed>.summarize_expression()")`` — renderer の
      名前だが対象が契約の外（``expensive_factory().summarize_expression(x)`` /
      ``self.expensive_property.summarize_expression(x)``）。receiver の構築で
      任意処理が走り得るので「有界な描画」とは言えず、guard の中でも不可。
    * ``("", "")`` — renderer ではない。

    種別を分けるのは、名前だけで renderer と認めて対象を捨てると、局所変数を
    1 つ挟むだけで契約を抜けられるため（``s = factory().summarize_expression(x)``
    → ``self._debug_print(s)``）。:func:`_debug_only_locals` は同じ種別で
    追跡する。
    """

    if not isinstance(node, ast.Call):
        return ("", "")
    name = _called_name(node)
    if name not in renderers:
        return ("", "")
    if _is_declared_render_target(node.func):
        return ("renderer", f"{name}()")
    return ("unsafe_renderer", f"<computed>.{name}()")


def _summary_call_label(node: ast.AST, renderers: FrozenSet[str]) -> str:
    """宣言された対象で呼ばれた bounded renderer ならその名前（R3 用）。"""

    kind, label = _summary_call(node, renderers)
    return label if kind == "renderer" else ""


def _is_debug_sink(node: ast.Call, renderers: FrozenSet[str]) -> bool:
    name = _called_name(node)
    if not name or name in renderers or name in DEBUG_PREDICATES:
        return False
    return name == "print" or "debug" in name.lower()


def _is_simple_argument(node: ast.AST) -> bool:
    """委譲呼び出しの引数として認める形。

    局所名と定数だけ。``self.foo`` のような属性参照も認めない: property /
    descriptor は任意の処理を起動でき、それが軽いと構文からは言えないため
    （実在の wrapper はどれも局所名と定数しか渡していないので、狭めても困らない）。
    ``*items`` / ``**mapping`` も拒否する（展開の時点で任意 iterable / mapping を
    読む）。
    """

    return isinstance(node, (ast.Name, ast.Constant))


def call_target_shape(func: ast.AST) -> Optional[debug_render.RenderCallTarget]:
    """呼び出し対象を canonical な形にする（表せなければ None）。

    ``summarize_expression`` → ``("name",)``、
    ``self._debug_expr_summary`` → ``("attr", "self", ())``、
    ``self._debug_reporter.debug_expr_summary`` →
    ``("attr", "self", ("_debug_reporter",))``。``factory().render`` /
    ``registry[key].render`` のように receiver を計算する形は None。
    """

    if isinstance(func, ast.Name):
        return ("name",)
    if isinstance(func, ast.Attribute):
        path: List[str] = []
        node: ast.AST = func.value
        while isinstance(node, ast.Attribute):
            path.append(node.attr)
            node = node.value
        if isinstance(node, ast.Name):
            return ("attr", node.id, tuple(reversed(path)))
    return None


def _is_declared_render_target(func: ast.AST) -> bool:
    """renderer / 前準備 / wrapper 委譲を呼んでよい対象か。

    owner の :data:`DEBUG_RENDER_CALL_TARGETS` との完全一致。任意の
    Attribute chain を許すと ``self.expensive_property.summarize_expression(x)``
    のように **property / descriptor 経由で任意処理が起動する**形まで「有界な
    描画」として通る。本 package に実在するのは素の関数呼び出しと
    ``self`` / ``cls`` に束縛された method、および reporter 1 段だけなので、
    それ以外は fail-closed にする。

    renderer 認識・wrapper 導出・代入追跡がこの 1 か所を共有する。
    """

    return call_target_shape(func) in DEBUG_RENDER_CALL_TARGETS


#: 別の **束縛** を作る構文。名前の追跡はここへ降りない。comprehension も
#: Python 3 では独自の scope を持つ（``[x for summary in ...]`` の ``summary``
#: は外側の束縛ではない）。
NESTED_SCOPE_NODES = (
    ast.FunctionDef,
    ast.AsyncFunctionDef,
    ast.Lambda,
    ast.ClassDef,
    ast.ListComp,
    ast.SetComp,
    ast.DictComp,
    ast.GeneratorExp,
)

#: 本体が **その場では実行されない** 構文。式の走査はここへ降りない
#: （``thunk = lambda: expr.to_string()`` は代入の時点では何も描画しない）。
#: comprehension と class 本体はその場で評価されるので含めない。
DEFERRED_SCOPE_NODES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)

#: comprehension の **最初の** iterable だけは外側の scope で評価される
#: （``[f(x) for x in summary]`` の ``summary`` は外側の名前）。
_COMPREHENSIONS = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)


def _walk_bounded(
    node: ast.AST, boundary: "Callable[[ast.AST], Optional[Sequence[ast.AST]]]"
) -> Iterator[ast.AST]:
    """``node`` 以下を、``boundary`` が引いた境界まで辿る。

    ``boundary(child)`` が ``None`` を返せば child ごと辿り、node 列を返せば
    child 自身は飛ばしてその列だけを辿る（境界の向こう側で、なお今回の走査に
    含めたい部分を渡すため）。

    scope の意味づけは 2 つあるが（束縛の scope と評価のタイミング）、走査の
    実装はこれ 1 つ。境界の定義だけを別にする。
    """

    stack: List[ast.AST] = [node]
    while stack:
        current = stack.pop()
        yield current
        for child in ast.iter_child_nodes(current):
            crossed = boundary(child)
            if crossed is None:
                stack.append(child)
            else:
                stack.extend(crossed)


def _defining_scope_parts(node: ast.AST) -> List[ast.AST]:
    """``node`` の中で、**それを定義する側の scope** で評価される部分。

    decorator / default 引数 / annotation / base class は、関数や class を作る
    その場で評価され、外側の名前を読む（``def f(x=summary):`` の ``summary`` は
    外側の ``summary``）。本体だけが別 scope・別のタイミングになる。
    """

    parts: List[ast.AST] = []
    arguments = getattr(node, "args", None)
    if isinstance(arguments, ast.arguments):
        parts += [default for default in arguments.defaults if default is not None]
        parts += [default for default in arguments.kw_defaults if default is not None]
        for argument in (
            arguments.posonlyargs + arguments.args + arguments.kwonlyargs
            + [arguments.vararg, arguments.kwarg]
        ):
            if argument is not None and argument.annotation is not None:
                parts.append(argument.annotation)
    parts += list(getattr(node, "decorator_list", []))
    parts += list(getattr(node, "bases", []))
    parts += [keyword.value for keyword in getattr(node, "keywords", [])]
    returns = getattr(node, "returns", None)
    if returns is not None:
        parts.append(returns)
    return parts


def _binding_boundary(child: ast.AST) -> Optional[Sequence[ast.AST]]:
    """名前の束縛が変わる境界。

    向こう側の本体は別の束縛なので辿らないが、header（default 引数・annotation・
    decorator・base class）はこちら側の名前を読むので辿る。
    """

    if isinstance(child, _COMPREHENSIONS):
        # 中は別 scope だが、最初の iterable だけは外側で評価される。
        return [child.generators[0].iter] if child.generators else []
    if isinstance(child, NESTED_SCOPE_NODES):
        return _defining_scope_parts(child)
    return None


def _evaluation_boundary(child: ast.AST) -> Optional[Sequence[ast.AST]]:
    """いま評価されるかどうかの境界。

    ``lambda`` / ``def`` の本体は後で呼ばれたときに走るので、この場の走査には
    含めない（呼び出し側の文脈を知らないので、別 scope として改めて解析する）。
    header は定義時に評価されるので辿る。comprehension と class 本体はその場で
    評価されるので境界ではない。
    """

    if isinstance(child, DEFERRED_SCOPE_NODES):
        return _defining_scope_parts(child)
    return None


def walk_lexical_scope(node: ast.AST) -> Iterator[ast.AST]:
    """``node`` 以下を、**入れ子の束縛 scope へは降りずに**辿る。

    ``def`` / ``async def`` / ``lambda`` / ``class`` / comprehension の中の名前は
    別の束縛なので、外側の局所名の読み出しとして数えてはいけない。``ast.walk``
    で全部辿ると、内側の同名 parameter への read が「production も読んでいる」と
    誤解され、外側の R2 / R3 / R6 をすり抜けられる（逆に、内側の read を外側の
    局所名と取り違えて誤検出もする）。

    代入・読み出し・sink・guard 条件の収集はすべてこの 1 つの走査を使う。入れ子
    の scope は scanner 本体が別 scope として独立に解析する。名前解決はしない
    （必要なのは「この scope の構文か」だけ）。
    """

    return _walk_bounded(node, _binding_boundary)


def walk_evaluated_now(node: ast.AST) -> Iterator[ast.AST]:
    """``node`` のうち、**いまこの場で評価される**部分だけを辿る。

    ``if self.debug: thunk = lambda: expr.to_string()`` の ``to_string()`` は
    代入の時点では走らないので、ここで R1 として数えるのは誤検出。lambda / def
    の本体は :meth:`_EagerDebugRenderingScanner._visit_deferred_scopes` が別
    scope として改めて解析する（無視はしない）。comprehension と class 本体は
    その場で評価されるので、そのまま辿る。
    """

    return _walk_bounded(node, _evaluation_boundary)


def function_body_nodes(
    function: "ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda",
) -> Iterator[ast.AST]:
    """関数の **本体だけ**を lexical scope として辿る。

    decorator / default 引数 / annotation は関数を **定義する側**の scope で
    評価されるので、本体の局所名の読み出しに混ぜない
    （``def f(x=summary):`` の ``summary`` は外側の名前）。
    """

    body = (
        [function.body]
        if isinstance(function, ast.Lambda)
        else list(function.body)
    )
    for statement in body:
        crossed = _binding_boundary(statement)
        if crossed is None:
            yield from walk_lexical_scope(statement)
        else:
            # 本体の中の ``def`` / ``class`` — header だけがこの scope の話。
            for part in crossed:
                yield from walk_lexical_scope(part)


def _assignment_kind(value: ast.AST, renderers: FrozenSet[str]) -> Tuple[str, str]:
    """代入の右辺が debug 用に何を作るか（``(種別, 表示)``）。"""

    entry = ("", "")
    for inner in ast.walk(value):
        forbidden = _render_call_label(inner)
        if forbidden:
            return ("forbidden", forbidden)
        kind, label = _summary_call(inner, renderers)
        # unsafe は renderer より強い（対象が契約の外なので guard 内でも不可）。
        if kind == "unsafe_renderer":
            entry = (kind, label)
        elif kind == "renderer" and not entry[0]:
            entry = (kind, label)
    return entry


def _debug_only_locals(
    function: ast.FunctionDef | ast.AsyncFunctionDef,
    renderers: FrozenSet[str],
) -> Dict[int, Tuple[str, str]]:
    """**debug のためだけに**作られた値を作る代入 → ``(種別, 呼び出し名)``。

    ``rendered = ConditionNormalizer.get_simplified_string(cond)`` や
    ``summary = summarize_expression(expr)`` のように、一度変数へ入れてから
    debug message に渡す形を捕まえるための **代入 1 段**だけの追跡。汎用
    data-flow は要らない。種別は 3 つ:

    * ``"forbidden"`` — 禁止された呼び出し（R2。guard の有無に関わらず不可）
    * ``"unsafe_renderer"`` — renderer の名前だが対象が契約の外（R2 / R6。
      receiver の構築で任意処理が走り得るので guard の中でも不可）
    * ``"renderer"`` — 有界 renderer（R3。guard の外で組み立ててはいけない）

    鍵は **名前ではなく読み出し node の id**。同じ名前へ複数回代入する関数は
    珍しくなく（``key = a.stable_key()`` … ``key = b.stable_key()`` は本 package
    に 67 関数ある）、名前でまとめると「前の代入が production に読まれている」
    だけで後の debug 専用代入まで免除されてしまう。読み出しは **source 順で
    直前の代入**に割り当てる。分岐や loop を追う CFG は作らない: 先行代入が
    無い読み出しはどの代入にも割り当てないので、判断できないものは黙って
    免除側（= 報告しない）に倒れる。

    走査は :func:`function_body_nodes`、つまり **この関数の本体だけ**。
    decorator / default 引数 / annotation は関数を定義する側の scope で評価され
    るので混ぜない。入れ子の ``def`` / ``lambda`` / ``class`` / comprehension の
    同名変数も別の束縛なので混ぜない。

    production が同じ値を使っている場合（``smt = expr.to_smt()`` を制約に使い、
    ついでに debug にも出す）は対象外。その仕事は debug の有無に関わらず起きる
    ので debug 側の問題ではない。判定は「その代入の読み出しが **すべて** debug
    専用の位置（debug sink の引数、または guard 条件の後続 conjunct）にあるか」
    で行う。

    返り値は ``id(<Name node>) -> (種別, 表示)``。その読み出しだけが報告対象。
    """

    body = list(function_body_nodes(function))

    #: (行, 桁) 順に並べた代入。``definitions[name]`` は source 順。
    definitions: Dict[str, List[Tuple[Tuple[int, int], Tuple[str, str]]]] = {}
    for node in body:
        targets: List[ast.AST] = []
        if isinstance(node, ast.Assign):
            targets = list(node.targets)
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
            targets = [node.target]
        else:
            continue
        if node.value is None:
            continue
        entry = _assignment_kind(node.value, renderers)
        position = (node.lineno, node.col_offset)
        for target in targets:
            if isinstance(target, ast.Name):
                definitions.setdefault(target.id, []).append((position, entry))
    if not definitions:
        return {}
    for places in definitions.values():
        places.sort(key=lambda item: item[0])

    debug_positions = {
        id(name)
        for call in body
        if isinstance(call, ast.Call) and _is_debug_sink(call, renderers)
        for argument in list(call.args) + [keyword.value for keyword in call.keywords]
        for name in ast.walk(argument)
        if isinstance(name, ast.Name)
    }
    # guard 条件の後続 conjunct も debug 専用の読み出し位置。
    # ``summary = summarize_expression(expr)`` を ``if self.debug and summary:``
    # でしか読まない形は、sink 引数だけ見ていると debug-only と判定できない。
    debug_positions |= {
        id(name)
        for branch in body
        if isinstance(branch, (ast.If, ast.IfExp))
        for conjunct in debug_only_conjuncts(branch.test)
        for name in ast.walk(conjunct)
        if isinstance(name, ast.Name)
    }

    #: 代入（name, source 順の index）-> その代入を読んでいる Name node
    reads: Dict[Tuple[str, int], List[ast.Name]] = {}
    for node in body:
        if not isinstance(node, ast.Name) or not isinstance(node.ctx, ast.Load):
            continue
        places = definitions.get(node.id)
        if not places:
            continue
        here = (node.lineno, node.col_offset)
        index = -1
        for candidate, (position, _entry) in enumerate(places):
            if position < here:
                index = candidate
        if index < 0:
            # 最初の代入より前の読み出しは、この関数が作った値ではない。
            continue
        reads.setdefault((node.id, index), []).append(node)

    reported: Dict[int, Tuple[str, str]] = {}
    for name, places in definitions.items():
        for index, (_position, entry) in enumerate(places):
            if not entry[0]:
                continue
            names = reads.get((name, index))
            if not names or not all(id(node) in debug_positions for node in names):
                continue
            for node in names:
                reported[id(node)] = entry
    return reported


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
    if _called_name(call) not in known or not _is_declared_render_target(call.func):
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

    definitions: Dict[str, List[ast.AST]] = {}
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


def _receiver_path(node: ast.AST) -> Tuple[str, ...]:
    """受け手を **根から辿った名前の列**にする。

    ``self`` → ``("self",)``、``self.debug_reporter`` →
    ``("self", "debug_reporter")``。名前で辿れない受け手（``factory()`` /
    ``registry[key]`` / 任意の式）は ``("<computed>",)`` に潰す。潰した形は
    owner の宣言に載らないので、そのまま fail-closed になる。
    """

    if isinstance(node, ast.Name):
        return (node.id,)
    if isinstance(node, ast.Attribute):
        inner = _receiver_path(node.value)
        return inner + (node.attr,) if inner != COMPUTED_RECEIVER else COMPUTED_RECEIVER
    return COMPUTED_RECEIVER


def guard_descriptor(node: ast.AST) -> Optional[debug_render.GuardShape]:
    """式を **canonical guard descriptor** にする（guard 形でなければ None）。

    owner の :data:`DEBUG_GUARD_SHAPES` と完全一致で突き合わせるための正規形。
    ここは「その形が guard か」を判定せず、**形を写すだけ**なので、recognizer
    にも棚卸しにも同じものが使える（判定と観測で別実装を持たない）。

    ``getattr`` は receiver / 属性名 / 既定値がすべて静的に読めるときだけ
    その形を写し、読めない引数があれば ``("getattr", ("<computed>",), …)``
    に潰す（宣言と一致しないので拒否される）。
    """

    if isinstance(node, ast.Name):
        return ("name", node.id)
    if isinstance(node, ast.Attribute):
        return ("attr", _receiver_path(node.value), node.attr)
    if isinstance(node, ast.Call):
        func = node.func
        if isinstance(func, ast.Name) and func.id == "getattr":
            if not node.keywords and 2 <= len(node.args) <= 3:
                attribute = node.args[1]
                default = node.args[2] if len(node.args) == 3 else None
                if isinstance(attribute, ast.Constant) and type(attribute.value) is str:
                    if default is None or isinstance(default, ast.Constant):
                        return (
                            "getattr",
                            _receiver_path(node.args[0]),
                            attribute.value,
                            None if default is None else default.value,
                        )
            return ("getattr", COMPUTED_RECEIVER, UNREADABLE, UNREADABLE)
        if node.args or node.keywords:
            # 引数を取る呼び出しは「可否を答えるだけ」ではない。
            return None
        if isinstance(func, ast.Attribute):
            return ("call", _receiver_path(func.value), func.attr)
        if isinstance(func, ast.Name):
            return ("call", (), func.id)
    return None


def guard_shape_source(shape: debug_render.GuardShape) -> str:
    """canonical descriptor を、それを表す Python 式に戻す。

    owner が宣言した形から test 入力を作るための逆写像。test 側で production の
    guard 一覧を書き写さないで済むので、新しい guard を足すときに触るのは
    production と owner contract の 2 か所だけになる。

    ``("unsupported", ...)``（descriptor 文法の外の形）は式に戻せないので
    :class:`ValueError`。
    """

    kind = shape[0]
    if kind == "name":
        return shape[1]
    if kind == "attr":
        return ".".join(shape[1] + (shape[2],))
    if kind == "call":
        prefix = ".".join(shape[1])
        return f"{prefix}.{shape[2]}()" if prefix else f"{shape[2]}()"
    if kind == "getattr":
        receiver = ".".join(shape[1])
        if shape[3] is None:
            return f'getattr({receiver}, "{shape[2]}")'
        return f'getattr({receiver}, "{shape[2]}", {shape[3]!r})'
    raise ValueError(f"not a source-representable guard shape: {shape!r}")


def short_circuit_head(node: ast.AST) -> ast.AST:
    """条件式のうち **必ず最初に評価される** 末端の式。

    ``not X`` の ``X``、``A and B`` / ``A or B`` の ``A`` を辿り切る。2 項目
    以降は先頭項の結果しだいなので guard の位置ではない（``x and self.debug``
    は debug を見る前に ``x`` を評価する）。

    ``not``・boolean 演算子そのものは合成なので観測の対象にしない（中身の末端を
    見れば足りる）。棚卸しが同じ式を何通りにも数えないための正規化でもある。
    """

    if _is_negated(node):
        return short_circuit_head(node.operand)
    if isinstance(node, ast.BoolOp) and node.values:
        return short_circuit_head(node.values[0])
    return node


def _mentions_debug(text: object) -> bool:
    return "debug" in str(text).lower()


def _debug_names_in(node: ast.AST) -> Tuple[str, ...]:
    """式の中に現れる **debug を含む名前**（識別子・属性名・文字列定数）。"""

    found = set()
    for sub in ast.walk(node):
        if isinstance(sub, ast.Name) and _mentions_debug(sub.id):
            found.add(sub.id)
        elif isinstance(sub, ast.Attribute) and _mentions_debug(sub.attr):
            found.add(sub.attr)
        elif (
            isinstance(sub, ast.Constant)
            and type(sub.value) is str
            and _mentions_debug(sub.value)
        ):
            found.add(sub.value)
    return tuple(sorted(found))


def unsupported_guard_descriptor(node: ast.AST) -> debug_render.GuardShape:
    """canonical descriptor に落とせない **debug らしい式**の descriptor。

    比較（``self.debug is True``）や引数付き呼び出し（``debug_available(config)``）
    は :func:`guard_descriptor` の文法の外にある。これを「descriptor に
    できないから」と捨てると、未知の guard を production に足しても棚卸しに
    現れず、contract のずれに気付けない（= 文法の外側で fail-open になる）。

    そこで構文をそのまま残す: ``("unsupported", ast.dump(node,
    include_attributes=False))``。``ast.dump`` は node 種別・演算子種別・子の構造・
    属性名 / 識別子・定数の値と型を保つ一方、行番号や桁といった非意味情報は
    含まない。よって

    * 同値な構文は同じ descriptor（決定的）
    * ``x is True`` / ``x is False`` / ``x == y`` / ``x != y`` / ``x is not y``
      のように**意味が違えば別の descriptor**

    になる。要約した descriptor（node 種別 + 名前だけ等）では上のような形が
    衝突し、未知形が既知の baseline と偶然一致して素通りしてしまう。source
    文字列ではなく AST の正規化なので、空白や括弧の付け方には依存しない。
    """

    return ("unsupported", ast.dump(node, include_attributes=False))


def is_pure_debug_availability_test(node: ast.AST) -> bool:
    """**debug 可否の確認そのもの**か（owner が宣言した実在形との完全一致）。

    受け手・flag 名・述語名を別々の allow list で持って組み合わせると、
    production に存在しない ``self.DEBUG`` / ``cls.debug`` /
    ``strategy.debug_flag()`` / ``self.debug_reporter.debug_flag()`` まで
    guard として通ってしまう。判定は :data:`DEBUG_GUARD_SHAPES` との exact
    match だけで行い、直積は作らない。認識できない形はすべて「guard ではない」。

    wrapper 導出（:func:`_is_debug_guard_clause`）が使う contract。wrapper の
    guard 節は「debug 可否を見るだけ」でなければならない: ``if not
    (expensive_check() and self.debug): return`` は debug が偽でも
    ``expensive_check()`` を走らせるので、bounded wrapper とは呼べない。
    """

    return guard_descriptor(node) in DEBUG_GUARD_SHAPES


def branch_implies_debug_enabled(node: ast.AST) -> bool:
    """**この式が真なら debug が有効**と構文的に言えるか。

    scanner（R1 / R3 / R5 / R6）が使う contract。``and`` は **先頭が** debug
    可否のときだけ認める: 短絡評価により後続の項は debug が有効なときしか
    評価されないので、「debug OFF で診断用の処理が走らない」が成り立つ。
    順番が逆の ``if expensive() and self.debug:`` は debug OFF でも
    ``expensive()`` を走らせるため guard と認めない（production 側の ``and``
    guard はすべて debug を先頭に置く形へ揃えてある）。``or`` は debug が偽でも
    入るので不可。

    :func:`is_pure_debug_availability_test` より緩いのは意図的で、見ている
    性質が違う（到達条件 vs guard 自体の純粋さ）。後続 conjunct は
    :func:`debug_only_conjuncts` が debug 専用経路として別途検査する。
    """

    if isinstance(node, ast.BoolOp):
        return (
            isinstance(node.op, ast.And)
            and bool(node.values)
            and is_pure_debug_availability_test(node.values[0])
        )
    return is_pure_debug_availability_test(node)


def debug_only_conjuncts(node: ast.AST) -> List[ast.AST]:
    """debug atom が短絡評価で成立した **あとにだけ**評価される式。

    ``if self.debug and expr.to_string():`` の ``expr.to_string()`` は branch の
    body と同じく debug 専用の仕事なので、body と同じ規則で検査する必要がある
    （条件式の中だから見逃す、では guard の意味が無い）。``not`` を挟んだ
    ``if not (self.debug and expensive()): return`` も同じ（debug が有効なとき
    だけ ``expensive()`` が走る）。
    """

    if _is_negated(node):
        return debug_only_conjuncts(node.operand)
    if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And) and node.values:
        head, *rest = node.values
        if is_pure_debug_availability_test(head):
            return list(rest)
        # ``(self.debug and a) and b`` — 入れ子でも debug が先頭なら後続は debug 専用。
        inner = debug_only_conjuncts(head)
        return inner + list(rest) if inner else []
    return []


def _is_negated(test: ast.AST) -> bool:
    return isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not)


def _always_exits(body: Sequence[ast.stmt]) -> bool:
    return bool(body) and isinstance(body[-1], (ast.Return, ast.Raise, ast.Continue, ast.Break))


class _EagerDebugRenderingScanner:
    """1 module 分の AST を走査して 6 契約（R1〜R6）の違反を集める。"""

    def __init__(
        self,
        module: str,
        violations: EagerDebugRenderingViolations,
        renderers: FrozenSet[str] = OWNED_SUMMARY_FUNCTIONS,
    ) -> None:
        self.module = module
        self.violations = violations
        self.renderers = renderers
        #: **debug のためだけに作られた値を読んでいる** ``Name`` node の id ->
        #: ``(種別, 呼び出し名)``。種別は ``"forbidden"`` / ``"unsafe_renderer"``
        #: （R2・R6）か ``"renderer"``（R3）。
        #:
        #: 鍵が読み出し node そのものなので、同名の別束縛（入れ子 scope の
        #: parameter、同じ scope の別の代入）と取り違えようがない。
        self.debug_only_reads: Dict[int, Tuple[str, str]] = {}

    @contextmanager
    def _scope(self, function: Optional[ast.AST]) -> Iterator[None]:
        """lexical scope を 1 つ入れ替える（代入 1 段の追跡はこの単位）。"""

        outer = self.debug_only_reads
        self.debug_only_reads = (
            {} if function is None else _debug_only_locals(function, self.renderers)
        )
        try:
            yield
        finally:
            self.debug_only_reads = outer

    def _label_for(self, node: ast.Name) -> Tuple[str, str]:
        """その読み出しが debug 専用の値を読んでいるなら種別と表示。"""

        return self.debug_only_reads.get(id(node), ("", ""))

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
                self._visit_guard_condition(statement.test, guarded=guarded)
                self._walk_body(statement.body, guarded=True)
                self._walk_body(statement.orelse, guarded=guarded)
                continue
            if (
                isinstance(statement, ast.If)
                and _is_negated(statement.test)
                and branch_implies_debug_enabled(statement.test.operand)
            ):
                # `if not <debug available>: return` — 抜けた先は debug 専用。
                self._visit_guard_condition(statement.test, guarded=guarded)
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
            with self._scope(statement):
                self._walk_body(statement.body, guarded=False)
            return
        if isinstance(statement, ast.ClassDef):
            # 束縛としては別 scope なので局所名の追跡は持ち込まないが、本体は
            # **その場で**実行されるので guard 状態は引き継ぐ。
            for decorator in statement.decorator_list:
                self._visit_expression(decorator, guarded=guarded)
            with self._scope(None):
                self._walk_body(statement.body, guarded=guarded)
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
    def _visit_deferred_scopes(self, node: ast.AST) -> None:
        """``lambda`` の本体を **別 scope** として解析する。

        本体はこの式が評価される時点では走らないので、ここの guard 状態は
        引き継がない（``if self.debug: thunk = lambda: expr.to_string()`` を R1 と
        するのは誤検出）。無視するのではなく、呼び出し文脈が分からない以上
        guard 無しの scope として改めて見る — 入れ子の ``def`` を
        :meth:`_walk_statement` が扱うのと同じ扱い。

        式そのものが ``lambda`` のこともある（``thunk = lambda: ...``）ので、
        根も候補に含める。
        """

        candidates = [node] if isinstance(node, ast.Lambda) else []
        candidates += [
            child
            for sub in walk_evaluated_now(node)
            for child in ast.iter_child_nodes(sub)
            if isinstance(child, ast.Lambda)
        ]
        for lambda_node in candidates:
            with self._scope(lambda_node):
                self._visit_expression(lambda_node.body, guarded=False)

    def _visit_guard_condition(self, test: ast.AST, *, guarded: bool) -> None:
        """guard の条件式を検査する。

        ``and`` の後続 conjunct は **debug が有効なときだけ**評価されるので、
        body と同じく debug 専用経路として扱う（条件式の中だから見逃す、では
        guard の意味が無い）。先頭の debug atom は owner が宣言した形そのもの
        で、禁止呼び出しも renderer も前準備も含み得ないため走査しない。

        条件式は「出すかどうかを決める」だけの場所なので、後続 conjunct で
        renderer を呼ぶ形は R6、前準備 helper を呼ぶ形は R5 として報告する
        （禁止呼び出しは debug 専用経路の R1）。
        """

        trailing = debug_only_conjuncts(test)
        if not trailing:
            self._visit_expression(test, guarded=guarded)
            return
        for conjunct in trailing:
            self._visit_expression(conjunct, guarded=True)
            self._flag_guard_condition_work(conjunct)

    def _flag_guard_condition_work(self, node: ast.AST) -> None:
        for sub in walk_evaluated_now(node):
            if isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load):
                # 一度局所名へ入れてから条件式で読む形も同じ扱い（代入 1 段）。
                kind, label = self._label_for(sub)
                if kind == "forbidden":
                    self.violations.render_in_debug_guard.append(
                        (self.module, sub.lineno, f"{sub.id} = {label}")
                    )
                elif kind in ("renderer", "unsafe_renderer"):
                    self.violations.renderer_in_guard_condition.append(
                        (self.module, sub.lineno, f"{sub.id} = {label}")
                    )
                continue
            if not isinstance(sub, ast.Call):
                continue
            name = _called_name(sub)
            if name in self.renderers:
                self.violations.renderer_in_guard_condition.append(
                    (self.module, sub.lineno, f"{name}()")
                )
            elif name in PREPARATION_FUNCTIONS and self.module != CONTRACT_OWNER_MODULE:
                self.violations.unguarded_debug_preparation.append(
                    (self.module, sub.lineno, f"{name}()")
                )

    def _visit_expression(self, node: ast.AST, *, guarded: bool) -> None:
        self._visit_deferred_scopes(node)
        crossed = _evaluation_boundary(node)
        if crossed is not None:
            # 式そのものが遅延 scope（``lambda``）。本体は上で別に見たので、
            # ここでは定義時に評価される header だけを今の文脈で見る。
            for part in crossed:
                self._visit_expression(part, guarded=guarded)
            return
        for sub in walk_evaluated_now(node):
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
                    call_kind, call_label = _summary_call(inner, self.renderers)
                    if call_kind == "unsafe_renderer":
                        # renderer の名前でも、対象が契約の外なら「有界な描画」
                        # ではない（receiver の構築が任意処理）。
                        self.violations.render_in_debug_sink.append(
                            (self.module, sub.lineno, f"{_called_name(sub)}(... {call_label} ...)")
                        )
                    if isinstance(inner, ast.Name) and isinstance(inner.ctx, ast.Load):
                        kind, label = self._label_for(inner)
                        detail = f"{_called_name(sub)}(... {inner.id} = {label} ...)"
                        if kind in ("forbidden", "unsafe_renderer"):
                            self.violations.render_in_debug_sink.append(
                                (self.module, sub.lineno, detail)
                            )
                        elif kind == "renderer" and not guarded:
                            self.violations.unguarded_summary_in_debug_sink.append(
                                (self.module, sub.lineno, detail)
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

def test_no_renderer_in_a_guard_condition():
    violations = scan_package()
    assert not violations.renderer_in_guard_condition, violations.describe()


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
        ("expensive_check() and self.debug", False, False, "debug 判定の前に仕事をする"),
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
        ("summarize_widget(self.widget)", False, "属性参照は descriptor を起動しうる"),
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
        ('getattr(self, "debug")', False, "default 無し（production に無い形）"),
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


@pytest.mark.parametrize("name", sorted(debug_render.HEAVY_DIAGNOSTIC_CALLS | debug_render.UNBOUNDED_RENDER_CALLS))
def test_a_forbidden_call_is_caught_however_it_is_spelled(name):
    """``obj.f(x)`` でも ``from ... import f`` 後の ``f(x)`` でも同じ扱い。"""

    qualified = scan_source(
        "sample",
        "def f(self, value):\n"
        f"    self._debug_print(f'v={{owner.{name}(value)}}')\n",
    )
    direct = scan_source(
        "sample",
        "def f(self, value):\n"
        f"    self._debug_print(f'v={{{name}(value)}}')\n",
    )
    assert qualified.render_in_debug_sink, name
    assert direct.render_in_debug_sink, name


def test_a_direct_forbidden_call_is_caught_through_a_local():
    violations = scan_source(
        "sample",
        "def f(self, cond):\n"
        "    rendered = get_simplified_string(cond)\n"
        "    self._debug_print(rendered)\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_sink] == [
        "_debug_print(... rendered = get_simplified_string() ...)"
    ]


def test_a_bounded_renderer_through_a_local_still_needs_a_guard():
    """``summary = summarize_expression(expr)`` も debug OFF で走ってはいけない。"""

    unguarded = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    summary = summarize_expression(expr)\n"
        "    self._debug_print(summary)\n",
    )
    assert [entry[2] for entry in unguarded.unguarded_summary_in_debug_sink] == [
        "_debug_print(... summary = summarize_expression() ...)"
    ]

    guarded = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    if self.debug:\n"
        "        summary = summarize_expression(expr)\n"
        "        self._debug_print(summary)\n",
    )
    assert not guarded.unguarded_summary_in_debug_sink


def test_a_renderer_result_production_also_reads_is_not_a_debug_problem():
    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    summary = summarize_expression(expr)\n"
        "    record(summary)\n"
        "    self._debug_print(summary)\n",
    )
    assert not violations.unguarded_summary_in_debug_sink


@pytest.mark.parametrize(
    "call, accepted, label",
    [
        ("summarize_widget(widget)", True, "直接呼び出し"),
        ("self.summarize_widget(widget)", True, "self に束縛された method"),
        ("self._debug_reporter.summarize_widget(widget)", True, "宣言された reporter 1 段"),
        ("self.renderer.summarize_widget(widget)", False, "未宣言の受け手（property かもしれない）"),
        ("self.expensive_property.summarize_widget(widget)", False, "descriptor 経由"),
        ("expensive_factory().summarize_widget(widget)", False, "receiver で計算する"),
        ("registry[key].summarize_widget(widget)", False, "receiver が添字"),
        ("summarize_widget(self.expensive_property)", False, "引数が属性参照（descriptor）"),
        ("summarize_widget(container[index])", False, "引数が添字"),
    ],
)
def test_wrapper_call_target_and_arguments_are_fail_closed(call, accepted, label):
    source = (
        "class Host:\n"
        "    def _debug_widget_summary(self, widget, container, index, key):\n"
        f"        return {call}\n"
    )
    assert bool(_wrappers_in(source)) is accepted, label


#: owner が宣言した形（descriptor）から test 入力を作る。ここで production の
#: guard を書き写さない（書き写すと production / owner / test の 3 か所管理になる）。
_DECLARED_GUARD_SHAPES = sorted(DEBUG_GUARD_SHAPES, key=repr)


@pytest.mark.parametrize("shape", _DECLARED_GUARD_SHAPES, ids=repr)
def test_every_declared_guard_shape_round_trips(shape):
    """宣言 → 式 → descriptor が一致し、recognizer が受理すること。

    owner の宣言そのものを入力にしているので、test 側に guard 一覧の写しは無い。
    網羅性は :func:`test_the_declared_guard_shapes_are_exactly_the_ones_the_package_has`
    （production からの独立した棚卸し）が担保する。
    """

    node = ast.parse(guard_shape_source(shape), mode="eval").body
    assert guard_descriptor(node) == shape
    assert is_pure_debug_availability_test(node)


@pytest.mark.parametrize(
    "atom, label",
    [
        ("other.debug", "許可していない受け手"),
        ("factory().debug_available()", "受け手を計算する"),
        ("registry[key].debug", "受け手が添字"),
        ("self.debug_reporter.owner.debug", "受け手が 2 段より深い"),
        ("self._debug_available", "呼んでいない method object"),
        ("self.some_flag", "debug flag ではない"),
        ('getattr(factory(), "debug", False)', "getattr の受け手を計算する"),
        ('getattr(other, "debug", False)', "getattr の受け手が許可外"),
    ],
)
def test_an_unknown_guard_atom_is_refused(atom, label):
    assert not is_pure_debug_availability_test(ast.parse(atom, mode="eval").body), label


@pytest.mark.parametrize(
    "atom, label",
    [
        ("self.DEBUG", "flag 名だけ入れ替えた（実在しない）"),
        ("cls.debug", "受け手だけ入れ替えた（実在しない）"),
        ("context.DEBUG", "受け手と flag の組み合わせが実在しない"),
        ("strategy.debug_flag()", "述語を持たない受け手"),
        ("context._debug_available()", "述語を持たない受け手"),
        ("self.debug_reporter.debug_flag()", "受け手と述語の組み合わせが実在しない"),
        ('getattr(strategy, "DEBUG", False)', "getattr の受け手と属性が実在しない"),
        ("self.cache.debug_available()", "未知の受け手 path"),
        ("self.debug_reporter.owner.debug_available()", "受け手 path が 1 段深い"),
        ("cls.debug_reporter.debug_available()", "受け手 path の根が違う"),
    ],
)
def test_a_shape_that_only_exists_as_a_combination_is_refused(atom, label):
    """受け手 × flag × 述語の直積を作らない。

    3 つを別々の allow list で持つと、production に無い組み合わせまで guard と
    して通る。owner は **実在する形そのもの**を宣言し、判定は完全一致だけ。
    """

    assert not is_pure_debug_availability_test(ast.parse(atom, mode="eval").body), label


@pytest.mark.parametrize(
    "test_source, expected, label",
    [
        (
            "if self.debug and expr.to_string():\n    pass\n",
            ("render_in_debug_guard", "to_string()"),
            "後続 conjunct の full render は R1",
        ),
        (
            "if self.debug and get_simplified_string(cond):\n    pass\n",
            ("render_in_debug_guard", "get_simplified_string()"),
            "後続 conjunct の重い helper も R1",
        ),
        (
            "if self.debug and summarize_expression(expr):\n    pass\n",
            ("renderer_in_guard_condition", "summarize_expression()"),
            "後続 conjunct の renderer は R6",
        ),
        (
            "if self.debug and bounded_items(items):\n    pass\n",
            ("unguarded_debug_preparation", "bounded_items()"),
            "後続 conjunct の前準備は R5",
        ),
    ],
)
def test_work_after_the_debug_atom_in_an_and_guard_is_checked(test_source, expected, label):
    """``and`` の後続 conjunct は debug 専用経路として検査する。

    branch が guarded と判定されても、条件式の中でやっている仕事は見逃さない。
    """

    source = "def f(self, expr, cond, items):\n" + "".join(
        "    " + line if line.strip() else line for line in test_source.splitlines(True)
    )
    violations = scan_source("sample", source)
    bucket, detail = expected
    assert [entry[2] for entry in getattr(violations, bucket)] == [detail], label


@pytest.mark.parametrize(
    "condition",
    [
        "self.debug and items",
        "self.debug and count > 0",
        "self.debug and expr is not None",
        "self._debug_available() and tracked",
    ],
)
def test_a_cheap_second_conjunct_is_still_fine(condition):
    """production の正当な形（安い真偽判定）は通す。"""

    violations = scan_source(
        "sample",
        "def f(self, expr, items, tracked, count):\n"
        f"    if {condition}:\n"
        "        self._debug_print('x')\n",
    )
    assert not violations, violations.describe()


def test_a_renderer_read_only_in_a_guard_condition_is_caught():
    """代入 1 段で条件式へ渡す形も同じ（debug OFF でも renderer は走る）。"""

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    summary = summarize_expression(expr)\n"
        "    if self.debug and summary:\n"
        "        self._debug_print(summary)\n",
    )
    assert [entry[2] for entry in violations.renderer_in_guard_condition] == [
        "summary = summarize_expression()"
    ]


def test_a_forbidden_call_read_only_in_a_guard_condition_is_caught():
    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    rendered = expr.to_string()\n"
        "    if self.debug and rendered:\n"
        "        self._debug_print(rendered)\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_guard] == [
        "rendered = to_string()"
    ]


def test_a_value_production_also_uses_is_not_a_guard_condition_problem():
    """production も読む値は対象外（過検出で production を書き換えない）。"""

    violations = scan_source(
        "sample",
        "def f(self, expr, solver):\n"
        "    smt = expr.to_smt()\n"
        "    solver.add(smt)\n"
        "    if self.debug and smt:\n"
        "        self._debug_print('x')\n",
    )
    assert not violations.renderer_in_guard_condition
    assert not violations.render_in_debug_guard


def test_a_negated_and_guard_also_checks_the_work_after_the_atom():
    """``if not (self.debug and heavy()): return`` も debug ON でだけ heavy が走る。"""

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    if not (self.debug and expr.to_string()):\n"
        "        return\n"
        "    self._debug_print('x')\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_guard] == ["to_string()"]


def observed_guard_shapes(root: Path = PACKAGE_ROOT) -> Dict[debug_render.GuardShape, str]:
    """production の **guard 候補**を、recognizer も allow list も使わずに集める。

    「recognizer が認めたものを数える」と、未知の guard が増えても recognizer が
    拒否した時点で観測から消え、棚卸し test が PASS してしまう（契約が実測から
    ずれていても気付けない）。そこで、まず AST から候補を独立に取り出し、
    canonical descriptor にしてから owner の宣言と突き合わせる。

    候補の位置は「短絡評価で必ず最初に評価される」ところ（:func:`short_circuit_head`）:
    ``if <expr>:`` / ``if not <expr>: return`` / ``and`` ・ ``or`` の先頭項。
    そのうち **debug を含む名前が出てくる**式だけを候補とする（名前で絞るのは
    観測の範囲を決めるためで、guard かどうかの判定ではない）。

    canonical descriptor に落とせない式（比較・引数付き呼び出しなど）は捨てず、
    :func:`unsupported_guard_descriptor` の形で観測に残す。捨てると descriptor
    文法の外側で fail-open になり、``if self.debug is True:`` のような未知形を
    足しても棚卸しが素通りしてしまう。

    返り値は descriptor → 最初に見つけた場所（FAIL したとき直せるように）。
    """

    observed: Dict[debug_render.GuardShape, str] = {}
    for path in _iter_source_files(root):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if not isinstance(node, (ast.If, ast.IfExp)):
                continue
            atom = short_circuit_head(node.test)
            shape = guard_descriptor(atom)
            if shape is not None:
                name = shape[1] if shape[0] == "name" else shape[2]
                if not _mentions_debug(name):
                    continue
            elif _debug_names_in(atom):
                # descriptor 文法の外でも捨てない（捨てると未知形が観測から
                # 消えて、棚卸しが文法の外側で fail-open になる）。
                shape = unsupported_guard_descriptor(atom)
            else:
                continue
            observed.setdefault(shape, f"{path.relative_to(root)}:{node.lineno}")
    return observed


def test_the_declared_guard_shapes_are_exactly_the_ones_the_package_has():
    """宣言した exact shape と実測がずれたら FAIL（両方向）。

    * production に未知の debug guard を 1 つ足す → 観測にだけ現れて FAIL。
      足した人は「guard として認める」(:data:`DEBUG_GUARD_SHAPES`) か
      「名前は debug でも guard ではない」(:data:`DEBUG_SHAPED_NON_GUARDS`) かを
      owner で明示することになる。
    * production から消えた形が宣言に残っている → 宣言にだけ現れて FAIL。

    受け手 / flag 名 / 述語名の直積ではなく **形そのもの**を宣言しているので、
    ``self.DEBUG`` や ``strategy.debug_flag()`` のような実在しない組み合わせは
    そもそも宣言に現れない。
    """

    observed = observed_guard_shapes()
    declared = DEBUG_GUARD_SHAPES | DEBUG_SHAPED_NON_GUARDS
    missing = {shape: where for shape, where in observed.items() if shape not in declared}
    stale = declared - set(observed)
    assert not missing, f"undeclared debug guard shapes: {missing}"
    assert not stale, f"declared shapes no longer in the package: {sorted(stale)}"


def observed_render_call_targets(root: Path = PACKAGE_ROOT) -> Dict[debug_render.RenderCallTarget, str]:
    """production が renderer / 前準備 helper を **どの形で呼んでいるか**。

    guard の棚卸しと同じ考え方で、宣言（:data:`DEBUG_RENDER_CALL_TARGETS`）が
    実測からずれたら気付けるようにするための観測。表せない形（receiver を計算
    する形）は ``None`` キーで残すので、黙って落ちることはない。
    """

    renderers = bounded_renderer_names(root)
    observed: Dict[debug_render.RenderCallTarget, str] = {}
    for path in _iter_source_files(root):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            if _called_name(node) not in renderers | PREPARATION_FUNCTIONS:
                continue
            observed.setdefault(
                call_target_shape(node.func), f"{path.relative_to(root)}:{node.lineno}"
            )
    return observed


def test_the_declared_render_call_targets_are_the_ones_the_package_uses():
    """renderer を呼ぶ形の宣言が実測とずれたら FAIL（両方向）。

    広がる方向のずれは「使っていない受け手まで有界な描画とみなす」＝ contract の
    緩み、狭まる方向は stale。どちらも owner を直す合図。
    """

    observed = observed_render_call_targets()
    assert None not in observed, f"renderer called on a computed receiver: {observed.get(None)}"
    assert set(observed) == set(DEBUG_RENDER_CALL_TARGETS)


@pytest.mark.parametrize(
    "call, safe, label",
    [
        ("summarize_expression(expr)", True, "素の関数呼び出し"),
        ("self.summarize_expression(expr)", True, "self に束縛された method"),
        ("cls.summarize_expression(expr)", True, "cls に束縛された method"),
        ("self.debug_reporter.summarize_expression(expr)", True, "宣言された reporter"),
        ("self._debug_reporter.summarize_expression(expr)", True, "宣言された reporter"),
        ("self.expensive_property.summarize_expression(expr)", False, "descriptor 経由"),
        ("self.a.b.summarize_expression(expr)", False, "未宣言の 2 段"),
        ("other.summarize_expression(expr)", False, "未宣言の受け手"),
        ("expensive_factory().summarize_expression(expr)", False, "receiver を計算する"),
        ("registry[key].summarize_expression(expr)", False, "receiver が添字"),
    ],
)
def test_a_renderer_is_only_bounded_when_its_target_is_declared(call, safe, label):
    node = ast.parse(call, mode="eval").body
    kind, _ = _summary_call(node, frozenset({"summarize_expression"}))
    assert (kind == "renderer") is safe, label
    assert kind in ("renderer", "unsafe_renderer")


@pytest.mark.parametrize(
    "reader, bucket",
    [
        ("    self._debug_print(summary)\n", "render_in_debug_sink"),
        ("    if self.debug and summary:\n        self._debug_print('x')\n",
         "renderer_in_guard_condition"),
    ],
)
def test_an_unsafe_renderer_survives_a_local_assignment(reader, bucket):
    """局所変数を 1 つ挟んでも、契約外の対象で呼んだ renderer は通さない。"""

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    summary = expensive_factory().summarize_expression(expr)\n"
        + reader,
    )
    entries = [entry[2] for entry in getattr(violations, bucket)]
    assert entries and all("summarize_expression" in entry for entry in entries), entries


def test_an_unsafe_renderer_is_refused_inside_a_debug_guard_too():
    """guard の中でも不可（receiver の構築は debug ON でも任意処理）。"""

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    if self.debug:\n"
        "        self._debug_print(self.expensive_property.summarize_expression(expr))\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_sink] == [
        "_debug_print(... <computed>.summarize_expression() ...)"
    ]


@pytest.mark.parametrize(
    "test_source, label",
    [
        ("self.debug is True", "比較（descriptor 文法の外）"),
        ("debug_available(config)", "引数付きの述語呼び出し"),
        ("some_debug_expression(a, b)", "未知の debug 複合式"),
        ("self.debug_level > 0 and other", "`and` の先頭項が未知の複合式"),
    ],
)
def test_an_unknown_debug_shape_outside_the_grammar_is_still_observed(tmp_path, test_source, label):
    """descriptor に落とせない未知形も棚卸しに残る（文法の外でも fail-closed）。"""

    package = tmp_path / "pkg"
    package.mkdir()
    (package / "sample.py").write_text(
        f"def f(self, config, a, b, other, fallback_debug_flag):\n"
        f"    if {test_source}:\n"
        f"        pass\n",
        encoding="utf-8",
    )
    observed = set(observed_guard_shapes(package))
    assert observed, label
    assert all(shape[0] == "unsupported" for shape in observed), observed
    # 宣言に無いので、これを production へ足すと棚卸し test が FAIL する。
    assert not observed & (DEBUG_GUARD_SHAPES | DEBUG_SHAPED_NON_GUARDS), label


def test_a_comparison_on_a_guard_flag_is_not_confused_with_an_unrelated_one(tmp_path):
    """``self.debug is True`` と ``type(debug) is not bool`` を別物として扱う。"""

    left = unsupported_guard_descriptor(ast.parse("self.debug is True", mode="eval").body)
    right = unsupported_guard_descriptor(ast.parse("type(debug) is not bool", mode="eval").body)
    assert left != right
    # 後者は production に実在するので宣言済み、前者は未知。
    assert right in DEBUG_SHAPED_NON_GUARDS
    assert left not in (DEBUG_GUARD_SHAPES | DEBUG_SHAPED_NON_GUARDS)


@pytest.mark.parametrize(
    "sources",
    [
        [
            "type(debug) is not bool",
            "type(debug) is bool",
            "type(debug) == bool",
            "type(debug) != bool",
        ],
        ["self.debug is True", "self.debug is False"],
        ["self.debug > 0", "self.debug >= 0", "self.debug < 0"],
        ["debug_available(config)", "debug_available(other)", "debug_enabled(config)"],
    ],
)
def test_unsupported_descriptors_do_not_collide(sources):
    """意味の違う式は別 descriptor（衝突すると未知形が baseline に紛れる）。"""

    descriptors = [
        unsupported_guard_descriptor(ast.parse(source, mode="eval").body)
        for source in sources
    ]
    assert len(set(descriptors)) == len(sources), descriptors


def test_an_unsupported_descriptor_is_deterministic_and_location_free():
    """同値な構文は同じ descriptor。行や空白・括弧には依存しない。"""

    first = unsupported_guard_descriptor(ast.parse("self.debug is True", mode="eval").body)
    again = unsupported_guard_descriptor(ast.parse("self.debug is True", mode="eval").body)
    spaced = unsupported_guard_descriptor(
        ast.parse("(  self.debug   is   True  )", mode="eval").body
    )
    moved = unsupported_guard_descriptor(
        ast.parse("\n\n\nself.debug is True", mode="eval").body
    )
    assert first == again == spaced == moved
    assert "lineno" not in first[1] and "col_offset" not in first[1]


def test_a_new_unknown_guard_does_not_collide_with_the_existing_baseline():
    """未知形が既存 baseline と偶然一致して素通りしないこと。"""

    unknown = {
        unsupported_guard_descriptor(ast.parse(source, mode="eval").body)
        for source in (
            "self.debug is True",
            "self.debug is False",
            "type(debug) is bool",
            "debug_available(config)",
            "self.debug_level > 0",
        )
    }
    assert not unknown & (DEBUG_GUARD_SHAPES | DEBUG_SHAPED_NON_GUARDS)


_NESTED_SCOPE_SHADOWS = [
    (
        "内側の def が同名 parameter を持つ",
        "    def unrelated(summary):\n"
        "        consume(summary)\n",
    ),
    (
        "内側の lambda が同名 parameter を持つ",
        "    unrelated = lambda summary: consume(summary)\n",
    ),
    (
        "内側の class の method が同名 local を持つ",
        "    class Holder:\n"
        "        def take(self, summary):\n"
        "            return consume(summary)\n",
    ),
    (
        "内側の comprehension が同名を束縛する",
        "    consumed = [consume(summary) for summary in items]\n",
    ),
]


@pytest.mark.parametrize(
    "label, nested", _NESTED_SCOPE_SHADOWS, ids=[case[0] for case in _NESTED_SCOPE_SHADOWS]
)
def test_a_nested_scope_with_the_same_name_does_not_hide_an_unguarded_summary(label, nested):
    """内側 scope の同名変数があっても外側の R3 判定は変わらない。"""

    violations = scan_source(
        "sample",
        "def f(self, expr, items, consume):\n"
        "    summary = summarize_expression(expr)\n"
        + nested
        + "    self._debug_print(summary)\n",
    )
    assert [entry[2] for entry in violations.unguarded_summary_in_debug_sink] == [
        "_debug_print(... summary = summarize_expression() ...)"
    ], label


@pytest.mark.parametrize(
    "label, nested", _NESTED_SCOPE_SHADOWS, ids=[case[0] for case in _NESTED_SCOPE_SHADOWS]
)
def test_a_nested_scope_with_the_same_name_does_not_hide_a_forbidden_call(label, nested):
    violations = scan_source(
        "sample",
        "def f(self, expr, items, consume):\n"
        "    summary = expr.to_string()\n"
        + nested
        + "    self._debug_print(summary)\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_sink] == [
        "_debug_print(... summary = to_string() ...)"
    ], label


def test_a_nested_scope_name_is_not_attributed_to_the_outer_local():
    """逆向きも: 内側 scope の同名読み出しを外側の追跡結果と取り違えない。"""

    violations = scan_source(
        "sample",
        "def f(self, expr, apply):\n"
        "    summary = summarize_expression(expr)\n"
        "    if self.debug:\n"
        "        self._debug_print(summary)\n"
        "    apply(lambda summary: self._debug_print(summary))\n",
    )
    # 外側は guard 内なので R3 ではない。内側 lambda の ``summary`` は別の束縛
    # （引数）なので、それを外側の renderer 結果として報告してはいけない。
    assert not violations.unguarded_summary_in_debug_sink, violations.describe()


def test_a_nested_scope_is_still_analysed_on_its_own():
    """内側 scope を無視するのではなく、独立した scope として解析する。"""

    violations = scan_source(
        "sample",
        "def outer(self, expr):\n"
        "    def inner(self, expr):\n"
        "        summary = summarize_expression(expr)\n"
        "        self._debug_print(summary)\n"
        "    return inner\n",
    )
    assert [entry[2] for entry in violations.unguarded_summary_in_debug_sink] == [
        "_debug_print(... summary = summarize_expression() ...)"
    ]


def test_a_comprehensions_first_iterable_is_still_an_outer_read():
    """``[f(x) for x in smt]`` の ``smt`` は外側の読み出し（過検出しないため）。"""

    violations = scan_source(
        "sample",
        "def f(self, expr, g):\n"
        "    smt = expr.to_smt()\n"
        "    kept = [g(x) for x in smt]\n"
        "    self._debug_print(smt)\n"
        "    return kept\n",
    )
    assert not violations.render_in_debug_sink, violations.describe()


def test_a_value_production_also_uses_is_still_exempt_across_scopes():
    """production も読む値は従来どおり対象外（過検出しない）。"""

    violations = scan_source(
        "sample",
        "def f(self, expr, solver):\n"
        "    smt = expr.to_smt()\n"
        "    solver.add(smt)\n"
        "    self._debug_print(smt)\n",
    )
    assert not violations.render_in_debug_sink, violations.describe()


# -- A1: 関数 header は定義側の scope -----------------------------------------

@pytest.mark.parametrize(
    "header, label",
    [
        ("def g(self, expr, x=summary):", "default 引数"),
        ("def g(self, expr, x: summary = None):", "annotation"),
        ("def g(self, expr) -> summary:", "戻り値 annotation"),
        ("@decorate(summary)\n    def g(self, expr):", "decorator"),
    ],
)
def test_a_function_header_name_is_not_a_body_read(header, label):
    """header は関数を **定義する側**で評価される。body local の read ではない。"""

    violations = scan_source(
        "sample",
        "summary = object()\n"
        "class Host:\n"
        f"    {header}\n"
        "        summary = summarize_expression(expr)\n"
        "        self._debug_print(summary)\n",
    )
    assert [entry[2] for entry in violations.unguarded_summary_in_debug_sink] == [
        "_debug_print(... summary = summarize_expression() ...)"
    ], label


def test_a_nested_function_header_reads_the_outer_name():
    """逆向き: 内側 ``def`` の default は外側の名前を読む（過検出しない）。"""

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    summary = summarize_expression(expr)\n"
        "    def inner(x=summary):\n"
        "        return x\n"
        "    self._debug_print(summary)\n"
        "    return inner\n",
    )
    # 外側 ``summary`` は sink 以外（inner の default）でも読まれているので
    # production 共有として免除される。
    assert not violations.unguarded_summary_in_debug_sink, violations.describe()


# -- A2: 同名への再代入 --------------------------------------------------------

@pytest.mark.parametrize(
    "producer, bucket, detail",
    [
        ("summarize_expression(b)", "unguarded_summary_in_debug_sink",
         "_debug_print(... summary = summarize_expression() ...)"),
        ("b.to_string()", "render_in_debug_sink",
         "_debug_print(... summary = to_string() ...)"),
        ("expensive_factory().summarize_expression(b)", "render_in_debug_sink",
         "_debug_print(... summary = <computed>.summarize_expression() ...)"),
    ],
)
def test_a_later_debug_only_assignment_is_not_exempted_by_an_earlier_one(
    producer, bucket, detail
):
    """前の代入が production に読まれていても、後の debug 専用代入は別物。"""

    violations = scan_source(
        "sample",
        "def f(self, a, b, consume):\n"
        "    summary = summarize_expression(a)\n"
        "    consume(summary)\n"
        f"    summary = {producer}\n"
        "    self._debug_print(summary)\n",
    )
    assert [entry[2] for entry in getattr(violations, bucket)] == [detail]


def test_a_later_unsafe_renderer_assignment_is_caught_in_a_guard_condition():
    violations = scan_source(
        "sample",
        "def f(self, a, b, consume):\n"
        "    summary = summarize_expression(a)\n"
        "    consume(summary)\n"
        "    summary = expensive_factory().summarize_expression(b)\n"
        "    if self.debug and summary:\n"
        "        self._debug_print('x')\n",
    )
    assert [entry[2] for entry in violations.renderer_in_guard_condition] == [
        "summary = <computed>.summarize_expression()"
    ]


def test_an_earlier_debug_only_assignment_is_not_excused_by_a_later_production_one():
    """順序が逆でも、debug 専用の代入は debug 専用のまま。"""

    violations = scan_source(
        "sample",
        "def f(self, a, b, consume):\n"
        "    summary = summarize_expression(a)\n"
        "    self._debug_print(summary)\n"
        "    summary = compute(b)\n"
        "    consume(summary)\n",
    )
    assert [entry[2] for entry in violations.unguarded_summary_in_debug_sink] == [
        "_debug_print(... summary = summarize_expression() ...)"
    ]


def test_a_single_assignment_production_also_reads_is_still_exempt():
    """1 回だけの代入で production も読む値は従来どおり免除。"""

    violations = scan_source(
        "sample",
        "def f(self, expr, solver):\n"
        "    smt = expr.to_smt()\n"
        "    solver.add(smt)\n"
        "    self._debug_print(smt)\n",
    )
    assert not violations.render_in_debug_sink, violations.describe()


def test_repeated_production_assignments_stay_exempt():
    """``key = a.stable_key()`` … ``key = b.stable_key()`` 型（本 package に実在）。"""

    violations = scan_source(
        "sample",
        "def f(self, a, b, store):\n"
        "    key = a.stable_key()\n"
        "    store(key)\n"
        "    key = b.stable_key()\n"
        "    store(key)\n",
    )
    assert not violations, violations.describe()


# -- A3: 評価のタイミング ------------------------------------------------------

def test_a_lambda_body_is_not_evaluated_where_it_is_written():
    """``thunk = lambda: expr.to_string()`` は代入の時点では何も描画しない。"""

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    if self.debug:\n"
        "        thunk = lambda: expr.to_string()\n"
        "        return thunk\n",
    )
    assert not violations.render_in_debug_guard, violations.describe()


def test_a_lambda_default_is_evaluated_where_it_is_written():
    """default 引数は定義時に評価されるので、そこは今の文脈で見る。"""

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    if self.debug:\n"
        "        thunk = lambda rendered=expr.to_string(): rendered\n"
        "        return thunk\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_guard] == ["to_string()"]


def test_a_lambda_body_is_still_analysed_as_its_own_scope():
    """無視しているのではない: 本体の中の sink は別 scope として検出する。"""

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    return lambda: self._debug_print(summarize_expression(expr))\n",
    )
    assert [entry[2] for entry in violations.unguarded_summary_in_debug_sink] == [
        "_debug_print(... summarize_expression() ...)"
    ]


def test_a_comprehension_is_evaluated_where_it_is_written():
    """comprehension は遅延しない（generator 式も含め、その場で組み立てる）。"""

    violations = scan_source(
        "sample",
        "def f(self, conditions):\n"
        "    if self.debug:\n"
        "        rendered = [c.to_string() for c in conditions]\n"
        "        return rendered\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_guard] == ["to_string()"]


def test_a_class_body_is_evaluated_where_it_is_written():
    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    if self.debug:\n"
        "        class Holder:\n"
        "            rendered = expr.to_string()\n"
        "        return Holder\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_guard] == ["to_string()"]


def test_the_two_declared_sets_do_not_overlap():
    """同じ形を「guard」と「guard ではない」の両方に置かない。"""

    assert not (DEBUG_GUARD_SHAPES & DEBUG_SHAPED_NON_GUARDS)


def test_a_new_unknown_guard_shape_would_be_noticed(tmp_path):
    """棚卸しが non-vacuous か: 未知の形を 1 つ置いたら観測に現れる。"""

    package = tmp_path / "pkg"
    package.mkdir()
    (package / "sample.py").write_text(
        "def f(self):\n"
        "    if self.cache.debug_available():\n"
        "        pass\n"
        "    if self.debug:\n"
        "        pass\n",
        encoding="utf-8",
    )
    observed = observed_guard_shapes(package)
    assert ("call", ("self", "cache"), "debug_available") in observed
    assert ("call", ("self", "cache"), "debug_available") not in DEBUG_GUARD_SHAPES
    # 既知の形は観測されても宣言済みなので FAIL の原因にならない。
    assert ("attr", ("self",), "debug") in DEBUG_GUARD_SHAPES


def test_the_inventory_does_not_go_through_the_recognizer(tmp_path):
    """棚卸しは recognizer に依存しない（拒否された形も観測に残る）。"""

    package = tmp_path / "pkg"
    package.mkdir()
    (package / "sample.py").write_text(
        "def f(self, registry, key, factory, other):\n"
        "    if registry[key].debug:\n"
        "        pass\n"
        "    if factory().debug_available():\n"
        "        pass\n"
        "    if other.debug:\n"
        "        pass\n",
        encoding="utf-8",
    )
    observed = set(observed_guard_shapes(package))
    assert observed == {
        ("attr", COMPUTED_RECEIVER, "debug"),
        ("call", COMPUTED_RECEIVER, "debug_available"),
        ("attr", ("other",), "debug"),
    }
    # どれも recognizer は拒否する。観測されることと認めることは別。
    assert not observed & DEBUG_GUARD_SHAPES


@pytest.mark.parametrize(
    "test_source, guarded, label",
    [
        ("self.debug and force", True, "debug が先頭"),
        ("self.debug_flag() and items and other", True, "debug が先頭（3 項）"),
        ("force and self.debug", False, "debug より前に別の条件がある"),
        ("summarize_expression(expr) and self.debug", False, "renderer が先に走る"),
        ("bounded_items(items) and self.debug", False, "前準備が先に走る"),
        ("expr.to_string() and self.debug", False, "full render が先に走る"),
        ("self.debug or force", False, "or"),
    ],
)
def test_an_and_guard_must_evaluate_debug_first(test_source, guarded, label):
    """短絡評価で「debug OFF なら診断処理が走らない」を保証できる形だけ。"""

    node = ast.parse(test_source, mode="eval").body
    assert branch_implies_debug_enabled(node) is guarded, label


def test_a_renderer_called_on_a_computed_receiver_is_refused():
    """renderer の名前でも、受け手を組み立てて呼ぶ形は有界とみなさない。"""

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    if self.debug:\n"
        "        self._debug_print(f'{expensive_factory().summarize_expression(expr)}')\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_sink] == [
        "_debug_print(... <computed>.summarize_expression() ...)"
    ]


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

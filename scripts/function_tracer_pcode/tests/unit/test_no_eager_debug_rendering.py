# -*- coding: utf-8 -*-
"""debug 出力のための eager rendering を静的に禁止する guard（Issue #22 PR-22-A）。

`Expression.to_string()` / `to_smt()` / `repr()` は DAG を木として展開するので、
巨大式では debug の有無に関わらず解析時間を食う。debug message のために
これらを呼ぶと、``--debug`` を付けていなくても引数が先に評価される（helper が
関数の中で flag を見ても遅い）。本 test は AST 走査でその形を 0 件に固定する。

走査の責務は 2 つに分かれていて、helper を互いに流用しない:

* **検出** — 違反を見つける。debug sink / guard / 入れ子の並びまで必要なだけ辿る
  （:func:`statement_scope_nodes` / :func:`walk_evaluated_now`）
* **alias の追跡** — 一段だけ。**問いは 3 つで、混ぜない**:

  * producer origin :func:`tracked_producer_bindings` — producer の戻り値が
    どの名前に入ったか。**target × RHS root の両方**が条件を満たすときだけ追う:
    単一の局所 ``Name`` と、:func:`direct_tracked_producer`（RHS root そのものが
    producer）。``rendered = consume(expr.to_string())`` は producer が **走る**
    だけで ``rendered`` はその戻り値を受けていないので alias ではない（本 package
    に 145 箇所。root が producer なのは 191 箇所）。direct producer を chained /
    分解 / ``AugAssign`` / ``:=`` で束縛する形は、値と名前の対応を解かずに
    **B1 で拒否**する
  * rebind（**MUST**）:func:`statement_rebinds` — この文を実行したら **必ず**
    別の値へ束縛し直すか。window の終端
  * production 共有（**MUST**）:func:`_has_direct_production_read` — この区間で
    production が **必ず**読むか。読むなら免除

  構文の意味づけは positive grammar の owner が持ち、どれも whitelist（載って
  いない形は証拠ゼロ / 不明）: :func:`direct_production_expressions`（statement）、
  :func:`direct_production_reads`（expression）、:func:`bound_names`（binding
  構文の認識）。**構文を認識できることと provenance を言えることは別**で、後者は
  producer origin の狭い表が答える。「広く見てから条件で削る」のではなく、
  最初から狭い positive set

**この checker が保証すること / しないこと。**

保証する（すべて局所的な構文規則）:

1. debug 専用の renderer / 前準備は、明示的な debug guard の外で走らせない
2. ``to_string`` / ``to_smt`` / 重い診断 helper を debug 整形のために起動しない
3. debug sink の引数で契約外 / 無制限の renderer を起動しない
4. debug 専用の下ごしらえ（一度変数へ入れる形）は guard の中に置く
5. bounded renderer の wrapper は owner contract への単純委譲だけ
6. guard の形は owner の exact contract に一致するものだけ

**保証しない**: 「任意の Python コードを解析して、実行時にその値がどの代入から
来たかを証明すること」。分岐・loop・例外を跨いだ値の追跡はしない（簡易 CFG も
reaching definition も持たない）。曖昧な production site は checker を賢くする
のではなく、canonical な書き方へ寄せる:

.. code-block:: python

    if self._debug_available():
        summary = summarize_expression(expr)
        self._debug_print(summary)

責務は 3 つに分かれている:

* **debug contract** — ``analysis/debug/render.py``（何を guard / 有界な描画 /
  前準備 / 禁止呼び出しと認めるか）
* **実行領域の walker** — :func:`evaluation_region` と、そこから導かれる
  :func:`walk_evaluated_now` / :func:`walk_lexical_scope`。Python の
  「今走るか / 後で走るか / どこから別束縛か」だけを担当する
* **debug 規則の checker** — 下の R1〜R6。局所的な構文だけを見る

固定する 6 つの契約（と、追えない束縛を拒否する B1）:

* **R1** debug guard の中で禁止呼び出し（``analysis.debug.render`` の
  :data:`UNBOUNDED_RENDER_CALLS` と :data:`HEAVY_DIAGNOSTIC_CALLS`、および
  ``repr()`` / ``getattr(x, "to_string")()``）を呼ばない。guard の中は debug
  専用なので、そこにある full render や重い診断 helper は「debug のためだけに
  入力を辿っている」ことを意味する。
* **R2** debug sink（``print`` と名前に ``debug`` を含む呼び出し）の引数に
  禁止呼び出し（と契約外の renderer）を含めない。guard の有無に関わらず禁止
  （debug ON でも辿らない）。引数に直接書いた場合だけでなく、**一度変数へ入れて
  から渡す形**も見る（one-hop alias）。``to_string`` / ``to_smt`` は production
  でも正当に使うので、免除は :func:`direct_production_expressions` が認めた
  **直接式**に読み出しが見えるときだけ（statement 種別ごとの positive な表）。
* **R3** bounded renderer（``summarize_expression`` 等）を呼んでよいのは
  debug guard の中だけ。renderer は有界だが、debug OFF のときに走らせる理由が
  無い。**値の行き先は見ない — 呼んだ場所だけで決まる。** 例外は棚卸しで出た
  3 つ（契約の owner module / 別の renderer の定義の中 / ``__repr__`` ・
  ``__str__``）で、production 全体でもその 3 つしか無い。
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

代入 1 段の追跡が要るのは **forbidden / unsafe renderer だけ**。あれらは
production でも正当に使う呼び出しなので、「debug のためだけに作ったか」を見ないと
判断できない。bounded renderer は R3 が呼んだ場所で決めるので追跡しない。

追跡の担当範囲は「その代入から、**同じ文の並び**で次に同じ名前へ代入する文まで」。
**production 共有の免除も、その範囲の中に debug 以外の読み出しが構文として見える
ときだけ**与える。別 branch・loop・``try``・入れ子 scope の読み出しは、そこを本当に
通るかが control flow 次第なので免除の根拠にしない（証明できなければ免除しない）。

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
from typing import (
    Callable,
    Dict,
    FrozenSet,
    Iterator,
    List,
    NamedTuple,
    Optional,
    Sequence,
    Set,
    Tuple,
)

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
    """6 契約（R1〜R6）と binding contract の違反。すべて空なら PASS。"""

    render_in_debug_guard: List[Tuple[str, int, str]] = field(default_factory=list)
    render_in_debug_sink: List[Tuple[str, int, str]] = field(default_factory=list)
    renderer_outside_a_guard: List[Tuple[str, int, str]] = field(default_factory=list)
    render_in_dunder: List[Tuple[str, int, str]] = field(default_factory=list)
    unguarded_debug_preparation: List[Tuple[str, int, str]] = field(default_factory=list)
    renderer_in_guard_condition: List[Tuple[str, int, str]] = field(default_factory=list)
    unsupported_producer_binding: List[Tuple[str, int, str]] = field(default_factory=list)

    def __bool__(self) -> bool:
        return bool(
            self.render_in_debug_guard
            or self.render_in_debug_sink
            or self.renderer_outside_a_guard
            or self.render_in_dunder
            or self.unguarded_debug_preparation
            or self.renderer_in_guard_condition
            or self.unsupported_producer_binding
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
        for module, lineno, detail in self.renderer_outside_a_guard:
            lines.append(
                f"R3 {module}:{lineno}: {detail} runs outside a debug guard; "
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
        for module, lineno, detail in self.unsupported_producer_binding:
            lines.append(
                f"B1 {module}:{lineno}: {detail} binds the value of a tracked debug "
                "producer through a shape whose provenance this contract deliberately "
                "does not follow; give the producer its own plain local name first "
                "(`name = <producer>`) and read that name, or -- only when the shape "
                "itself has to become supported -- widen the producer-binding "
                "contract in tracked_producer_bindings() on purpose"
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
      有界なので debug guard の中でだけ使ってよい（R3。判定は呼んだ場所だけ）。
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


class Region(NamedTuple):
    """1 つの構文が作る **評価の領域**。

    Python の「どこが今走り、どこが後で走り、どこから名前の束縛が変わるか」を
    この 1 か所だけで定義する。scanner も代入の分類も棚卸しも、ここから導かれた
    走査を使う（同じ規則を helper ごとに書き直さない）。

    * ``now`` — その構文を評価した **その場で**走る部分式
    * ``deferred`` — 後で（呼び出し時 / 反復時に）走る部分式。作成地点の debug
      guard は継承しない
    * ``binds`` — ``deferred`` 側が別の名前空間か（局所名の追跡を持ち込まない）
    """

    now: List[ast.AST]
    deferred: List[ast.AST]
    binds: bool


def _header_parts(node: ast.AST, *, annotations: bool = True) -> List[ast.AST]:
    """``def`` / ``lambda`` / ``class`` の header（定義する側で評価される部分）。

    decorator / default 引数 / base class / keyword は、関数や class を作る
    その場で必ず評価され、外側の名前を読む（``def f(x=summary):`` の ``summary``
    は外側の ``summary``）。

    **annotation は module 次第**。``from __future__ import annotations`` がある
    module では文字列として保存されるだけで評価されない（本 package の production
    module 250 個がこれを使っている）。``annotations=False`` で外せる:

    * **免除の証明**では外す — 評価されるとは限らないものを production 共有の
      証拠にできない。これで exemption 側は module mode に依存しなくなる。
    * **検出**では入れたまま（安全側）。annotation の中で禁止呼び出しを走らせて
      いれば報告する。future import がある module では実際には走らないので
      過検出になり得るが、本 package の annotation 25,273 個のうち禁止呼び出し /
      renderer / 前準備を含むものは **0 件**で、どちらに倒しても現状は同じ。
      module 単位の評価モードを持ち込むより、安全側 1 つで済ませる。
    """

    parts: List[ast.AST] = []
    arguments = getattr(node, "args", None)
    if isinstance(arguments, ast.arguments):
        parts += [default for default in arguments.defaults if default is not None]
        parts += [default for default in arguments.kw_defaults if default is not None]
        if annotations:
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
    if annotations and returns is not None:
        parts.append(returns)
    return parts


def _comprehension_parts(node: ast.AST) -> Tuple[List[ast.AST], List[ast.AST]]:
    """comprehension を「最初の iterable」と「残り」に割る。

    最初の iterable だけは **外側の scope で、その場で**評価される
    （``[f(x) for x in items]`` の ``items``）。要素式・filter・2 本目以降の
    ``for`` の iterable は comprehension 自身の名前空間で走る。
    """

    generators = list(getattr(node, "generators", []))
    if not generators:
        return ([], [])
    first, rest = generators[0], generators[1:]
    inside: List[ast.AST] = []
    for field in ("elt", "key", "value"):
        part = getattr(node, field, None)
        if part is not None:
            inside.append(part)
    inside += list(first.ifs)
    for generator in rest:
        inside.append(generator.iter)
        inside += list(generator.ifs)
    return ([first.iter], inside)


def evaluation_region(node: ast.AST) -> Optional[Region]:
    """``node`` が作る :class:`Region`。領域を作らない構文なら ``None``。

    ``None`` は「ふつうの部分式なので、そのまま辿ってよい」の意味。

    ========================  ====================  ======================  ======
    構文                       今評価                 後で評価                 別束縛
    ========================  ====================  ======================  ======
    ``FunctionDef``           header                body                    yes
    ``AsyncFunctionDef``      header                body                    yes
    ``Lambda``                header(default 等)     body                    yes
    ``ClassDef``              header + body         --                      yes
    ``ListComp``              最初の iterable + 中   --                      yes
    ``SetComp``               最初の iterable + 中   --                      yes
    ``DictComp``              最初の iterable + 中   --                      yes
    ``GeneratorExp``          最初の iterable        要素 / filter / 2本目以降  yes
    ========================  ====================  ======================  ======

    ``GeneratorExp`` だけ中身が後回しなのは、generator が作成時には何も走らせず
    反復時に走るため。``if self.debug: gen = (render(x) for x in items)`` の
    ``render(x)`` は作成地点の guard の中にあるが、実際に走るのは反復時なので
    その guard を継承させてはいけない。
    """

    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return Region(_header_parts(node), list(node.body), True)
    if isinstance(node, ast.Lambda):
        return Region(_header_parts(node), [node.body], True)
    if isinstance(node, ast.ClassDef):
        # 本体はその場で走るが、名前空間は別。
        return Region(_header_parts(node) + list(node.body), [], True)
    if isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp)):
        first, inside = _comprehension_parts(node)
        return Region(first + inside, [], True)
    if isinstance(node, ast.GeneratorExp):
        first, inside = _comprehension_parts(node)
        return Region(first, inside, True)
    return None


def _walk_bounded(
    node: ast.AST, crossing: "Callable[[ast.AST], Optional[Sequence[ast.AST]]]"
) -> Iterator[ast.AST]:
    """``node`` 以下を、``crossing`` が引いた境界まで辿る。

    ``crossing(child)`` が ``None`` を返せば child ごと辿り、node 列を返せば
    child 自身は飛ばしてその列だけを辿る。走査の実装はこれ 1 つで、境界の
    定義だけを :func:`evaluation_region` から導く。
    """

    stack: List[ast.AST] = [node]
    while stack:
        current = stack.pop()
        yield current
        for child in ast.iter_child_nodes(current):
            crossed = crossing(child)
            if crossed is None:
                stack.append(child)
            else:
                stack.extend(crossed)


def _binding_crossing(child: ast.AST) -> Optional[Sequence[ast.AST]]:
    """名前の束縛が変わる境界（:attr:`Region.binds`）。header だけ辿る。"""

    region = evaluation_region(child)
    if region is None or not region.binds:
        return None
    if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)):
        return _header_parts(child)
    # comprehension: 最初の iterable だけが外側の名前を読む。
    return _comprehension_parts(child)[0]


def _now_crossing(child: ast.AST) -> Optional[Sequence[ast.AST]]:
    """いま評価されるかの境界（:attr:`Region.now`）。"""

    region = evaluation_region(child)
    return None if region is None else region.now


def walk_lexical_scope(node: ast.AST) -> Iterator[ast.AST]:
    """``node`` 以下を、**入れ子の束縛 scope へは降りずに**辿る。

    ``def`` / ``async def`` / ``lambda`` / ``class`` / comprehension の中の名前は
    別の束縛なので、外側の局所名の読み出しとして数えてはいけない。入れ子の
    scope は scanner 本体が別 scope として独立に解析する。名前解決はしない
    （必要なのは「この scope の構文か」だけ）。
    """

    return _walk_bounded(node, _binding_crossing)


def walk_evaluated_now(node: ast.AST) -> Iterator[ast.AST]:
    """``node`` のうち、**いまこの場で評価される**部分だけを辿る。

    ``thunk = lambda: expr.to_string()`` の ``to_string()`` も
    ``gen = (render(x) for x in items)`` の ``render(x)`` も、その文の時点では
    走らない。後回しの部分は
    :meth:`_EagerDebugRenderingScanner._visit_deferred_regions` が別 scope・
    guard 無しとして改めて解析する（無視はしない）。

    ``node`` 自身が領域を作ることもあるので根にも境界を当てる。実行タイミングを
    見るところは **すべて**この関数を通す。
    """

    region = evaluation_region(node)
    if region is None:
        yield from _walk_bounded(node, _now_crossing)
        return
    for part in region.now:
        yield from _walk_bounded(part, _now_crossing)


def deferred_regions_in(node: ast.AST) -> List[ast.AST]:
    """``node`` を評価しても **その場では走らない**部分（lambda 本体・generator 本体）。

    根も候補にする。``def`` は文なので式の中には現れず、
    :meth:`_EagerDebugRenderingScanner._walk_statement` が扱う。
    """

    found: List[ast.AST] = []
    for candidate in [node] + [
        child
        for sub in walk_evaluated_now(node)
        for child in ast.iter_child_nodes(sub)
    ]:
        region = evaluation_region(candidate)
        if region is not None:
            found += region.deferred
    return found


def statement_scope_nodes(statement: ast.stmt) -> Iterator[ast.AST]:
    """1 つの文のうち、**この scope に属する**部分を辿る。

    文そのものが ``def`` / ``class`` のときは header だけ（本体は別 scope）。
    :func:`walk_lexical_scope` は境界を子にしか当てないので、根が入れ子 scope の
    ときのためにここで受け止める。
    """

    crossed = _binding_crossing(statement)
    if crossed is None:
        yield from walk_lexical_scope(statement)
        return
    for part in crossed:
        yield from walk_lexical_scope(part)


def function_body_nodes(
    function: "ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda",
) -> Iterator[ast.AST]:
    """関数の **本体だけ**を lexical scope として辿る。

    header は関数を **定義する側**の scope で評価されるので、本体の局所名の
    読み出しに混ぜない（``def f(x=summary):`` の ``summary`` は外側の名前）。
    """

    body = [function.body] if isinstance(function, ast.Lambda) else list(function.body)
    for statement in body:
        yield from statement_scope_nodes(statement)


def direct_tracked_producer(
    value: ast.AST, renderers: FrozenSet[str]
) -> Tuple[str, str]:
    """``value`` **そのもの**が tracked producer の呼び出しか（``(種別, 表示)``）。

    「その式の値が producer の戻り値である」ことだけを答える。中は見ない:

    * ``rendered = expr.to_string()`` — 値は ``to_string()`` の戻り値 → producer
    * ``rendered = consume(expr.to_string())`` — 値は ``consume()`` の戻り値。
      ``to_string()`` は **RHS の中で走るが**、``rendered`` が受け取るのはその
      結果ではない → producer ではない

    この 2 つを混同すると、``rendered`` を producer の別名とみなして「debug 専用に
    作った値」と誤認する。本 package には後者が 145 箇所ある（root が producer
    なのは 191 箇所）。**どちらなのかは root を見れば判る**ので、値の流れを追う
    解析は要らない。

    「RHS の中で producer が走るか」は別の性質で、検出側（R1 / R2）が見る。
    provenance の判定にその問いを流用しない。
    """

    forbidden = _render_call_label(value)
    if forbidden:
        return ("forbidden", forbidden)
    kind, label = _summary_call(value, renderers)
    if kind == "unsafe_renderer":
        return (kind, label)
    return ("", "")


def bound_names(target: ast.AST) -> Optional[Set[str]]:
    """代入先が束縛する **局所名**。表に無い形は ``None``（不明）。

    3 番目の positive grammar。statement / expression と同じで、知っている形だけを
    並べ、知らない形は黙って無視せず「不明」と言う。

    * ``Name`` — その名前
    * ``Tuple`` / ``List`` — 要素が束縛する名前すべて（位置の対応は追わない）
    * ``Starred`` — 中身
    * ``Subscript`` / ``Attribute`` — 局所名は束縛しない（既知・空集合）

    ``a[i] = v`` や ``o.x = v`` は「知らない」ではなく「局所名を作らない」なので
    空集合。本当に知らない形だけが ``None`` で、呼び出し側が安全側に倒す。

    **構文として何が束縛されるかを答えるだけ**。「その producer の値がどの名前に
    入ったか」は別の問いで、:func:`tracked_producer_bindings` が支持する形を
    明示的に並べて答える（構文を認識できることは provenance を言えることを
    意味しない）。ここは :func:`statement_rebinds` のような構文認識に使う。
    """

    if isinstance(target, ast.Name):
        return {target.id}
    if isinstance(target, (ast.Tuple, ast.List)):
        names: Set[str] = set()
        for element in target.elts:
            found = bound_names(element)
            if found is None:
                return None
            names |= found
        return names
    if isinstance(target, ast.Starred):
        return bound_names(target.value)
    if isinstance(target, (ast.Subscript, ast.Attribute)):
        return set()
    return None


def statement_rebinds(statement: ast.stmt, name: str) -> bool:
    """その文を実行すると ``name`` が **必ず**束縛し直されるか。

    window を切るのに使う。ここも positive grammar で、**無条件に**束縛する
    構文だけを数える:

    * ``Assign`` / ``AnnAssign``（値つき）/ ``AugAssign`` の代入先
    * ``with`` / ``async with`` の ``as``（本体に入る前に必ず束縛される）
    * ``def`` / ``async def`` / ``class`` が作る名前
    * ``import`` / ``from ... import`` が作る名前
    * その文の直接式にある ``:=``（:func:`direct_production_expressions` と
      :func:`_certain_subexpressions` で「必ず評価される」と言える位置のもの）

    数えないもの — そこを通るとは限らないから:

    * ``for`` の target（列が空なら束縛されない）
    * ``except ... as`` / ``match`` の capture（例外・case 次第）
    * 入れ子の文の並びの中の代入（別 branch かもしれない。18 巡目までの
      「条件付き再代入は前の定義を打ち消さない」契約と同じ）

    判らない代入先（:func:`bound_names` が ``None``）は「束縛したかもしれない」
    に倒す — 見落とすと、もう届かない値の読み出しを古い代入のせいにしてしまう。
    """

    targets: List[ast.AST] = []
    if isinstance(statement, ast.Assign):
        targets += list(statement.targets)
    elif isinstance(statement, ast.AugAssign):
        targets.append(statement.target)
    elif isinstance(statement, ast.AnnAssign) and statement.value is not None:
        targets.append(statement.target)
    elif isinstance(statement, (ast.With, ast.AsyncWith)):
        targets += [
            item.optional_vars for item in statement.items if item.optional_vars is not None
        ]
    elif isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return statement.name == name
    elif isinstance(statement, (ast.Import, ast.ImportFrom)):
        return any(
            (alias.asname or alias.name.split(".")[0]) == name for alias in statement.names
        )
    for expression in direct_production_expressions(statement) or ():
        targets += [
            node.target
            for node in _certainly_evaluated(expression)
            if isinstance(node, ast.NamedExpr)
        ]
    for target in targets:
        names = bound_names(target)
        if names is None or name in names:
            return True
    return False


#: 一段追跡する producer の種別。bounded renderer は R3 が呼び出し位置で決めるので
#: ここには入らない。
TRACKED_PRODUCER_KINDS = ("forbidden", "unsafe_renderer")


class ProducerBinding(NamedTuple):
    """tracked producer の値が入った局所名、または「追えない束縛」。

    ``name`` が ``None`` なら **unsupported** — その束縛の形では、producer の値が
    どの名前に入ったかを局所的に言えない。呼び出し側は黙って飛ばさず契約違反と
    して報告する（:attr:`EagerDebugRenderingViolations.unsupported_producer_binding`）。
    """

    name: Optional[str]
    kind: str
    label: str
    lineno: int


def tracked_producer_bindings(
    statement: ast.stmt, renderers: FrozenSet[str]
) -> List[ProducerBinding]:
    """tracked producer の値がどの局所名に入ったか（**追えた形だけ**）。

    3 つの問いのうち producer origin を担当する owner:

    * producer origin（ここ）— その値がどの名前に入ったか
    * rebind（:func:`statement_rebinds`）— 実行したら **必ず**束縛し直すか
    * production 共有（:func:`_has_direct_production_read`）— **必ず**読むか

    追跡は **target × RHS root** の両方が条件を満たすときだけ:

    * RHS root が :func:`direct_tracked_producer` — 値が producer の戻り値そのもの
    * target が単一の局所 ``Name``

    実測（この文の実行で tracked producer が走る代入 336 件）: RHS root が
    producer なのは 191、残り 145 は ``consume(producer)`` のように **RHS の中で
    走るだけ**。後者は ``rendered`` が producer の戻り値を受けていないので alias
    ではない（B1 でもない — 正当な production の書き方）。target 側は同じ 336 件で
    ``Name`` 330 / ``Subscript`` 3 / ``Attribute`` 3、chained・分解・``AugAssign``
    は 0。

    * ``name = <producer>`` / ``name: T = <producer>`` — 追跡する
    * ``obj.attr = <producer>`` / ``obj[key] = <producer>`` — 局所名を作らないので
      追う対象が無い（unsupported ではない）

    **direct producer を**それ以外の形で束縛しようとしたら **B1 unsupported**:
    chained assignment、分解代入（Tuple / List / Starred）、``AugAssign``、
    ``:=``。どれも production に 1 件も無いのに、正しく追うには値と名前の対応を
    解く必要がある（``used = rendered = f()`` は 2 つの名前が同じ値を指すので
    片方の production 使用がもう片方を免除する。``other, rendered = (f(), 0)``
    は位置で値が決まる）。**そういう解析は作らない** — 書かれたら拒否して、
    単純な形へ直してもらう。

    RHS root が producer **でない**ときは、target の形が何であれ B1 にしない。
    ``a = b = consume(producer)`` は alias を作っていないだけで、正当な production
    の書き方だから。

    :func:`bound_names` は構文として何が束縛されるかを答えるが、**構文を認識
    できることと、producer の値がどの名前に入ったかを言えることは別**。ここでは
    前者に頼らず、追える形を明示的に並べる。
    """

    if isinstance(statement, ast.AnnAssign):
        targets: List[ast.AST] = [statement.target]
    elif isinstance(statement, ast.Assign):
        targets = list(statement.targets)
    elif isinstance(statement, ast.AugAssign):
        targets = [statement.target]
    else:
        targets = []

    events: List[ProducerBinding] = []
    value = getattr(statement, "value", None)
    if targets and value is not None:
        kind, label = direct_tracked_producer(value, renderers)
        if kind in TRACKED_PRODUCER_KINDS:
            single = targets[0] if len(targets) == 1 else None
            if isinstance(statement, ast.AugAssign) or single is None:
                # ``x += producer`` は元の値と混ざり、chained は 1 つの値が複数の
                # 名前に入る。どちらも production に無いので追わない。
                events.append(ProducerBinding(None, kind, label, statement.lineno))
            elif isinstance(single, ast.Name):
                events.append(ProducerBinding(single.id, kind, label, statement.lineno))
            elif isinstance(single, (ast.Subscript, ast.Attribute)):
                pass  # 局所名を作らないので追う対象が無い
            else:
                events.append(ProducerBinding(None, kind, label, statement.lineno))

    # ``(name := producer)`` は production に 1 件も無い。値の行き先を言うには
    # 式の中の消費まで見ることになるので、追わず拒否する。
    for node in walk_evaluated_now(statement):
        if not isinstance(node, ast.NamedExpr):
            continue
        kind, label = direct_tracked_producer(node.value, renderers)
        if kind in TRACKED_PRODUCER_KINDS:
            events.append(ProducerBinding(None, kind, label, node.lineno))
    return events


def _statement_lists(
    function: "ast.FunctionDef | ast.AsyncFunctionDef | ast.Lambda",
) -> Iterator[List[ast.stmt]]:
    """この scope に現れる文の並び（入れ子の束縛 scope へは降りない）。"""

    body = [function.body] if isinstance(function, ast.Lambda) else list(function.body)
    stack: List[List[ast.stmt]] = [body]
    while stack:
        block = stack.pop()
        if not block or not isinstance(block[0], ast.stmt):
            continue
        yield block
        for statement in block:
            if evaluation_region(statement) is not None:
                continue  # def / class — 中は別 scope
            for _field, value in ast.iter_fields(statement):
                if isinstance(value, list) and value and isinstance(value[0], ast.stmt):
                    stack.append(value)
            for handler in getattr(statement, "handlers", []):
                stack.append(handler.body)
            for case in getattr(statement, "cases", []):
                stack.append(case.body)


def _local_window(block: List[ast.stmt], index: int, name: str) -> List[ast.stmt]:
    """``block[index]`` の代入が担当する範囲 — 次に同名へ代入する文の手前まで。

    **同じ文の並びの中だけ**。別 branch / loop / ``try`` の文は入らない。
    """

    window: List[ast.stmt] = []
    for statement in block[index + 1:]:
        if statement_rebinds(statement, name):
            break
        window.append(statement)
    return window


#: production 共有の証拠として見てよい直接式を、**statement 種別ごとに**決める表。
#:
#: 値が「production でも使われている」と言えるのは、その文を実行したときに
#: **必ずその場で評価される**式で読まれているときだけ。入れ子の文の並び
#: （``if`` の body、loop の body、``try`` の body、``match`` の case）は、そこへ
#: 到達するかが control flow 次第なので証拠にしない。``except`` の型や ``match``
#: の case guard も同じ（例外が起きたとき / その case を試すときにしか評価
#: されない）。
#:
#: 各要素は「その文の、どの field を直接式として見るか」。``()`` は「直接式は
#: 無い」（``pass`` や ``import`` のように式を評価しない文、および ``try`` の
#: ように中身が全部別の並びになる文）。
#:
#: ここに **無い種別は既定で証拠なし**（:func:`direct_production_expressions` が
#: ``None`` を返す）。新しい文法が増えても、黙って免除が広がることはない。
_DIRECT_PRODUCTION_FIELDS: Dict[str, Tuple[str, ...]] = {
    # 式をそのまま評価する文
    "Expr": ("value",),
    "Return": ("value",),
    "Delete": ("targets",),
    "Assign": ("targets", "value"),
    "AugAssign": ("target", "value"),
    # annotation は ``from __future__ import annotations`` の有無で評価されたり
    # されなかったりするので証拠にしない（``__header__`` と同じ扱い）。
    "AnnAssign": ("target", "value"),
    "Raise": ("exc", "cause"),
    "Assert": ("test",),
    # 判定だけがその場で走る文（body / orelse は別の並び）
    "If": ("test",),
    "While": ("test",),
    "For": ("iter",),
    "AsyncFor": ("iter",),
    "Match": ("subject",),
    # ``with`` は context manager 式だけがその場で評価される
    "With": ("items",),
    "AsyncWith": ("items",),
    # 定義時に評価される header だけ（本体は別 scope・別のタイミング）
    "FunctionDef": ("__header__",),
    "AsyncFunctionDef": ("__header__",),
    "ClassDef": ("__header__",),
    # 直接式を持たない文
    "Try": (),
    "Import": (),
    "ImportFrom": (),
    "Global": (),
    "Nonlocal": (),
    "Pass": (),
    "Break": (),
    "Continue": (),
    # Python 3.11+。``try`` と同じく中身は全部別の並び。
    "TryStar": (),
}


def direct_production_expressions(statement: ast.stmt) -> Optional[List[ast.AST]]:
    """``statement`` を実行したとき **その場で必ず評価される**直接式。

    production 共有の免除は、この式の中の読み出しだけを証拠にする
    （:func:`_has_direct_production_read`）。表は :data:`_DIRECT_PRODUCTION_FIELDS`
    ただ 1 つで、statement 種別ごとに明示してある。

    知らない種別には ``None`` を返す（証拠なし = 免除しない）。新しい文法が
    増えても既定で fail-closed。

    これは **限定的な構文ヒューリスティック**であって、実行時にその値がどこから
    来たかを証明するものではない。分岐・loop・例外を跨いだ値の追跡はしない。
    """

    fields = _DIRECT_PRODUCTION_FIELDS.get(type(statement).__name__)
    if fields is None:
        return None
    found: List[ast.AST] = []
    for field in fields:
        if field == "__header__":
            # annotation は module 次第で評価されないので証拠にしない。
            found += _header_parts(statement, annotations=False)
            continue
        value = getattr(statement, field, None)
        if value is None:
            continue
        if field == "items":
            found += [item.context_expr for item in value]
            continue
        if isinstance(value, list):
            found += [part for part in value if isinstance(part, ast.AST)]
            continue
        found.append(value)
    return found


def _certain_subexpressions(node: ast.expr) -> Optional[List[ast.expr]]:
    """``node`` を評価したら **必ず**評価される直下の部分式。未対応なら ``None``。

    「この式を評価すれば、この名前を確実に読む」を局所的に言うためだけの表。
    Python の式を全部理解する必要は無く、production が実際に使っている形
    （:func:`direct_production_reads` の docstring に棚卸し結果）だけを並べる。

    条件付きに評価される部分は **入れない**:

    * ``BoolOp`` は先頭の operand だけ（``a and b`` の ``b`` は ``a`` 次第）
    * ``IfExp`` は ``test`` だけ（``body`` / ``orelse`` は分岐の先）
    * ``Compare`` は ``left`` と最初の comparator だけ（``a < b < c`` は連鎖で短絡）
    * comprehension は最初の iterable だけ（要素式・filter は別の束縛・別の回数）
    * ``lambda`` 本体、generator 本体は評価されない

    ここに無い種別（``Yield`` / ``YieldFrom`` / ``Lambda`` / ``Slice`` など）は
    ``None`` を返し、証拠ゼロとして扱われる（fail-closed）。
    """

    if isinstance(node, ast.Name):
        return []
    if isinstance(node, (ast.Tuple, ast.List)):
        return list(node.elts)
    if isinstance(node, ast.Dict):
        return [key for key in node.keys if key is not None] + list(node.values)
    if isinstance(node, ast.Call):
        return [node.func] + list(node.args) + [keyword.value for keyword in node.keywords]
    if isinstance(node, ast.Subscript):
        return [node.value, node.slice]
    if isinstance(node, ast.Attribute):
        return [node.value]
    if isinstance(node, ast.BinOp):
        return [node.left, node.right]
    if isinstance(node, ast.UnaryOp):
        return [node.operand]
    if isinstance(node, ast.Compare):
        # ``a < b < c`` は ``a < b`` が偽なら ``c`` を読まない。
        return [node.left] + node.comparators[:1]
    if isinstance(node, ast.JoinedStr):
        return list(node.values)
    if isinstance(node, ast.FormattedValue):
        return [node.value] + ([node.format_spec] if node.format_spec is not None else [])
    if isinstance(node, ast.BoolOp):
        return node.values[:1]
    if isinstance(node, ast.IfExp):
        return [node.test]
    if isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
        # 最初の iterable だけが外側の scope で、かつ必ず評価される。
        return [node.generators[0].iter] if node.generators else []
    if isinstance(node, ast.Lambda):
        # 本体は呼ばれるまで走らない。default 引数は定義時に走るが、本 package に
        # その形は無いので証拠にしない（要るようになったらここへ足す）。
        return []
    if isinstance(node, ast.Constant):
        return []
    return None


def _certainly_evaluated(expression: ast.expr) -> Iterator[ast.expr]:
    """``expression`` を評価したら **必ず**評価される部分式をすべて辿る。

    :func:`_certain_subexpressions` の表を閉包しただけ。証拠の判定
    （:func:`direct_production_reads`）と ``:=`` の束縛判定が同じ走査を使う。
    """

    stack: List[ast.expr] = [expression]
    while stack:
        node = stack.pop()
        yield node
        parts = _certain_subexpressions(node)
        if parts is not None:
            stack.extend(parts)


def direct_production_reads(
    expression: ast.expr, name: str, debug_reads: Set[int] = frozenset()
) -> bool:
    """``expression`` を評価すれば ``name`` を **確実に読む**と局所的に言えるか。

    production 共有の免除は、これが真の読み出しだけを証拠にする。``walk_evaluated_now``
    は「今の評価フェーズで走り得る部分」を表すので広すぎる — 短絡の後ろ側、
    ``IfExp`` の枝、comprehension の中の別束縛まで含んでしまう。免除には
    「必ず読む」が要るので、専用の狭い表（:func:`_certain_subexpressions`）で判定する。

    本 package が実際に必要としている形（337 の exemption site を棚卸しした結果）:
    ``Name`` / ``Tuple`` / ``List`` / ``Dict`` / ``Call`` の func・引数・keyword /
    ``Subscript`` / ``Attribute`` / ``BinOp`` / ``UnaryOp`` / ``Compare`` /
    f-string / ``BoolOp`` の先頭 / ``IfExp`` の test / comprehension の最初の iterable。
    それ以外は証拠ゼロ。

    lexical scope は跨がない: comprehension や ``lambda`` の中は辿らないので、
    ``[rendered for rendered in items]`` の内側の束縛を外側の名前と取り違えない。
    Python の式評価器を作るものではなく、限定的な構文ヒューリスティックである。

    ``debug_reads`` に入っている読み出し（debug sink の引数・guard 条件）は
    production の証拠にしない — それ自体が「debug のために読んでいる」場所。
    """

    return any(
        isinstance(node, ast.Name)
        and isinstance(node.ctx, ast.Load)
        and node.id == name
        and id(node) not in debug_reads
        for node in _certainly_evaluated(expression)
    )


def _has_direct_production_read(
    window: Sequence[ast.stmt], name: str, debug_reads: Set[int]
) -> bool:
    """``window`` に production 共有の証拠があるか（**MUST** の問い）。

    2 段の positive grammar だけで決まる:

    * statement 段 — :func:`direct_production_expressions`（その文を実行したら
      必ず評価される式はどれか）
    * expression 段 — :func:`direct_production_reads`（その式を評価したら
      その名前を必ず読むか）

    どちらも whitelist で、載っていない形は証拠ゼロ。検出側の走査
    （:func:`statement_scope_nodes` / :func:`walk_evaluated_now`）はここでは
    使わない — 見たいものが違う（「走り得るか」ではなく「必ず読むか」）。
    producer origin だけが **MAY**（:func:`tracked_producer_bindings`）で、
    rebind と免除は **MUST**。
    """

    for statement in window:
        for expression in direct_production_expressions(statement) or ():
            if direct_production_reads(expression, name, debug_reads):
                return True
    return False


def _debug_only_locals(
    function: ast.FunctionDef | ast.AsyncFunctionDef,
    renderers: FrozenSet[str],
) -> Tuple[Dict[int, Tuple[str, str]], List[ProducerBinding]]:
    """**debug のためだけに**作られた値を読んでいる名前 → ``(種別, 呼び出し名)``。

    AST の意味づけはここに持たない。3 つの owner を組み合わせるだけ:

    * :func:`tracked_producer_bindings` — **MAY**: producer の値がどの名前へ
      入り得るか
    * :func:`statement_rebinds`（:func:`_local_window` 経由）— **MUST**: どこで
      その名前が必ず束縛し直されるか
    * :func:`_has_direct_production_read` — **MUST**: その区間で production が
      必ず読むか（読むなら免除）

    追う producer は :data:`TRACKED_PRODUCER_KINDS` の 2 つだけ。``to_string`` /
    ``to_smt`` は production でも正当に使う呼び出しなので、「debug のためだけに
    作ったか」を見ないと判断できない。bounded renderer は R3 が呼び出し位置で
    決めるので追わない。

    返り値は ``(報告対象の読み出し, 束縛先が判らなかった producer)``。後者は
    黙って捨てず、呼び出し側が契約違反として報告する。
    """

    reported: Dict[int, Tuple[str, str]] = {}
    unsupported: List[ProducerBinding] = []
    for block in _statement_lists(function):
        for index, statement in enumerate(block):
            for binding in tracked_producer_bindings(statement, renderers):
                if binding.name is None:
                    unsupported.append(binding)
                    continue
                window = _local_window(block, index, binding.name)
                debug_reads = _debug_read_positions(window, renderers)
                if _has_direct_production_read(window, binding.name, debug_reads):
                    continue  # production も読む値 — debug 側の問題ではない
                for target in window:
                    for node in statement_scope_nodes(target):
                        if (
                            isinstance(node, ast.Name)
                            and isinstance(node.ctx, ast.Load)
                            and node.id == binding.name
                            and id(node) in debug_reads
                        ):
                            reported[id(node)] = (binding.kind, binding.label)
    return reported, unsupported


def _debug_read_positions(
    window: Sequence[ast.stmt], renderers: FrozenSet[str]
) -> Set[int]:
    """``window`` の中で **debug 専用の読み出し位置**にある ``Name`` node。

    debug sink の引数か、debug guard 条件の後続 conjunct。
    """

    positions = {
        id(name)
        for statement in window
        for call in statement_scope_nodes(statement)
        if isinstance(call, ast.Call) and _is_debug_sink(call, renderers)
        for argument in list(call.args) + [keyword.value for keyword in call.keywords]
        for name in walk_evaluated_now(argument)
        if isinstance(name, ast.Name)
    }
    positions |= {
        id(name)
        for statement in window
        for branch in statement_scope_nodes(statement)
        if isinstance(branch, (ast.If, ast.IfExp))
        for conjunct in debug_only_conjuncts(branch.test)
        for name in walk_evaluated_now(conjunct)
        if isinstance(name, ast.Name)
    }
    return positions


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
        #: だけ（R2 / R6）。bounded renderer は R3 が呼び出し位置で決めるので
        #: ここには現れない。
        #:
        #: 鍵が読み出し node そのものなので、同名の別束縛（入れ子 scope の
        #: parameter、同じ scope の別の代入）と取り違えようがない。
        self.debug_only_reads: Dict[int, Tuple[str, str]] = {}
        #: いま走査している関数名（内側が末尾）。R3 の免除判定に使う。
        self.function_names: List[str] = []

    def _may_render_here(self) -> bool:
        """有界 renderer を guard 無しで呼んでよい場所か。

        棚卸しで出た 3 つだけ: 契約の owner module、別の renderer の定義の中
        （wrapper の委譲）、``__repr__`` / ``__str__``（そこで有界な要約を返すのが
        R4 の目的そのもの）。ほかは guard の中でだけ。
        """

        if self.module == CONTRACT_OWNER_MODULE:
            return True
        if not self.function_names:
            return False
        innermost = self.function_names[-1]
        return innermost in self.renderers or innermost in RENDER_FREE_DUNDERS

    @contextmanager
    def _scope(self, function: Optional[ast.AST]) -> Iterator[None]:
        """lexical scope を 1 つ入れ替える（代入 1 段の追跡はこの単位）。"""

        outer = self.debug_only_reads
        if function is None:
            self.debug_only_reads = {}
        else:
            self.debug_only_reads, unsupported = _debug_only_locals(
                function, self.renderers
            )
            for binding in unsupported:
                # 束縛先の形が判らない producer を黙って飛ばさない。
                self.violations.unsupported_producer_binding.append(
                    (self.module, binding.lineno, binding.label)
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
            # ``repr()`` が走らせるのは本体のうち **その場で評価される**部分。
            # 中の ``lambda`` / ``def`` / generator の本体は呼ばれるまで走らない
            # （根が入れ子 ``def`` のときも降りないよう、root を見る入口を使う）。
            for sub in (
                inner
                for statement in node.body
                for inner in walk_evaluated_now(statement)
            ):
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
        if isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            # decorator / default 引数 / annotation / base class / metaclass は
            # **この文が実行される時点で**評価されるので、今の guard 文脈で見る。
            # 入口は :func:`_header_parts` の 1 つだけ（lambda と同じ
            # 評価モデル）。本体だけが別の実行文脈になる。
            for part in _header_parts(statement):
                self._visit_expression(part, guarded=guarded)
            if isinstance(statement, ast.ClassDef):
                # 束縛としては別 scope だが、本体は**その場で**実行される。
                with self._scope(None):
                    self._walk_body(statement.body, guarded=guarded)
                return
            # 別の呼び出し文脈で実行されるので guard を引き継がない。
            self.function_names.append(statement.name)
            try:
                with self._scope(statement):
                    self._walk_body(statement.body, guarded=False)
            finally:
                self.function_names.pop()
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
    def _visit_deferred_regions(self, node: ast.AST) -> None:
        """後回しになる部分（``lambda`` 本体・generator 本体）を別に解析する。

        その部分はこの式を評価した時点では走らないので、ここの guard 状態を
        引き継がない（``if self.debug: thunk = lambda: expr.to_string()`` や
        ``gen = (render(x) for x in items)`` を R1 とするのは誤検出）。無視する
        のではなく、走る文脈が分からない以上 guard 無しとして改めて見る — 入れ子
        の ``def`` を :meth:`_walk_statement` が扱うのと同じ扱い。

        どこが後回しかは :func:`evaluation_region` が 1 か所で決めている。
        """

        for deferred in deferred_regions_in(node):
            with self._scope(None):
                self._visit_expression(deferred, guarded=False)

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
        self._visit_deferred_regions(node)
        for sub in walk_evaluated_now(node):
            label = _render_call_label(sub)
            if label and guarded:
                self.violations.render_in_debug_guard.append((self.module, sub.lineno, label))
            call_kind, call_label = _summary_call(sub, self.renderers)
            if call_kind == "renderer" and not guarded and not self._may_render_here():
                # R3: 有界 renderer を呼んでよいのは debug guard の中だけ
                # （owner / renderer 定義 / ``__repr__`` を除く）。値がどこへ
                # 流れるかは見ない — 呼んだ場所だけで決まる。
                self.violations.renderer_outside_a_guard.append(
                    (self.module, sub.lineno, call_label)
                )
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
                # 引数のうち **その場で評価される**部分だけ。``lambda`` や
                # generator を渡す形は、その場では何も走らせない。
                for inner in walk_evaluated_now(argument):
                    render = _render_call_label(inner)
                    if render:
                        self.violations.render_in_debug_sink.append(
                            (self.module, sub.lineno, f"{_called_name(sub)}(... {render} ...)")
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
                        if kind:
                            self.violations.render_in_debug_sink.append(
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
    assert not violations.renderer_outside_a_guard, violations.describe()


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
    assert [entry[2] for entry in violations.renderer_outside_a_guard] == [
        "summarize_widget()"
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
    assert [entry[2] for entry in violations.renderer_outside_a_guard] == [
        "summarize_expression()"
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
    assert bool(violations.renderer_outside_a_guard) is not guarded, label


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
    assert unguarded.renderer_outside_a_guard


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


def test_a_nested_scope_name_is_not_attributed_to_the_outer_local():
    """内側 scope の同名読み出しを外側の追跡結果と取り違えない。"""

    violations = scan_source(
        "sample",
        "def f(self, expr, apply, consume):\n"
        "    rendered = expr.to_string()\n"
        "    consume(rendered)\n"
        "    apply(lambda rendered: self._debug_print(rendered))\n",
    )
    # 外側の ``rendered`` は production も読むので免除。内側 lambda の
    # ``rendered`` は別の束縛（引数）なので、外側の値として報告してはいけない。
    assert not violations.render_in_debug_sink, violations.describe()


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
    assert [entry[2] for entry in violations.renderer_outside_a_guard] == [
        "summarize_expression()"
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
    assert [entry[2] for entry in violations.renderer_outside_a_guard] == [
        "summarize_expression()"
    ], label


def test_a_nested_function_header_reads_the_outer_name():
    """内側 ``def`` の default は外側の名前を読む（過検出しない）。"""

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    rendered = expr.to_string()\n"
        "    def inner(x=rendered):\n"
        "        return x\n"
        "    self._debug_print(rendered)\n"
        "    return inner\n",
    )
    # 外側 ``rendered`` は sink 以外（inner の default）でも読まれているので
    # production 共有として免除される。
    assert not violations.render_in_debug_sink, violations.describe()


# -- A2: 同名への再代入 --------------------------------------------------------

@pytest.mark.parametrize(
    "producer, bucket, detail",
    [
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
    assert [entry[2] for entry in violations.renderer_outside_a_guard] == [
        "summarize_expression()"
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
    assert [entry[2] for entry in violations.renderer_outside_a_guard] == [
        "summarize_expression()"
    ]


def test_a_comprehension_is_evaluated_where_it_is_written():
    """list / set / dict の内包表記はその場で全部走る（generator とは別）。"""

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


# -- A1: control flow をまたぐ再代入 -------------------------------------------

_CONDITIONAL_REASSIGNMENTS = [
    ("if", "    if cond:\n        summary = cheap\n"),
    ("if/else", "    if cond:\n        summary = cheap\n    else:\n        pass\n"),
    ("0 回あり得る for", "    for item in items:\n        summary = cheap\n"),
    ("0 回あり得る while", "    while cond:\n        summary = cheap\n"),
    ("try", "    try:\n        summary = cheap\n    except Exception:\n        pass\n"),
    ("except 側", "    try:\n        pass\n    except Exception:\n        summary = cheap\n"),
    ("with の中の if", "    with lock:\n        if cond:\n            summary = cheap\n"),
]


def test_a_straight_line_reassignment_still_kills_the_earlier_definition():
    """同じ直列区間の再代入は従来どおり上書きとして扱う。"""

    violations = scan_source(
        "sample",
        "def f(self, a, b, consume):\n"
        "    rendered = a.to_string()\n"
        "    consume(rendered)\n"
        "    rendered = b.to_string()\n"
        "    self._debug_print(rendered)\n",
    )
    # 前半は production に読まれて免除、後半だけが報告される。
    assert [entry[2] for entry in violations.render_in_debug_sink] == [
        "_debug_print(... rendered = to_string() ...)"
    ]


def test_a_straight_line_reassignment_inside_a_branch_still_kills():
    """直列かどうかは block 単位。``if`` の中でも同じ block なら上書き。"""

    violations = scan_source(
        "sample",
        "def f(self, a, b, cond, consume):\n"
        "    if cond:\n"
        "        rendered = a.to_string()\n"
        "        consume(rendered)\n"
        "        rendered = b\n"
        "        self._debug_print(rendered)\n",
    )
    assert not violations.render_in_debug_sink, violations.describe()


def test_an_outer_assignment_reaches_a_read_inside_a_branch():
    """外側の直列代入は、あとから入る branch の中の読み出しにも届く。"""

    violations = scan_source(
        "sample",
        "def f(self, expr, cond):\n"
        "    summary = summarize_expression(expr)\n"
        "    if cond:\n"
        "        self._debug_print(summary)\n",
    )
    assert [entry[2] for entry in violations.renderer_outside_a_guard] == [
        "summarize_expression()"
    ]


def test_a_conditionally_reassigned_value_production_also_reads_is_exempt():
    """条件付き再代入でも、production が読むなら従来どおり免除。"""

    violations = scan_source(
        "sample",
        "def f(self, expr, cheap, cond, solver):\n"
        "    smt = expr.to_smt()\n"
        "    if cond:\n"
        "        smt = cheap\n"
        "    solver.add(smt)\n"
        "    self._debug_print(smt)\n",
    )
    assert not violations.render_in_debug_sink, violations.describe()


# -- A2: 定義時に評価される式 ---------------------------------------------------

@pytest.mark.parametrize(
    "definition, label",
    [
        ("def inner(x=expr.to_string()):\n            pass", "default 引数"),
        ("def inner(x: expr.to_string() = None):\n            pass", "parameter annotation"),
        ("def inner() -> expr.to_string():\n            pass", "戻り値 annotation"),
        ("@decorate(expr.to_string())\n        def inner():\n            pass", "decorator"),
        ("class Holder(expr.to_string()):\n            pass", "class base"),
        ("class Holder(metaclass=expr.to_string()):\n            pass", "class keyword"),
        ("@decorate(expr.to_string())\n        class Holder:\n            pass", "class decorator"),
    ],
)
def test_a_defining_time_expression_inside_a_guard_is_checked(definition, label):
    """定義時に**その場で**評価される式は R1 の対象。"""

    violations = scan_source(
        "sample",
        "def f(self, expr, decorate):\n"
        "    if self.debug:\n"
        f"        {definition}\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_guard] == ["to_string()"], label


def test_a_nested_function_body_does_not_inherit_the_guard():
    """本体は別の実行文脈。定義時の式だけが今の文脈。"""

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    if self.debug:\n"
        "        def inner():\n"
        "            return expr.to_string()\n",
    )
    assert not violations.render_in_debug_guard, violations.describe()


# -- A3: 代入分類と式走査で評価の意味をそろえる --------------------------------

def test_a_lambda_assignment_is_not_classified_as_a_forbidden_call():
    """``thunk = lambda: expr.to_string()`` は代入の時点では何も描画しない。"""

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    thunk = lambda: expr.to_string()\n"
        "    self._debug_print(thunk)\n",
    )
    assert not violations.render_in_debug_sink, violations.describe()


def test_a_lambda_default_in_an_assignment_is_not_a_producer_alias():
    """``thunk = lambda rendered=expr.to_string(): ...`` の値は lambda。

    ``to_string()`` は代入の時点で走る（default 引数なので）が、``thunk`` が
    受け取るのは lambda であって producer の戻り値ではない。alias にはしない。
    走ってしまうこと自体は検出側（R2）の仕事。
    """

    value = ast.parse("lambda rendered=expr.to_string(): rendered", mode="eval").body
    assert direct_tracked_producer(value, OWNED_SUMMARY_FUNCTIONS) == ("", "")

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    thunk = lambda rendered=expr.to_string(): rendered\n"
        "    self._debug_print(thunk)\n",
    )
    assert not violations.unsupported_producer_binding, violations.describe()
    # sink へ渡るのは thunk なので、alias 由来の R2 にはならない。
    assert not [
        entry for entry in violations.render_in_debug_sink if "thunk =" in entry[2]
    ], violations.describe()


def test_the_producer_classifier_looks_only_at_the_root():
    """provenance は root だけを見る（中で producer が走るかは別の性質）。"""

    direct = ast.parse("expr.to_string()", mode="eval").body
    nested = ast.parse("consume(expr.to_string())", mode="eval").body
    deferred = ast.parse("lambda: expr.to_string()", mode="eval").body

    assert direct_tracked_producer(direct, OWNED_SUMMARY_FUNCTIONS)[0] == "forbidden"
    assert direct_tracked_producer(nested, OWNED_SUMMARY_FUNCTIONS) == ("", "")
    assert direct_tracked_producer(deferred, OWNED_SUMMARY_FUNCTIONS) == ("", "")


# -- 評価モデルの表 -------------------------------------------------------------

_EVALUATION_MODEL = [
    # ラベル, ソース, 今評価される marker 数, 後で評価される marker 数, 別束縛か。
    # ``NOW`` / ``LATER`` の名前が、それぞれどちら側に現れるかを数える。
    ("FunctionDef", "def g(a=NOW, b: NOW = None) -> NOW:\n    LATER\n", 3, 1, True),
    ("AsyncFunctionDef", "async def g(a=NOW) -> NOW:\n    LATER\n", 2, 1, True),
    ("Lambda", "lambda a=NOW: LATER", 1, 1, True),
    ("ClassDef", "@NOW\nclass C(NOW, metaclass=NOW):\n    NOW\n", 4, 0, True),
    ("ListComp", "[NOW for x in NOW if NOW]", 3, 0, True),
    ("SetComp", "{NOW for x in NOW if NOW}", 3, 0, True),
    ("DictComp", "{NOW: NOW for x in NOW if NOW}", 4, 0, True),
    ("GeneratorExp", "(LATER for x in NOW if LATER)", 1, 2, True),
    ("GeneratorExp 2 本目", "(LATER for x in NOW for y in LATER)", 1, 2, True),
]


def _markers(parts, marker):
    return sum(
        1
        for part in parts
        for node in ast.walk(part)
        if isinstance(node, ast.Name) and node.id == marker
    )


@pytest.mark.parametrize(
    "label, source, now, deferred, binds",
    _EVALUATION_MODEL,
    ids=[case[0] for case in _EVALUATION_MODEL],
)
def test_the_evaluation_model_is_fixed(label, source, now, deferred, binds):
    """どこが今走り、どこが後で走り、どこから別束縛かを 1 つの表で固定する。

    この規則は :func:`evaluation_region` だけが持つ。走査も代入の分類も棚卸しも
    そこから導かれるので、ここが動かない限り全経路の意味が揃う。
    """

    parsed = ast.parse(source).body[0]
    node = parsed.value if isinstance(parsed, ast.Expr) else parsed
    region = evaluation_region(node)
    assert region is not None, label
    assert _markers(region.now, "NOW") == now, (label, "NOW")
    assert _markers(region.now, "LATER") == 0, (label, "LATER が今評価側にある")
    assert _markers(region.deferred, "LATER") == deferred, (label, "LATER")
    assert _markers(region.deferred, "NOW") == 0, (label, "NOW が後回し側にある")
    assert region.binds is binds, label


def test_an_ordinary_expression_makes_no_region():
    """領域を作らない構文は ``None``（そのまま辿ってよい）。"""

    for source in ("a + b", "f(x)", "obj.attr", "items[0]", "a if b else c"):
        node = ast.parse(source, mode="eval").body
        assert evaluation_region(node) is None, source


@pytest.mark.parametrize(
    "label, source, bucket, detail",
    [
        (
            "最初の iterable は今評価",
            "def f(self, conds):\n"
            "    if self.debug:\n"
            "        gen = (x for x in [c.to_string() for c in conds])\n"
            "        return gen\n",
            "render_in_debug_guard",
            "to_string()",
        ),
        (
            "要素式は後で評価",
            "def f(self, items):\n"
            "    if self.debug:\n"
            "        gen = (self._debug_print(summarize_expression(x)) for x in items)\n"
            "        return gen\n",
            "renderer_outside_a_guard",
            "summarize_expression()",
        ),
        (
            "filter は後で評価",
            "def f(self, items):\n"
            "    if self.debug:\n"
            "        gen = (x for x in items if self._debug_print(summarize_expression(x)))\n"
            "        return gen\n",
            "renderer_outside_a_guard",
            "summarize_expression()",
        ),
        (
            "2 本目の iterable は後で評価",
            "def f(self, items):\n"
            "    if self.debug:\n"
            "        gen = (y for x in items for y in self._debug_print(summarize_expression(x)))\n"
            "        return gen\n",
            "renderer_outside_a_guard",
            "summarize_expression()",
        ),
    ],
)
def test_a_generator_body_does_not_inherit_the_guard(label, source, bucket, detail):
    """generator は作成時に何も走らせない。中身は反復時なので guard を継がない。"""

    violations = scan_source("sample", source)
    assert [entry[2] for entry in getattr(violations, bucket)] == [detail], label


def test_a_comprehension_runs_where_it_is_written():
    """list / set / dict の内包表記は作成時に全部走る（generator と違う）。"""

    for opening, closing in (("[", "]"), ("{", "}")):
        violations = scan_source(
            "sample",
            "def f(self, conds):\n"
            "    if self.debug:\n"
            f"        rendered = {opening}c.to_string() for c in conds{closing}\n"
            "        return rendered\n",
        )
        assert [entry[2] for entry in violations.render_in_debug_guard] == ["to_string()"]


# -- control flow を跨ぐ再代入は「何も打ち消さない」 ------------------------------

_SIBLING_REASSIGNMENTS = [
    ("if / else の別 branch",
     "    if cond:\n        summary = cheap\n    else:\n        pass\n        self._debug_print(summary)\n"),
    ("match の別 case",
     "    match cond:\n        case 1:\n            summary = cheap\n"
     "        case _:\n            pass\n            self._debug_print(summary)\n"),
    ("try の本体と finally",
     "    try:\n        summary = cheap\n    finally:\n        self._debug_print(summary)\n"),
    ("try の本体と except",
     "    try:\n        summary = cheap\n    except Exception:\n        self._debug_print(summary)\n"),
    ("loop の中と後",
     "    for item in items:\n        summary = cheap\n    self._debug_print(summary)\n"),
    ("if の中と後",
     "    if cond:\n        summary = cheap\n    self._debug_print(summary)\n"),
]


def test_only_the_next_assignment_in_the_same_statement_list_ends_the_window():
    """同じ並びの次の代入までが、その代入の担当範囲。"""

    violations = scan_source(
        "sample",
        "def f(self, a, b, consume):\n"
        "    rendered = a.to_string()\n"
        "    consume(rendered)\n"
        "    rendered = b.to_string()\n"
        "    self._debug_print(rendered)\n",
    )
    # 前半は production も読むので免除、後半だけが報告される。
    assert [entry[2] for entry in violations.render_in_debug_sink] == [
        "_debug_print(... rendered = to_string() ...)"
    ]


def test_the_checker_keeps_no_statement_path_machinery():
    """control-flow 推論を持ち込み直していないこと（設計の固定）。"""

    import scripts.function_tracer_pcode.tests.unit.test_no_eager_debug_rendering as module

    for gone in ("StatementPath", "_unconditionally_precedes", "_statement_paths"):
        assert not hasattr(module, gone), f"{gone} is back"


# -- R3: 有界 renderer は「呼んだ場所」で決まる ---------------------------------

def test_a_renderer_outside_a_guard_is_refused_wherever_the_value_goes():
    """値の行き先は見ない。guard の外で呼んだ時点で違反。"""

    for tail in (
        "    return summary\n",
        "    self._debug_print(summary)\n",
        "    consume(summary)\n",
        "",
    ):
        violations = scan_source(
            "sample",
            "def f(self, expr, consume):\n"
            "    summary = summarize_expression(expr)\n" + tail,
        )
        assert [entry[2] for entry in violations.renderer_outside_a_guard] == [
            "summarize_expression()"
        ], tail


def test_a_renderer_inside_a_guard_is_fine():
    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    if self._debug_available():\n"
        "        summary = summarize_expression(expr)\n"
        "        self._debug_print(summary)\n",
    )
    assert not violations, violations.describe()


@pytest.mark.parametrize(
    "module, source, label",
    [
        (
            CONTRACT_OWNER_MODULE,
            "def summarize_widget(value):\n    return summarize_expression(value)\n",
            "owner module",
        ),
        (
            "sample",
            "def _debug_expr_summary(self, expr):\n    return summarize_expression(expr)\n",
            "renderer 定義の中（wrapper の委譲）",
        ),
        (
            "sample",
            "class Holder:\n"
            "    def __repr__(self):\n"
            "        return f'Holder({summarize_expression(self.value)})'\n",
            "__repr__（有界な要約を返すのが R4 の目的）",
        ),
    ],
)
def test_the_three_places_a_renderer_may_run_without_a_guard(module, source, label):
    """棚卸しで出た 3 つの免除だけ。ほかは guard の中でだけ。"""

    renderers = OWNED_SUMMARY_FUNCTIONS | {"_debug_expr_summary"}
    violations = scan_source(module, source, renderers)
    assert not violations.renderer_outside_a_guard, label


def test_an_ordinary_function_is_not_exempt():
    """免除は 3 つだけ — ふつうの関数名では効かない。"""

    violations = scan_source(
        "sample",
        "def build_report(self, expr):\n    return summarize_expression(expr)\n",
    )
    assert [entry[2] for entry in violations.renderer_outside_a_guard] == [
        "summarize_expression()"
    ]


# -- production 共有の免除は「同じ文の並び」でだけ証明する ----------------------

_OTHER_BLOCK_READS = [
    ("sibling if / else",
     "def f(self, expr, cheap, cond, consume):\n"
     "    rendered = cheap\n"
     "    if cond:\n"
     "        rendered = expr.to_string()\n"
     "        self._debug_print(rendered)\n"
     "    else:\n"
     "        consume(rendered)\n"),
    ("try / except",
     "def f(self, expr, consume):\n"
     "    try:\n"
     "        rendered = expr.to_string()\n"
     "        self._debug_print(rendered)\n"
     "    except Exception:\n"
     "        consume(rendered)\n"),
    ("match の別 case",
     "def f(self, expr, cond, consume):\n"
     "    match cond:\n"
     "        case 1:\n"
     "            rendered = expr.to_string()\n"
     "            self._debug_print(rendered)\n"
     "        case _:\n"
     "            consume(rendered)\n"),
    ("loop の外",
     "def f(self, expr, items, consume):\n"
     "    for item in items:\n"
     "        rendered = expr.to_string()\n"
     "        self._debug_print(rendered)\n"
     "    consume(rendered)\n"),
    ("入れ子 scope",
     "def f(self, expr, consume):\n"
     "    rendered = expr.to_string()\n"
     "    self._debug_print(rendered)\n"
     "    def later(rendered=None):\n"
     "        return consume(rendered)\n"
     "    return later\n"),
]


@pytest.mark.parametrize(
    "label, source", _OTHER_BLOCK_READS, ids=[case[0] for case in _OTHER_BLOCK_READS]
)
def test_a_production_read_in_another_block_does_not_grant_exemption(label, source):
    """別 branch / loop / 入れ子 scope の read は免除の根拠にしない。

    その経路を本当に通るかは control flow の話で、この checker は推論しない。
    証明できなければ免除しない（fail-closed）。
    """

    violations = scan_source("sample", source)
    assert [entry[2] for entry in violations.render_in_debug_sink] == [
        "_debug_print(... rendered = to_string() ...)"
    ], label


@pytest.mark.parametrize(
    "producer, detail",
    [
        ("expr.to_string()", "_debug_print(... rendered = to_string() ...)"),
        ("expr.to_smt()", "_debug_print(... rendered = to_smt() ...)"),
        (
            "expensive_factory().summarize_expression(expr)",
            "_debug_print(... rendered = <computed>.summarize_expression() ...)",
        ),
    ],
)
def test_the_sibling_branch_rule_holds_for_every_tracked_producer(producer, detail):
    violations = scan_source(
        "sample",
        "def f(self, expr, cheap, cond, consume):\n"
        "    rendered = cheap\n"
        "    if cond:\n"
        f"        rendered = {producer}\n"
        "        self._debug_print(rendered)\n"
        "    else:\n"
        "        consume(rendered)\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_sink] == [detail]


def test_a_production_read_in_the_same_statement_list_does_grant_exemption():
    """同じ並びで production read が構文的に見えるときだけ免除する。"""

    violations = scan_source(
        "sample",
        "def f(self, expr, solver):\n"
        "    smt = expr.to_smt()\n"
        "    solver.add(smt)\n"
        "    self._debug_print(smt)\n",
    )
    assert not violations.render_in_debug_sink, violations.describe()



def test_a_debug_read_inside_a_nested_body_is_still_detected():
    """検出のほうは入れ子の中まで見る（免除だけが直列区間に限られる）。"""

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    rendered = expr.to_string()\n"
        "    if self.debug:\n"
        "        self._debug_print(rendered)\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_sink] == [
        "_debug_print(... rendered = to_string() ...)"
    ]


def test_the_exemption_grammar_stops_at_a_nested_statement():
    """免除用の直接式に入れ子の文が含まれないこと（owner contract）。"""

    statement = ast.parse("if cond:\n    consume(rendered)\n").body[0]
    names = {
        node.id
        for expression in direct_production_expressions(statement)
        for node in walk_evaluated_now(expression)
        if isinstance(node, ast.Name)
    }
    assert names == {"cond"}, names
    # 比較用: 検出側の走査は中まで見る（別 helper・別責務）。
    wider = {
        node.id
        for node in statement_scope_nodes(statement)
        if isinstance(node, ast.Name)
    }
    assert wider == {"cond", "consume", "rendered"}, wider


# -- production 共有の免除: statement 種別ごとの表 ------------------------------

def _exempts(source: str) -> bool:
    """``rendered`` が production 共有として免除されるか（違反 0 なら免除）。"""

    violations = scan_source("sample", source)
    return not violations.render_in_debug_sink


def _with_statement(statement: str) -> str:
    body = "".join(f"    {line}\n" for line in statement.splitlines())
    return (
        "def f(self, expr, cond, items, lock, value, consume, Holder):\n"
        "    rendered = expr.to_string()\n"
        + body
        + "    self._debug_print(rendered)\n"
    )


#: (ラベル, 文, 免除されるか)。「その文を実行したら必ず評価される位置」に
#: ``rendered`` があるときだけ免除。入れ子の並び・例外型・case guard は対象外。
_EXEMPTION_GRAMMAR = [
    # 直接式 → 免除される
    ("Expr の value", "consume(rendered)", True),
    ("Assign の value", "keep = rendered", True),
    ("Assign の target 添字", "items[rendered] = 1", True),
    ("AnnAssign の value", "keep: str = rendered", True),
    ("AugAssign の value", "value += rendered", True),
    ("Return の value", "return rendered", True),
    ("Delete の target", "del items[rendered]", True),
    ("Raise の exc", "raise ValueError(rendered)", True),
    ("Assert の test", "assert rendered", True),
    ("If の test", "if rendered:\n    pass", True),
    ("While の test", "while rendered:\n    break", True),
    ("For の iter", "for item in rendered:\n    pass", True),
    ("AsyncFor の iter", None, True),  # 下で async 関数として別に組む
    ("With の context", "with rendered:\n    pass", True),
    ("Match の subject", "match rendered:\n    case _:\n        pass", True),
    ("FunctionDef の default", "def inner(x=rendered):\n    pass", True),
    ("ClassDef の base", "class Sub(rendered):\n    pass", True),
    # 入れ子の並び・条件付きの位置 → 免除されない
    ("If の body", "if cond:\n    consume(rendered)", False),
    ("If の orelse", "if cond:\n    pass\nelse:\n    consume(rendered)", False),
    ("While の body", "while cond:\n    consume(rendered)", False),
    ("For の body", "for item in items:\n    consume(rendered)", False),
    ("With の body", "with lock:\n    consume(rendered)", False),
    ("Try の body", "try:\n    consume(rendered)\nexcept Exception:\n    pass", False),
    ("Try の except 型", "try:\n    pass\nexcept rendered:\n    pass", False),
    ("Try の handler body", "try:\n    pass\nexcept Exception:\n    consume(rendered)", False),
    ("Try の orelse", "try:\n    pass\nexcept Exception:\n    pass\nelse:\n    consume(rendered)", False),
    ("Try の finally", "try:\n    pass\nfinally:\n    consume(rendered)", False),
    ("Match の case guard", "match value:\n    case 1 if rendered:\n        pass", False),
    ("Match の case body", "match value:\n    case _:\n        consume(rendered)", False),
    ("FunctionDef の本体", "def inner():\n    return consume(rendered)", False),
    ("ClassDef の本体", "class Sub:\n    kept = rendered", False),
]


@pytest.mark.parametrize(
    "label, statement, exempt",
    [case for case in _EXEMPTION_GRAMMAR if case[1] is not None],
    ids=[case[0] for case in _EXEMPTION_GRAMMAR if case[1] is not None],
)
def test_the_exemption_grammar_is_fixed(label, statement, exempt):
    """免除の根拠になる位置を statement 種別ごとに固定する。

    「必ずその場で評価される直接式」だけが production 共有の証拠。入れ子の文の
    並び、``except`` の型、``match`` の case guard は条件付きなので対象外。
    """

    assert _exempts(_with_statement(statement)) is exempt, label


def test_an_async_for_iterable_is_a_direct_expression():
    """``async for`` の iterable も直接式（body は対象外）。"""

    exempted = scan_source(
        "sample",
        "async def f(self, expr, consume):\n"
        "    rendered = expr.to_string()\n"
        "    async for item in rendered:\n"
        "        pass\n"
        "    self._debug_print(rendered)\n",
    )
    assert not exempted.render_in_debug_sink, exempted.describe()
    reported = scan_source(
        "sample",
        "async def f(self, expr, items, consume):\n"
        "    rendered = expr.to_string()\n"
        "    async for item in items:\n"
        "        consume(rendered)\n"
        "    self._debug_print(rendered)\n",
    )
    assert [entry[2] for entry in reported.render_in_debug_sink] == [
        "_debug_print(... rendered = to_string() ...)"
    ]


def test_an_async_with_context_is_a_direct_expression():
    exempted = scan_source(
        "sample",
        "async def f(self, expr):\n"
        "    rendered = expr.to_string()\n"
        "    async with rendered:\n"
        "        pass\n"
        "    self._debug_print(rendered)\n",
    )
    assert not exempted.render_in_debug_sink, exempted.describe()


def test_every_statement_kind_is_in_the_exemption_grammar():
    """この Python の全 statement 種別が表にあること。

    新しい種別が増えたらここで FAIL する。表に載せるまでは
    :func:`direct_production_expressions` が ``None`` を返すので、黙って免除が
    広がることはない（既定 fail-closed）。
    """

    present = {kind.__name__ for kind in ast.stmt.__subclasses__()}
    missing = present - set(_DIRECT_PRODUCTION_FIELDS)
    assert not missing, f"statement kinds with no declared exemption grammar: {sorted(missing)}"


def test_an_unknown_statement_kind_grants_no_exemption():
    """表に無い種別は既定で証拠なし（permissive に通らない）。"""

    class _FutureStatement(ast.stmt):
        _fields = ("value",)

    unknown = _FutureStatement()
    unknown.value = ast.parse("rendered", mode="eval").body
    assert direct_production_expressions(unknown) is None
    assert not _has_direct_production_read([unknown], "rendered", set())


@pytest.mark.parametrize(
    "producer, detail",
    [
        ("expr.to_string()", "_debug_print(... rendered = to_string() ...)"),
        ("expr.to_smt()", "_debug_print(... rendered = to_smt() ...)"),
        (
            "expensive_factory().summarize_expression(expr)",
            "_debug_print(... rendered = <computed>.summarize_expression() ...)",
        ),
    ],
)
def test_a_conditional_position_grants_no_exemption_for_any_producer(producer, detail):
    violations = scan_source(
        "sample",
        "def f(self, expr, consume):\n"
        f"    rendered = {producer}\n"
        "    try:\n"
        "        pass\n"
        "    except rendered:\n"
        "        pass\n"
        "    self._debug_print(rendered)\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_sink] == [detail]


def test_a_deferred_body_inside_a_direct_expression_is_not_evidence():
    """直接式の中でも、``lambda`` 本体のように後回しの部分は証拠にしない。"""

    violations = scan_source(
        "sample",
        "def f(self, expr, apply):\n"
        "    rendered = expr.to_string()\n"
        "    apply(lambda: consume(rendered))\n"
        "    self._debug_print(rendered)\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_sink] == [
        "_debug_print(... rendered = to_string() ...)"
    ]


def test_a_nested_function_body_is_not_reachable_from_repr():
    """R4: ``__repr__`` の中の ``def`` 本体は呼ばれるまで走らない。"""

    violations = scan_source(
        "sample",
        "class Sample:\n"
        "    def __repr__(self):\n"
        "        def later():\n"
        "            return self.value.to_string()\n"
        "        return 'Sample'\n",
    )
    assert not violations.render_in_dunder, violations.describe()
    # 本体が直接書かれていれば従来どおり検出する。
    direct = scan_source(
        "sample",
        "class Sample:\n"
        "    def __repr__(self):\n"
        "        return self.value.to_string()\n",
    )
    assert [entry[2] for entry in direct.render_in_dunder] == ["__repr__ calls to_string()"]


# -- expression 段の positive grammar ------------------------------------------

def _exempts_expression(tail: str) -> bool:
    """``rendered`` が production 共有として免除されるか。"""

    violations = scan_source(
        "sample",
        "def f(self, expr, cond, items, cheap, key, consume):\n"
        "    rendered = expr.to_string()\n"
        + tail
        + "    self._debug_print(rendered)\n",
    )
    return not violations.render_in_debug_sink


#: (ラベル, 文, 免除されるか)。「この式を評価すれば必ずその名前を読む」と
#: 局所的に言える位置だけが証拠。条件付き・別束縛・後回しの位置は対象外。
_EXPRESSION_GRAMMAR = [
    # 必ず読む位置 → 証拠になる
    ("そのまま渡す", "    consume(rendered)\n", True),
    ("Call の keyword", "    consume(key=rendered)\n", True),
    ("Tuple の要素", "    consume((rendered, 1))\n", True),
    ("List の要素", "    consume([rendered])\n", True),
    ("Dict の値", "    consume({'k': rendered})\n", True),
    ("Subscript の添字", "    consume(items[rendered])\n", True),
    ("Subscript の対象", "    consume(rendered[0])\n", True),
    ("Attribute の対象", "    consume(rendered.attr)\n", True),
    ("BinOp", "    consume(rendered + cheap)\n", True),
    ("UnaryOp", "    consume(not rendered)\n", True),
    ("Compare の左", "    consume(rendered == cond)\n", True),
    ("Compare の最初の comparator", "    consume(cond == rendered)\n", True),
    ("f-string", "    consume(f'{rendered}')\n", True),
    ("BoolOp の先頭", "    consume(rendered and cond)\n", True),
    ("IfExp の test", "    consume(cheap if rendered else cheap)\n", True),
    ("comprehension の最初の iterable", "    consume([x for x in rendered])\n", True),
    ("Call の func", "    consume(rendered())\n", True),
    # 条件付き・別束縛・後回し → 証拠にしない
    ("BoolOp and の後ろ", "    consume(cond and rendered)\n", False),
    ("BoolOp or の後ろ", "    consume(cond or rendered)\n", False),
    ("IfExp の body", "    consume(rendered if cond else cheap)\n", False),
    ("IfExp の orelse", "    consume(cheap if cond else rendered)\n", False),
    ("Compare の 2 つ目の comparator", "    consume(cond < cheap < rendered)\n", False),
    ("comprehension の shadow", "    consume([rendered for rendered in items])\n", False),
    ("comprehension の要素式", "    consume([rendered for x in items])\n", False),
    ("comprehension の filter", "    consume([x for x in items if rendered])\n", False),
    ("generator 本体", "    consume(x for x in items if rendered)\n", False),
    ("lambda 本体", "    consume(lambda: rendered)\n", False),
    ("lambda の default（実在しないので対象外）", "    consume(lambda x=rendered: x)\n", False),
]


@pytest.mark.parametrize(
    "label, tail, exempt",
    _EXPRESSION_GRAMMAR,
    ids=[case[0] for case in _EXPRESSION_GRAMMAR],
)
def test_the_expression_exemption_grammar_is_fixed(label, tail, exempt):
    """免除の証拠になる式の位置を固定する。

    statement 段（:func:`direct_production_expressions`）で「その文を実行したら
    必ず評価される式」を選んだあと、expression 段
    （:func:`direct_production_reads`）で「その式を評価したら必ずその名前を読むか」
    を見る。2 段とも whitelist で、載っていない形は証拠ゼロ。
    """

    assert _exempts_expression(tail) is exempt, label


@pytest.mark.parametrize(
    "source, supported",
    [
        ("rendered", True),
        ("(rendered,)", True),
        ("[rendered]", True),
        ("{'k': rendered}", True),
        ("f(rendered)", True),
        ("items[rendered]", True),
        ("rendered.attr", True),
        ("rendered + 1", True),
        ("not rendered", True),
        ("rendered == 1", True),
        ("f'{rendered}'", True),
        ("rendered and x", True),
        ("rendered if x else y", True),
        ("[x for x in rendered]", True),
        ("lambda: rendered", True),   # 形は既知（本体は辿らない）
        ("1", True),
    ],
)
def test_the_expression_grammar_covers_what_production_uses(source, supported):
    """棚卸しで出た形はすべて表にあること（``None`` を返さない）。"""

    node = ast.parse(source, mode="eval").body
    assert (_certain_subexpressions(node) is not None) is supported, source


def test_an_unsupported_expression_kind_gives_no_evidence():
    """表に無い式（``yield`` 等）は証拠ゼロ（fail-closed）。"""

    function = ast.parse("def g():\n    x = yield rendered\n").body[0]
    yielded = function.body[0].value
    assert _certain_subexpressions(yielded) is None
    assert not direct_production_reads(yielded, "rendered")


def test_a_debug_read_is_never_production_evidence():
    """sink の引数そのものを production の証拠にしない。"""

    call = ast.parse("self._debug_print(rendered)", mode="eval").body
    name = next(
        node for node in ast.walk(call)
        if isinstance(node, ast.Name) and node.id == "rendered"
    )
    assert direct_production_reads(call, "rendered")
    assert not direct_production_reads(call, "rendered", {id(name)})


# -- binding grammar ------------------------------------------------------------

@pytest.mark.parametrize(
    "source, expected, label",
    [
        ("name = 0", {"name"}, "単純な名前"),
        ("a, b = 0, 1", {"a", "b"}, "tuple 分解"),
        ("[a, b] = 0, 1", {"a", "b"}, "list 分解"),
        ("a, *rest = items", {"a", "rest"}, "starred"),
        ("(a, (b, c)) = x", {"a", "b", "c"}, "入れ子の分解"),
        ("items[0] = x", set(), "添字は局所名を作らない"),
        ("obj.attr = x", set(), "属性は局所名を作らない"),
        ("a, obj.attr = x", {"a"}, "分解の一部が属性"),
    ],
)
def test_the_binding_grammar_is_fixed(source, expected, label):
    """代入先が束縛する局所名を 1 か所で決める（3 番目の positive grammar）。"""

    target = ast.parse(source).body[0].targets[0]
    assert bound_names(target) == expected, label


def test_an_unknown_target_shape_is_unknown_not_empty():
    """知らない形は空集合ではなく ``None``（呼び出し側が安全側に倒せるように）。"""

    class _FutureTarget(ast.expr):
        _fields = ()

    assert bound_names(_FutureTarget()) is None


def test_a_destructured_producer_is_refused_not_guessed():
    """分解代入は位置で値が決まる。解かずに B1 で拒否する。"""

    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    rendered, other = expr.to_string()\n"
        "    self._debug_print(rendered)\n",
    )
    assert not violations.render_in_debug_sink
    assert [entry[2] for entry in violations.unsupported_producer_binding] == [
        "to_string()"
    ]


def test_a_starred_producer_target_is_refused_too():
    violations = scan_source(
        "sample",
        "def f(self, expr):\n"
        "    rendered, *rest = expr.to_string()\n"
        "    self._debug_print(rendered)\n",
    )
    assert [entry[2] for entry in violations.unsupported_producer_binding] == [
        "to_string()"
    ]


@pytest.mark.parametrize(
    "rebind, ends, label",
    [
        ("    rendered, other = ('cheap', 0)\n", True, "分解代入"),
        ("    rendered = 'cheap'\n", True, "単純な再代入"),
        ("    with lock as rendered:\n        pass\n", True, "with の as"),
        ("    def rendered():\n        pass\n", True, "同名の def"),
        ("    class rendered:\n        pass\n", True, "同名の class"),
        ("    import rendered\n", True, "import"),
        ("    from pkg import thing as rendered\n", True, "from import as"),
        ("    for rendered in items:\n        pass\n", False, "for の target（0 回あり得る）"),
        ("    try:\n        pass\n    except Exception as rendered:\n        pass\n",
         False, "except の as（例外次第）"),
        ("    if cond:\n        rendered = 'cheap'\n", False, "入れ子の並びの中の代入"),
    ],
)
def test_only_an_unconditional_rebinding_ends_the_window(rebind, ends, label):
    """window を切るのは **必ず**束縛し直す構文だけ。

    切りすぎると、届いている値の読み出しを見逃す。切らなすぎると、もう届かない
    値の読み出しを古い代入のせいにする。
    """

    violations = scan_source(
        "sample",
        "def f(self, expr, cond, items, lock):\n"
        "    rendered = expr.to_string()\n"
        + rebind
        + "    self._debug_print(rendered)\n",
    )
    # 束縛し直されていれば、その sink 読み出しは古い代入のものではない。
    assert bool(violations.render_in_debug_sink) is not ends, label


# -- annotation は免除の証拠にしない --------------------------------------------

@pytest.mark.parametrize(
    "header, label",
    [
        ("def inner(x: rendered):\n        pass", "parameter annotation"),
        ("def inner() -> rendered:\n        pass", "戻り値 annotation"),
    ],
)
@pytest.mark.parametrize("future", [True, False], ids=["future あり", "future なし"])
def test_an_annotation_is_never_production_evidence(header, label, future):
    """annotation は module 次第で評価されないので、免除の証拠にしない。

    ``from __future__ import annotations`` の有無で判定が変わらないこと
    （exemption 側は module の評価モードに依存しない）。
    """

    prologue = "from __future__ import annotations\n" if future else ""
    violations = scan_source(
        "sample",
        prologue
        + "def outer(self, expr):\n"
        "    rendered = expr.to_string()\n"
        f"    {header}\n"
        "    self._debug_print(rendered)\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_sink] == [
        "_debug_print(... rendered = to_string() ...)"
    ], (label, future)


def test_a_default_argument_is_still_production_evidence():
    """default は必ず定義時に評価されるので証拠のまま。"""

    violations = scan_source(
        "sample",
        "def outer(self, expr):\n"
        "    rendered = expr.to_string()\n"
        "    def inner(x=rendered):\n"
        "        return x\n"
        "    self._debug_print(rendered)\n",
    )
    assert not violations.render_in_debug_sink, violations.describe()


@pytest.mark.parametrize("future", [True, False], ids=["future あり", "future なし"])
def test_detection_treats_an_annotation_the_same_either_way(future):
    """検出側は安全側に倒して module mode に依存しない。

    本 package の annotation 25,273 個に禁止呼び出しは 0 件なので、どちらに
    倒しても現状の判定は変わらない。過検出側（= 評価されるとみなす）に統一し、
    module 単位の評価モードを持ち込まない。
    """

    prologue = "from __future__ import annotations\n" if future else ""
    violations = scan_source(
        "sample",
        prologue
        + "def f(self, expr):\n"
        "    if self.debug:\n"
        "        def inner(x: expr.to_string()):\n"
        "            pass\n",
    )
    assert [entry[2] for entry in violations.render_in_debug_guard] == ["to_string()"]


# -- producer origin は MAY、rebind と免除は MUST ------------------------------

def _producer_case(body: str) -> EagerDebugRenderingViolations:
    return scan_source(
        "sample",
        "def f(self, expr, cond, consume, rendered):\n" + body,
    )


#: (ラベル, 文, 追えるか)。支持するのは production 実測の 2 形だけ。
#: それ以外で tracked producer を束縛する形は B1（unsupported）。
_PRODUCER_ORIGIN_GRAMMAR = [
    ("単純な Assign", "    rendered = expr.to_string()\n", True),
    ("AnnAssign", "    rendered: str = expr.to_string()\n", True),
    ("chained assign", "    other = rendered = expr.to_string()\n", False),
    ("分解代入", "    rendered, other = expr.to_string()\n", False),
    ("starred", "    rendered, *rest = expr.to_string()\n", False),
    ("AugAssign", "    rendered += expr.to_string()\n", False),
    ("walrus 単独", "    (rendered := expr.to_string())\n", False),
    ("walrus を呼び出しの引数で", "    consume(rendered := expr.to_string())\n", False),
    ("walrus が短絡の後ろ", "    cond and (rendered := expr.to_string())\n", False),
]


@pytest.mark.parametrize(
    "label, body, supported",
    _PRODUCER_ORIGIN_GRAMMAR,
    ids=[case[0] for case in _PRODUCER_ORIGIN_GRAMMAR],
)
def test_the_producer_origin_contract_is_inventory_backed(label, body, supported):
    """producer の値がどの名前に入ったかを言えるのは、実測にある 2 形だけ。

    ``used = rendered = f()`` は 1 つの値が 2 つの名前を指すので、片方の
    production 使用がもう片方を免除する。``other, rendered = (f(), 0)`` は位置で
    値が決まる。どちらも正しく追うには値と名前の対応を解く解析が要るが、
    production には 1 件も無い。だから **解かずに拒否**する。
    """

    violations = _producer_case(body + "    self._debug_print(rendered)\n")
    assert bool(violations.render_in_debug_sink) is supported, label
    assert bool(violations.unsupported_producer_binding) is not supported, label


def test_a_chained_producer_does_not_lose_its_production_use():
    """chained を推論していた頃の誤検出が出ないこと。

    ``used`` は production が読んでいるので、同じ値を指す ``rendered`` を
    「debug 専用」と報告してはいけない。B1 に倒すことで誤検出が消える。
    """

    violations = _producer_case(
        "    used = rendered = expr.to_string()\n"
        "    consume(used)\n"
        "    self._debug_print(rendered)\n"
    )
    assert not violations.render_in_debug_sink, violations.describe()
    assert violations.unsupported_producer_binding


def test_a_target_that_binds_no_local_is_not_unsupported():
    """``obj.attr = producer`` / ``d[k] = producer`` は追う対象が無いだけ。"""

    for body in ("    obj.attr = expr.to_string()\n", "    store[key] = expr.to_string()\n"):
        violations = scan_source(
            "sample", "def f(self, expr, obj, store, key):\n" + body
        )
        assert not violations.unsupported_producer_binding, body
        assert not violations, violations.describe()


def test_a_deferred_walrus_is_not_an_origin_here():
    """``lambda`` 本体の ``:=`` はこの文では走らないので B1 にもしない。"""

    violations = _producer_case(
        "    thunk = lambda: (rendered := expr.to_string())\n"
        "    self._debug_print(rendered)\n"
    )
    assert not violations.render_in_debug_sink, violations.describe()
    assert not violations.unsupported_producer_binding, violations.describe()


def test_an_unsupported_producer_binding_fails_loudly():
    """束縛先の形が判らない producer を黙って飛ばさない。"""

    class _FutureTarget(ast.expr):
        _fields = ()
        _attributes = ("lineno", "col_offset")

    assert bound_names(_FutureTarget()) is None

    source = "def f(self, expr):\n    rendered = expr.to_string()\n"
    tree = ast.parse(source)
    assignment = tree.body[0].body[0]
    unknown = _FutureTarget()
    unknown.lineno, unknown.col_offset = assignment.lineno, 0
    assignment.targets = [unknown]

    violations = EagerDebugRenderingViolations()
    _EagerDebugRenderingScanner("sample", violations, OWNED_SUMMARY_FUNCTIONS).scan(tree)
    assert [entry[2] for entry in violations.unsupported_producer_binding] == [
        "to_string()"
    ]
    assert bool(violations) is True
    assert "B1 " in violations.describe()


def test_a_supported_binding_reports_nothing_unsupported():
    violations = _producer_case(
        "    rendered = expr.to_string()\n    self._debug_print(rendered)\n"
    )
    assert not violations.unsupported_producer_binding


def test_no_unsupported_producer_binding_in_the_package():
    violations = scan_package()
    assert not violations.unsupported_producer_binding, violations.describe()


# -- producer が「走る」ことと「値が入る」ことは別 ------------------------------

_RHS_ROOT_GRAMMAR = [
    # (ラベル, RHS, root が producer か)
    ("producer そのもの", "expr.to_string()", True),
    ("unsafe renderer そのもの", "expensive_factory().summarize_expression(expr)", True),
    ("別の呼び出しの戻り値", "consume(expr.to_string())", False),
    ("組み込みの戻り値", "len(expr.to_string())", False),
    ("変換関数の戻り値", "transform(expr.to_string())", False),
    ("tuple の要素", "(expr.to_string(), other)", False),
    ("list の要素", "[expr.to_string()]", False),
    ("dict の値", "{'k': expr.to_string()}", False),
    ("f-string", "f'{expr.to_string()}'", False),
    ("連結", "expr.to_string() + other", False),
    ("比較", "expr.to_string() == other", False),
    ("条件式", "expr.to_string() if cond else other", False),
    ("添字", "expr.to_string()[0]", False),
    ("属性", "expr.to_string().upper", False),
    ("lambda（本体で走る）", "lambda: expr.to_string()", False),
]


@pytest.mark.parametrize(
    "label, source, is_root",
    _RHS_ROOT_GRAMMAR,
    ids=[case[0] for case in _RHS_ROOT_GRAMMAR],
)
def test_the_producer_value_contract_looks_at_the_rhs_root(label, source, is_root):
    """「値が producer の戻り値か」は root だけで決まる。

    ``rendered = consume(expr.to_string())`` は ``to_string()`` を走らせるが、
    ``rendered`` が受け取るのは ``consume()`` の戻り値。両者を混同すると
    ``rendered`` を producer の別名とみなしてしまう（本 package に 145 箇所）。
    """

    value = ast.parse(source, mode="eval").body
    kind, _ = direct_tracked_producer(value, OWNED_SUMMARY_FUNCTIONS)
    assert bool(kind) is is_root, label


@pytest.mark.parametrize(
    "label, rhs",
    [
        ("別の呼び出しの戻り値", "consume(expr.to_string())"),
        ("組み込みの戻り値", "len(expr.to_string())"),
        ("tuple の要素", "(expr.to_string(), other)"),
        ("f-string", "f'{expr.to_string()}'"),
        ("変換関数の戻り値", "transform(expr.to_string())"),
    ],
)
def test_a_nested_producer_is_not_an_alias_and_not_a_violation(label, rhs):
    """RHS の中で producer が走るだけなら alias ではない（B1 でもない）。"""

    violations = scan_source(
        "sample",
        "def f(self, expr, consume, transform, other):\n"
        f"    rendered = {rhs}\n"
        "    self._debug_print(rendered)\n",
    )
    assert not [
        entry for entry in violations.render_in_debug_sink if "rendered =" in entry[2]
    ], (label, violations.describe())
    assert not violations.unsupported_producer_binding, label


@pytest.mark.parametrize(
    "label, body",
    [
        ("chained", "    a = rendered = consume(expr.to_string())\n"),
        ("分解", "    rendered, other = consume(expr.to_string())\n"),
        ("AugAssign", "    rendered += consume(expr.to_string())\n"),
        ("walrus", "    (rendered := consume(expr.to_string()))\n"),
    ],
)
def test_an_unsupported_target_with_a_nested_producer_is_not_refused(label, body):
    """B1 は **direct producer** を追えないときだけ。

    ``a = b = consume(producer)`` は alias を作っていないだけで、正当な
    production の書き方。target の形だけを理由に拒否しない。
    """

    violations = scan_source(
        "sample",
        "def f(self, expr, consume, a, other, rendered):\n"
        + body
        + "    self._debug_print(rendered)\n",
    )
    assert not violations.unsupported_producer_binding, (label, violations.describe())


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

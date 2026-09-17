# -*- coding: utf-8 -*-
"""debug 表示の所有者（Issue #22）。

debug message に式・条件を載せる手段は本 module だけが持つ。``to_string()`` /
``to_smt()`` は共有 DAG を木として全展開するので、debug 出力からは呼ばない。
ここにある renderer は **出力量も走査量も有界**。巨大な式・長い列・巨大な値を
渡されても、見る量が入力サイズに依存しない:

* 深さ（``summarize_expression``）、node 数と fan-out
  （``summarize_structural_preview``）、列の件数（``summarize_*s``）、
  dataclass field 数（``summarize_runtime_ref``）をそれぞれ上限で縛る
* 1 要素の表示は ``_primitive_text`` だけを使う。exact type で判定し、任意
  object の ``__str__`` / ``__repr__`` / ``stable_key()`` / ``to_dict()`` を
  起動しない。大きい int は 10 進化せず bit 幅、長い str は slice で示す
* 判定に使う structural key（``core.structural``）は debug から呼ばない。
  あちらの予算は node 数しか縛らないので、operand / branch / value の中身を
  辿り得る

本 module は「契約の語彙」も所有する。静的 guard
（``tests/unit/test_no_eager_debug_rendering.py``）はこの 3 つを import して
使うので、新しい bounded renderer を足すときに触るのは本 module だけでよい:

* :data:`BOUNDED_DEBUG_RENDERERS` — debug message に入れてよい描画関数
* :data:`UNBOUNDED_RENDER_CALLS` — debug message に入れてはいけない描画 method
* :data:`DEBUG_AVAILABILITY_PREDICATES` — 出力可否を答えるだけの述語

family 側の wrapper（``_debug_expr_summary`` など）は本 module の renderer へ
委譲するだけなので名前を数え上げない。静的 guard が委譲を辿って同一視する。

debug guard の置き方: guard が複数 module に散る family は host class に
``_debug_available()`` / ``debug_available()`` を 1 つ持ち、そこだけを判定点に
する（recurrence / returns / expander / PHI / simplifier）。guard が 1 module に
閉じる class は ``self.debug`` がその判定点。
"""

from __future__ import annotations

from collections.abc import Sized
from dataclasses import fields, is_dataclass
from enum import Enum
from itertools import islice
from typing import Any, Callable, FrozenSet, Iterable, List, Optional, Set, Tuple

from scripts.function_tracer_pcode.core import Condition, Expression, ExpressionType


def summarize_expression(expr: Optional[Expression], max_depth: int = 4) -> str:
    """Render a compact, cycle-safe summary without full pretty-printing."""
    if expr is None:
        return "None"

    visited: Set[int] = set()

    def _render(node: Optional[Expression], depth: int) -> str:
        if node is None:
            return "None"
        if depth <= 0:
            return "..."

        node_id = id(node)
        if node_id in visited:
            return "<cycle>"
        visited.add(node_id)

        try:
            expr_type = getattr(node, "expr_type", None)
            # 既定値を ``str(expr_type)`` にすると、name が無いときに任意
            # object の ``__str__`` が走る。名前は bounded な取り方で得る。
            expr_type_name = _expression_kind(node)

            if expr_type == ExpressionType.CONSTANT:
                return f"CONST({_primitive_text(getattr(node, 'value', None))})"

            if expr_type == ExpressionType.PARAMETER:
                return f"PARAM({_node_name(node)})"

            if expr_type == ExpressionType.VARIABLE:
                return f"VAR({_node_name(node)})"

            if expr_type == ExpressionType.UNKNOWN:
                return f"UNKNOWN({_node_name(node)})"

            if expr_type == ExpressionType.CALL:
                return f"CALL({_node_name(node)}, argc={_container_length(node.operands)})"

            if expr_type == ExpressionType.INTRINSIC:
                return f"INTRINSIC({_node_name(node)}, argc={_container_length(node.operands)})"

            if expr_type == ExpressionType.MEMORY:
                children = _first_children(node.operands, 1)
                return f"MEM[{_render(children[0] if children else None, depth - 1)}]"

            if expr_type == ExpressionType.UNARY_OP:
                children = _first_children(node.operands, 1)
                operator = _primitive_text(node.operator) if node.operator else "UNARY"
                return f"{operator}({_render(children[0] if children else None, depth - 1)})"

            if expr_type == ExpressionType.BINARY_OP:
                operands = _first_children(node.operands, 2)
                left = _render(operands[0] if len(operands) > 0 else None, depth - 1)
                right = _render(operands[1] if len(operands) > 1 else None, depth - 1)
                return f"{_primitive_text(node.operator) if node.operator else 'BINARY'}({left}, {right})"

            if expr_type == ExpressionType.PHI:
                return f"PHI(branches={_container_length(node.value)})"

            return expr_type_name
        finally:
            visited.discard(node_id)

    return _render(expr, max_depth)


def _node_name(node: Any) -> str:
    name = getattr(node, "name", None)
    return _primitive_text(name) if name else "?"


def _container_length(value: Any) -> str:
    """要素数を O(1) で聞ける組み込み容器だけ数える。

    任意 object の ``__len__`` / ``__bool__`` は何をするか分からないので、
    exact type で判定して外れたら件数を名乗らない。
    """

    if value is None:
        return "0"
    return str(len(value)) if type(value) in (list, tuple, dict, set, frozenset) else "?"


def _first_children(value: Any, count: int) -> list:
    """子の先頭 ``count`` 個だけを読む（列全体を反復しない）。"""

    if value is None:
        return []
    try:
        return list(islice(iter(value), max(0, int(count))))
    except TypeError:
        return []


def summarize_condition(condition: Optional[Condition], max_depth: int = 4) -> str:
    if condition is None:
        return "None"
    expr_summary = summarize_expression(condition.expression, max_depth=max_depth)
    return f"(not {expr_summary})" if condition.negated else expr_summary


#: debug サマリーに並べる要素数の既定上限。列の長さ自体は打ち切り件数で示す。
DEFAULT_MAX_ITEMS = 8

#: 1 要素あたりの最大文字数（テキスト化の上限）。
DEFAULT_MAX_TEXT = 80

#: 整数をそのまま 10 進で出す上限。これを超えたら桁数ではなく bit 幅で示す。
DEFAULT_MAX_INT_BITS = 64

#: :func:`summarize_structural_preview` が見る node 数の上限。
DEFAULT_MAX_PREVIEW_NODES = 24

#: 1 node から辿る子の数の上限（fan-out）。CALL / INTRINSIC の巨大 operand 群や
#: PHI の巨大 branch 群を全部辿らないための hard bound。
DEFAULT_MAX_PREVIEW_FANOUT = 4


def _summarize_sequence(
    items: Optional[Iterable[Any]],
    render_item: Callable[[Any], str],
    max_items: int,
) -> str:
    """列を ``[a, b, +3 more]`` 形式の有界文字列にする。

    **走査も有界**: 長さを O(1) で聞ける列（``Sized``）なら先頭 ``max_items``
    個だけを読み、残数は ``len()`` から求める。長さの分からない iterable /
    generator は ``max_items + 1`` 個までしか読まず、残数は数えずに ``+more``
    とだけ書く。「debug のために列を最後まで回す」ことが起きないのが契約。
    """

    if items is None:
        return "[]"
    limit = max(0, int(max_items))
    total = len(items) if isinstance(items, Sized) else None
    # 長さが分かるなら余分な 1 個も読まない。分からないときだけ 1 個だけ
    # 先読みして「まだ続きがある」ことを知る。
    head = list(islice(iter(items), limit if total is not None else limit + 1))
    overflowed = total is None and len(head) > limit
    if overflowed:
        head = head[:limit]
    rendered = [render_item(item) for item in head]

    body = ", ".join(rendered)
    if total is not None and total > len(rendered):
        suffix = f"+{total - len(rendered)} more"
    elif overflowed:
        # 残数は数えない（数えると列を最後まで回すことになる）。
        suffix = "+more"
    else:
        suffix = ""
    if suffix:
        body = f"{body}, {suffix}" if body else suffix
    return f"[{body}]"


def summarize_expressions(
    expressions: Optional[Iterable[Optional[Expression]]],
    max_depth: int = 4,
    max_items: int = DEFAULT_MAX_ITEMS,
) -> str:
    """式列の有界サマリー。full render しないので debug 出力から安全に呼べる。"""

    return _summarize_sequence(
        expressions,
        lambda item: summarize_expression(item, max_depth=max_depth),
        max_items,
    )


def summarize_conditions(
    conditions: Optional[Iterable[Optional[Condition]]],
    max_depth: int = 4,
    max_items: int = DEFAULT_MAX_ITEMS,
) -> str:
    """条件列の有界サマリー。full render しないので debug 出力から安全に呼べる。"""

    return _summarize_sequence(
        conditions,
        lambda item: summarize_condition(item, max_depth=max_depth),
        max_items,
    )


def summarize_values(
    values: Optional[Iterable[Any]],
    max_text: int = DEFAULT_MAX_TEXT,
    max_items: int = DEFAULT_MAX_ITEMS,
) -> str:
    """既に短いテキストの列（演算子名・別 renderer の出力）を束ねる。

    件数と 1 要素の長さを bound する。要素自体を有界にするのは呼び出し側の
    責任で、式や条件をそのまま渡してはいけない
    （:func:`summarize_expressions` / :func:`summarize_conditions` を使う）。
    """

    return _summarize_sequence(
        values, lambda value: _primitive_text(value, max_text), max_items
    )


def _primitive_text(value: Any, max_text: int = DEFAULT_MAX_TEXT) -> str:
    """入力サイズに依存しない表示だけを返す。

    ``str(value)`` / ``repr(value)`` は任意 object の実装を起動するので使わない
    （frozen dataclass は field を再帰展開する）。判定は **exact type** で行い、
    subclass の ``__str__`` には触れない。大きい値も「作ってから切る」のでは
    なく、最初から作らない:

    * ``int`` は ``DEFAULT_MAX_INT_BITS`` を超えたら 10 進化せず bit 幅で示す
    * ``str`` は先頭 ``max_text`` 文字だけを slice する
    * ``bytes`` は長さだけ（16 進化しない）
    * 容器・その他の object は型名（と組み込み容器なら要素数）だけ
    """

    limit = max(0, int(max_text))
    kind = type(value)
    if value is None:
        return "None"
    if kind is bool:
        return "True" if value else "False"
    if kind is int:
        bits = value.bit_length()
        return str(value) if bits <= DEFAULT_MAX_INT_BITS else f"<int bits={bits}>"
    if kind is float:
        return repr(value)
    if kind is str:
        return value if len(value) <= limit else value[:limit] + "..."
    if kind is bytes:
        return f"<bytes len={len(value)}>"
    if kind in (list, tuple, dict, set, frozenset):
        return f"<{kind.__name__} len={len(value)}>"
    if isinstance(value, Enum):
        name = getattr(value, "name", None)
        if type(name) is str:
            return name if len(name) <= limit else name[:limit] + "..."
    return f"<{kind.__name__}>"


def summarize_runtime_ref(runtime_ref: Any, max_fields: int = DEFAULT_MAX_ITEMS) -> str:
    """runtime ref を型名 + 定数時間で読める primitive field で表す。

    ``stable_key()`` は **呼ばない**。``LoopSummaryRef.stable_key`` のように
    seed / witness / guard / case を全部辿って式のキーを組み立てる実装があり、
    debug 表示のために起動してよい処理ではない（Issue #22）。``repr`` も同じ
    理由で使わない（frozen dataclass は field を再帰展開する）。

    出す情報は「型名」と「dataclass field のうち primitive なもの」だけで、
    どちらも ref の中身の大きさに依存しない。識別子が要る場面では判定側の
    structural key を見ること（debug 表示は identity ではない）。
    """

    if runtime_ref is None:
        return "None"
    type_name = type(runtime_ref).__name__
    items = _primitive_dataclass_fields(runtime_ref, max_fields)
    if not items:
        return type_name
    return f"{type_name}{summarize_values(items, max_items=max_fields)}"


def _primitive_dataclass_fields(value: Any, max_fields: int) -> Tuple[str, ...]:
    """dataclass の primitive field を ``name=value`` の列で返す（先頭 N 件）。

    field の数は型ごとに定数で、各 field の読み出しも O(1)。入れ子の式・列は
    型名に落ちるので、ref が抱える中身を辿ることはない。
    """

    if not is_dataclass(value) or isinstance(value, type):
        return ()
    limit = max(0, int(max_fields))
    items = []
    for field in fields(value):
        if len(items) >= limit:
            break
        attribute = getattr(value, field.name, None)
        if attribute is None or isinstance(attribute, (bool, int, float, str, Enum)):
            items.append(f"{field.name}={_primitive_text(attribute)}")
    return tuple(items)


def summarize_structural_preview(
    expr: Optional[Expression],
    max_nodes: int = DEFAULT_MAX_PREVIEW_NODES,
    max_fanout: int = DEFAULT_MAX_PREVIEW_FANOUT,
) -> str:
    """式の構造を **hard bound つきで** 覗く debug 専用 preview。

    判定に使う structural key（``core.structural.expression_key``）は debug から
    呼ばない。あちらの予算は「何 node 辿るか」しか縛らないので、CALL /
    INTRINSIC の operand 全件、PHI の branch 全件、``value`` に入った巨大な
    容器や ``stable_key()`` を持つ object を辿り得る。

    ここで保証するのは 3 つとも hard bound であること:

    * 見る node 数 ≤ ``max_nodes``
    * 1 node から辿る子の数 ≤ ``max_fanout``（列の残りは読まない）
    * 1 node の local 表示は :func:`_primitive_text` だけを使う（任意 object の
      ``__str__`` / ``stable_key()`` / ``to_dict()`` を起動しない）

    これは identity ではなく triage 用の手掛かり。等価性の判断には使わない。
    """

    if expr is None:
        return "None"

    node_limit = max(1, int(max_nodes))
    fanout_limit = max(0, int(max_fanout))
    records: List[str] = []
    visited: Set[int] = set()
    pending: List[Any] = [expr]
    truncated = False

    while pending:
        if len(records) >= node_limit:
            truncated = True
            break
        node = pending.pop(0)
        if node is None:
            continue
        node_id = id(node)
        if node_id in visited:
            records.append("<shared>")
            continue
        visited.add(node_id)
        records.append(_structural_node_record(node))
        children = _first_children(getattr(node, "operands", None), fanout_limit)
        if _expression_kind(node) == "PHI":
            children = _phi_branch_values(getattr(node, "value", None), fanout_limit)
        pending.extend(children)

    if truncated or pending:
        records.append("+more")
    return "[" + ", ".join(records) + "]"


def _expression_kind(node: Any) -> str:
    expr_type = getattr(node, "expr_type", None)
    name = getattr(expr_type, "name", None)
    return name if type(name) is str else "?"


def _structural_node_record(node: Any) -> str:
    """1 node の local 表示。すべて定数時間の field だけで作る。"""

    parts = [_expression_kind(node)]
    operator = getattr(node, "operator", None)
    if operator:
        parts.append(_primitive_text(operator))
    name = getattr(node, "name", None)
    if name:
        parts.append(_primitive_text(name))
    size = getattr(node, "size", None)
    if size is not None:
        parts.append(f"size={_primitive_text(size)}")
    value = getattr(node, "value", None)
    if value is not None and _expression_kind(node) != "PHI":
        parts.append(f"value={_primitive_text(value)}")
    return ":".join(parts)


def _phi_branch_values(branches: Any, max_fanout: int) -> List[Any]:
    """PHI branch の先頭数件から値側だけを取り出す（全 branch を読まない）。"""

    values = []
    for branch in _first_children(branches, max_fanout):
        if isinstance(branch, (tuple, list)) and len(branch) == 2:
            values.append(branch[1])
        else:
            values.append(branch)
    return values


def summarize_expression_identity(
    expr: Optional[Expression],
    max_depth: int = 3,
) -> str:
    """式の identity を debug 用に有界表示する（要約 + 構造 preview + 由来）。

    3 つの欄はいずれも hard bound つき: ``summarize_expression`` が深さ、
    ``summarize_structural_preview`` が node 数と fan-out、
    ``summarize_runtime_ref`` が field 数を縛る。production の structural key は
    ここでは作らない（#76 のレビュー指摘は「debug 行が式を識別できること」で、
    ``tests/unit/test_debug_reporter.py`` がそれを固定している）。
    """

    if expr is None:
        return "None"

    return (
        f"{summarize_expression(expr, max_depth=max_depth)} "
        f"[type={_expression_kind(expr)}, size={_primitive_text(getattr(expr, 'size', None))}, "
        f"read_order={_primitive_text(getattr(expr, 'read_order_key', None))}, "
        f"runtime_ref={summarize_runtime_ref(getattr(expr, 'runtime_ref', None))}, "
        f"structural_preview={summarize_structural_preview(expr)}]"
    )


#: debug message に入れてよい描画関数（本 module が所有する）。
#: family 側の wrapper はここへ委譲するだけなので列挙しない。静的 guard が
#: 委譲を辿って同一視する。
BOUNDED_DEBUG_RENDERERS: FrozenSet[str] = frozenset({
    "summarize_expression",
    "summarize_condition",
    "summarize_expressions",
    "summarize_conditions",
    "summarize_values",
    "summarize_runtime_ref",
    "summarize_structural_preview",
    "summarize_expression_identity",
})

#: 共有 DAG を木として全展開する描画。debug message に入れてはいけない。
UNBOUNDED_RENDER_CALLS: FrozenSet[str] = frozenset({"to_string", "to_smt"})

#: 出力可否を答えるだけの述語（呼んでも何も描画しない）。
DEBUG_AVAILABILITY_PREDICATES: FrozenSet[str] = frozenset({
    "debug_available",
    "_debug_available",
    "debug_flag",
})

#: 出力可否を表す属性。guard 節の形を静的 guard が判定するのに使う。
DEBUG_AVAILABILITY_FLAGS: FrozenSet[str] = frozenset({"debug", "DEBUG"})

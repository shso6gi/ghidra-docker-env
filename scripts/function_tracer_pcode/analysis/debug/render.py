# -*- coding: utf-8 -*-
"""debug 表示の所有者（Issue #22）。

debug message に式・条件を載せる手段は本 module だけが持つ。``to_string()`` /
``to_smt()`` は共有 DAG を木として全展開するので、debug 出力からは呼ばない。
ここにある renderer は **出力量も走査量も有界** で、巨大な式・長い列を渡されても
先頭だけを見る。

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
from typing import Any, Callable, FrozenSet, Iterable, Optional, Set, Tuple

from scripts.function_tracer_pcode.core import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.structural import expression_key_safe


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
            expr_type_name = getattr(expr_type, "name", str(expr_type))

            if expr_type == ExpressionType.CONSTANT:
                try:
                    value = int(node.value)
                except Exception:
                    value = getattr(node, "value", "?")
                return f"CONST({value})"

            if expr_type == ExpressionType.PARAMETER:
                return f"PARAM({node.name or '?'})"

            if expr_type == ExpressionType.VARIABLE:
                return f"VAR({node.name or '?'})"

            if expr_type == ExpressionType.UNKNOWN:
                return f"UNKNOWN({node.name or '?'})"

            if expr_type == ExpressionType.CALL:
                arg_count = len(node.operands or [])
                return f"CALL({node.name or '?'}, argc={arg_count})"

            if expr_type == ExpressionType.INTRINSIC:
                arg_count = len(node.operands or [])
                return f"INTRINSIC({node.name or '?'}, argc={arg_count})"

            if expr_type == ExpressionType.MEMORY:
                inner = _render((node.operands or [None])[0], depth - 1)
                return f"MEM[{inner}]"

            if expr_type == ExpressionType.UNARY_OP:
                inner = _render((node.operands or [None])[0], depth - 1)
                return f"{node.operator or 'UNARY'}({inner})"

            if expr_type == ExpressionType.BINARY_OP:
                operands = node.operands or []
                left = _render(operands[0] if len(operands) > 0 else None, depth - 1)
                right = _render(operands[1] if len(operands) > 1 else None, depth - 1)
                return f"{node.operator or 'BINARY'}({left}, {right})"

            if expr_type == ExpressionType.PHI:
                branches = node.value or []
                return f"PHI(branches={len(branches)})"

            return expr_type_name
        finally:
            visited.discard(node_id)

    return _render(expr, max_depth)


def summarize_condition(condition: Optional[Condition], max_depth: int = 4) -> str:
    if condition is None:
        return "None"
    expr_summary = summarize_expression(condition.expression, max_depth=max_depth)
    return f"(not {expr_summary})" if condition.negated else expr_summary


#: debug サマリーに並べる要素数の既定上限。列の長さ自体は打ち切り件数で示す。
DEFAULT_MAX_ITEMS = 8

#: :func:`summarize_values` の 1 要素あたり最大文字数。
DEFAULT_MAX_TEXT = 80

#: identity 表示の途中で握れる失敗。構造キーの走査は不正な node / 深い入れ子で
#: これらを投げうる。debug 表示のためにそれ以外を握り潰さない（#108 の方向）。
_RECOVERABLE_IDENTITY_ERRORS = (AttributeError, TypeError, ValueError, RecursionError)


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

    limit = max(0, int(max_text))

    def _render(value: Any) -> str:
        text = _primitive_text(value)
        return text if len(text) <= limit else text[:limit] + "..."

    return _summarize_sequence(values, _render, max_items)


def _primitive_text(value: Any) -> str:
    """定数時間で作れる表示だけを返す。

    ``str(value)`` を無条件に呼ぶと、frozen dataclass のように field を再帰
    展開する ``__repr__`` を起動してしまう。primitive でないものは型名だけに
    落とす（debug 表示のために入力を辿らない、が契約）。
    """

    if value is None:
        return "None"
    if isinstance(value, Enum):
        return value.name
    if isinstance(value, (bool, int, float, str)):
        return str(value)
    return f"<{type(value).__name__}>"


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


def summarize_expression_identity(
    expr: Optional[Expression],
    max_depth: int = 3,
) -> str:
    """式の identity を debug 用に有界表示する（要約 + 構造キー + 由来）。

    ``structural`` は予算付きの :func:`expression_key_safe` なので、予算超過や
    opaque node では ``None`` になる。この識別子を失わないことは #76 のレビュー
    指摘で ``tests/unit/test_debug_reporter.py`` が固定している。走査量を
    node 予算だけで抑えるため、runtime ref の semantic key は含めない。
    """

    if expr is None:
        return "None"

    read_order_key = getattr(expr, "read_order_key", None)
    runtime_ref_summary = summarize_runtime_ref(getattr(expr, "runtime_ref", None))
    try:
        # ``include_semantic_runtime_refs=True``（既定）は node ごとに
        # ``runtime_ref.stable_key()`` を呼ぶ。node 数は budget で有界でも
        # 1 つの key の構築は有界ではないので、debug 表示では切る。ref の
        # 情報は上の ``runtime_ref`` 欄が別に出す。判定側が使う structural
        # key の既定は変えていない。
        structural_key = expression_key_safe(
            expr,
            include_memory_read_order=True,
            include_semantic_runtime_refs=False,
        )
    except _RECOVERABLE_IDENTITY_ERRORS:
        structural_key = None
    return (
        f"{summarize_expression(expr, max_depth=max_depth)} "
        f"[type={expr.expr_type.name}, size={expr.size}, "
        f"read_order={read_order_key}, runtime_ref={runtime_ref_summary}, "
        f"structural={structural_key}]"
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

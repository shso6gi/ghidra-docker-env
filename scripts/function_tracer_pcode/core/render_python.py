# -*- coding: utf-8 -*-
"""人向けの式表示（Python 風）。**証拠・表示専用**で、identity には使わない。

判定に使う表現は `core/structural.py`（構造 identity）と
`core/render_smt`（solver 入力）が持つ。ここが作るのは読むための文字列なので、
書式を変えても cache の当たり外れや証明の一致条件が動いてはいけない。
`to_string()` を key に使っている site が無いことは静的テストで固定する。

描画は DAG を 1 回だけ辿る（`core/render_plan`）。共有部分式は
`@h<8 桁>` の参照にして末尾の `where` で 1 回だけ書く。木として展開し直すと、
共有の多い式では表示が指数的に膨らみ、深い式では Python の再帰が尽きる。
"""

from __future__ import annotations

import hashlib
import re
from typing import Dict, List, NamedTuple, Optional

from scripts.function_tracer_pcode.core.render_metrics import record_render
from scripts.function_tracer_pcode.core.render_output import CountingWriter, RenderCounters
from scripts.function_tracer_pcode.core.render_plan import (
    NO_SHARING_POLICY,
    PLACEHOLDER_MARK,
    BindingNamespace,
    RenderGraphCycleError,
    RenderPlanInvariantError,
    SharingPolicy,
    build_render_plan,
    check_plan_invariants,
    collect_reserved_symbols,
    write_expansion,
)
from scripts.function_tracer_pcode.core.semantic_snapshot import traverse_semantic_graph


class HumanRenderContext(NamedTuple):
    """人向け表示の文脈。`simplify` だけが表示を変える。"""

    simplify: bool = True


#: 表示に現れる名前（変数名・関数名・共有参照）。共有参照の名前がこれらと
#: ぶつからないことを namespace owner が保証する。
_HUMAN_SYMBOL_RE = re.compile(r"(?P<bare>[@A-Za-z_][A-Za-z0-9_@.]*)")

#: fragment 中の子の参照（番号ごと）。
_PLACEHOLDER_RE = re.compile(PLACEHOLDER_MARK + r"\d+" + PLACEHOLDER_MARK)

#: 共有参照の接頭辞と形。
HUMAN_SHARED_PREFIX = "@h"
HUMAN_SHARED_TEMPLATE = "{prefix}{index}"

#: 人向け表示の共有方針。
#:
#: 共有参照は「同じ部分式が 2 回以上出る」かつ「それなりに大きい」ときだけ。
#: 小さい式に参照を挟むとかえって読みにくく、既存の表示が理由なく変わる。
#: `inline_max_bytes` は深い式で中間文字列が伸び続けるのを止めるためのもので、
#: これが無いと深さに対して連結費用が 2 乗になる。
HUMAN_SHARING_POLICY = SharingPolicy(
    min_shared_bytes=64,
    inline_max_bytes=4096,
    min_shared_tree_nodes=64,
    reference_bytes_estimate=11,
)

#: 人向け表示の項の性質（現状は空。足すならここと分類器の 2 箇所）。
_HUMAN_TERM_PROPERTIES = ()


def _classify_human_fragment(fragment: str, head, exact: bool):
    """人向け表示には「描画結果を見て分岐する」下流が無い。

    それでも分類器を通すのは、性質が必要になったときに足す場所を 1 つに
    しておくため（`RenderedTerm` は常に性質を持つ）。
    """

    return _HUMAN_TERM_PROPERTIES


def expression_to_string(expr, simplify: bool = True, *, shared: bool = True) -> str:
    """式を Python 互換の文字列へ変換する。"""

    return render_human_text(expr, HumanRenderContext(simplify=bool(simplify)), shared=shared)


def render_human_text(
    root,
    context: HumanRenderContext,
    *,
    shared: bool = True,
    limit_bytes: Optional[int] = None,
) -> str:
    """DAG を 1 回だけ辿って表示文字列を作る。

    node 本体が作るのは自分の分と子の参照だけで、木への展開は
    `CountingWriter` へ流しながら行う（上限に達したらそこで止まる）。
    """

    counters = RenderCounters(render_invocations=1)

    def body(node, node_context, resolve):
        return _render_human_node(node, node_context, resolve)

    policy = HUMAN_SHARING_POLICY if shared else NO_SHARING_POLICY
    try:
        plan = build_render_plan(
            root,
            context,
            body=body,
            classify=_classify_human_fragment,
            policy=policy,
            counters=counters,
            limit_bytes=limit_bytes,
            site="core.render_python",
        )
    except RenderGraphCycleError:
        # 閉路を受け入れないという判定は走査 owner が持つ。表示側は「進めない」
        # としか言わない（判定の実装を 2 つにしない）。
        traverse_semantic_graph(root)
        raise
    names: Dict[int, str] = {}
    if plan.bound_order:
        namespace = BindingNamespace(
            collect_reserved_symbols(plan, pattern=_HUMAN_SYMBOL_RE),
            prefix=HUMAN_SHARED_PREFIX,
            template=HUMAN_SHARED_TEMPLATE,
        )
        shapes = _fragment_shape_digests(plan)
        # 種はすでに形の digest。名前空間 owner は衝突解決だけを担う。
        allocated = namespace.allocate_keyed(
            [shapes[index] for index in plan.bound_order], digest=lambda seed: seed
        )
        names = {index: allocated[position] for position, index in enumerate(plan.bound_order)}
    check_plan_invariants(plan, names)
    counters.case_count += _phi_case_count(plan)

    writer = CountingWriter(limit_bytes=limit_bytes, site="core.render_python.emit")
    write_expansion(writer, plan, plan.root_index, names)
    if plan.bound_order:
        writer.write(" where ")
        for position, index in enumerate(plan.bound_order):
            if position:
                writer.write("; ")
            writer.write(names[index])
            writer.write(" = ")
            write_expansion(writer, plan, index, names)
    text = writer.getvalue()
    counters.emitted_bytes = writer.emitted_bytes
    record_render(counters)
    return text


def _fragment_shape_digests(plan) -> Dict[int, str]:
    """各 instance の「形」の digest。同じ形の部分式には同じ名前が付く。

    fragment は子を走査順の番号で指すので、番号をそのまま種にすると同じ形でも
    走査の都合で名前が変わる。番号は印に潰し、子の digest を畳み込む。子が先に
    決まる順（post-order）で回すので再帰しない。
    """

    digests: Dict[int, str] = {}
    for index in plan.post_order:
        instance = plan.instances[index]
        parts = [_strip_placeholder_indices(instance.fragment)]
        parts.extend(digests[child] for child in instance.used_children)
        digests[index] = _shared_reference_digest("\x01".join(parts))
    return digests


def _strip_placeholder_indices(fragment: str) -> str:
    return _PLACEHOLDER_RE.sub(PLACEHOLDER_MARK, fragment)


def _phi_case_count(plan) -> int:
    """描いた PHI branch（case）の数。node 本体の中で数えると、子の解決による
    再実行の回数だけ水増しされる。"""

    total = 0
    for instance in plan.instances:
        expr_type = getattr(instance.node, "expr_type", None)
        if expr_type is None:
            continue
        if expr_type == expr_type.__class__.PHI:
            total += len(getattr(instance.node, "value", None) or ())
    return total


def _shared_reference_digest(seed: str) -> str:
    """共有参照名の安定な種。同じ形の部分式には同じ名前が付く。

    衝突しない保証は hash ではなく namespace owner が持つ（8 桁は読みやすさの
    ためで、一意性の根拠にはしない）。
    """

    return hashlib.blake2b(seed.encode("utf-8"), digest_size=4).hexdigest()


class _HumanChildRenderer:
    """node 本体が子を描く唯一の口。"""

    __slots__ = ("_resolve", "_context")

    def __init__(self, resolve, context: HumanRenderContext) -> None:
        self._resolve = resolve
        self._context = context

    @property
    def context(self) -> HumanRenderContext:
        return self._context

    def fragment(self):
        """自分の分を **数えながら**書く口（driver 所有）。

        幅が子の数に比例する node はここを通す。`join` で一度に畳むと、上限
        超えの文字列を作ってからしか止められない。
        """

        return self._resolve.fragment()

    def __call__(self, node, *, simplify=None) -> str:
        context = (
            self._context if simplify is None else HumanRenderContext(simplify=bool(simplify))
        )
        return self._resolve(node, context)


class _DetachedHumanChildRenderer:
    """driver の外から子を描く口（helper の単体利用向け）。再帰はしない。"""

    __slots__ = ("_context",)

    def __init__(self, context: HumanRenderContext) -> None:
        self._context = context

    @property
    def context(self) -> HumanRenderContext:
        return self._context

    def fragment(self):
        """driver の外には上限の owner が居ないので、ここは **開けない**。

        素通りさせるより、そういう経路を作った時点で止める。
        """

        raise RenderPlanInvariantError(
            "a node body asked for a counted fragment outside the render driver; "
            "render through render_human_text so the limit has an owner"
        )

    def __call__(self, node, *, simplify=None) -> str:
        context = (
            self._context if simplify is None else HumanRenderContext(simplify=bool(simplify))
        )
        return render_human_text(node, context)


def _is_expression_node(value) -> bool:
    return hasattr(value, "_to_string_internal")


def _render_human_node(node, context: HumanRenderContext, resolve) -> str:
    render_child = _HumanChildRenderer(resolve, context)
    if getattr(node, "expr_type", None) is None:
        if hasattr(node, "expression"):
            return _render_condition_text(node, render_child)
        if hasattr(node, "to_string"):
            return str(node.to_string())
        return str(node)
    return _render_expression_text(node, context, render_child)


def _render_condition_text(condition, render_child) -> str:
    """`Condition.to_string()` と同じ形（式 + 反転）。

    条件の中の式は常に `simplify=True` で描く（`Condition.to_string()` が
    引数を取らないので、従来もそうなっていた）。ここで文脈の `simplify` を
    伝播させると、`to_string(simplify=False)` のときだけ表示が変わる。
    """

    expression = getattr(condition, "expression", None)
    if expression is None:
        return "true"
    expr_str = render_child(expression, simplify=True)
    if getattr(condition, "negated", False):
        return f"(not {expr_str})"
    return expr_str


def _render_expression_text(expr, context: HumanRenderContext, render_child) -> str:
    simplify = context.simplify
    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type == expr_kind.CONSTANT:
        return expr._format_constant(expr.value)

    if expr_type == expr_kind.PARAMETER:
        return expr.name if expr.name else f"param_{expr.value}"

    if expr_type == expr_kind.VARIABLE:
        return expr.name if expr.name else "var"

    if expr_type == expr_kind.BINARY_OP:
        left = expr.operands[0]
        right = expr.operands[1]

        if expr.operator == "PIECE":
            return format_piece_expression(expr, left, right, simplify, render_child=render_child)

        if expr.operator == "SUBPIECE":
            return format_subpiece_expression(expr, left, right, simplify, render_child=render_child)

        left_str = render_child(left)
        right_str = render_child(right)
        op = expr._get_python_operator(expr.operator)
        return f"({left_str} {op} {right_str})"

    if expr_type == expr_kind.UNARY_OP:
        operand = render_child(expr.operands[0])
        op = expr._get_python_operator(expr.operator)
        if op == "not":
            return f"(not {operand})"
        if op in ("-", "~"):
            return f"({op}{operand})"
        return f"{op}({operand})"

    if expr_type in (expr_kind.CALL, expr_kind.INTRINSIC):
        # 引数の数だけ長くなる node なので、`join` で一度に畳まず 1 個ずつ
        # 数えながら置く（上限に達した時点で止まる）。
        fragment = render_child.fragment()
        fragment.literal(f"{expr.name}(")
        for position, operand in enumerate(getattr(expr, "operands", None) or ()):
            if position:
                fragment.literal(", ")
            fragment.term(render_child(operand))
        return fragment.literal(")").build()

    if expr_type == expr_kind.MEMORY:
        addr = render_child(expr.operands[0])
        return f"MEM[{addr}]"

    if expr_type == expr_kind.PHI:
        branches = expr.value
        if not branches:
            return "UNKNOWN"
        if len(branches) == 1:
            _, val = branches[0]
            if _is_expression_node(val):
                return render_child(val)
            return str(val)

        # branch の数だけ長くなる node なので、`join` で一度に畳まない。
        fragment = render_child.fragment()
        fragment.literal("PHI(")
        for position, (cond, val) in enumerate(branches):
            if position:
                fragment.literal(", ")
            if _is_expression_node(val):
                fragment.term(render_child(val))
            else:
                fragment.literal(str(val))
            if cond is None:
                continue
            fragment.literal(" if ")
            if _is_expression_node(cond):
                fragment.term(render_child(cond))
            elif hasattr(cond, "to_string"):
                fragment.term(render_child(cond, simplify=True))
            else:
                fragment.literal(str(cond))
        return fragment.literal(")").build()

    return expr.name if expr.name else "UNKNOWN"


def format_piece_expression(expr, high, low, simplify: bool, *, render_child=None) -> str:
    """PIECE を Python 互換形式に変換する。"""

    if render_child is None:
        render_child = _DetachedHumanChildRenderer(HumanRenderContext(simplify=bool(simplify)))
    high_str = render_child(high)
    low_str = render_child(low)
    shift_bits = low.get_bit_width()

    if simplify:
        high_kind = high.expr_type.__class__
        low_kind = low.expr_type.__class__
        if high.expr_type == high_kind.CONSTANT and high.value == 0:
            return low_str
        if low.expr_type == low_kind.CONSTANT and low.value == 0:
            return f"({high_str} << {shift_bits})"

    return f"(({high_str} << {shift_bits}) | {low_str})"


def format_subpiece_expression(expr, source, offset, simplify: bool, *, render_child=None) -> str:
    """SUBPIECE を Python 互換形式に変換する。"""

    if render_child is None:
        render_child = _DetachedHumanChildRenderer(HumanRenderContext(simplify=bool(simplify)))
    source_str = render_child(source)

    offset_kind = offset.expr_type.__class__
    if offset.expr_type == offset_kind.CONSTANT:
        byte_offset = offset.value
    else:
        offset_str = render_child(offset)
        output_bits = expr.get_bit_width()
        mask = (1 << output_bits) - 1
        mask_str = expr._format_constant(mask)
        return f"(({source_str} >> ({offset_str} * 8)) & {mask_str})"

    output_bits = expr.get_bit_width()
    mask = (1 << output_bits) - 1
    mask_str = expr._format_constant(mask)
    shift_bits = byte_offset * 8

    if simplify and shift_bits == 0:
        return f"({source_str} & {mask_str})"

    return f"(({source_str} >> {shift_bits}) & {mask_str})"


def get_python_operator(operator: Optional[str]) -> str:
    """P-code オペレータを Python 演算子へ変換する。"""
    if operator is None:
        return ""

    op_map: Dict[str, str] = {
        "INT_ADD": "+",
        "INT_SUB": "-",
        "INT_MULT": "*",
        "INT_DIV": "//",
        "INT_SDIV": "//",
        "INT_REM": "%",
        "INT_SREM": "%",
        "INT_AND": "&",
        "INT_OR": "|",
        "INT_XOR": "^",
        "INT_LEFT": "<<",
        "INT_RIGHT": ">>",
        "INT_SRIGHT": ">>",
        "INT_EQUAL": "==",
        "INT_NOTEQUAL": "!=",
        "INT_LESS": "<",
        "INT_SLESS": "<",
        "INT_LESSEQUAL": "<=",
        "INT_SLESSEQUAL": "<=",
        "BOOL_AND": "and",
        "BOOL_OR": "or",
        "BOOL_XOR": "^",
        "INT_NEGATE": "~",
        "INT_2COMP": "-",
        "BOOL_NEGATE": "not",
        "INT_ZEXT": "int",
        "INT_SEXT": "int",
        "COPY": "",
        "FLOAT_ADD": "+",
        "FLOAT_SUB": "-",
        "FLOAT_MULT": "*",
        "FLOAT_DIV": "/",
    }
    return op_map.get(operator, operator)

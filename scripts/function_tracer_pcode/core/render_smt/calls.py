# -*- coding: utf-8 -*-
"""Uninterpreted-function declarations for ``ExpressionType.CALL`` nodes.

CALL の描画 (``render.to_smt``) と symbol 命名 (``normalize_call_symbol_name``)
は既に ``render.py`` にある。宣言収集だけが condition SMT oracle の中に private
実装として存在していたので、それをここへ移して **CALL の UF 宣言規則を 1 か所に
する**（Issue #20 PR-B2）。oracle と conditional formula builder が別々の規則を
持つと、同じ式が別の sort で宣言され得る。

規則（既存 oracle の実装そのまま）:

* 関数名は ``normalize_call_symbol_name(expr.name)``
* 引数 sort は各 operand の ``expression_smt_bit_width``
* 戻り sort は CALL node 自身の ``expression_smt_bit_width``
* 幅は oracle から引き継いだ正規化（``max(1, ...)``）をそのまま使う。CALL 側の
  幅検証は、CALL を作る前に catalog signature と厳密一致を確認する
  conditional view の責務であり、ここで判定を変えると oracle の答えが動く
* **同名なのに signature が違う CALL は fail closed**。silent rename も
  片側優先もしない（別関数を同じ UF に潰すと、証明していない値の一致を
  主張することになる）。
"""

from __future__ import annotations

from typing import Any, Dict, Iterable, List, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.core.render_smt.render import (
    normalize_call_symbol_name,
)
from scripts.function_tracer_pcode.core.render_smt.widths import (
    expression_smt_bit_width,
)


#: ``{call_symbol: (argument_bit_widths, return_bit_width)}``
CallSmtDeclarations = Dict[str, Tuple[Tuple[int, ...], int]]


class CallDeclarationConflict(ValueError):
    """同じ CALL symbol に別の signature が要求された（fail closed）。"""


def call_smt_declaration(node: Any) -> Optional[Tuple[str, Tuple[int, ...], int]]:
    """1 個の CALL node の ``(symbol, argument widths, return width)`` を返す。

    CALL でない / 名前が取れない / 幅が取れない場合は ``None``。
    """

    expr_type = getattr(node, "expr_type", None)
    expr_kind = getattr(expr_type, "__class__", None)
    if expr_type is None or expr_kind is None or expr_type != expr_kind.CALL:
        return None

    call_name = normalize_call_symbol_name(getattr(node, "name", None))
    if not call_name:
        return None

    argument_widths: List[int] = []
    for operand in getattr(node, "operands", None) or []:
        bits = max(1, int(expression_smt_bit_width(operand) or 0))
        if bits <= 0:
            return None
        argument_widths.append(bits)

    return_bits = max(1, int(expression_smt_bit_width(node) or 0))
    if return_bits <= 0:
        return None
    return call_name, tuple(argument_widths), return_bits


def add_call_smt_declaration(
    declarations: CallSmtDeclarations,
    node: Any,
) -> bool:
    """``node`` の宣言を ``declarations`` に足す。

    足せたら ``True``、CALL でない・幅が取れないなら ``False``。同名で
    signature が食い違う場合は :class:`CallDeclarationConflict`。
    """

    collected = call_smt_declaration(node)
    if collected is None:
        return False
    call_name, argument_widths, return_bits = collected
    signature = (argument_widths, return_bits)
    prior = declarations.get(call_name)
    if prior is not None and prior != signature:
        raise CallDeclarationConflict(
            f"call symbol {call_name} is required with two signatures: {prior} and {signature}"
        )
    declarations[call_name] = signature
    return True


def _iter_expression_nodes(expr: Any) -> Iterable[Any]:
    pending: List[Any] = [expr]
    seen: set = set()
    while pending:
        current = pending.pop()
        if current is None:
            continue
        current_id = id(current)
        if current_id in seen:
            continue
        seen.add(current_id)
        yield current

        expr_type = getattr(current, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_type is None or expr_kind is None:
            continue
        if expr_type == expr_kind.PHI and getattr(current, "value", None):
            for condition, value in reversed(current.value):
                if value is not None:
                    pending.append(value)
                condition_expr = (
                    getattr(condition, "expression", None) if condition is not None else None
                )
                if condition_expr is not None:
                    pending.append(condition_expr)
            continue
        for operand in reversed(list(getattr(current, "operands", None) or [])):
            if operand is not None:
                pending.append(operand)


def collect_call_smt_declarations(
    expr: Any,
    declarations: Optional[CallSmtDeclarations] = None,
) -> Optional[CallSmtDeclarations]:
    """式木の CALL 宣言をすべて集める。

    宣言できない CALL が 1 つでもあれば ``None``（fail closed）。同名で
    signature が食い違う場合は :class:`CallDeclarationConflict` を送出する。
    ``declarations`` を渡すと、その辞書へ蓄積して同じ辞書を返す。
    """

    collected: CallSmtDeclarations = {} if declarations is None else declarations
    for node in _iter_expression_nodes(expr):
        expr_type = getattr(node, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_type is None or expr_kind is None or expr_type != expr_kind.CALL:
            continue
        if not add_call_smt_declaration(collected, node):
            return None
    return collected


def expression_contains_call(expr: Any) -> bool:
    """式木に CALL 応用が含まれるか。

    ``expression_contains_unsupported_smt_ops`` の ``allow_call`` が作る差分と
    同じ対象を、他の unsupported 判定に触れずに直接見るための述語。lane 境界
    （無条件 formula は CALL を受け付けない）の検査に使う。
    """

    for node in _iter_expression_nodes(expr):
        expr_type = getattr(node, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_type is not None and expr_kind is not None and expr_type == expr_kind.CALL:
            return True
    return False


def call_smt_declaration_lines(declarations: Mapping[str, Tuple[Tuple[int, ...], int]]) -> List[str]:
    """``(declare-fun ...)`` 行を決定的な順序で返す。"""

    lines: List[str] = []
    for call_name, (argument_widths, return_bits) in sorted(declarations.items()):
        arguments = " ".join(f"(_ BitVec {bits})" for bits in argument_widths)
        lines.append(f"(declare-fun {call_name} ({arguments}) (_ BitVec {return_bits}))")
    return lines

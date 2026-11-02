"""P-code intrinsic declarations and lowerings."""

from __future__ import annotations

from typing import List, Mapping, Optional
from scripts.function_tracer_pcode.core.intrinsics import (
    COUNTED_LOOP_SUM_OPCODE,
    COUNTED_STATE_TRANSITION_VALUE_OPCODE,
    READONLY_SUM_OPCODE,
    STATE_TRANSITION_LOOP_COUNT_OPCODE,
    PTRADD_OPCODE,
    PTRSUB_OPCODE,
)


def memory_function_name(name: str, side_tag: Optional[str]) -> str:
    """値が memory の内容に依存する関数（read-only の表の和 `READONLY_SUM`）の名前。側ごとに別の関数にする
    （Issue #282, I1: 同じ名前の関数を左右で共有すると、側ごとの公理が左右の memory を等しくする）。"""

    from scripts.function_tracer_pcode.core.render_smt.sides import side_qualified_name

    return side_qualified_name(name, side_tag)


def collect_intrinsic_smt_declarations(expr, side_tag: Optional[str] = None) -> List[str]:
    """Collect deterministic SMT declarations needed for supported intrinsic applications."""
    declarations: List[str] = []
    seen = set()
    for node in _iter_expression_nodes(expr):
        if node is None or getattr(node, "expr_type", None) is None:
            continue
        expr_kind = node.expr_type.__class__
        if node.expr_type != expr_kind.INTRINSIC:
            continue
        decl = _intrinsic_smt_declaration(node, side_tag)
        if decl is None or decl in seen:
            continue
        seen.add(decl)
        declarations.append(decl)
    return declarations


def _memory_side_tag(symbol_name_mapping) -> Optional[str]:
    """memory に依存する関数を描く側。側の無い写像（左右の query の材料かもしれない描画）では描かない。"""

    from scripts.function_tracer_pcode.core.render_smt.render import UndeclaredSmtSymbolError
    from scripts.function_tracer_pcode.core.render_smt.sides import mapping_side_tag

    tag = mapping_side_tag(symbol_name_mapping)
    if symbol_name_mapping is not None and tag is None:
        raise UndeclaredSmtSymbolError(symbol_kind="MEMORY_FUNCTION", symbol="memory-dependent loop summary")
    return tag


def _intrinsic_smt_declaration(expr, side_tag: Optional[str] = None) -> Optional[str]:
    opcode = getattr(expr, "opcode", None)
    mnemonic = getattr(expr, "name", None) or ""
    operands = getattr(expr, "operands", None) or []

    if opcode == READONLY_SUM_OPCODE or mnemonic == "READONLY_SUM":
        if len(operands) != 2:
            raise ValueError(f"READONLY_SUM expects 2 operands, got {len(operands)}")
        base_bits = max(1, int(expression_smt_bit_width(operands[0]) or 1))
        count_bits = max(1, int(expression_smt_bit_width(operands[1]) or 1))
        result_bits = max(1, int(expression_smt_bit_width(expr) or 1))
        return (
            f"(declare-fun {memory_function_name(_readonly_sum_function_name(expr), side_tag)} "
            f"((_ BitVec {base_bits}) (_ BitVec {count_bits})) "
            f"(_ BitVec {result_bits}))"
        )

    if opcode == COUNTED_LOOP_SUM_OPCODE or mnemonic == "COUNTED_LOOP_SUM":
        if _counted_loop_sum_has_exact_lowering(expr):
            return None
        if len(operands) != 3:
            raise ValueError(f"COUNTED_LOOP_SUM expects 3 operands, got {len(operands)}")
        base_bits = max(1, int(expression_smt_bit_width(operands[0]) or 1))
        start_bits = max(1, int(expression_smt_bit_width(operands[1]) or 1))
        limit_bits = max(1, int(expression_smt_bit_width(operands[2]) or 1))
        result_bits = max(1, int(expression_smt_bit_width(expr) or 1))
        return (
            f"(declare-fun {_counted_loop_sum_function_name(expr)} "
            f"((_ BitVec {base_bits}) (_ BitVec {start_bits}) (_ BitVec {limit_bits})) "
            f"(_ BitVec {result_bits}))"
        )

    if opcode == STATE_TRANSITION_LOOP_COUNT_OPCODE or mnemonic == "STATE_TRANSITION_LOOP_COUNT":
        if len(operands) != 1:
            raise ValueError(f"STATE_TRANSITION_LOOP_COUNT expects 1 operand, got {len(operands)}")
        state_bits = max(1, int(expression_smt_bit_width(operands[0]) or 1))
        result_bits = max(1, int(expression_smt_bit_width(expr) or 1))
        return (
            f"(declare-fun {_state_transition_loop_count_function_name(expr)} "
            f"((_ BitVec {state_bits})) "
            f"(_ BitVec {result_bits}))"
        )

    if opcode == COUNTED_STATE_TRANSITION_VALUE_OPCODE or mnemonic == "COUNTED_STATE_TRANSITION_VALUE":
        if _counted_state_transition_value_has_exact_lowering(expr):
            return None
        if len(operands) != 3:
            raise ValueError(f"COUNTED_STATE_TRANSITION_VALUE expects 3 operands, got {len(operands)}")
        init_bits = max(1, int(expression_smt_bit_width(operands[0]) or 1))
        start_bits = max(1, int(expression_smt_bit_width(operands[1]) or 1))
        limit_bits = max(1, int(expression_smt_bit_width(operands[2]) or 1))
        result_bits = max(1, int(expression_smt_bit_width(expr) or 1))
        return (
            f"(declare-fun {_counted_state_transition_value_function_name(expr)} "
            f"((_ BitVec {init_bits}) (_ BitVec {start_bits}) (_ BitVec {limit_bits})) "
            f"(_ BitVec {result_bits}))"
        )

    return None


def _intrinsic_result_bits(expr) -> int:
    explicit_bits = expression_smt_bit_width(expr)
    if explicit_bits > 0:
        return explicit_bits
    operands = getattr(expr, "operands", None) or []
    if operands:
        return max(expression_smt_bit_width(operand) for operand in operands)
    return 0


def _lower_intrinsic_to_smt(
    expr,
    *,
    prefer_signed_arithmetic: bool,
    symbol_name_mapping: Optional[Mapping[str, str]],
    address_context: bool,
    float_mode: str = "uf",
    render_child=None,
) -> str:
    """intrinsic の lowering。子は `render_child` 経由でしか描かない。

    `render_child` は driver が渡す「子を描く口」。単体で呼ばれたとき（test や
    他 module からの直接利用）は同じ反復 driver を起こす口を作る — 再帰する
    renderer へは戻らない。
    """

    if render_child is None:
        render_child = _detached_child_renderer(
            prefer_signed_arithmetic=prefer_signed_arithmetic,
            symbol_name_mapping=symbol_name_mapping,
            address_context=address_context,
            float_mode=float_mode,
        )
    opcode = getattr(expr, "opcode", None)
    mnemonic = getattr(expr, "name", None) or ""
    operands = getattr(expr, "operands", None) or []
    result_bits = _intrinsic_result_bits(expr)

    if opcode == PTRADD_OPCODE or mnemonic == "PTRADD":
        if len(operands) != 3:
            raise ValueError(f"PTRADD expects 3 operands, got {len(operands)}")
        base, index, element_size = operands
        base_smt = render_child(
            base,
            address_context=True,
        )
        index_smt = render_child(index)
        elem_smt = render_child(element_size)
        target_bits = max(
            result_bits,
            expression_smt_bit_width(base),
            expression_smt_bit_width(index),
            expression_smt_bit_width(element_size),
            1,
        )
        base_smt = _coerce_expr_to_bitvec_width(base, base_smt, target_bits, float_mode=float_mode)
        index_smt = _coerce_expr_to_bitvec_width(index, index_smt, target_bits, float_mode=float_mode)
        elem_smt = _coerce_expr_to_bitvec_width(element_size, elem_smt, target_bits, float_mode=float_mode)
        return f"(bvadd {base_smt} (bvmul {index_smt} {elem_smt}))"

    if opcode == PTRSUB_OPCODE or mnemonic == "PTRSUB":
        if len(operands) != 2:
            raise ValueError(f"PTRSUB expects 2 operands, got {len(operands)}")
        base, offset = operands
        base_smt = render_child(
            base,
            address_context=True,
        )
        offset_smt = render_child(offset)
        target_bits = max(
            result_bits,
            expression_smt_bit_width(base),
            expression_smt_bit_width(offset),
            1,
        )
        base_smt = _coerce_expr_to_bitvec_width(base, base_smt, target_bits, float_mode=float_mode)
        offset_smt = _coerce_expr_to_bitvec_width(offset, offset_smt, target_bits, float_mode=float_mode)
        return f"(bvadd {base_smt} {offset_smt})"

    if opcode == READONLY_SUM_OPCODE or mnemonic == "READONLY_SUM":
        if len(operands) != 2:
            raise ValueError(f"READONLY_SUM expects 2 operands, got {len(operands)}")
        base, count = operands
        base_bits = max(1, int(expression_smt_bit_width(base) or 1))
        count_bits = max(1, int(expression_smt_bit_width(count) or 1))
        base_smt = render_child(
            base,
            address_context=True,
        )
        count_smt = render_child(count)
        base_smt = _coerce_expr_to_bitvec_width(base, base_smt, base_bits, float_mode=float_mode)
        count_smt = _coerce_expr_to_bitvec_width(
            count,
            count_smt,
            count_bits,
            prefer_sign_extension=_expr_prefers_signed_extension(count),
            float_mode=float_mode,
        )
        return f"({memory_function_name(_readonly_sum_function_name(expr), _memory_side_tag(symbol_name_mapping))} {base_smt} {count_smt})"

    if opcode == COUNTED_LOOP_SUM_OPCODE or mnemonic == "COUNTED_LOOP_SUM":
        if len(operands) != 3:
            raise ValueError(f"COUNTED_LOOP_SUM expects 3 operands, got {len(operands)}")
        base, start, limit = operands
        base_bits = max(1, int(expression_smt_bit_width(base) or 1))
        start_bits = max(1, int(expression_smt_bit_width(start) or 1))
        limit_bits = max(1, int(expression_smt_bit_width(limit) or 1))
        base_smt = render_child(base)
        start_smt = render_child(start)
        limit_smt = render_child(limit)
        base_smt = _coerce_expr_to_bitvec_width(base, base_smt, base_bits, float_mode=float_mode)
        start_smt = _coerce_expr_to_bitvec_width(
            start,
            start_smt,
            start_bits,
            prefer_sign_extension=_expr_prefers_signed_extension(start),
            float_mode=float_mode,
        )
        limit_smt = _coerce_expr_to_bitvec_width(
            limit,
            limit_smt,
            limit_bits,
            prefer_sign_extension=_expr_prefers_signed_extension(limit),
            float_mode=float_mode,
        )
        exact_smt = _counted_loop_sum_exact_smt(
            expr,
            base_smt=base_smt,
            start_smt=start_smt,
            limit_smt=limit_smt,
            base_bits=base_bits,
            start_bits=start_bits,
            limit_bits=limit_bits,
            result_bits=max(1, int(expression_smt_bit_width(expr) or 1)),
            prefer_signed_arithmetic=prefer_signed_arithmetic,
            symbol_name_mapping=symbol_name_mapping,
            address_context=address_context,
            float_mode=float_mode,
            render_child=render_child,
        )
        if exact_smt is not None:
            return exact_smt
        return f"({_counted_loop_sum_function_name(expr)} {base_smt} {start_smt} {limit_smt})"

    if opcode == STATE_TRANSITION_LOOP_COUNT_OPCODE or mnemonic == "STATE_TRANSITION_LOOP_COUNT":
        if len(operands) != 1:
            raise ValueError(f"STATE_TRANSITION_LOOP_COUNT expects 1 operand, got {len(operands)}")
        state = operands[0]
        state_bits = max(1, int(expression_smt_bit_width(state) or 1))
        state_smt = render_child(state)
        state_smt = _coerce_expr_to_bitvec_width(
            state,
            state_smt,
            state_bits,
            prefer_sign_extension=_expr_prefers_signed_extension(state),
            float_mode=float_mode,
        )
        return f"({_state_transition_loop_count_function_name(expr)} {state_smt})"

    if opcode == COUNTED_STATE_TRANSITION_VALUE_OPCODE or mnemonic == "COUNTED_STATE_TRANSITION_VALUE":
        if len(operands) != 3:
            raise ValueError(f"COUNTED_STATE_TRANSITION_VALUE expects 3 operands, got {len(operands)}")
        rendered = []
        operand_bits = []
        for operand in operands:
            bits = max(1, int(expression_smt_bit_width(operand) or 1))
            operand_smt = render_child(operand)
            rendered.append(
                _coerce_expr_to_bitvec_width(
                    operand,
                    operand_smt,
                    bits,
                    prefer_sign_extension=_expr_prefers_signed_extension(operand),
                    float_mode=float_mode,
                )
            )
            operand_bits.append(bits)
        exact_smt = _counted_state_transition_exact_smt(
            expr,
            init_smt=rendered[0],
            start_smt=rendered[1],
            limit_smt=rendered[2],
            init_bits=operand_bits[0],
            start_bits=operand_bits[1],
            limit_bits=operand_bits[2],
            result_bits=max(1, int(expression_smt_bit_width(expr) or 1)),
        )
        if exact_smt is not None:
            return exact_smt
        return f"({_counted_state_transition_value_function_name(expr)} {' '.join(rendered)})"

    if mnemonic == "NEON_ext":
        return _lower_neon_ext_operands_to_smt(
            expr,
            operands,
            prefer_signed_arithmetic=prefer_signed_arithmetic,
            symbol_name_mapping=symbol_name_mapping,
            address_context=address_context,
            float_mode=float_mode,
            result_bits=result_bits,
            render_child=render_child,
        )

    raise UnsupportedSmtIntrinsicError(mnemonic=mnemonic, opcode=opcode)


# Sibling modules reference each other at call time; import them last to avoid cycles.
from scripts.function_tracer_pcode.core.render_smt.loop_lowering import (
    _counted_loop_sum_exact_smt,
    _counted_loop_sum_function_name,
    _counted_loop_sum_has_exact_lowering,
    _counted_state_transition_exact_smt,
    _counted_state_transition_value_function_name,
    _counted_state_transition_value_has_exact_lowering,
    _lower_neon_ext_operands_to_smt,
    _readonly_sum_function_name,
    _state_transition_loop_count_function_name,
)
from scripts.function_tracer_pcode.core.render_smt.render import (
    UnsupportedSmtIntrinsicError,
    _detached_child_renderer,
)
from scripts.function_tracer_pcode.core.render_smt.unknowns import (
    _iter_expression_nodes,
)
from scripts.function_tracer_pcode.core.render_smt.widths import (
    _coerce_expr_to_bitvec_width,
    _expr_prefers_signed_extension,
    expression_smt_bit_width,
)

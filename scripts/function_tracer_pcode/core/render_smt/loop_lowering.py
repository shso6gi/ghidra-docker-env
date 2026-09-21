"""counted-loop sum / state-transition loop / read-only reduction の SMT 描画。

ここは **描画だけ** を担う。どの lowering か・厳密 lowering が可能か・その
parameter は何かは `core/loop_lowering_semantics.py` が凍結時に決めており、
この module は `semantic_projection(expr).loop_lowering` が返す不変な値を読む。
loop summary ref の class も field 名もここでは出てこない。
"""

from __future__ import annotations

import hashlib
import re
from typing import Any, List, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.core.loop_lowering_semantics import (
    LoopLoweringSemantics,
    LoweringKind,
)
from scripts.function_tracer_pcode.core.semantic_snapshot import semantic_projection


def _neon_ext_operands_are_smt_supported(expr) -> bool:
    operands = list(getattr(expr, "operands", None) or [])
    if len(operands) != 4:
        return False
    first, second, byte_offset_expr, element_size_expr = operands
    byte_offset = _expr_constant_int(byte_offset_expr)
    element_size = _expr_constant_int(element_size_expr)
    if byte_offset is None or element_size != 1:
        return False
    try:
        first_bits = expression_smt_bit_width(first)
        second_bits = expression_smt_bit_width(second)
        result_bits = max(1, int(expression_smt_bit_width(expr) or 0))
    except RENDER_FAILURES:
        # 属性の評価も反復 driver を回すので、閉路や内部不整合を告げてくる。
        # それを「この形は SMT に落とせない」に化けさせない。
        raise
    except Exception:
        return False
    if first_bits <= 0 or second_bits <= 0:
        return False
    if first_bits != second_bits:
        return False
    if first_bits % 8 != 0 or second_bits % 8 != 0 or result_bits % 8 != 0:
        return False
    source_bytes = (first_bits + second_bits) // 8
    result_bytes = result_bits // 8
    return 0 <= int(byte_offset) and int(byte_offset) + result_bytes <= source_bytes


def _lowering(expr) -> LoopLoweringSemantics:
    """この式の lowering 意味（凍結時に確定済み）。

    生の `runtime_ref` を読まないのは、SMT 関数名と厳密 lowering の可否が
    「描画のときに ref をどう読んだか」で決まらないようにするため。
    """

    return semantic_projection(expr).loop_lowering


def _lowering_of_kind(expr, kind: LoweringKind) -> Optional[LoopLoweringSemantics]:
    """期待する種別のときだけ lowering 意味を返す。"""

    lowering = _lowering(expr)
    return lowering if lowering.kind is kind else None


def _identity_digest(lowering: LoopLoweringSemantics) -> str:
    return hashlib.sha1(repr(lowering.identity).encode("utf-8")).hexdigest()[:16]


def _operand_bit_widths(expr, count: int) -> Tuple[int, ...]:
    operands = getattr(expr, "operands", None) or []
    return tuple(
        expression_smt_bit_width(operands[index]) if len(operands) > index else 0
        for index in range(count)
    )


def _readonly_sum_function_name(expr) -> str:
    base_bits, count_bits = _operand_bit_widths(expr, 2)
    result_bits = max(1, int(expression_smt_bit_width(expr) or 1))
    lowering = _lowering_of_kind(expr, LoweringKind.READONLY_REDUCTION)
    if lowering is None:
        return f"rt_readonly_sum_{base_bits}_{count_bits}_{result_bits}"
    reduction_kind = re.sub(r"[^A-Za-z0-9_]+", "_", lowering.reduction_kind or "sum")
    digest = _identity_digest(lowering)
    return f"rt_{reduction_kind}_{digest}_{base_bits}_{count_bits}_{result_bits}"


def _state_transition_loop_count_function_name(expr) -> str:
    (state_bits,) = _operand_bit_widths(expr, 1)
    result_bits = max(1, int(expression_smt_bit_width(expr) or 1))
    lowering = _lowering_of_kind(expr, LoweringKind.STATE_TRANSITION_LOOP_COUNT)
    if lowering is None:
        return f"rt_state_transition_loop_count_{state_bits}_{result_bits}"
    digest = _identity_digest(lowering)
    return f"rt_state_transition_loop_count_{digest}_{state_bits}_{result_bits}"


def _counted_state_transition_value_function_name(expr) -> str:
    init_bits, start_bits, limit_bits = _operand_bit_widths(expr, 3)
    result_bits = max(1, int(expression_smt_bit_width(expr) or 1))
    lowering = _lowering_of_kind(expr, LoweringKind.COUNTED_STATE_TRANSITION_VALUE)
    if lowering is None:
        return f"rt_counted_state_transition_value_{init_bits}_{start_bits}_{limit_bits}_{result_bits}"
    digest = _identity_digest(lowering)
    return (
        f"rt_counted_state_transition_value_{digest}_"
        f"{init_bits}_{start_bits}_{limit_bits}_{result_bits}"
    )


def _counted_state_transition_value_has_exact_lowering(expr) -> bool:
    lowering = _lowering_of_kind(expr, LoweringKind.COUNTED_STATE_TRANSITION_VALUE)
    return lowering is not None and lowering.exact_lowering_available


def _counted_state_transition_exact_smt(
    expr,
    *,
    init_smt: str,
    start_smt: str,
    limit_smt: str,
    init_bits: int,
    start_bits: int,
    limit_bits: int,
    result_bits: int,
) -> Optional[str]:
    lowering = _lowering_of_kind(expr, LoweringKind.COUNTED_STATE_TRANSITION_VALUE)
    if lowering is None or lowering.exact_multiplier is None:
        return None
    multiplier = lowering.exact_multiplier
    count_bits = max(1, int(start_bits), int(limit_bits))
    start_count = _coerce_smt_bitvec_width(start_smt, start_bits, count_bits, prefer_sign_extension=False)
    limit_count = _coerce_smt_bitvec_width(limit_smt, limit_bits, count_bits, prefer_sign_extension=False)
    zero_count = f"(_ bv0 {count_bits})"
    if lowering.signed_loop:
        active_count = f"(ite (bvsle {limit_count} {start_count}) {zero_count} (bvsub {limit_count} {start_count}))"
    else:
        active_count = f"(ite (bvule {limit_count} {start_count}) {zero_count} (bvsub {limit_count} {start_count}))"
    init_result = _coerce_smt_bitvec_width(
        init_smt,
        init_bits,
        result_bits,
        prefer_sign_extension=False,
    )
    pow_smt = _constant_multiplier_pow_smt(
        int(multiplier),
        active_count,
        count_bits=count_bits,
        result_bits=result_bits,
    )
    return f"(bvmul {init_result} {pow_smt})"


def _constant_multiplier_pow_smt(
    multiplier: int,
    count_smt: str,
    *,
    count_bits: int,
    result_bits: int,
) -> str:
    result_bits = max(1, int(result_bits))
    modulus = 1 << result_bits
    factor = int(multiplier) % modulus
    factors: List[int] = []
    for _bit_index in range(max(1, int(count_bits))):
        factors.append(factor)
        factor = (factor * factor) % modulus
    body = f"pow_acc_{len(factors)}"
    for index in range(len(factors), -1, -1):
        if index == 0:
            value = f"(_ bv1 {result_bits})"
        else:
            bit_index = index - 1
            selected = f"(= ((_ extract {bit_index} {bit_index}) {count_smt}) #b1)"
            factor_term = f"(_ bv{factors[bit_index]} {result_bits})"
            previous = f"pow_acc_{index - 1}"
            value = f"(ite {selected} (bvmul {previous} {factor_term}) {previous})"
        body = f"(let ((pow_acc_{index} {value})) {body})"
    return body


def _counted_loop_sum_function_name(expr) -> str:
    base_bits, start_bits, limit_bits = _operand_bit_widths(expr, 3)
    result_bits = max(1, int(expression_smt_bit_width(expr) or 1))
    lowering = _lowering_of_kind(expr, LoweringKind.COUNTED_LOOP_SUM)
    if lowering is None:
        return f"rt_counted_loop_sum_{base_bits}_{start_bits}_{limit_bits}_{result_bits}"
    digest = _identity_digest(lowering)
    return (
        f"rt_counted_loop_sum_{digest}_"
        f"{base_bits}_{start_bits}_{limit_bits}_{result_bits}"
    )


def _counted_loop_sum_has_exact_lowering(expr) -> bool:
    lowering = _lowering_of_kind(expr, LoweringKind.COUNTED_LOOP_SUM)
    return lowering is not None and lowering.exact_lowering_available


def _lower_neon_ext_operands_to_smt(
    expr,
    operands,
    *,
    prefer_signed_arithmetic: bool,
    symbol_name_mapping: Optional[Mapping[str, str]],
    address_context: bool,
    float_mode: str,
    result_bits: int,
    render_child=None,
) -> str:
    if render_child is None:
        render_child = _detached_child_renderer(
            prefer_signed_arithmetic=prefer_signed_arithmetic,
            symbol_name_mapping=symbol_name_mapping,
            address_context=address_context,
            float_mode=float_mode,
        )
    if len(operands) != 4:
        raise ValueError(f"NEON_ext expects 4 operands, got {len(operands)}")
    first, second, byte_offset_expr, element_size_expr = operands
    byte_offset = _expr_constant_int(byte_offset_expr)
    if byte_offset is None:
        raise ValueError("NEON_ext requires a constant byte offset")
    element_size = _expr_constant_int(element_size_expr)
    if element_size != 1:
        raise ValueError("NEON_ext requires element_size operand 1")
    first_bits = expression_smt_bit_width(first)
    second_bits = expression_smt_bit_width(second)
    result_bits = max(1, int(result_bits or expression_smt_bit_width(expr) or 0))
    if first_bits <= 0 or second_bits <= 0:
        raise ValueError("NEON_ext requires sized vector operands")
    if first_bits != second_bits:
        raise ValueError("NEON_ext requires equal-width vector operands")
    if first_bits % 8 != 0 or second_bits % 8 != 0 or result_bits % 8 != 0:
        raise ValueError("NEON_ext requires byte-aligned vectors")
    byte_offset = int(byte_offset)
    source_bytes = (first_bits + second_bits) // 8
    result_bytes = result_bits // 8
    if byte_offset < 0 or byte_offset + result_bytes > source_bytes:
        raise ValueError("NEON_ext byte offset exceeds concatenated vector width")
    first_smt = render_child(first)
    second_smt = render_child(second)
    first_smt = _coerce_expr_to_bitvec_width(first, first_smt, first_bits, float_mode=float_mode)
    second_smt = _coerce_expr_to_bitvec_width(second, second_smt, second_bits, float_mode=float_mode)

    pieces: List[str] = []
    first_bytes = first_bits // 8
    for out_index in range(result_bytes - 1, -1, -1):
        source_index = byte_offset + out_index
        if source_index < first_bytes:
            source_smt = first_smt
            local_index = source_index
        else:
            source_smt = second_smt
            local_index = source_index - first_bytes
        low_bit = local_index * 8
        pieces.append(_smt_extract(low_bit + 7, low_bit, source_smt))
    return _smt_concat(pieces)


def _counted_loop_sum_exact_smt(
    expr,
    *,
    base_smt: str,
    start_smt: str,
    limit_smt: str,
    base_bits: int,
    start_bits: int,
    limit_bits: int,
    result_bits: int,
    prefer_signed_arithmetic: bool = False,
    symbol_name_mapping: Optional[Mapping[str, str]] = None,
    address_context: Optional[Mapping[str, Any]] = None,
    float_mode: str = "real",
    render_child=None,
) -> Optional[str]:
    lowering = _lowering_of_kind(expr, LoweringKind.COUNTED_LOOP_SUM)
    if lowering is None:
        return None
    if render_child is None:
        render_child = _detached_child_renderer(
            prefer_signed_arithmetic=prefer_signed_arithmetic,
            symbol_name_mapping=symbol_name_mapping,
            address_context=address_context,
            float_mode=float_mode,
        )

    induction_step = lowering.induction_step
    residue_cases = lowering.residue_cases
    residue_bias_terms = lowering.residue_bias_terms
    if induction_step == 0 or not residue_cases:
        return None

    signed_loop = lowering.signed_loop
    wide_bits = max(64, result_bits * 2, base_bits, start_bits, limit_bits)
    wide_base = _smt_extend_to_width(expr.operands[0], base_smt, wide_bits, signed=signed_loop)
    wide_start = _smt_extend_to_width(expr.operands[1], start_smt, wide_bits, signed=signed_loop)
    wide_limit = _smt_extend_to_width(expr.operands[2], limit_smt, wide_bits, signed=signed_loop)
    zero = _smt_bv_const(0, wide_bits)
    one = _smt_bv_const(1, wide_bits)

    def _triangular(value_smt: str) -> str:
        incremented = f"(bvadd {value_smt} {one})"
        product = f"(bvmul {value_smt} {incremented})"
        return f"(bvlshr {product} {one})"

    def _exact_progression_sum(first_smt: str, count_smt: str, *, step: int) -> str:
        count_minus_one = f"(bvsub {count_smt} {one})"
        triangular = _triangular(count_minus_one)
        stride_term = _smt_scale_term(triangular, step, wide_bits)
        leading_term = f"(bvmul {count_smt} {first_smt})"
        total_nonzero = leading_term
        if stride_term is not None:
            total_nonzero = f"(bvadd {leading_term} {stride_term})"
        return f"(ite (= {count_smt} {zero}) {zero} {total_nonzero})"

    def _loop_le(left_smt: str, right_smt: str) -> str:
        operator = "bvsle" if signed_loop else "bvule"
        return f"({operator} {left_smt} {right_smt})"

    def _distance_le(left_smt: str, right_smt: str) -> str:
        return f"(bvule {left_smt} {right_smt})"

    def _bias_terms_for_case(modulus: int, residue: int) -> Tuple[Any, ...]:
        return tuple(
            term.bias_expression
            for term in residue_bias_terms
            if term.modulus == int(modulus) and term.residue == int(residue)
        )

    def _render_bias_term(bias_expr) -> Optional[str]:
        bias_bits = max(1, int(expression_smt_bit_width(bias_expr) or result_bits or 1))
        try:
            bias_smt = render_child(bias_expr)
        except RENDER_FAILURES:
            # 予算の打ち切りと内部不整合は「この項は描けなかった」ではない。
            # 下の broad handler へ落とすと、上限で止めたことが lowering の
            # 断念に化けて、予算が効かないまま解析が続く。
            raise
        except Exception:
            return None
        bias_smt = _coerce_expr_to_bitvec_width(
            bias_expr,
            bias_smt,
            bias_bits,
            prefer_sign_extension=_expr_prefers_signed_extension(bias_expr),
            float_mode=float_mode,
        )
        return _smt_extend_to_width(
            bias_expr,
            bias_smt,
            wide_bits,
            signed=_expr_prefers_signed_extension(bias_expr),
        )

    def _add_bias_expression_terms(total_smt: str, count_smt: str, modulus: int, residue: int) -> Optional[str]:
        total_with_terms = total_smt
        for bias_expr in _bias_terms_for_case(modulus, residue):
            wide_bias = _render_bias_term(bias_expr)
            if wide_bias is None:
                return None
            total_with_terms = f"(bvadd {total_with_terms} (bvmul {count_smt} {wide_bias}))"
        return total_with_terms

    def _ceil_div_positive(value_smt: str, divisor: int) -> str:
        divisor = int(divisor)
        if divisor <= 1:
            return value_smt
        decremented = f"(bvsub {value_smt} {one})"
        if divisor & (divisor - 1) == 0:
            shift_amount = _smt_bv_const(divisor.bit_length() - 1, wide_bits)
            quotient = f"(bvlshr {decremented} {shift_amount})"
        else:
            quotient = f"(bvudiv {decremented} {_smt_bv_const(divisor, wide_bits)})"
        return f"(bvadd {quotient} {one})"

    if induction_step == 1:
        n_expr = f"(bvsub {wide_limit} {wide_start})"
        no_iteration = _loop_le(wide_limit, wide_start)
        count_all_expr = f"(ite {no_iteration} {zero} {n_expr})"
        total = wide_base
        for case in residue_cases:
            modulus = case.modulus
            residue = case.residue
            coeff = case.coefficient
            bias = case.bias
            if modulus <= 1:
                count_expr = count_all_expr
                offset_expr = zero
            else:
                mask = modulus - 1
                if mask <= 0 or (mask & (mask + 1)) != 0:
                    return None
                mask_smt = _smt_bv_const(mask, wide_bits)
                residue_smt = _smt_bv_const(residue, wide_bits)
                start_low = f"(bvand {wide_start} {mask_smt})"
                raw_offset = f"(bvsub {residue_smt} {start_low})"
                offset_expr = f"(bvand {raw_offset} {mask_smt})"
                positive_span = f"(bvsub {n_expr} {offset_expr})"
                no_matching_residue = f"(or {no_iteration} {_distance_le(n_expr, offset_expr)})"
                count_nonzero = _ceil_div_positive(positive_span, modulus)
                count_expr = f"(ite {no_matching_residue} {zero} {count_nonzero})"
            first_expr = f"(bvadd {wide_start} {offset_expr})"
            progression_sum = _exact_progression_sum(first_expr, count_expr, step=modulus)
            coeff_term = _smt_scale_term(progression_sum, coeff, wide_bits)
            bias_term = _smt_scale_term(count_expr, bias, wide_bits)
            for term in (coeff_term, bias_term):
                if term is not None:
                    total = f"(bvadd {total} {term})"
            total = _add_bias_expression_terms(total, count_expr, modulus, residue)
            if total is None:
                return None
        return _smt_low_bits(total, wide_bits, result_bits)

    if any(case.modulus != 1 for case in residue_cases):
        return None

    if induction_step > 0:
        span_expr = f"(bvsub {wide_limit} {wide_start})"
        no_iteration = _loop_le(wide_limit, wide_start)
    else:
        span_expr = f"(bvsub {wide_start} {wide_limit})"
        no_iteration = _loop_le(wide_start, wide_limit)
    count_nonzero = span_expr
    step_magnitude = abs(induction_step)
    if step_magnitude != 1:
        count_nonzero = _ceil_div_positive(span_expr, step_magnitude)
    count_expr = f"(ite {no_iteration} {zero} {count_nonzero})"
    progression_sum = _exact_progression_sum(wide_start, count_expr, step=induction_step)
    total = wide_base
    for case in residue_cases:
        coeff_term = _smt_scale_term(progression_sum, case.coefficient, wide_bits)
        bias_term = _smt_scale_term(count_expr, case.bias, wide_bits)
        for term in (coeff_term, bias_term):
            if term is not None:
                total = f"(bvadd {total} {term})"
        total = _add_bias_expression_terms(total, count_expr, case.modulus, case.residue)
        if total is None:
            return None
    return _smt_low_bits(total, wide_bits, result_bits)


# Sibling modules reference each other at call time; import them last to avoid cycles.
from scripts.function_tracer_pcode.core.render_plan import RENDER_FAILURES
from scripts.function_tracer_pcode.core.render_smt.render import (
    _detached_child_renderer,
)
from scripts.function_tracer_pcode.core.render_smt.widths import (
    _coerce_expr_to_bitvec_width,
    _coerce_smt_bitvec_width,
    _expr_constant_int,
    _expr_prefers_signed_extension,
    _smt_bv_const,
    _smt_concat,
    _smt_extend_to_width,
    _smt_extract,
    _smt_low_bits,
    _smt_scale_term,
    expression_smt_bit_width,
)

"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.equivalence.strategies.pairwise``."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence
from ._shared import (
    Expression,
    ExpressionType,
    ReadonlyReductionTermRef,
    ReturnCase,
    canonicalize_location,
    expression_smt_bit_width,
)

def _impl__expression_contains_reduction_count_surface_at_width(
    self,
    expr: Optional[Expression],
    case: ReturnCase,
    accumulator_proof,
    width_bits: int,
) -> bool:
    if expr is None:
        return False
    expr_bits = max(1, int(expression_smt_bit_width(expr) or 0))
    if (
        expr_bits == int(width_bits)
        and self._parameter_matches_reduction_count_identity(expr, case, accumulator_proof)
    ):
        return True
    if (
        getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP
        and getattr(expr, "operator", None) == "SUBPIECE"
        and len(getattr(expr, "operands", None) or []) == 2
    ):
        source, offset = expr.operands
        try:
            offset_is_low = (
                getattr(offset, "expr_type", None) == ExpressionType.CONSTANT
                and int(getattr(offset, "value", 0) or 0) == 0
            )
        except (TypeError, ValueError):
            offset_is_low = False
        if (
            offset_is_low
            and expr_bits == int(width_bits)
            and self._parameter_matches_reduction_count_identity(source, case, accumulator_proof)
        ):
            return True
    if (
        getattr(expr, "expr_type", None) == ExpressionType.UNARY_OP
        and getattr(expr, "operator", None) in {"CAST", "COPY"}
        and len(getattr(expr, "operands", None) or []) == 1
        and expr_bits == int(width_bits)
        and self._parameter_matches_reduction_count_identity(expr.operands[0], case, accumulator_proof)
    ):
        return True
    for operand in getattr(expr, "operands", None) or ():
        if self._expression_contains_reduction_count_surface_at_width(
            operand,
            case,
            accumulator_proof,
            width_bits,
        ):
            return True
    if getattr(expr, "expr_type", None) == ExpressionType.PHI and getattr(expr, "value", None):
        for condition, value in expr.value:
            if condition is not None and self._expression_contains_reduction_count_surface_at_width(
                getattr(condition, "expression", None),
                case,
                accumulator_proof,
                width_bits,
            ):
                return True
            if self._expression_contains_reduction_count_surface_at_width(
                value,
                case,
                accumulator_proof,
                width_bits,
            ):
                return True
    return False

def _impl__exact_reduction_count_constant(self, expr: Optional[Expression]) -> Optional[int]:
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.CONSTANT:
        return None
    try:
        return int(getattr(expr, "value", None))
    except (TypeError, ValueError):
        return None

def _impl__extract_readonly_reduction_terms_from_expression(
    self,
    expr: Optional[Expression],
    parameters: Sequence[Dict[str, Any]],
    pointer_base_ref,
    *,
    program_is_big_endian: Optional[bool] = None,
) -> Optional[tuple[ReadonlyReductionTermRef, ...]]:
    extracted = self._extract_readonly_reduction_terms_and_bias_from_expression(
        expr,
        parameters,
        pointer_base_ref,
        program_is_big_endian=program_is_big_endian,
    )
    if extracted is None:
        return None
    terms, bias = extracted
    if int(bias) != 0:
        return None
    return terms

def _impl__extract_readonly_reduction_terms_and_bias_from_expression(
    self,
    expr: Optional[Expression],
    parameters: Sequence[Dict[str, Any]],
    pointer_base_ref,
    *,
    program_is_big_endian: Optional[bool] = None,
) -> Optional[tuple[tuple[ReadonlyReductionTermRef, ...], int]]:
    if expr is None or pointer_base_ref is None:
        return None
    extracted: List[ReadonlyReductionTermRef] = []
    constant_bias = 0
    for sign, term in self._flatten_readonly_add_terms(expr):
        if getattr(term, "expr_type", None) == ExpressionType.CONSTANT:
            value = self._raw_constant_value(term)
            if value is None:
                return None
            constant_bias += int(sign) * int(value)
            continue
        if sign != 1:
            return None
        descriptor = self._extract_readonly_reduction_term_descriptor(
            term,
            parameters,
            pointer_base_ref,
            program_is_big_endian=program_is_big_endian,
        )
        if descriptor is None:
            return None
        extracted.append(descriptor)
    if not extracted:
        return None
    extracted.sort(key=lambda item: (int(item.byte_offset), int(item.access_size)))
    return tuple(extracted), int(constant_bias)

def _impl__flatten_readonly_add_terms(
    self,
    expr: Expression,
    sign: int = 1,
) -> List[tuple[int, Expression]]:
    if getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP and len(getattr(expr, "operands", []) or []) == 2:
        if getattr(expr, "operator", None) == "INT_ADD":
            return self._flatten_readonly_add_terms(expr.operands[0], sign) + self._flatten_readonly_add_terms(
                expr.operands[1],
                sign,
            )
        if getattr(expr, "operator", None) == "INT_SUB":
            return self._flatten_readonly_add_terms(expr.operands[0], sign) + self._flatten_readonly_add_terms(
                expr.operands[1],
                -sign,
            )
    return [(sign, expr)]

def _impl__extract_readonly_reduction_term_descriptor(
    self,
    expr: Optional[Expression],
    parameters: Sequence[Dict[str, Any]],
    pointer_base_ref,
    *,
    lsb_byte_offset: int = 0,
    narrowed_size: Optional[int] = None,
    program_is_big_endian: Optional[bool] = None,
) -> Optional[ReadonlyReductionTermRef]:
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        if expr.operator == "INT_SEXT":
            return None
        if expr.operator in {"INT_ZEXT", "CAST", "COPY"}:
            return self._extract_readonly_reduction_term_descriptor(
                expr.operands[0],
                parameters,
                pointer_base_ref,
                lsb_byte_offset=lsb_byte_offset,
                narrowed_size=narrowed_size,
                program_is_big_endian=program_is_big_endian,
            )

    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        if expr.operator == "SUBPIECE":
            byte_offset = self._raw_constant_value(expr.operands[1])
            if byte_offset is None or byte_offset < 0:
                return None
            return self._extract_readonly_reduction_term_descriptor(
                expr.operands[0],
                parameters,
                pointer_base_ref,
                lsb_byte_offset=lsb_byte_offset + int(byte_offset),
                narrowed_size=max(1, int(expr.size or 0)),
                program_is_big_endian=program_is_big_endian,
            )
        if expr.operator == "INT_RIGHT":
            shift_bits = self._raw_constant_value(expr.operands[1])
            if shift_bits is None or shift_bits < 0 or (int(shift_bits) % 8) != 0:
                return None
            return self._extract_readonly_reduction_term_descriptor(
                expr.operands[0],
                parameters,
                pointer_base_ref,
                lsb_byte_offset=lsb_byte_offset + (int(shift_bits) // 8),
                narrowed_size=narrowed_size or max(1, int(expr.size or 0)),
                program_is_big_endian=program_is_big_endian,
            )
        if expr.operator == "INT_AND":
            mask_width = self._low_mask_width_bytes(expr.operands[0], expr.operands[1])
            value_expr = expr.operands[0]
            if mask_width is None:
                mask_width = self._low_mask_width_bytes(expr.operands[1], expr.operands[0])
                value_expr = expr.operands[1]
            if mask_width is not None:
                return self._extract_readonly_reduction_term_descriptor(
                    value_expr,
                    parameters,
                    pointer_base_ref,
                    lsb_byte_offset=lsb_byte_offset,
                    narrowed_size=narrowed_size or mask_width,
                    program_is_big_endian=program_is_big_endian,
                )

    if expr.expr_type != ExpressionType.MEMORY or not expr.operands:
        return None
    load_size = max(1, int(expr.size or 0))
    access_size = max(1, int(narrowed_size or load_size))
    if lsb_byte_offset < 0 or access_size > load_size or lsb_byte_offset + access_size > load_size:
        return None
    if (int(lsb_byte_offset) != 0 or access_size != load_size) and program_is_big_endian is None:
        return None
    location = canonicalize_location(expr.operands[0], parameters, size=load_size)
    if location is None:
        return None
    base_ref = getattr(location, "base_ref", None)
    if base_ref is None:
        return None
    base_key = getattr(base_ref, "semantic_key", lambda: None)()
    proof_base_key = getattr(pointer_base_ref, "semantic_key", lambda: None)()
    if base_key is None or proof_base_key is None or base_key != proof_base_key:
        return None
    if program_is_big_endian is True:
        byte_offset = int(location.offset) + (load_size - access_size - int(lsb_byte_offset))
    else:
        byte_offset = int(location.offset) + int(lsb_byte_offset)
    return ReadonlyReductionTermRef(byte_offset=byte_offset, access_size=access_size)

def _impl__readonly_reduction_values_equivalent(
    self,
    left: Expression,
    right: Expression,
) -> bool:
    return self._intrinsic_runtime_values_equivalent(left, right)

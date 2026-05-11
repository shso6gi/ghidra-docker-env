# -*- coding: utf-8 -*-
"""Solver-proven rewrite fallback for pairwise queries."""

from __future__ import annotations

from typing import Any, Dict, Optional

from ...model import Expression, ExpressionType
from ..formula.returns import coerce_value_to_bitvec_width
from ..normalize import (
    NormalizationContext,
    NormalizationSettings,
    are_structurally_equivalent,
    normalize_expression,
)
from .pairwise_models import QueryResult, ReturnCase
from .pairwise_query_builder import build_pair_query


def try_solver_proven_rewrite_equivalence(
    strategy,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str,
) -> QueryResult:
    settings = getattr(strategy, "solver_proven_rewrite_settings", None)
    if settings is None:
        settings = NormalizationSettings.safe()

    rewritten_expr1 = _build_rewrite_candidate(case1.value_expr, settings)
    rewritten_expr2 = _build_rewrite_candidate(case2.value_expr, settings)

    changed1 = _expr_signature(rewritten_expr1) != _expr_signature(case1.value_expr)
    changed2 = _expr_signature(rewritten_expr2) != _expr_signature(case2.value_expr)
    if not changed1 and not changed2:
        result = QueryResult(is_equivalent=None)
        result.pair_stage = "rewrite-no-change"
        result.blocking_reason = "solver_proven_rewrite_no_change"
        result.blocking_detail = "solver-proven rewrite produced no candidate rewrite"
        return result

    if changed1:
        if not _prove_rewrite(
            strategy,
            base_ctx,
            case1,
            param_replace_fn1,
            rewritten_expr1,
            pair_id,
            label="rewrite-proof-1",
        ):
            result = QueryResult(is_equivalent=None)
            result.pair_stage = "rewrite-proof-1"
            result.blocking_reason = "solver_proven_rewrite_proof_failed"
            result.blocking_detail = "left rewrite candidate could not be proven equivalent"
            return result
    else:
        rewritten_expr1 = case1.value_expr

    if changed2:
        if not _prove_rewrite(
            strategy,
            base_ctx,
            case2,
            param_replace_fn2,
            rewritten_expr2,
            pair_id,
            label="rewrite-proof-2",
        ):
            result = QueryResult(is_equivalent=None)
            result.pair_stage = "rewrite-proof-2"
            result.blocking_reason = "solver_proven_rewrite_proof_failed"
            result.blocking_detail = "right rewrite candidate could not be proven equivalent"
            return result
    else:
        rewritten_expr2 = case2.value_expr

    rewritten_case1 = _clone_case_with_value_expr(case1, rewritten_expr1)
    rewritten_case2 = _clone_case_with_value_expr(case2, rewritten_expr2)
    if _rewritten_values_are_trivially_equal(
        strategy,
        base_ctx,
        rewritten_case1,
        rewritten_case2,
    ):
        result = QueryResult(is_equivalent=True)
        result.pair_stage = "rewrite-structural"
        return result

    rewritten_query = build_pair_query(
        base_ctx,
        rewritten_case1,
        rewritten_case2,
        param_replace_fn1,
        param_replace_fn2,
        pair_id,
    )
    result = strategy._solve_query_internal(
        rewritten_query,
        pair_id,
        stage="rewrite-ineq",
        use_hard_timeout=True,
    )
    result.last_query = rewritten_query
    result.pair_stage = "rewrite-ineq"
    return result


def _rewritten_values_are_trivially_equal(
    strategy,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
) -> bool:
    if base_ctx.get("return_size1", 32) != base_ctx.get("return_size2", 32):
        return False
    if case1.should_sign_extend_value() != case2.should_sign_extend_value() and not _sign_extension_irrelevant(
        base_ctx,
        case1.value_expr,
        case2.value_expr,
    ):
        return False

    left = case1.value_expr
    right = case2.value_expr
    if _intrinsic_values_match(strategy, case1, case2):
        return True

    equivalent, _reason = are_structurally_equivalent(
        left,
        right,
        debug=bool(getattr(strategy, "debug", False)),
    )
    if not equivalent:
        return False
    return _expression_sizes_compatible(left, right)


def _sign_extension_irrelevant(
    base_ctx: Dict[str, Any],
    left: Expression,
    right: Expression,
) -> bool:
    target_bits = int(base_ctx.get("return_size1", 32) or 32)
    left_bits = _expr_known_bits(left)
    right_bits = _expr_known_bits(right)
    return left_bits is not None and right_bits is not None and left_bits >= target_bits and right_bits >= target_bits


def _expr_known_bits(expr: Expression) -> Optional[int]:
    size = int(getattr(expr, "size", 0) or 0)
    if size <= 0:
        return None
    return size * 8


def _intrinsic_values_match(strategy, case1: ReturnCase, case2: ReturnCase) -> bool:
    intrinsic_equivalent = getattr(strategy, "_intrinsic_runtime_values_equivalent", None)
    if not callable(intrinsic_equivalent):
        return False
    try:
        return bool(
            intrinsic_equivalent(
                case1.value_expr,
                case2.value_expr,
                left_case=case1,
                right_case=case2,
            )
        )
    except TypeError:
        return bool(intrinsic_equivalent(case1.value_expr, case2.value_expr))


def _expression_sizes_compatible(left: Expression, right: Expression) -> bool:
    left_size = int(getattr(left, "size", 0) or 0)
    right_size = int(getattr(right, "size", 0) or 0)
    if left_size > 0 and right_size > 0 and left_size != right_size:
        return False

    left_operands = list(getattr(left, "operands", []) or [])
    right_operands = list(getattr(right, "operands", []) or [])
    if len(left_operands) != len(right_operands):
        return False
    return all(
        _expression_sizes_compatible(left_operand, right_operand)
        for left_operand, right_operand in zip(left_operands, right_operands)
    )


def _clone_case_with_value_expr(case: ReturnCase, value_expr: Expression) -> ReturnCase:
    return ReturnCase(
        index=case.index,
        conditions=list(case.conditions),
        value_expr=value_expr,
        return_info=case.return_info,
        normalized_value_expr=value_expr,
        return_type=case.return_type,
        return_type_obj=case.return_type_obj,
        source_indices=list(case.source_indices),
        parameters=list(case.parameters),
        effect_summary=case.effect_summary,
        comparison_surface=case.comparison_surface,
        summary_conditions=list(case.summary_conditions),
    )


def _build_rewrite_candidate(expr: Expression, settings: NormalizationSettings) -> Expression:
    pre_rewritten = _apply_solver_proven_candidate_rewrites(expr)
    normalized = normalize_expression(
        pre_rewritten,
        NormalizationContext(settings=settings),
    )
    return _apply_solver_proven_candidate_rewrites(normalized)


def _apply_solver_proven_candidate_rewrites(expr: Expression) -> Expression:
    expr_type = getattr(expr, "expr_type", None)
    if expr_type != ExpressionType.BINARY_OP:
        return expr

    operands = list(getattr(expr, "operands", []) or [])
    if len(operands) != 2:
        return expr

    left = _apply_solver_proven_candidate_rewrites(operands[0])
    right = _apply_solver_proven_candidate_rewrites(operands[1])
    operator = getattr(expr, "operator", None)

    rewritten = _maybe_rewrite_modulo_expansion(expr, operator, left, right)
    if rewritten is not None:
        return rewritten

    if operator in {
        "INT_ADD",
        "INT_MULT",
        "INT_AND",
        "INT_OR",
        "INT_XOR",
        "INT_EQUAL",
        "INT_NOTEQUAL",
    }:
        ordered = sorted([left, right], key=_exact_expr_key)
        if ordered[0] is not left or ordered[1] is not right:
            return Expression(
                ExpressionType.BINARY_OP,
                operator=operator,
                operands=ordered,
                size=getattr(expr, "size", None),
            )

    if left is operands[0] and right is operands[1]:
        return expr

    return Expression(
        ExpressionType.BINARY_OP,
        operator=operator,
        operands=[left, right],
        size=getattr(expr, "size", None),
    )


def _maybe_rewrite_modulo_expansion(
    original_expr: Expression,
    operator: Optional[str],
    left: Expression,
    right: Expression,
) -> Optional[Expression]:
    if operator != "INT_SUB":
        return None

    multiplicands = _extract_binary_operands(right, "INT_MULT")
    if multiplicands is None:
        return None

    dividend = None
    divisor = None
    remainder_operator = None
    for candidate_div, candidate_other in (
        multiplicands,
        (multiplicands[1], multiplicands[0]),
    ):
        div_operands = _extract_binary_operands(candidate_div, "INT_SDIV")
        if div_operands is not None:
            dividend, divisor = div_operands
            remainder_operator = "INT_SREM"
            if _exprs_match(left, dividend) and _exprs_match(candidate_other, divisor):
                break
        div_operands = _extract_binary_operands(candidate_div, "INT_DIV")
        if div_operands is not None:
            dividend, divisor = div_operands
            remainder_operator = "INT_REM"
            if _exprs_match(left, dividend) and _exprs_match(candidate_other, divisor):
                break
    else:
        return None

    return Expression(
        ExpressionType.BINARY_OP,
        operator=remainder_operator,
        operands=[left, divisor],
        size=getattr(original_expr, "size", None),
    )


def _extract_binary_operands(expr: Expression, operator: str):
    if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    if getattr(expr, "operator", None) != operator:
        return None
    operands = list(getattr(expr, "operands", []) or [])
    if len(operands) != 2:
        return None
    return operands[0], operands[1]


def _exprs_match(left: Expression, right: Expression) -> bool:
    return _exact_expr_key(left) == _exact_expr_key(right)


def _exact_expr_key(expr: Expression) -> str:
    try:
        return expr.to_smt()
    except Exception:
        structural_key = getattr(expr, "structural_key", None)
        if callable(structural_key):
            return repr(structural_key(budget=256))
        return repr(expr)


def _expr_signature(expr: Expression) -> object:
    try:
        return expr.to_smt()
    except Exception:
        structural_key = getattr(expr, "structural_key", None)
        if callable(structural_key):
            return structural_key(budget=256)
        return repr(expr)


def _prove_rewrite(
    strategy,
    base_ctx: Dict[str, Any],
    case: ReturnCase,
    param_replace_fn,
    rewritten_expr: Expression,
    pair_id: str,
    *,
    label: str,
) -> bool:
    query = _build_rewrite_proof_query(
        base_ctx,
        case,
        param_replace_fn,
        rewritten_expr,
        label,
    )
    result = strategy._solve_query_internal(
        query,
        pair_id,
        stage=label,
        use_hard_timeout=False,
    )
    return result.is_equivalent is True


def _build_rewrite_proof_query(
    base_ctx: Dict[str, Any],
    case: ReturnCase,
    param_replace_fn,
    rewritten_expr: Expression,
    label: str,
) -> str:
    return_size = base_ctx.get("return_size1", 32)
    if label.endswith("-2"):
        return_size = base_ctx.get("return_size2", return_size)

    original_expr, proof_expr = _extract_minimal_rewrite_difference(
        case.value_expr,
        rewritten_expr,
    )
    proof_target_bits = _proof_target_bits(original_expr, proof_expr, return_size)

    use_sign_extension = False
    original_smt = _render_expression_smt(
        original_expr,
        param_replace_fn,
        proof_target_bits,
        use_sign_extension=use_sign_extension,
    )
    rewritten_smt = _render_expression_smt(
        proof_expr,
        param_replace_fn,
        proof_target_bits,
        use_sign_extension=use_sign_extension,
    )

    lines = [
        "; ============================================================",
        f"; Solver-proven rewrite proof: {label}",
        "; ============================================================",
        "",
        "(set-logic QF_BV)",
        "",
    ]
    lines.extend(base_ctx["header_lines"])
    lines.append("")
    lines.append("; ----------------------------------------")
    lines.append("; Case conditions")
    lines.append("; ----------------------------------------")
    for condition_smt in case.get_conditions_smt(param_replace_fn):
        lines.append(f"(assert {condition_smt})")
    lines.append("")
    lines.append("; ----------------------------------------")
    lines.append("; Rewrite non-equivalence check")
    lines.append("; ----------------------------------------")
    lines.append(f"(assert (not (= {original_smt} {rewritten_smt})))")
    lines.append("")
    lines.append("(check-sat)")
    return "\n".join(lines)


def _extract_minimal_rewrite_difference(
    original_expr: Expression,
    rewritten_expr: Expression,
):
    if _exact_expr_key(original_expr) == _exact_expr_key(rewritten_expr):
        return original_expr, rewritten_expr

    if (
        getattr(original_expr, "expr_type", None) != getattr(rewritten_expr, "expr_type", None)
        or getattr(original_expr, "operator", None) != getattr(rewritten_expr, "operator", None)
    ):
        return original_expr, rewritten_expr

    original_operands = list(getattr(original_expr, "operands", []) or [])
    rewritten_operands = list(getattr(rewritten_expr, "operands", []) or [])
    if len(original_operands) != len(rewritten_operands):
        return original_expr, rewritten_expr

    differing_indices = [
        index
        for index, (lhs, rhs) in enumerate(zip(original_operands, rewritten_operands))
        if _exact_expr_key(lhs) != _exact_expr_key(rhs)
    ]
    if len(differing_indices) != 1:
        return original_expr, rewritten_expr

    differing_index = differing_indices[0]
    return _extract_minimal_rewrite_difference(
        original_operands[differing_index],
        rewritten_operands[differing_index],
    )


def _proof_target_bits(
    original_expr: Expression,
    rewritten_expr: Expression,
    fallback_bits: int,
) -> int:
    original_bits = getattr(original_expr, "size", None)
    rewritten_bits = getattr(rewritten_expr, "size", None)
    if isinstance(original_bits, int) and isinstance(rewritten_bits, int):
        return max(original_bits, rewritten_bits) * 8
    if isinstance(original_bits, int):
        return original_bits * 8
    if isinstance(rewritten_bits, int):
        return rewritten_bits * 8
    return fallback_bits


def _render_expression_smt(
    expr: Expression,
    param_replace_fn,
    target_bits: int,
    *,
    use_sign_extension: bool,
) -> str:
    if param_replace_fn is None:
        rendered = expr.to_smt()
    else:
        try:
            rendered = param_replace_fn(expr)
        except TypeError:
            rendered = param_replace_fn(expr.to_smt())
    if not isinstance(rendered, str):
        to_smt = getattr(rendered, "to_smt", None)
        rendered = to_smt() if callable(to_smt) else str(rendered)
    return coerce_value_to_bitvec_width(
        expr,
        rendered,
        target_bits,
        use_sign_extension=use_sign_extension,
    )

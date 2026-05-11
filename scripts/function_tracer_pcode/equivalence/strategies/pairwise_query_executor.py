# -*- coding: utf-8 -*-
"""Query execution helpers for PairwiseStrategy."""
import inspect
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

from ...smt import SolverStatus
from ..formula.returns import (
    ReturnWidthMismatchError,
    expression_has_unresolved_value,
    require_equal_return_bit_widths,
)
from .pairwise_models import QueryResult


def solve_query_internal(strategy, query: str, pair_id: str, stage: str = "full", use_hard_timeout: bool = False) -> QueryResult:
    """クエリを実行する"""
    timeout = strategy.per_query_timeout_hard if use_hard_timeout else strategy.per_query_timeout
    parallel_result = _run_query_with_timeout(strategy.solver_runner, query, timeout=timeout)
    counterexample_raw = None
    if parallel_result.is_equivalent is False:
        counterexample_raw = parallel_result.get_counterexample()

    if parallel_result.is_equivalent is True:
        result_str = "UNSAT"
    elif parallel_result.is_equivalent is False:
        result_str = "SAT"
    else:
        result_str = "UNKNOWN/TIMEOUT"

    elapsed = parallel_result.results[0].elapsed_time if parallel_result.results else 0.0
    strategy._debug_print(f"  Pair {pair_id} {stage}: {result_str} (t={elapsed:.3f}s)")

    _log_solver_errors(strategy, query, parallel_result.results)

    if strategy.save_unknown_queries and parallel_result.is_equivalent is None:
        strategy._save_unknown_query(query, pair_id, stage)

    return QueryResult(
        is_equivalent=parallel_result.is_equivalent,
        counterexample_raw=counterexample_raw,
    )


def solve_query_twostage(
    strategy,
    base_ctx: Dict[str, Any],
    case1,
    case2,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str
) -> QueryResult:
    """二段階チェックを実行する"""
    cond_query = strategy._build_condition_only_query(
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        pair_id,
    )
    stage1_result = strategy._solve_query_internal(
        cond_query,
        pair_id,
        stage="conds-only",
        use_hard_timeout=False,
    )
    if stage1_result.is_equivalent is True:
        stage1_result.last_query = cond_query
        stage1_result.pair_stage = "conds-only"
        return stage1_result

    contextual_unresolved = getattr(strategy, "_case_value_contains_unresolved", None)
    if contextual_unresolved is not None:
        has_unresolved_value = (
            contextual_unresolved(
                case1,
                case2.conditions,
                own_render_fn=param_replace_fn1,
                extra_render_fn=param_replace_fn2,
                base_ctx=base_ctx,
                query_label=f"{pair_id}:value1",
            )
            or contextual_unresolved(
                case2,
                case1.conditions,
                own_render_fn=param_replace_fn2,
                extra_render_fn=param_replace_fn1,
                base_ctx=base_ctx,
                query_label=f"{pair_id}:value2",
            )
        )
    else:
        has_unresolved_value = (
            expression_has_unresolved_value(case1.value_expr)
            or expression_has_unresolved_value(case2.value_expr)
        )

    if has_unresolved_value:
        strategy._debug_print(
            f"  Pair {pair_id} with-ineq skipped: unresolved value expression detected"
        )
        if getattr(strategy, "_active_normalization_stats", None) is not None:
            strategy._active_normalization_stats["unknown_results"] += 1
        result = QueryResult(is_equivalent=None)
        result.last_query = cond_query
        result.pair_stage = "with-ineq-skipped"
        return result

    try:
        require_equal_return_bit_widths(
            base_ctx.get("return_size1", 32),
            base_ctx.get("return_size2", 32),
            context="pairwise value inequality",
        )
    except ReturnWidthMismatchError as exc:
        strategy._debug_print(f"  Pair {pair_id} with-ineq skipped: {exc}")
        if getattr(strategy, "_active_normalization_stats", None) is not None:
            strategy._active_normalization_stats["unknown_results"] += 1
        result = QueryResult(is_equivalent=None)
        result.last_query = cond_query
        result.pair_stage = "return-width-mismatch"
        return result

    full_query = strategy._build_pair_query(
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        pair_id,
    )
    stage2_result = strategy._solve_query_internal(
        full_query,
        pair_id,
        stage="with-ineq",
        use_hard_timeout=True,
    )
    stage2_result.last_query = full_query
    stage2_result.pair_stage = "with-ineq"

    if (
        stage2_result.is_equivalent is None
        and getattr(strategy, "enable_solver_proven_rewrite_fallback", False)
    ):
        if getattr(strategy, "_active_normalization_stats", None) is not None:
            strategy._active_normalization_stats["solver_proven_rewrite_attempts"] += 1
        rewrite_result = strategy._try_solver_proven_rewrite_equivalence(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
        )
        if rewrite_result.is_equivalent is True:
            if getattr(strategy, "_active_normalization_stats", None) is not None:
                strategy._active_normalization_stats["solver_proven_rewrite_successes"] += 1
            return rewrite_result
        if rewrite_result.is_equivalent is False:
            if getattr(strategy, "_active_normalization_stats", None) is not None:
                strategy._active_normalization_stats["solver_proven_rewrite_successes"] += 1
            return rewrite_result
        if getattr(strategy, "_active_normalization_stats", None) is not None:
            strategy._active_normalization_stats["solver_proven_rewrite_failures"] += 1

    if (
        stage2_result.is_equivalent is None
        and getattr(strategy, "enable_normalization_fallback", False)
    ):
        if getattr(strategy, "_active_normalization_stats", None) is not None:
            strategy._active_normalization_stats["timeout_fallback_attempts"] += 1
        norm_result = strategy._try_normalization_equivalence(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
        )
        if norm_result.is_equivalent is True:
            norm_result.last_query = full_query
            norm_result.pair_stage = "norm-ineq"
            return norm_result
        if norm_result.is_equivalent is False:
            norm_result.last_query = full_query
            norm_result.pair_stage = "norm-ineq"
            return norm_result

    return stage2_result


def validate_counterexample_across_cases(
    strategy,
    base_ctx: Dict[str, Any],
    cases1: Sequence,
    cases2: Sequence,
    param_replace_fn1,
    param_replace_fn2,
    sat_case_indices: Tuple[int, int],
    counterexample_raw: Optional[Dict[str, Any]],
) -> bool:
    """
    SAT 反例が本当に決定的かを、同一モデルで全ケースに対して再検証する。

    同じ入力モデルで:
    - 元の SAT ペアが実際に到達不能なら偽反例
    - 他の到達可能ケース対で値が等しいなら、case split が不完全で偽反例の可能性が高い
    """
    return _validate_counterexample_model(
        strategy,
        base_ctx,
        cases1,
        cases2,
        param_replace_fn1,
        param_replace_fn2,
        counterexample_raw,
        decisive_pairs=[sat_case_indices],
    )


def validate_counterexample_globally(
    strategy,
    base_ctx: Dict[str, Any],
    cases1: Sequence,
    cases2: Sequence,
    param_replace_fn1,
    param_replace_fn2,
    counterexample_raw: Optional[Dict[str, Any]],
) -> bool:
    """
    monolithic SAT 反例が case split 全体で一意に非等価を示すか検証する。

    到達可能な equal pair が 1 つでもあれば、同一モデルが複数の枝割り当てを
    同時に満たしており、反例は曖昧とみなして UNKNOWN へ倒す。
    """
    return _validate_counterexample_model(
        strategy,
        base_ctx,
        cases1,
        cases2,
        param_replace_fn1,
        param_replace_fn2,
        counterexample_raw,
        decisive_pairs=None,
    )


def _validate_counterexample_model(
    strategy,
    base_ctx: Dict[str, Any],
    cases1: Sequence,
    cases2: Sequence,
    param_replace_fn1,
    param_replace_fn2,
    counterexample_raw: Optional[Dict[str, Any]],
    decisive_pairs: Optional[Sequence[Tuple[int, int]]],
) -> bool:
    if not counterexample_raw:
        return True

    model_assertions = _build_model_assertions(base_ctx, counterexample_raw)
    if not model_assertions:
        return True

    decisive_pair_set = set(decisive_pairs or [])
    decisive_pair_feasible = False
    feasible_distinguishing_pair = False

    for i, case1 in enumerate(cases1):
        for j, case2 in enumerate(cases2):
            feasible = _check_pair_feasibility_under_model(
                strategy,
                base_ctx,
                case1,
                case2,
                param_replace_fn1,
                param_replace_fn2,
                model_assertions,
                pair_id=f"({i},{j})",
            )
            if feasible is None:
                strategy._debug_print(
                    f"  Counterexample validation for pair ({i},{j}) was inconclusive"
                )
                return False
            if not feasible:
                continue

            if (i, j) in decisive_pair_set:
                decisive_pair_feasible = True

            equal = _check_pair_equality_under_model(
                strategy,
                base_ctx,
                case1,
                case2,
                param_replace_fn1,
                param_replace_fn2,
                model_assertions,
                pair_id=f"({i},{j})",
            )
            if equal is None:
                strategy._debug_print(
                    f"  Equality re-check for pair ({i},{j}) was inconclusive"
                )
                return False
            if equal:
                strategy._debug_print(
                    f"  Counterexample is ambiguous: model also matches equal pair ({i},{j})"
                )
                return False
            feasible_distinguishing_pair = True

    if decisive_pair_set and not decisive_pair_feasible:
        strategy._debug_print(
            "  Counterexample rejected: original SAT pair is infeasible under the model"
        )
        return False

    if not feasible_distinguishing_pair:
        strategy._debug_print(
            "  Counterexample rejected: no feasible distinguishing case pair under the model"
        )
        return False

    return True


def _check_pair_feasibility_under_model(
    strategy,
    base_ctx: Dict[str, Any],
    case1,
    case2,
    param_replace_fn1,
    param_replace_fn2,
    model_assertions: Sequence[str],
    pair_id: str,
) -> Optional[bool]:
    query = _build_model_validation_query(
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        model_assertions,
        equality=False,
    )
    result = _run_validation_query(strategy, query, f"{pair_id}:feasible")
    if result is None:
        return None
    return result


def _check_pair_equality_under_model(
    strategy,
    base_ctx: Dict[str, Any],
    case1,
    case2,
    param_replace_fn1,
    param_replace_fn2,
    model_assertions: Sequence[str],
    pair_id: str,
) -> Optional[bool]:
    try:
        query = _build_model_validation_query(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            model_assertions,
            equality=True,
        )
    except ReturnWidthMismatchError as exc:
        strategy._debug_print(f"  Equality re-check for pair {pair_id} blocked: {exc}")
        return None
    result = _run_validation_query(strategy, query, f"{pair_id}:equal")
    if result is None:
        return None
    return result


def _run_validation_query(strategy, query: str, label: str) -> Optional[bool]:
    timeout = min(getattr(strategy, "per_query_timeout", 5), 5)
    parallel_result = _run_query_with_timeout(strategy.solver_runner, query, timeout=timeout)

    _log_solver_errors(strategy, query, parallel_result.results)
    if parallel_result.is_equivalent is True:
        return False
    if parallel_result.is_equivalent is False:
        return True

    strategy._debug_print(f"  Validation query {label} returned UNKNOWN/TIMEOUT")
    return None


def _run_query_with_timeout(solver_runner, query: str, timeout: int):
    """solver_runner.run_sequential(query, timeout=...) をサポートしていれば使う。"""
    run_sequential = getattr(solver_runner, "run_sequential", None)
    if run_sequential is None:
        raise AttributeError("solver_runner has no run_sequential method")

    try:
        signature = inspect.signature(run_sequential)
    except (TypeError, ValueError):
        try:
            return run_sequential(query, timeout=timeout)
        except TypeError as exc:
            if "unexpected keyword argument" in str(exc) and "timeout" in str(exc):
                return run_sequential(query)
            raise

    has_timeout_parameter = "timeout" in signature.parameters
    has_var_keyword = any(
        param.kind == inspect.Parameter.VAR_KEYWORD
        for param in signature.parameters.values()
    )
    if has_timeout_parameter or has_var_keyword:
        try:
            return run_sequential(query, timeout=timeout)
        except TypeError as exc:
            if "unexpected keyword argument" in str(exc) and "timeout" in str(exc):
                return run_sequential(query)
            raise

    return run_sequential(query)


def _build_model_validation_query(
    base_ctx: Dict[str, Any],
    case1,
    case2,
    param_replace_fn1,
    param_replace_fn2,
    model_assertions: Sequence[str],
    equality: bool,
) -> str:
    return_size1 = base_ctx.get("return_size1", 32)
    return_size2 = base_ctx.get("return_size2", 32)
    value1_smt = case1.get_value_smt(
        param_replace_fn1,
        target_bits=return_size1,
        use_sign_extension=case1.should_sign_extend_value(),
    )
    value2_smt = case2.get_value_smt(
        param_replace_fn2,
        target_bits=return_size2,
        use_sign_extension=case2.should_sign_extend_value(),
    )

    lines: List[str] = [
        "(set-logic QF_BV)",
        "",
    ]
    symbol_bit_widths = dict(_iter_declared_symbols(base_ctx))
    value1_smt = _normalize_smt_expr_widths(value1_smt, symbol_bit_widths)
    value2_smt = _normalize_smt_expr_widths(value2_smt, symbol_bit_widths)
    lines.extend(base_ctx["header_lines"])
    lines.extend(model_assertions)
    lines.extend(_build_case_assertions(case1, param_replace_fn1, symbol_bit_widths))
    lines.extend(_build_case_assertions(case2, param_replace_fn2, symbol_bit_widths))
    if equality:
        lines.extend(
            _build_value_equality_assertions(
                value1_smt,
                value2_smt,
                return_size1,
                return_size2,
                symbol_bit_widths=symbol_bit_widths,
            )
        )
    lines.append("(check-sat)")
    return "\n".join(lines)


def _build_case_assertions(
    case,
    param_replace_fn,
    symbol_bit_widths: Optional[Dict[str, int]] = None,
) -> List[str]:
    lines: List[str] = []
    for cond_str in case.get_conditions_smt(param_replace_fn):
        normalized_cond_str = _normalize_condition_smt(cond_str, symbol_bit_widths or {})
        lines.append(f"(assert {normalized_cond_str})")
    return lines


def _normalize_condition_smt(cond_smt: str, symbol_bit_widths: Dict[str, int]) -> str:
    return _normalize_smt_expr_widths(cond_smt, symbol_bit_widths)


def _normalize_smt_expr_widths(expr_smt: str, symbol_bit_widths: Dict[str, int]) -> str:
    try:
        ast = _parse_smt_expr(expr_smt)
    except ValueError:
        return expr_smt

    try:
        normalized = _normalize_smt_ast(ast, symbol_bit_widths)
        return _smt_expr_to_string(normalized)
    except Exception:
        return expr_smt


def _parse_smt_expr(smt_expr: str):
    tokens = _tokenize_smt_expr(smt_expr)
    ast, index = _parse_smt_tokens(tokens, 0)
    if index != len(tokens):
        raise ValueError(f"unconsumed SMT tokens for expression: {smt_expr}")
    return ast


def _tokenize_smt_expr(smt_expr: str) -> List[str]:
    tokens: List[str] = []
    i = 0
    length = len(smt_expr)
    while i < length:
        ch = smt_expr[i]
        if ch.isspace():
            i += 1
            continue
        if ch in ("(", ")"):
            tokens.append(ch)
            i += 1
            continue
        start = i
        while i < length and not smt_expr[i].isspace() and smt_expr[i] not in ("(", ")"):
            i += 1
        tokens.append(smt_expr[start:i])
    return tokens


def _parse_smt_tokens(tokens: List[str], start: int):
    if start >= len(tokens):
        raise ValueError("unexpected end of SMT tokens")

    token = tokens[start]
    if token == "(":
        index = start + 1
        items: List = []
        while index < len(tokens):
            if tokens[index] == ")":
                return items, index + 1
            child, index = _parse_smt_tokens(tokens, index)
            items.append(child)
        if index >= len(tokens):
            raise ValueError("unexpected end of SMT tokens")
        raise ValueError("unterminated SMT expression")
    if token == ")":
        raise ValueError("unexpected close paren")
    return token, start + 1


def _normalize_smt_ast(ast, symbol_bit_widths: Dict[str, int]):
    if not isinstance(ast, list):
        return ast
    if not ast:
        return ast

    op = ast[0]
    args = [_normalize_smt_ast(arg, symbol_bit_widths) for arg in ast[1:]]
    if isinstance(op, str) and op in _SIGNED_COMPARISON_OPS | _UNSIGNED_COMPARISON_OPS:
        return _normalize_comparison_expression(op, args, symbol_bit_widths, signed=True if op in _SIGNED_COMPARISON_OPS else False)
    if isinstance(op, str) and op in {"=", "distinct"}:
        return _normalize_equality_expression(op, args, symbol_bit_widths)
    if isinstance(op, str) and op in _BITVECTOR_BINARY_OPS:
        return _normalize_bitvector_binary_expression(op, args, symbol_bit_widths)
    return [op, *args]


_SIGNED_COMPARISON_OPS = {
    "bvslt",
    "bvsle",
    "bvsgt",
    "bvsge",
}

_UNSIGNED_COMPARISON_OPS = {
    "bvult",
    "bvule",
    "bvugt",
    "bvuge",
}

_SIGNED_BITVECTOR_BINARY_OPS = {
    "bvsdiv",
    "bvsrem",
}

_BITVECTOR_BINARY_OPS = {
    "bvand",
    "bvor",
    "bvxor",
    "bvnand",
    "bvnor",
    "bvxnor",
    "bvadd",
    "bvsub",
    "bvmul",
    "bvudiv",
    "bvsdiv",
    "bvurem",
    "bvsrem",
    "bvshl",
    "bvlshr",
    "bvashr",
}


def _normalize_comparison_expression(op: str, args, symbol_bit_widths: Dict[str, int], *, signed: bool):
    if len(args) < 2:
        return [op, *args]

    widths = [_infer_smt_bit_width(arg, symbol_bit_widths) for arg in args[:2]]
    if any(width is None for width in widths[:2]):
        return [op, *args]
    target_width = max(widths[:2])
    if target_width <= 0 or widths[0] == target_width and widths[1] == target_width:
        return [op, *args]

    normalized_args = list(args)
    if widths[0] < target_width:
        normalized_args[0] = _extend_smt_node(args[0], target_width - widths[0], signed=signed)
    if widths[1] < target_width:
        normalized_args[1] = _extend_smt_node(args[1], target_width - widths[1], signed=signed)
    return [op, *normalized_args]


def _normalize_equality_expression(op: str, args, symbol_bit_widths: Dict[str, int]):
    if len(args) < 2:
        return [op, *args]

    widths = [_infer_smt_bit_width(arg, symbol_bit_widths) for arg in args]
    if any(width is None for width in widths):
        return [op, *args]
    target_width = max(widths)
    if target_width <= 0 or all(width == target_width for width in widths):
        return [op, *args]

    normalized_args = [
        _coerce_smt_node_width(arg, width, target_width, signed=False)
        for arg, width in zip(args, widths)
    ]
    return [op, *normalized_args]


def _normalize_bitvector_binary_expression(op: str, args, symbol_bit_widths: Dict[str, int]):
    if len(args) < 2:
        return [op, *args]
    left = args[0]
    current = args[1]
    rest = list(args[2:])
    normalized = _normalize_bitvector_pair(
        op,
        left,
        current,
        symbol_bit_widths,
    )
    result = [normalized[0], normalized[1]]
    for next_arg in rest:
        result_width = _infer_smt_bit_width([op, *result], symbol_bit_widths)
        next_width = _infer_smt_bit_width(next_arg, symbol_bit_widths)
        if result_width is None or next_width is None:
            result.append(next_arg)
            continue
        target_width = max(result_width, next_width)
        signed = op in _SIGNED_BITVECTOR_BINARY_OPS
        result_node = [op, *result]
        result_node = _coerce_smt_node_width(
            result_node,
            result_width,
            target_width,
            signed=signed,
        )
        next_arg = _coerce_smt_node_width(
            next_arg,
            next_width,
            target_width,
            signed=signed,
        )
        result = [result_node, next_arg]
    return [op, *result]


def _normalize_bitvector_pair(op: str, left, right, symbol_bit_widths: Dict[str, int]):
    left_width = _infer_smt_bit_width(left, symbol_bit_widths)
    right_width = _infer_smt_bit_width(right, symbol_bit_widths)
    if left_width is None or right_width is None:
        return left, right
    target_width = _preferred_bitvector_binary_width(left, right, left_width, right_width)
    if target_width <= 0 or left_width == right_width:
        return left, right
    signed = op in _SIGNED_BITVECTOR_BINARY_OPS
    return (
        _coerce_smt_node_width(left, left_width, target_width, signed=signed),
        _coerce_smt_node_width(right, right_width, target_width, signed=signed),
    )


def _coerce_smt_node_width(node, source_width: int, target_width: int, *, signed: bool):
    if source_width <= 0 or target_width <= 0 or source_width == target_width:
        return node
    constant = _resize_smt_bv_constant(node, target_width)
    if constant is not None:
        return constant
    if source_width < target_width:
        return _extend_smt_node(node, target_width - source_width, signed=signed)
    return [["_", "extract", str(target_width - 1), "0"], node]


def _preferred_bitvector_binary_width(left, right, left_width: int, right_width: int) -> int:
    if left_width == right_width:
        return left_width
    if _is_smt_bv_constant(left) and not _is_smt_bv_constant(right):
        return right_width
    if _is_smt_bv_constant(right) and not _is_smt_bv_constant(left):
        return left_width
    return max(left_width, right_width)


def _is_smt_bv_constant(node) -> bool:
    return (
        isinstance(node, list)
        and len(node) >= 3
        and node[0] == "_"
        and isinstance(node[1], str)
        and node[1].startswith("bv")
    )


def _extend_smt_node(node, extend_bits: int, *, signed: bool):
    if extend_bits <= 0:
        return node
    ext_op = "sign_extend" if signed else "zero_extend"
    return [["_", ext_op, str(extend_bits)], node]


def _resize_smt_bv_constant(node, target_width: int):
    if not isinstance(node, list) or len(node) < 3 or node[0] != "_":
        return None
    value_token = node[1]
    if not isinstance(value_token, str) or not value_token.startswith("bv"):
        return None
    value = _try_parse_int(value_token[2:])
    if value is None:
        return None
    return ["_", f"bv{int(value) % (1 << target_width)}", str(target_width)]


def _infer_smt_bit_width(node, symbol_bit_widths: Dict[str, int]):
    if isinstance(node, str):
        width = symbol_bit_widths.get(node)
        if width is not None:
            return width
        return None

    if not isinstance(node, list) or not node:
        return None

    op = node[0]
    if isinstance(op, list):
        return _infer_smt_indexed_operator_width(op, node[1:], symbol_bit_widths)

    if op == "_":
        if len(node) >= 3 and node[1] == "extract":
            hi = _try_parse_int(node[2])
            lo = _try_parse_int(node[3])
            if hi is not None and lo is not None:
                return hi - lo + 1
        if len(node) >= 4 and node[1] in {"zero_extend", "sign_extend"}:
            inner = _infer_smt_bit_width(node[3], symbol_bit_widths)
            extend_bits = _try_parse_int(node[2])
            if inner is not None and extend_bits is not None:
                return inner + extend_bits
        if len(node) >= 3 and node[1].startswith("bv"):
            width = _try_parse_int(node[2])
            if width is not None:
                return width
        return None
    if op in {"concat"} and len(node) >= 3:
        left = _infer_smt_bit_width(node[1], symbol_bit_widths)
        right = _infer_smt_bit_width(node[2], symbol_bit_widths)
        if left is not None and right is not None:
            return left + right
    if op in {"ite", "=", "distinct"}:
        if len(node) >= 3:
            first = _infer_smt_bit_width(node[1], symbol_bit_widths)
            second = _infer_smt_bit_width(node[2], symbol_bit_widths)
            if first is not None and second is not None:
                return max(first, second)
    if op in {"not", "bvnot", "bvneg"}:
        return _infer_smt_bit_width(node[1], symbol_bit_widths)
    if op in {"bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor", "bvadd", "bvsub", "bvmul", "bvudiv", "bvsdiv", "bvurem", "bvsrem", "bvshl", "bvlshr", "bvashr"}:
        if len(node) >= 3:
            left = _infer_smt_bit_width(node[1], symbol_bit_widths)
            right = _infer_smt_bit_width(node[2], symbol_bit_widths)
            if left is not None and right is not None:
                return max(left, right)
    return None


def _infer_smt_indexed_operator_width(
    op: List[Any],
    args: List,
    symbol_bit_widths: Dict[str, int],
) -> Optional[int]:
    if not op or op[0] != "_" or not isinstance(op[1], str):
        return None

    if op[1] == "extract" and len(op) >= 4:
        hi = _try_parse_int(op[2])
        lo = _try_parse_int(op[3])
        if hi is not None and lo is not None:
            return hi - lo + 1

    if op[1] in {"zero_extend", "sign_extend"} and len(op) >= 3 and args:
        inner = _infer_smt_bit_width(args[0], symbol_bit_widths)
        extend_bits = _try_parse_int(op[2])
        if inner is not None and extend_bits is not None:
            return inner + extend_bits

    if op[1].startswith("bv") and len(op) >= 3:
        width = _try_parse_int(op[2])
        if width is not None:
            return width
    return None


def _try_parse_int(text: str) -> Optional[int]:
    try:
        return int(text, 10)
    except (TypeError, ValueError):
        return None


def _smt_expr_to_string(node) -> str:
    if not isinstance(node, list):
        return str(node)
    if len(node) == 0:
        return "()"
    return f"({' '.join(_smt_expr_to_string(item) for item in node)})"


def _build_value_equality_assertions(
    value1_smt: str,
    value2_smt: str,
    return_size1: int,
    return_size2: int,
    *,
    symbol_bit_widths: Optional[Dict[str, int]] = None,
) -> List[str]:
    def _assert_equal(equality_smt: str) -> str:
        normalized = _normalize_smt_expr_widths(equality_smt, symbol_bit_widths or {})
        return f"(assert {normalized})"

    require_equal_return_bit_widths(
        return_size1,
        return_size2,
        context="counterexample validation value equality",
    )
    return [_assert_equal(f"(= {value1_smt} {value2_smt})")]


def _build_model_assertions(base_ctx: Dict[str, Any], counterexample_raw: Dict[str, Any]) -> List[str]:
    declarations = list(_iter_declared_symbols(base_ctx))
    assertions: List[str] = []
    for symbol_name, bit_width in declarations:
        if symbol_name not in counterexample_raw:
            continue
        raw_value = counterexample_raw[symbol_name]
        if not isinstance(raw_value, int):
            continue
        normalized = raw_value % (1 << bit_width)
        assertions.append(f"(assert (= {symbol_name} (_ bv{normalized} {bit_width})))")
    return assertions


def _iter_declared_symbols(base_ctx: Dict[str, Any]) -> Iterable[Tuple[str, int]]:
    for param in base_ctx.get("params1", []):
        yield param.smt_name, param.bit_width
    for param in base_ctx.get("params2", []):
        yield param.smt_name, param.bit_width
    for extra in base_ctx.get("extra_vars1", []):
        yield extra.smt_name, extra.bit_width
    for extra in base_ctx.get("extra_vars2", []):
        yield extra.smt_name, extra.bit_width
    for symbol_name, bit_width in base_ctx.get("runtime_unknown_declarations", []):
        yield symbol_name, bit_width


def _log_solver_errors(strategy, query: str, solver_results) -> None:
    if not solver_results:
        return

    for solver_result in solver_results:
        if solver_result.status != SolverStatus.ERROR:
            continue

        error_msg = solver_result.error_message or ""
        strategy._debug_print(f"  Solver error: {error_msg}")

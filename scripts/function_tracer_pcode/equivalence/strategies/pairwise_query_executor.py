# -*- coding: utf-8 -*-
"""Query execution helpers for PairwiseStrategy."""

from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

from ...smt import SolverStatus
from ..formula.returns import (
    expression_has_unresolved_value,
    should_sign_extend_value,
)
from .pairwise_models import QueryResult


def solve_query_internal(strategy, query: str, pair_id: str, stage: str = "full", use_hard_timeout: bool = False) -> QueryResult:
    """クエリを実行する"""
    old_timeout = strategy.solver_runner.timeout
    timeout = strategy.per_query_timeout_hard if use_hard_timeout else strategy.per_query_timeout
    strategy.solver_runner.timeout = timeout

    try:
        parallel_result = strategy.solver_runner.run_sequential(query)
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
    finally:
        strategy.solver_runner.timeout = old_timeout


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
            contextual_unresolved(case1, case2.conditions)
            or contextual_unresolved(case2, case1.conditions)
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

    if stage2_result.is_equivalent is None:
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
    query = _build_model_validation_query(
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        model_assertions,
        equality=True,
    )
    result = _run_validation_query(strategy, query, f"{pair_id}:equal")
    if result is None:
        return None
    return result


def _run_validation_query(strategy, query: str, label: str) -> Optional[bool]:
    old_timeout = strategy.solver_runner.timeout
    timeout = min(getattr(strategy, "per_query_timeout", 5), 5)
    strategy.solver_runner.timeout = timeout
    try:
        parallel_result = strategy.solver_runner.run_sequential(query)
    finally:
        strategy.solver_runner.timeout = old_timeout

    _log_solver_errors(strategy, query, parallel_result.results)
    if parallel_result.is_equivalent is True:
        return False
    if parallel_result.is_equivalent is False:
        return True

    strategy._debug_print(f"  Validation query {label} returned UNKNOWN/TIMEOUT")
    return None


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
        use_sign_extension=should_sign_extend_value(
            getattr(case1, "return_type", None),
            case1.value_expr,
            case1.conditions,
            return_type_obj=getattr(case1, "return_type_obj", None),
        ),
    )
    value2_smt = case2.get_value_smt(
        param_replace_fn2,
        target_bits=return_size2,
        use_sign_extension=should_sign_extend_value(
            getattr(case2, "return_type", None),
            case2.value_expr,
            case2.conditions,
            return_type_obj=getattr(case2, "return_type_obj", None),
        ),
    )

    lines: List[str] = [
        "(set-logic QF_BV)",
        "",
    ]
    lines.extend(base_ctx["header_lines"])
    lines.extend(model_assertions)
    lines.extend(_build_case_assertions(case1, param_replace_fn1))
    lines.extend(_build_case_assertions(case2, param_replace_fn2))
    if equality:
        lines.extend(_build_value_equality_assertions(value1_smt, value2_smt, return_size1, return_size2))
    lines.append("(check-sat)")
    return "\n".join(lines)


def _build_case_assertions(case, param_replace_fn) -> List[str]:
    lines: List[str] = []
    for cond_str in case.get_conditions_smt(param_replace_fn):
        lines.append(f"(assert {cond_str})")
    return lines


def _build_value_equality_assertions(
    value1_smt: str,
    value2_smt: str,
    return_size1: int,
    return_size2: int,
) -> List[str]:
    if return_size1 == return_size2:
        return [f"(assert (= {value1_smt} {value2_smt}))"]

    overlap = min(return_size1, return_size2)
    if return_size1 < return_size2:
        return [
            f"(assert (= {value1_smt} ((_ extract {overlap - 1} 0) {value2_smt})))"
        ]
    return [
        f"(assert (= ((_ extract {overlap - 1} 0) {value1_smt}) {value2_smt}))"
    ]


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


def _log_solver_errors(strategy, query: str, solver_results) -> None:
    if not solver_results:
        return

    for solver_result in solver_results:
        if solver_result.status != SolverStatus.ERROR:
            continue

        error_msg = solver_result.error_message or ""
        strategy._debug_print(f"  Solver error: {error_msg}")
        if "unknown constant" not in error_msg:
            continue

        import re

        match = re.search(r"unknown constant (\w+)", error_msg)
        if not match:
            continue

        unknown_sym = match.group(1)
        strategy._debug_print(f"  !!! Unknown symbol detected: '{unknown_sym}'")
        strategy._debug_print("  This symbol should have been replaced during symbol mapping.")
        if not strategy.debug:
            continue

        lines = query.split("\n")
        for index, line in enumerate(lines):
            if unknown_sym not in line:
                continue
            start = max(0, index - 2)
            end = min(len(lines), index + 3)
            strategy._debug_print(f"  Context (lines {start}-{end}):")
            for context_index in range(start, end):
                marker = " >>> " if context_index == index else "     "
                strategy._debug_print(f"{marker}{lines[context_index]}")

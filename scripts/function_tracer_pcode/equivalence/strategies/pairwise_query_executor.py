# -*- coding: utf-8 -*-
"""Query execution helpers for PairwiseStrategy."""

from typing import Any, Dict

from ...smt import SolverStatus
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

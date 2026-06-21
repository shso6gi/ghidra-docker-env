# -*- coding: utf-8 -*-
"""Query execution helpers for PairwiseStrategy."""
import inspect
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

from ...smt import SolverStatus
from ..unknown_reason import UnknownRecoveryActionStatus
from ..formula.returns import (
    ReturnWidthMismatchError,
    expression_has_unresolved_value,
    require_equal_return_bit_widths,
)
from .pairwise_models import QueryResult


def _is_void_return_placeholder(expr: Any) -> bool:
    expr_type = getattr(getattr(expr, "expr_type", None), "name", None)
    return expr_type == "UNKNOWN" and str(getattr(expr, "name", "") or "").lower() == "void"


def _cases_have_void_return_placeholders(case1, case2) -> bool:
    return (
        _is_void_return_placeholder(getattr(case1, "value_expr", None))
        and _is_void_return_placeholder(getattr(case2, "value_expr", None))
    )


def _record_return_width_block(strategy, exc: ReturnWidthMismatchError) -> None:
    stats = getattr(strategy, "_active_normalization_stats", None)
    if stats is None:
        return
    reason_id = getattr(exc, "reason_id", "return_width_bridge_missing")
    stats[reason_id] = int(stats.get(reason_id, 0) or 0) + 1


def _return_width_abi_guard_relation_lines(base_ctx: Dict[str, Any]) -> List[str]:
    """Build object-derived ABI/semantic parameter relations for guard reachability."""

    params1 = {
        getattr(param, "index", None): param
        for param in base_ctx.get("params1", ()) or ()
        if getattr(param, "index", None) is not None
    }
    params2 = {
        getattr(param, "index", None): param
        for param in base_ctx.get("params2", ()) or ()
        if getattr(param, "index", None) is not None
    }

    lines: List[str] = []
    for index in sorted(set(params1) & set(params2)):
        param1 = params1[index]
        param2 = params2[index]
        try:
            width1 = int(getattr(param1, "bit_width", 0) or 0)
            width2 = int(getattr(param2, "bit_width", 0) or 0)
        except (TypeError, ValueError):
            continue
        if width1 <= 0 or width2 <= 0 or width1 == width2:
            continue

        if width1 > width2:
            wide = param1
            narrow = param2
            wide_bits = width1
            narrow_bits = width2
        else:
            wide = param2
            narrow = param1
            wide_bits = width2
            narrow_bits = width1

        signedness = getattr(wide, "semantic_signedness", None)
        semantic_bits = getattr(wide, "semantic_narrow_bits", None)
        try:
            semantic_bits = int(semantic_bits) if semantic_bits is not None else None
        except (TypeError, ValueError):
            semantic_bits = None
        if signedness not in {"signed", "unsigned"} or semantic_bits != narrow_bits:
            continue

        extend_bits = wide_bits - narrow_bits
        if extend_bits <= 0:
            continue
        ext_op = "sign_extend" if signedness == "signed" else "zero_extend"
        lines.extend(
            [
                (
                    f"; param[{index}] return-width guard ABI relation: "
                    f"{getattr(wide, 'smt_name', '<wide>')} is {signedness} "
                    f"{narrow_bits}-bit semantic extension of "
                    f"{getattr(narrow, 'smt_name', '<narrow>')}"
                ),
                (
                    f"(assert (= {wide.smt_name} ((_ {ext_op} {extend_bits}) "
                    f"{narrow.smt_name})))"
                ),
            ]
        )

    if not lines:
        return []
    return [
        "",
        "; " + "-" * 40,
        "; Return-width guard ABI relations",
        "; Object-derived semantic-width relations used only for guard reachability",
        "; " + "-" * 40,
        *lines,
        "",
    ]


def _build_return_width_abi_guard_query(
    cond_query: str,
    base_ctx: Dict[str, Any],
) -> Optional[str]:
    relation_lines = _return_width_abi_guard_relation_lines(base_ctx)
    if not relation_lines:
        return None

    check_sat = "(check-sat)"
    stripped = cond_query.rstrip()
    if stripped.endswith(check_sat):
        prefix = stripped[: -len(check_sat)].rstrip()
        return "\n".join([prefix, *relation_lines, check_sat])
    return "\n".join([stripped, *relation_lines, check_sat])


def _fallback_stable_key(value: Any):
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            return stable_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
    return None


def _fallback_return_width_bridge_object_target_key(
    base_ctx: Dict[str, Any],
    case1,
    case2,
    pair_id: str,
    exc: ReturnWidthMismatchError,
) -> Tuple[Any, ...]:
    def _width(value: Any, fallback: Any) -> Optional[int]:
        for candidate in (value, fallback):
            if candidate is None:
                continue
            try:
                bits = int(candidate)
            except (TypeError, ValueError):
                continue
            if bits > 0:
                return bits
        return None

    return_size1 = _width(getattr(exc, "return_size1", None), base_ctx.get("return_size1"))
    return_size2 = _width(getattr(exc, "return_size2", None), base_ctx.get("return_size2"))
    return (
        "return_width_bridge",
        ("pair", pair_id),
        ("return_widths", return_size1, return_size2),
        _fallback_return_width_side_object_key("left", case1, return_size1),
        _fallback_return_width_side_object_key("right", case2, return_size2),
    )


def _fallback_return_width_side_object_key(
    side_label: str,
    case,
    return_size: Optional[int],
) -> Tuple[Any, ...]:
    return_info = getattr(case, "return_info", None)
    value_expr = getattr(case, "value_expr", None)
    try:
        case_index = int(getattr(case, "index", -1))
    except (TypeError, ValueError):
        case_index = None
    source_indices = []
    for source_index in getattr(case, "source_indices", ()) or ():
        try:
            source_indices.append(int(source_index))
        except (TypeError, ValueError):
            continue
    return (
        "return_width_side",
        side_label,
        None,
        ("return_size", return_size),
        None,
        (
            "return_case_partition_member",
            case_index,
            tuple(source_indices),
            (
                "return_case",
                case_index,
                getattr(return_info, "address", None),
                _fallback_stable_key(getattr(return_info, "pcode_op_ref", None)),
                getattr(return_info, "pcode_identity", None),
                getattr(return_info, "pcode_order", None),
            ),
            (
                "comparison_surface",
                getattr(getattr(case, "comparison_surface", None), "kind", None),
                getattr(getattr(case, "comparison_surface", None), "explicit_bit_width", None),
                getattr(getattr(case, "comparison_surface", None), "use_sign_extension", None),
            ),
            (
                "value",
                getattr(getattr(value_expr, "expr_type", None), "name", None),
                getattr(value_expr, "operator", None),
                getattr(value_expr, "size", None),
                _fallback_stable_key(getattr(value_expr, "runtime_ref", None)),
            ),
        ),
    )


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
        solver_results=parallel_result,
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
        result.blocking_reason = "unresolved_value_expression"
        result.blocking_detail = "value expression contains UNKNOWN or unsupported SMT operation"
        return result

    if _cases_have_void_return_placeholders(case1, case2):
        result = QueryResult(is_equivalent=True)
        result.last_query = cond_query
        result.pair_stage = "void-return"
        return result

    try:
        require_equal_return_bit_widths(
            base_ctx.get("return_size1", 32),
            base_ctx.get("return_size2", 32),
            context="pairwise value inequality",
        )
    except ReturnWidthMismatchError as exc:
        abi_guard_query = _build_return_width_abi_guard_query(cond_query, base_ctx)
        if abi_guard_query is not None:
            abi_guard_result = strategy._solve_query_internal(
                abi_guard_query,
                pair_id,
                stage="conds-only-return-width-abi-guard",
                use_hard_timeout=False,
            )
            if abi_guard_result.is_equivalent is True:
                abi_guard_result.last_query = abi_guard_query
                abi_guard_result.pair_stage = "conds-only-return-width-abi-guard"
                return abi_guard_result

        strategy._debug_print(f"  Pair {pair_id} with-ineq skipped: {exc}")
        result = QueryResult(is_equivalent=None)
        result.last_query = cond_query
        result.pair_stage = "return-width-mismatch"
        result.blocking_reason = getattr(exc, "reason_id", "return_width_bridge_missing")
        result.blocking_detail = str(exc)
        target_key_builder = getattr(strategy, "_return_width_bridge_object_target_key", None)
        if callable(target_key_builder):
            result.object_target_key = target_key_builder(
                base_ctx=base_ctx,
                case1=case1,
                case2=case2,
                pair_id=pair_id,
                mismatch=exc,
            )
        if result.object_target_key is None:
            result.object_target_key = _fallback_return_width_bridge_object_target_key(
                base_ctx,
                case1,
                case2,
                pair_id,
                exc,
            )
        result.action_status = UnknownRecoveryActionStatus.PLANNED
        bridge_solver = getattr(strategy, "_solve_return_width_bridge_with_completed_proof", None)
        if callable(bridge_solver):
            bridged_result = bridge_solver(
                base_ctx,
                case1,
                case2,
                param_replace_fn1,
                param_replace_fn2,
                pair_id,
                object_target_key=result.object_target_key,
                blocking_detail=result.blocking_detail,
            )
            if bridged_result is not None:
                return bridged_result
        if getattr(strategy, "_active_normalization_stats", None) is not None:
            strategy._active_normalization_stats["unknown_results"] += 1
        _record_return_width_block(strategy, exc)
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
        if getattr(rewrite_result, "blocking_reason", None):
            stage2_result.blocking_reason = rewrite_result.blocking_reason
            stage2_result.blocking_detail = rewrite_result.blocking_detail
            stage2_result.pair_stage = rewrite_result.pair_stage or stage2_result.pair_stage
            stage2_result.evidence_kind = getattr(rewrite_result, "evidence_kind", None)
            stage2_result.object_target_key = getattr(rewrite_result, "object_target_key", None)
            stage2_result.proof_obligation_id = getattr(rewrite_result, "proof_obligation_id", None)
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
        if getattr(norm_result, "blocking_reason", None):
            stage2_result.blocking_reason = norm_result.blocking_reason
            stage2_result.blocking_detail = norm_result.blocking_detail
            stage2_result.pair_stage = norm_result.pair_stage or stage2_result.pair_stage

    if stage2_result.is_equivalent is None and not getattr(stage2_result, "blocking_reason", None):
        stage2_result.blocking_reason = "solver_unknown_timeout"
        stage2_result.blocking_detail = "pairwise solver query timed out or returned unknown"
        stage2_result.evidence_kind = "query_hash"
        target_builder = getattr(strategy, "_solver_timeout_object_target_key", None)
        if callable(target_builder):
            stage2_result.object_target_key = target_builder(
                analysis1=base_ctx.get("analysis1"),
                analysis2=base_ctx.get("analysis2"),
                stage=stage2_result.pair_stage or "with-ineq",
                query=stage2_result.last_query,
                timeout_seconds=getattr(strategy, "per_query_timeout_hard", None),
                pair_id=pair_id,
                parallel_result=getattr(stage2_result, "solver_results", None),
            )

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


def count_counterexample_model_assertions(
    base_ctx: Dict[str, Any],
    counterexample_raw: Optional[Dict[str, Any]],
) -> int:
    if not counterexample_raw:
        return 0
    return len(_build_model_assertions(base_ctx, counterexample_raw))


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
        strategy._debug_print(
            "  Counterexample rejected: model contains no replay-target declarations"
        )
        return False

    feasible_cases1 = _collect_feasible_cases_under_model(
        strategy,
        base_ctx,
        cases1,
        param_replace_fn1,
        model_assertions,
        side_label="function1",
    )
    if feasible_cases1 is None:
        return False
    feasible_cases2 = _collect_feasible_cases_under_model(
        strategy,
        base_ctx,
        cases2,
        param_replace_fn2,
        model_assertions,
        side_label="function2",
    )
    if feasible_cases2 is None:
        return False

    side1_consistent = _feasible_case_values_are_consistent_under_model(
        strategy,
        base_ctx,
        feasible_cases1,
        param_replace_fn1,
        model_assertions,
        return_size=base_ctx.get("return_size1", 32),
        side_label="function1",
    )
    if side1_consistent is None:
        return False
    if not side1_consistent:
        return False
    side2_consistent = _feasible_case_values_are_consistent_under_model(
        strategy,
        base_ctx,
        feasible_cases2,
        param_replace_fn2,
        model_assertions,
        return_size=base_ctx.get("return_size2", 32),
        side_label="function2",
    )
    if side2_consistent is None:
        return False
    if not side2_consistent:
        return False

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


def _collect_feasible_cases_under_model(
    strategy,
    base_ctx: Dict[str, Any],
    cases: Sequence,
    param_replace_fn,
    model_assertions: Sequence[str],
    side_label: str,
) -> Optional[List[Tuple[int, Any]]]:
    feasible_cases: List[Tuple[int, Any]] = []
    for index, case in enumerate(cases):
        feasible = _check_case_feasibility_under_model(
            strategy,
            base_ctx,
            case,
            param_replace_fn,
            model_assertions,
            case_id=f"{side_label}[{index}]",
        )
        if feasible is None:
            strategy._debug_print(
                f"  Counterexample validation for {side_label} case {index} was inconclusive"
            )
            return None
        if feasible:
            feasible_cases.append((index, case))
    return feasible_cases


def _feasible_case_values_are_consistent_under_model(
    strategy,
    base_ctx: Dict[str, Any],
    feasible_cases: Sequence[Tuple[int, Any]],
    param_replace_fn,
    model_assertions: Sequence[str],
    return_size: int,
    side_label: str,
) -> Optional[bool]:
    if len(feasible_cases) < 2:
        return True
    for left_pos, (left_index, left_case) in enumerate(feasible_cases):
        for right_index, right_case in feasible_cases[left_pos + 1 :]:
            equal = _check_same_side_case_equality_under_model(
                strategy,
                base_ctx,
                left_case,
                right_case,
                param_replace_fn,
                model_assertions,
                return_size=return_size,
                pair_id=f"{side_label}[{left_index},{right_index}]",
            )
            if equal is None:
                strategy._debug_print(
                    "  Counterexample validation for "
                    f"{side_label} cases {left_index} and {right_index} was inconclusive"
                )
                return None
            if not equal:
                strategy._debug_print(
                    "  Counterexample is ambiguous: model matches multiple "
                    f"{side_label} return cases with different values "
                    f"({left_index}, {right_index})"
                )
                return False
    return True


def _check_case_feasibility_under_model(
    strategy,
    base_ctx: Dict[str, Any],
    case,
    param_replace_fn,
    model_assertions: Sequence[str],
    case_id: str,
) -> Optional[bool]:
    query = _build_single_case_model_validation_query(
        base_ctx,
        case,
        param_replace_fn,
        model_assertions,
    )
    result = _run_validation_query(strategy, query, f"{case_id}:feasible")
    if result is None:
        return None
    return result


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


def _check_same_side_case_equality_under_model(
    strategy,
    base_ctx: Dict[str, Any],
    case1,
    case2,
    param_replace_fn,
    model_assertions: Sequence[str],
    return_size: int,
    pair_id: str,
) -> Optional[bool]:
    try:
        query = _build_same_side_case_equality_validation_query(
            base_ctx,
            case1,
            case2,
            param_replace_fn,
            model_assertions,
            return_size=return_size,
        )
    except ReturnWidthMismatchError as exc:
        strategy._debug_print(f"  Same-side equality re-check for {pair_id} blocked: {exc}")
        return None
    result = _run_validation_query(strategy, query, f"{pair_id}:same-side-equal")
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


def _build_single_case_model_validation_query(
    base_ctx: Dict[str, Any],
    case,
    param_replace_fn,
    model_assertions: Sequence[str],
) -> str:
    lines: List[str] = [
        f"(set-logic {base_ctx.get('smt_logic', 'QF_BV')})",
        "",
    ]
    lines.extend(base_ctx["header_lines"])
    lines.extend(model_assertions)
    lines.extend(_build_case_assertions(case, param_replace_fn))
    lines.append("(check-sat)")
    return "\n".join(lines)


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


def _build_same_side_case_equality_validation_query(
    base_ctx: Dict[str, Any],
    case1,
    case2,
    param_replace_fn,
    model_assertions: Sequence[str],
    return_size: int,
) -> str:
    value1_smt = case1.get_value_smt(
        param_replace_fn,
        target_bits=return_size,
        use_sign_extension=case1.should_sign_extend_value(),
    )
    value2_smt = case2.get_value_smt(
        param_replace_fn,
        target_bits=return_size,
        use_sign_extension=case2.should_sign_extend_value(),
    )

    lines: List[str] = [
        f"(set-logic {base_ctx.get('smt_logic', 'QF_BV')})",
        "",
    ]
    lines.extend(base_ctx["header_lines"])
    lines.extend(model_assertions)
    lines.extend(_build_case_assertions(case1, param_replace_fn))
    lines.extend(_build_case_assertions(case2, param_replace_fn))
    lines.extend(
        _build_value_equality_assertions(
            value1_smt,
            value2_smt,
            return_size,
            return_size,
        )
    )
    lines.append("(check-sat)")
    return "\n".join(lines)


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
        f"(set-logic {base_ctx.get('smt_logic', 'QF_BV')})",
        "",
    ]
    lines.extend(base_ctx["header_lines"])
    lines.extend(model_assertions)
    lines.extend(_build_case_assertions(case1, param_replace_fn1))
    lines.extend(_build_case_assertions(case2, param_replace_fn2))
    if equality:
        lines.extend(
            _build_value_equality_assertions(
                value1_smt,
                value2_smt,
                return_size1,
                return_size2,
            )
        )
    lines.append("(check-sat)")
    return "\n".join(lines)


def _build_case_assertions(
    case,
    param_replace_fn,
) -> List[str]:
    return [f"(assert {cond_str})" for cond_str in case.get_conditions_smt(param_replace_fn)]


def _build_value_equality_assertions(
    value1_smt: str,
    value2_smt: str,
    return_size1: int,
    return_size2: int,
) -> List[str]:
    require_equal_return_bit_widths(
        return_size1,
        return_size2,
        context="counterexample validation value equality",
    )
    return [f"(assert (= {value1_smt} {value2_smt}))"]


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

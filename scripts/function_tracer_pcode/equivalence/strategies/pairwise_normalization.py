# -*- coding: utf-8 -*-
"""Normalization fallback helpers for PairwiseStrategy."""

from .pairwise_models import QueryResult


def try_normalization_equivalence(
    strategy,
    base_ctx,
    case1,
    case2,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str,
    normalize_expression_fn,
    normalization_context_cls,
    sign_facts_cls,
    extract_min_excluded_params_fn,
    extract_upper_bound_facts_fn,
    extract_sign_facts_fn,
    contains_udiv_fn,
    normalize_udiv_with_guard_fn,
    are_structurally_equivalent_fn,
    get_structural_summary_fn,
    normalization_rule_application_cls,
):
    """正規化して値式を SMT で比較する"""
    normalization_stats = getattr(strategy, "_active_normalization_stats", None)
    value1_orig = case1.value_expr
    value2_orig = case2.value_expr

    header_lines = base_ctx.get("header_lines", [])
    min_excluded_smt = extract_min_excluded_params_fn(header_lines, debug=strategy.debug)
    upper_bounds_smt = extract_upper_bound_facts_fn(header_lines, debug=strategy.debug)
    if strategy.debug and min_excluded_smt:
        strategy._debug_print(f"MIN-excluded SMT vars: {min_excluded_smt}")
    if strategy.debug and upper_bounds_smt:
        strategy._debug_print(f"Upper-bound SMT vars: {upper_bounds_smt}")

    smt_to_original = {}
    for param_info in base_ctx.get("params1", []):
        smt_to_original[param_info.smt_name] = param_info.original_name
    for param_info in base_ctx.get("params2", []):
        smt_to_original[param_info.smt_name] = param_info.original_name
    for extra_var in base_ctx.get("extra_vars1", []):
        smt_to_original[extra_var.smt_name] = extra_var.original_name
    for extra_var in base_ctx.get("extra_vars2", []):
        smt_to_original[extra_var.smt_name] = extra_var.original_name

    min_excluded_original = set()
    for smt_name in min_excluded_smt:
        if smt_name in smt_to_original:
            min_excluded_original.add(smt_to_original[smt_name])

    upper_bounds_original = _translate_upper_bounds(upper_bounds_smt, smt_to_original)

    if strategy.debug and min_excluded_original:
        strategy._debug_print(f"MIN-excluded original vars: {min_excluded_original}")
    if strategy.debug and upper_bounds_original:
        strategy._debug_print(f"Upper-bound original vars: {upper_bounds_original}")

    if strategy.debug:
        strategy._debug_print("  Extracting sign facts from conditions...")

    facts1 = extract_sign_facts_fn(case1.conditions, debug=strategy.debug)
    facts2 = extract_sign_facts_fn(case2.conditions, debug=strategy.debug)
    combined_facts = sign_facts_cls()
    combined_facts.merge(facts1)
    combined_facts.merge(facts2)

    nonneg_original = _translate_fact_names(combined_facts.nonneg_vars, smt_to_original)
    pos_original = _translate_fact_names(combined_facts.pos_vars, smt_to_original)
    neg_original = _translate_fact_names(combined_facts.neg_vars, smt_to_original)
    nonzero_original = _translate_fact_names(combined_facts.nonzero_vars, smt_to_original)
    nonneg_exprs = set(combined_facts.nonneg_exprs)
    pos_exprs = set(combined_facts.pos_exprs)
    neg_exprs = set(combined_facts.neg_exprs)
    nonzero_exprs = set(combined_facts.nonzero_exprs)
    upper_bounds_original = _merge_upper_bounds(
        upper_bounds_original,
        _translate_upper_bounds(combined_facts.upper_bounds, smt_to_original),
    )

    if strategy.debug:
        if nonneg_original:
            strategy._debug_print(f"Sign facts: nonneg={nonneg_original}")
        if pos_original:
            strategy._debug_print(f"Sign facts: pos={pos_original}")
        if neg_original:
            strategy._debug_print(f"Sign facts: neg={neg_original}")
        if nonzero_original:
            strategy._debug_print(f"Sign facts: nonzero={nonzero_original}")
        if nonneg_exprs:
            strategy._debug_print(f"Expr facts: nonneg={sorted(nonneg_exprs)}")
        if neg_exprs:
            strategy._debug_print(f"Expr facts: neg={sorted(neg_exprs)}")
        if upper_bounds_original:
            strategy._debug_print(f"Range facts: upper_bounds={upper_bounds_original}")

    norm_context = normalization_context_cls(
        debug=strategy.debug,
        min_excluded_params=min_excluded_original,
        nonneg_vars=nonneg_original,
        pos_vars=pos_original,
        neg_vars=neg_original,
        nonzero_vars=nonzero_original,
        nonneg_exprs=nonneg_exprs,
        pos_exprs=pos_exprs,
        neg_exprs=neg_exprs,
        nonzero_exprs=nonzero_exprs,
        upper_bounds=upper_bounds_original,
        allow_unsafe=False,
    )

    if strategy.debug:
        strategy._debug_print("  Phase 1: Facts-based normalization...")

    value1_norm = normalize_expression_fn(value1_orig, norm_context)
    value2_norm = normalize_expression_fn(value2_orig, norm_context)

    case1_conds_smt = case1.get_conditions_smt(param_replace_fn1)
    case2_conds_smt = case2.get_conditions_smt(param_replace_fn2)

    value1_norm = _normalize_udiv_if_present(
        strategy,
        value1_norm,
        "Value1",
        base_ctx,
        case1_conds_smt,
        case2_conds_smt,
        norm_context,
        param_replace_fn1,
        contains_udiv_fn,
        normalize_udiv_with_guard_fn,
        normalize_expression_fn,
    )
    value2_norm = _normalize_udiv_if_present(
        strategy,
        value2_norm,
        "Value2",
        base_ctx,
        case1_conds_smt,
        case2_conds_smt,
        norm_context,
        param_replace_fn2,
        contains_udiv_fn,
        normalize_udiv_with_guard_fn,
        normalize_expression_fn,
    )

    def _render_with_replacer(expr, param_replace_fn):
        if param_replace_fn is None:
            return expr.to_smt()
        try:
            return param_replace_fn(expr)
        except TypeError:
            return param_replace_fn(expr.to_smt())

    value1_smt_orig = _render_with_replacer(value1_orig, param_replace_fn1)
    value2_smt_orig = _render_with_replacer(value2_orig, param_replace_fn2)
    value1_smt_norm = _render_with_replacer(value1_norm, param_replace_fn1)
    value2_smt_norm = _render_with_replacer(value2_norm, param_replace_fn2)

    strategy._debug_print(f"  Pair {pair_id} normalization attempt:")
    strategy._debug_print(f"    Original 1: {value1_smt_orig[:200]}")
    strategy._debug_print(f"    Original 2: {value2_smt_orig[:200]}")

    changed1 = value1_smt_orig != value1_smt_norm
    changed2 = value2_smt_orig != value2_smt_norm
    strategy._debug_print(
        f"    Normalized 1: {value1_smt_norm[:200] if changed1 else '(no change)'}"
    )
    strategy._debug_print(
        f"    Normalized 2: {value2_smt_norm[:200] if changed2 else '(no change)'}"
    )

    if norm_context.applied_rules:
        strategy._debug_print("    Applied rules:")
        for rule in norm_context.applied_rules:
            strategy._debug_print(f"      - {rule.rule_name}: {rule.reason}")
    else:
        strategy._debug_print("    No normalization rules applied")

    normalization_rules = []
    for rule_app in norm_context.applied_rules:
        normalization_rules.append(
            normalization_rule_application_cls(
                rule_name=rule_app.rule_name,
                reason=rule_app.reason,
                applied_to=f"pair_{pair_id}",
                before=rule_app.before_expr,
                after=rule_app.after_expr,
            )
        )

    if not changed1 and not changed2:
        strategy._debug_print("    No normalization applied -> remain UNKNOWN")
        if normalization_stats is not None:
            normalization_stats["no_change_pairs"] += 1
            normalization_stats["unknown_results"] += 1
        result = QueryResult(is_equivalent=None)
        result.normalization_rules = normalization_rules
        return result

    if normalization_stats is not None:
        normalization_stats["changed_pairs"] += 1

    is_struct_eq, struct_reason = are_structurally_equivalent_fn(
        value1_norm,
        value2_norm,
        debug=strategy.debug,
    )
    if is_struct_eq:
        strategy._debug_print("    STRUCTURAL MATCH DETECTED, SMT CONFIRMATION REQUIRED")
        strategy._debug_print(f"      Reason: {struct_reason}")
        strategy._debug_print(
            f"      Structure: {get_structural_summary_fn(value1_norm, max_depth=5)}"
        )
    elif strategy.debug:
        strategy._debug_print("    Structural match not detected:")
        strategy._debug_print(
            f"      Structure1: {get_structural_summary_fn(value1_norm, max_depth=5)}"
        )
        strategy._debug_print(
            f"      Structure2: {get_structural_summary_fn(value2_norm, max_depth=5)}"
        )
        strategy._debug_print(f"      Reason: {struct_reason}")

    strategy._debug_print("    Proceeding to SMT solver (norm-ineq)...")
    norm_query = strategy._build_normalized_inequality_query(
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        value1_norm,
        value2_norm,
        value1_smt_norm,
        value2_smt_norm,
        pair_id,
    )
    norm_result = strategy._solve_query_internal(
        norm_query,
        pair_id,
        stage="norm-ineq",
        use_hard_timeout=False,
    )
    norm_result.normalization_rules = normalization_rules

    if norm_result.is_equivalent is True:
        if normalization_stats is not None:
            normalization_stats["unsat_results"] += 1
        strategy._debug_print("    Normalized inequality: UNSAT -> values are equivalent")
        if is_struct_eq:
            strategy._debug_print("    (Structural match was confirmed by SMT)")
        strategy._debug_print(
            f"  Pair {pair_id} normalization: values became equivalent -> UNSAT"
        )
        return norm_result

    if norm_result.is_equivalent is False:
        if normalization_stats is not None:
            normalization_stats["sat_results"] += 1
        strategy._debug_print("    Normalized inequality: SAT -> genuine counterexample found")
        if is_struct_eq:
            strategy._debug_print(
                "    WARNING: Structural match detected but SMT found counterexample!"
            )
            strategy._debug_print(
                "    This indicates the structural check may have false positives."
            )
        strategy._debug_print(
            f"  Pair {pair_id} normalization: found counterexample -> NOT EQUIVALENT"
        )
        return norm_result

    strategy._debug_print("    Normalized inequality: UNKNOWN -> remain UNKNOWN")
    if normalization_stats is not None:
        normalization_stats["unknown_results"] += 1
    if is_struct_eq:
        strategy._debug_print("    (Structural match detected but SMT solver timed out)")
    return norm_result


def _translate_fact_names(var_names, smt_to_original):
    translated = set()
    for var_name in var_names:
        translated.add(smt_to_original.get(var_name, var_name))
    return translated


def _translate_upper_bounds(upper_bounds, smt_to_original):
    translated = {}
    for var_name, bound in upper_bounds.items():
        original_name = smt_to_original.get(var_name, var_name)
        current = translated.get(original_name)
        if current is None or bound < current:
            translated[original_name] = bound
    return translated


def _merge_upper_bounds(left, right):
    merged = dict(left)
    for var_name, bound in right.items():
        current = merged.get(var_name)
        if current is None or bound < current:
            merged[var_name] = bound
    return merged


def _normalize_udiv_if_present(
    strategy,
    value_norm,
    label: str,
    base_ctx,
    case1_conds_smt,
    case2_conds_smt,
    norm_context,
    param_replace_fn,
    contains_udiv_fn,
    normalize_udiv_with_guard_fn,
    normalize_expression_fn,
):
    if not contains_udiv_fn(value_norm):
        return value_norm

    if strategy.debug:
        strategy._debug_print(
            f"  {label} contains UDIV after Phase 1, trying Phase 2 (SMT guard proof)..."
        )

    value_norm_phase2 = normalize_udiv_with_guard_fn(
        value_norm,
        base_ctx,
        case1_conds_smt,
        case2_conds_smt,
        strategy.solver_runner,
        norm_context,
        param_replace_fn,
    )
    if value_norm_phase2 is value_norm:
        return value_norm

    if strategy.debug:
        strategy._debug_print(f"  {label}: Phase 2 applied transformations")
        strategy._debug_print(f"  {label}: Re-applying Phase 1 after Phase 2...")
    return normalize_expression_fn(value_norm_phase2, norm_context)

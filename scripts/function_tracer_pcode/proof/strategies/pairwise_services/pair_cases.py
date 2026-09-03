"""Pair case collection: parameter objects, unknown expression classification and case assembly."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.proof.strategies.pairwise_services._shared import (
    Condition,
    ConditionSMTOracle,
    ConditionSimplifier,
    Expression,
    ExpressionSafetyChecker,
    ExpressionType,
    FunctionReturnAnalysis,
    NormalizationContext,
    NormalizationRuleApplication,
    ParallelResult,
    QueryResult,
    ReturnCase,
    SignFacts,
    SolverResult,
    SolverStatus,
    StrategyResult,
    UnknownReasonId,
    are_structurally_equivalent,
    build_canonical_return_observation_query,
    expression_smt_bit_width,
    extract_return_cases,
    extract_upper_bound_facts,
    get_structural_summary,
    make_unknown_reason,
    normalize_udiv_with_guard,
    try_normalization_equivalence,
)
from scripts.function_tracer_pcode.proof.strategies.pairwise_services._api import (
    contains_udiv,
    extract_min_excluded_params,
    extract_sign_facts,
    normalize_expression,
)


def _impl__conditions_with_object_identity_parameter_symbols(
    self,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]] = (),
) -> List[Condition]:
    symbol_by_identity: Dict[tuple, str] = {}

    def parameter_symbol(expr: Expression) -> str:
        key = self._parameter_object_identity_key(expr, parameters)
        if key is None:
            key = self._opaque_parameter_object_identity_key(expr)
        symbol = symbol_by_identity.get(key)
        if symbol is None:
            symbol = f"__phase3_param_{len(symbol_by_identity)}"
            symbol_by_identity[key] = symbol
        return symbol

    def clone_value(value):
        if isinstance(value, Expression):
            return clone_expr(value)
        if isinstance(value, Condition):
            return Condition(clone_expr(value.expression), value.negated)
        if isinstance(value, tuple):
            return tuple(clone_value(item) for item in value)
        if isinstance(value, list):
            return [clone_value(item) for item in value]
        return value

    def clone_expr(expr: Expression) -> Expression:
        expr_type = getattr(expr, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_type is not None and expr_kind is not None and expr_type == expr_kind.PARAMETER:
            return expr.clone_with(name=parameter_symbol(expr), runtime_ref=None)
        cloned_operands = [clone_expr(operand) for operand in (getattr(expr, "operands", None) or [])]
        cloned_value = clone_value(getattr(expr, "value", None))
        return expr.clone_with(operands=cloned_operands, value=cloned_value)

    return [
        Condition(clone_expr(condition.expression), bool(getattr(condition, "negated", False)))
        for condition in conditions or []
        if condition is not None and getattr(condition, "expression", None) is not None
    ]


def _impl__parameter_object_identity_key(
    self,
    expr: Expression,
    parameters: Sequence[Dict[str, Any]] = (),
) -> Optional[tuple]:
    size_bits = max(1, int(expression_smt_bit_width(expr) or getattr(expr, "get_bit_width", lambda: 0)() or 0))
    try:
        index = int(getattr(expr, "value", -1))
    except (TypeError, ValueError):
        index = -1
    if index >= 0:
        return ("parameter_index", index, size_bits)
    storage_info = getattr(expr, "storage_info", None)
    storage_key_fn = getattr(storage_info, "storage_identity_key", None)
    if callable(storage_key_fn):
        storage_key = storage_key_fn()
        if storage_key is not None:
            return ("parameter_storage", storage_key, size_bits)
    return None


def _impl__opaque_parameter_object_identity_key(self, expr: Expression) -> tuple:
    size_bits = max(1, int(expression_smt_bit_width(expr) or getattr(expr, "get_bit_width", lambda: 0)() or 0))
    return ("unresolved_parameter_object", id(expr), size_bits)


def _impl__normalize_constant_bias(self, value: int, result_size: int) -> int:
    bits = max(1, int(result_size or 0)) * 8
    return int(value) % (1 << bits)


def _impl__raw_constant_value(self, expr: Optional[Expression]) -> Optional[int]:
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.CONSTANT:
        return None
    try:
        return int(expr.value)
    except (TypeError, ValueError):
        return None


def _impl__low_mask_width_bytes(
    self,
    value_expr: Optional[Expression],
    mask_expr: Optional[Expression],
) -> Optional[int]:
    del value_expr
    mask = self._raw_constant_value(mask_expr)
    if mask is None or mask < 0:
        return None
    width = 0
    current = int(mask)
    while current & 0xFF == 0xFF:
        width += 1
        current >>= 8
    if current != 0 or width <= 0:
        return None
    return width


def _impl__expressions_share_object_centric_structure(
    self,
    left: Optional[Expression],
    right: Optional[Expression],
) -> bool:
    if left is None or right is None:
        return False
    if left.expr_type == ExpressionType.INTRINSIC or right.expr_type == ExpressionType.INTRINSIC:
        return self._intrinsic_runtime_values_equivalent(left, right)
    equivalent, _reason = are_structurally_equivalent(left, right, debug=self.debug)
    return equivalent


def _impl__try_normalization_equivalence(
    self,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str
) -> QueryResult:
    return try_normalization_equivalence(
        self,
        base_ctx,
        case1,
        case2,
        param_replace_fn1,
        param_replace_fn2,
        pair_id,
        normalize_expression_fn=normalize_expression,
        normalization_context_cls=NormalizationContext,
        sign_facts_cls=SignFacts,
        extract_min_excluded_params_fn=extract_min_excluded_params,
        extract_upper_bound_facts_fn=extract_upper_bound_facts,
        extract_sign_facts_fn=extract_sign_facts,
        contains_udiv_fn=contains_udiv,
        normalize_udiv_with_guard_fn=normalize_udiv_with_guard,
        are_structurally_equivalent_fn=are_structurally_equivalent,
        get_structural_summary_fn=get_structural_summary,
        normalization_rule_application_cls=NormalizationRuleApplication,
    )


def _impl__extract_return_cases(
    self,
    analysis: FunctionReturnAnalysis
) -> List[ReturnCase]:
    return extract_return_cases(
        analysis,
        normalization_settings=self.normalization_settings,
    )


def _impl__prune_unreachable_cases(
    self,
    cases: List[ReturnCase],
    base_ctx: Dict[str, Any],
    param_replace_fn,
    label: str,
) -> List[ReturnCase]:
    if not cases:
        return cases

    reachable_cases: List[ReturnCase] = []
    pruned_count = 0

    for case in cases:
        if ConditionSimplifier.is_contradiction(case.conditions):
            pruned_count += 1
            self._debug_print(
                f"  {label}[{case.index}]: pruned by contradiction precheck"
            )
            continue

        if not self._case_contains_unresolved_expression(
            case,
            own_render_fn=param_replace_fn,
            base_ctx=base_ctx,
            query_label=f"{label}[{case.index}]",
        ):
            reachable_cases.append(case)
            continue

        if not case.conditions:
            reachable_cases.append(case)
            continue

        if any(
            self._expression_contains_unresolved(cond.expression)
            for cond in case.conditions
        ):
            reachable_cases.append(case)
            continue

        query = self._build_single_case_condition_query(
            base_ctx,
            case,
            param_replace_fn,
            label,
        )
        result = self._solve_query_internal(
            query,
            f"{label}[{case.index}]",
            stage="case-feasible",
            use_hard_timeout=False,
        )

        if result.is_equivalent is True:
            pruned_count += 1
            self._debug_print(
                f"  {label}[{case.index}]: pruned as unreachable by SMT"
            )
            continue

        reachable_cases.append(case)

    if reachable_cases:
        return reachable_cases

    if pruned_count > 0:
        self._debug_print(
            f"  {label}: pruning removed every case; keeping originals conservatively"
        )
    return cases


def _impl__register_pairwise_extra_assertions(
    self,
    base_ctx: Dict[str, Any],
    pair_id: str,
    assertions: Sequence[str],
) -> None:
    if not assertions:
        self._clear_pairwise_extra_assertions(base_ctx, pair_id)
        return
    by_pair = base_ctx.setdefault("pairwise_extra_assertions_by_pair", {})
    by_pair[pair_id] = tuple(str(item) for item in assertions if str(item).strip())


def _impl__clear_pairwise_extra_assertions(
    self,
    base_ctx: Dict[str, Any],
    pair_id: str,
) -> None:
    by_pair = base_ctx.get("pairwise_extra_assertions_by_pair")
    if isinstance(by_pair, dict):
        by_pair.pop(pair_id, None)
    evidence_by_pair = base_ctx.get("pairwise_unresolved_deferred_call_lowering_evidence_by_pair")
    if isinstance(evidence_by_pair, dict):
        evidence_by_pair.pop(pair_id, None)
    lowered_keys_by_pair = base_ctx.get("pairwise_unresolved_deferred_call_lowered_unknown_keys_by_pair")
    if isinstance(lowered_keys_by_pair, dict):
        lowered_keys_by_pair.pop(pair_id, None)


def _impl__collect_case_unknown_expression_nodes(self, case: ReturnCase) -> Tuple[Any, ...]:
    result: List[Any] = []
    seen = set()

    def add_from(expr: Any) -> None:
        for unknown in self._collect_unknown_expression_nodes(expr):
            key = self._expression_runtime_object_key(unknown)
            if key in seen:
                continue
            seen.add(key)
            result.append(unknown)

    add_from(getattr(case, "value_expr", None))
    for condition in getattr(case, "conditions", None) or ():
        add_from(getattr(condition, "expression", None))
    return tuple(result)


def _impl__collect_unknown_expression_nodes(self, expr: Any) -> Tuple[Any, ...]:
    result: List[Any] = []
    self._collect_unknown_expression_nodes_into(expr, result)
    return tuple(result)


def _impl__collect_unknown_expression_nodes_into(self, expr: Any, result: List[Any]) -> None:
    if expr is None or getattr(expr, "expr_type", None) is None:
        return
    if expr.expr_type == ExpressionType.UNKNOWN:
        result.append(expr)
        return
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for condition, value in expr.value:
            if condition is not None:
                self._collect_unknown_expression_nodes_into(condition.expression, result)
            self._collect_unknown_expression_nodes_into(value, result)
        return
    for operand in getattr(expr, "operands", []) or []:
        self._collect_unknown_expression_nodes_into(operand, result)


def _impl__solve_canonical_return_observation(
    self,
    base_ctx: Dict[str, Any],
    case1: ReturnCase,
    case2: ReturnCase,
    param_replace_fn1,
    param_replace_fn2,
    pair_id: str,
    *,
    object_target_key: Optional[Tuple[Any, ...]] = None,
    blocking_detail: str = "",
) -> Optional[QueryResult]:
    """Execute only a fully proven canonical return observation query."""

    self._last_canonical_return_width_pending_evidence = None
    def block(subreason: str, detail: str) -> None:
        self._last_canonical_return_width_pending_evidence = {
            "reason_id": "return_width_bridge_missing",
            "subreason": subreason,
            "detail": detail,
            "pair_id": pair_id,
            "object_target_key": object_target_key,
            "proof_system": "canonical_return_width_v1",
        }
    prepared = (base_ctx.get("return_width_observations_by_pair") or {}).get(pair_id)
    if not getattr(prepared, "proven", False):
        blockers = tuple(getattr(prepared, "blockers", ()) or ())
        detail = "; ".join(
            f"{item.blocker_kind}:{item.missing_slot}" for item in blockers
        ) or "canonical return observation is unavailable"
        block("canonical_observation_blocked", detail)
        return None
    try:
        query = build_canonical_return_observation_query(
            base_ctx,
            case1,
            case2,
            param_replace_fn1,
            param_replace_fn2,
            pair_id,
            view=prepared.view,
            receipt=prepared.binding_receipt,
        )
    except ValueError as exc:
        block("canonical_binding_inapplicable", str(exc))
        return None
    stats = getattr(self, "_active_normalization_stats", None)
    if stats is not None:
        stats["pair_width_projection_queries"] = (
            int(stats.get("pair_width_projection_queries", 0)) + 1
        )
        stats["width_canonical_consumer_queries"] = (
            int(stats.get("width_canonical_consumer_queries", 0)) + 1
        )
    result = self._solve_query_internal(
        query,
        pair_id,
        stage="canonical-return-observation-ineq",
        use_hard_timeout=True,
    )
    result.last_query = query
    result.pair_stage = "canonical-return-observation-ineq"
    result.return_width_observation_view_digest = prepared.view.digest
    result.consumer_binding_receipt_digest = prepared.binding_receipt.binding_digest
    return result


def _impl__create_aggregate_result(
    self,
    is_equivalent: Optional[bool],
    elapsed_time: float,
    counterexample_raw: Optional[Dict]
) -> ParallelResult:
    status_map = {
        True: SolverStatus.UNSAT,
        False: SolverStatus.SAT,
        None: SolverStatus.UNKNOWN,
    }
    status = status_map.get(is_equivalent, SolverStatus.UNKNOWN)
    solver_result = SolverResult(
        solver_name="pairwise_aggregate",
        status=status,
        elapsed_time=elapsed_time,
        model=counterexample_raw,
    )
    return ParallelResult(results=[solver_result])


def _impl__cases_are_contradictory(
    self,
    case1: ReturnCase,
    case2: ReturnCase,
) -> bool:
    combined_conditions = list(case1.conditions) + list(case2.conditions)
    if not combined_conditions:
        return False
    identity_conditions = self._conditions_with_object_identity_parameter_symbols(
        combined_conditions,
        list(getattr(case1, "parameters", None) or [])
        + list(getattr(case2, "parameters", None) or []),
    )
    solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
    if solver_result is not None:
        return solver_result
    return ConditionSimplifier.object_centric_is_contradiction(identity_conditions)


def _impl__get_expression_safety_checker(
    self,
    base_ctx: Optional[Dict[str, Any]] = None,
) -> ExpressionSafetyChecker:
    active = getattr(self, "_active_safety_checker", None)
    if active is not None:
        return active
    return ExpressionSafetyChecker(
        solver_runner=self.solver_runner,
        debug_print=self._debug_print,
        per_query_timeout=self.per_query_timeout,
        base_ctx=base_ctx,
    )


def _impl__create_empty_result(self) -> StrategyResult:
    return StrategyResult(
        is_equivalent=None,
        solver_results=ParallelResult(results=[]),
        total_pairs=0,
        unsat_pairs=0,
        sat_pairs=0,
        unknown_pairs=0,
        error_pairs=0,
        unknown_reasons=[
            make_unknown_reason(
                UnknownReasonId.EMPTY_RETURN_CASES,
                stage="S_PAIRWISE",
            )
        ],
    )


def _impl__debug_symbol_mapping(self, base_ctx: Dict[str, Any]) -> None:
    self._debug_print("Symbol replacement mapping:")
    self._debug_print("  Function 1:")
    for param in base_ctx["params1"]:
        self._debug_print(f"    {param.original_name} -> {param.smt_name}")
    for var in base_ctx.get("extra_vars1", []):
        self._debug_print(f"    {var.original_name} -> {var.smt_name}")
    self._debug_print("  Function 2:")
    for param in base_ctx["params2"]:
        self._debug_print(f"    {param.original_name} -> {param.smt_name}")
    for var in base_ctx.get("extra_vars2", []):
        self._debug_print(f"    {var.original_name} -> {var.smt_name}")


def _impl__rewrite_cases_with_parameter_fragments(
    self,
    cases: List[ReturnCase],
    extra_vars: List[Any],
) -> None:
    fragment_map = {}
    for extra in extra_vars or []:
        analysis = getattr(extra, "analysis", None)
        if analysis is None or not analysis.is_parameter_fragment() or analysis.fragment_info is None:
            continue
        fragment_map[extra.original_name] = analysis.fragment_info

    if not fragment_map:
        return

    for case in cases:
        changed = False

        rewritten_conditions: List[Condition] = []
        for cond in case.conditions:
            rewritten_expr = self._rewrite_expr_with_parameter_fragments(
                cond.expression,
                fragment_map,
            )
            rewritten_conditions.append(Condition(rewritten_expr, cond.negated))
            changed = changed or (rewritten_expr is not cond.expression)

        rewritten_value = self._rewrite_expr_with_parameter_fragments(
            case.value_expr,
            fragment_map,
        )
        changed = changed or (rewritten_value is not case.value_expr)

        if not changed:
            continue

        case.update_conditions(rewritten_conditions, summary_conditions=rewritten_conditions)
        case.value_expr = rewritten_value
        case.normalized_value_expr = normalize_expression(
            rewritten_value,
            NormalizationContext(settings=self.normalization_settings),
        )
        case._value_smt_cache.clear()


def _impl__rewrite_expr_with_parameter_fragments(
    self,
    expr: Expression,
    fragment_map: Dict[str, Any],
) -> Expression:
    if expr is None:
        return expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        changed = False
        branches = []
        for cond, value in expr.value:
            rewritten_cond = None
            if cond is not None:
                rewritten_cond_expr = self._rewrite_expr_with_parameter_fragments(
                    cond.expression,
                    fragment_map,
                )
                rewritten_cond = Condition(rewritten_cond_expr, cond.negated)
                changed = changed or (rewritten_cond_expr is not cond.expression)
            rewritten_value = self._rewrite_expr_with_parameter_fragments(value, fragment_map)
            changed = changed or (rewritten_value is not value)
            branches.append((rewritten_cond, rewritten_value))

        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt

    operands = getattr(expr, "operands", None) or []
    rewritten_operands = [
        self._rewrite_expr_with_parameter_fragments(operand, fragment_map)
        for operand in operands
    ]
    operands_changed = any(new is not old for new, old in zip(rewritten_operands, operands))

    candidate = expr
    if operands_changed:
        candidate = Expression(
            expr_type=expr.expr_type,
            value=expr.value,
            operator=expr.operator,
            operands=rewritten_operands,
            size=expr.size,
            name=expr.name,
            data_type=expr.data_type,
            data_type_obj=getattr(expr, "data_type_obj", None),
            storage_info=expr.storage_info,
            read_order_key=expr.read_order_key,
            runtime_ref=getattr(expr, "runtime_ref", None),
            opcode=getattr(expr, "opcode", None),
        )

    collapsed = self._collapse_parameter_fragment_extension(candidate, fragment_map)
    return collapsed


def _impl__collapse_parameter_fragment_extension(
    self,
    expr: Expression,
    fragment_map: Dict[str, Any],
) -> Expression:
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP:
        return expr

    if expr.operator == "PIECE" and len(expr.operands) == 2:
        high, low = expr.operands
        collapsed = self._build_fragment_extension_expr(high, low, fragment_map)
        if collapsed is not None:
            return collapsed
        return expr

    if expr.operator != "INT_OR" or len(expr.operands) != 2:
        return expr

    left, right = expr.operands
    collapsed = self._match_shift_or_fragment_expr(left, right, fragment_map)
    if collapsed is not None:
        return collapsed
    collapsed = self._match_shift_or_fragment_expr(right, left, fragment_map)
    if collapsed is not None:
        return collapsed
    return expr


def _impl__match_shift_or_fragment_expr(
    self,
    shifted_expr: Expression,
    low_expr: Expression,
    fragment_map: Dict[str, Any],
) -> Optional[Expression]:
    if (
        shifted_expr.expr_type != ExpressionType.BINARY_OP
        or shifted_expr.operator != "INT_LEFT"
        or len(shifted_expr.operands) != 2
    ):
        return None

    shift_amount = shifted_expr.operands[1]
    if shift_amount.expr_type != ExpressionType.CONSTANT:
        return None

    return self._build_fragment_extension_expr(
        shifted_expr.operands[0],
        low_expr,
        fragment_map,
        expected_shift_bits=int(shift_amount.value),
    )


def _impl__build_fragment_extension_expr(
    self,
    high_expr: Expression,
    low_expr: Expression,
    fragment_map: Dict[str, Any],
    expected_shift_bits: Optional[int] = None,
) -> Optional[Expression]:
    if high_expr.expr_type != ExpressionType.VARIABLE or not high_expr.name:
        return None

    fragment_info = fragment_map.get(high_expr.name)
    if fragment_info is None:
        return None

    if low_expr.expr_type not in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
        return None
    if low_expr.name != fragment_info.parent_param_name:
        return None

    if expected_shift_bits is not None and expected_shift_bits != fragment_info.parent_param_bit_width:
        return None

    ext_op = "INT_SEXT" if fragment_info.extension_type.name == "SIGN_EXTEND" else "INT_ZEXT"
    rebuilt = Expression.unary_op(ext_op, low_expr)
    rebuilt.size = max(1, fragment_info.base_register_size_bits // 8)
    rebuilt.data_type = getattr(low_expr, "data_type", None)
    return rebuilt

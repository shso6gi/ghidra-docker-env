"""Recurrence summarisation entry point: counter/parameter candidates, loop bounds, placeholder matching and base-case discovery."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    Condition,
    Counter,
    Expression,
    ExpressionType,
    ParameterInfo,
    ReturnInfo,
    _runtime_expression_signature,
    get_declared_type_signedness,
    parameter_identity_key_from_descriptor,
    parameter_identity_key_from_expression,
)


def _impl_try_summarize_function(self, function, high_function, analysis) -> Optional[Tuple[List[ReturnInfo], str]]:
    if function is None or high_function is None or analysis is None:
        return None

    if len(getattr(analysis, "parameters", []) or []) == 1:
        summary = self._try_summarize_linear_self_recursion(function, high_function, analysis)
        if summary is not None:
            return summary

    summary = self._try_summarize_readonly_pointer_reduction(function, high_function, analysis)
    if summary is not None:
        return summary

    summary = self._try_summarize_vectorized_affine_progression_sum(function, high_function, analysis)
    if summary is not None:
        return summary

    summary = self._try_summarize_multiplicative_phi_return_region(
        function,
        high_function,
        analysis,
    )
    if summary is not None:
        return summary

    summary = self._try_summarize_counted_scalar_loop(function, high_function, analysis)
    if summary is not None:
        return summary

    summary = self._try_summarize_proved_return_region_state_transition_composition(
        function,
        high_function,
        analysis,
    )
    if summary is not None:
        return summary

    summary = self._try_summarize_state_transition_loop(function, high_function, analysis)
    if summary is not None:
        return summary

    summary = self._try_summarize_branch_accumulator_loop(analysis)
    if summary is not None:
        return summary
    return None


def _impl__counter_parameter_candidate_matches_descriptor(
    self,
    candidate: Optional[Expression],
    counter_param: dict,
) -> bool:
    if candidate is None or getattr(candidate, "expr_type", None) != ExpressionType.PARAMETER:
        return False
    expected_storage = self._summary_storage_info_from_parameter(counter_param)
    candidate_storage = getattr(candidate, "storage_info", None)
    if expected_storage is not None:
        return (
            candidate_storage is not None
            and self._storage_infos_refer_to_same_parameter_slot(candidate_storage, expected_storage)
        )
    try:
        expected_index = int(counter_param.get("index"))
    except (TypeError, ValueError):
        expected_index = -1
    try:
        candidate_index = int(getattr(candidate, "value", -1))
    except (TypeError, ValueError):
        candidate_index = -1
    if expected_index >= 0 or candidate_index >= 0:
        return expected_index >= 0 and expected_index == candidate_index
    expected_identity = None
    try:
        expected_identity = parameter_identity_key_from_descriptor(counter_param)
    except Exception:
        expected_identity = None
    candidate_identity = None
    try:
        candidate_identity = parameter_identity_key_from_expression(candidate)
    except Exception:
        candidate_identity = None
    if expected_identity is not None or candidate_identity is not None:
        return expected_identity is not None and expected_identity == candidate_identity
    return False


def _impl__complete_counter_constant_cover(
    self,
    conditions: Sequence[Condition],
    counter_expr: Expression,
    *,
    search_limit: int = 64,
) -> Optional[Tuple[int, ...]]:
    size = max(1, int(getattr(counter_expr, "size", 0) or 4))
    possible_values: List[int] = []
    for value in range(0, int(search_limit) + 1):
        equality = Condition(
            Expression.binary_op(
                "INT_EQUAL",
                counter_expr,
                Expression.constant(value, size=size),
            ),
            False,
        )
        is_unsat = self._condition_conjunction_unsat_with_solver(list(conditions) + [equality])
        if is_unsat is None:
            return None
        if is_unsat is False:
            possible_values.append(value)
        elif is_unsat is not True:
            return None
    if not possible_values:
        return None
    disjunction = None
    for value in possible_values:
        equality_expr = Expression.binary_op(
            "INT_EQUAL",
            counter_expr,
            Expression.constant(value, size=size),
        )
        equality_expr.size = 1
        if disjunction is None:
            disjunction = equality_expr
        else:
            disjunction = Expression.binary_op("BOOL_OR", disjunction, equality_expr)
            disjunction.size = 1
    outside_cover = Condition(disjunction, True)
    cover_complete = self._condition_conjunction_unsat_with_solver(list(conditions) + [outside_cover])
    if cover_complete is None:
        return None
    if cover_complete is not True:
        return None
    return tuple(possible_values)


def _impl__counter_parameter_candidate_can_normalize(
    self,
    candidate: Optional[Expression],
    counter_param: dict,
    counter_expr: Expression,
) -> bool:
    if candidate is None or getattr(candidate, "expr_type", None) != ExpressionType.PARAMETER:
        return False
    if counter_expr is None or getattr(counter_expr, "expr_type", None) != ExpressionType.PARAMETER:
        return False
    candidate_storage = getattr(candidate, "storage_info", None)
    counter_storage = getattr(counter_expr, "storage_info", None)
    if candidate_storage is not None or counter_storage is not None:
        return (
            candidate_storage is not None
            and counter_storage is not None
            and self._storage_infos_refer_to_same_parameter_slot(candidate_storage, counter_storage)
        )
    candidate_identity = self._parameter_expression_semantic_identity(candidate)
    counter_identity = self._parameter_expression_semantic_identity(counter_expr)
    if candidate_identity is not None or counter_identity is not None:
        return candidate_identity is not None and candidate_identity == counter_identity
    expected_index = None
    try:
        if counter_param.get("index") is not None:
            expected_index = int(counter_param.get("index"))
    except (TypeError, ValueError):
        expected_index = None
    try:
        candidate_index = int(getattr(candidate, "value", -1))
        counter_index = int(getattr(counter_expr, "value", -1))
    except (TypeError, ValueError):
        candidate_index = counter_index = -1
    if candidate_index < 0:
        return False
    if counter_index >= 0:
        return candidate_index == counter_index
    return expected_index is not None and candidate_index == expected_index


def _impl__unique_parameters_by_name(parameters: Optional[Sequence[dict]]) -> Dict[str, dict]:
    by_name: Dict[str, dict] = {}
    name_counts: Dict[str, int] = {}
    for param in parameters or ():
        if not isinstance(param, dict):
            continue
        name = str(param.get("name") or "")
        if not name:
            continue
        name_counts[name] = name_counts.get(name, 0) + 1
        by_name.setdefault(name, param)
    return {
        name: param
        for name, param in by_name.items()
        if name_counts.get(name, 0) == 1
    }


def _impl__small_integer_power_roots(
    self,
    value: int,
    *,
    max_root: int = 256,
) -> Tuple[int, ...]:
    try:
        value = int(value)
    except (TypeError, ValueError):
        return ()
    if value <= 1:
        return ()
    roots: List[int] = []
    for root in range(2, int(max_root) + 1):
        product = root * root
        while product < value:
            product *= root
        if product == value:
            roots.append(root)
    return tuple(roots)


def _impl__build_auxiliary_parameter_infos(
    self,
    symbol_specs: Sequence[dict],
) -> List[ParameterInfo]:
    infos: List[ParameterInfo] = []
    for spec in sorted(
        symbol_specs or [],
        key=lambda item: (
            self._summary_symbol_identity_sort_key(item.get("identity")),
            int(item.get("size", 0) or 0),
        ),
    ):
        aux_name = str(spec.get("aux_name") or "")
        if not aux_name:
            continue
        width_bits = max(1, int(spec.get("size", 0) or 4)) * 8
        infos.append(
            ParameterInfo(
                original_name=aux_name,
                smt_name=aux_name,
                bit_width=width_bits,
                index=int(spec.get("aux_index", -1) or -1),
                is_signed=bool(spec.get("is_signed", True)),
            )
        )
    return infos


def _impl__adjust_loop_bound_for_strict_relation(
    self,
    bound_expr: Expression,
    delta: int,
) -> Expression:
    if delta == 0:
        return bound_expr
    adjusted = Expression.binary_op(
        "INT_ADD" if delta > 0 else "INT_SUB",
        bound_expr,
        Expression.constant(abs(delta), size=bound_expr.size or 4),
    )
    adjusted.size = bound_expr.size
    return adjusted


def _impl__parse_counter_comparison(
    self,
    expr: Optional[Expression],
    counter_name: str,
) -> Optional[Tuple[str, Expression, bool]]:
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None
    operator = expr.operator
    if operator not in {"INT_SLESS", "INT_SLESSEQUAL", "INT_LESS", "INT_LESSEQUAL"}:
        return None
    signed = operator.startswith("INT_S")
    left, right = expr.operands
    left_is_counter = self._expr_matches_counter_placeholder(left, counter_name)
    right_is_counter = self._expr_matches_counter_placeholder(right, counter_name)
    if left_is_counter == right_is_counter:
        return None
    if left_is_counter:
        relation = "<" if operator in {"INT_SLESS", "INT_LESS"} else "<="
        return relation, right, signed
    relation = ">" if operator in {"INT_SLESS", "INT_LESS"} else ">="
    return relation, left, signed


def _impl__expr_matches_counter_placeholder(
    self,
    expr: Optional[Expression],
    counter_name: str,
) -> bool:
    normalized = self._normalize_counter_view(expr, counter_name)
    return bool(normalized is not None and getattr(normalized[0], "name", None) == counter_name)


def _impl__safe_expr_text(self, expr: Optional[Expression]) -> str:
    signature = _runtime_expression_signature(expr)
    return repr(signature)


def _impl__substitute_generated_loop_variable_aliases(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    replacement: Expression,
) -> Optional[Expression]:
    if expr is None:
        return None
    placeholder_name = str(getattr(placeholder, "name", "") or "")
    if not placeholder_name.startswith("__loop_"):
        return expr
    if (
        getattr(expr, "expr_type", None) == ExpressionType.VARIABLE
        and str(getattr(expr, "name", "") or "") == placeholder_name
    ):
        return self._coerce_summary_expression_to_size(
            replacement,
            max(1, int(getattr(expr, "size", 0) or getattr(replacement, "size", 0) or 4)),
            signed=self._expression_prefers_signed_extension(replacement),
        )
    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
        left = self._substitute_generated_loop_variable_aliases(
            expr.operands[0],
            placeholder,
            replacement,
        )
        right = self._substitute_generated_loop_variable_aliases(
            expr.operands[1],
            placeholder,
            replacement,
        )
        if left is expr.operands[0] and right is expr.operands[1]:
            return expr
        rebuilt = Expression.binary_op(expr.operator, left, right)
        rebuilt.size = expr.size
        return rebuilt
    if expr.expr_type == ExpressionType.UNARY_OP and len(expr.operands) == 1:
        operand = self._substitute_generated_loop_variable_aliases(
            expr.operands[0],
            placeholder,
            replacement,
        )
        if operand is expr.operands[0]:
            return expr
        rebuilt = Expression.unary_op(expr.operator, operand)
        rebuilt.size = expr.size
        return rebuilt
    if expr.expr_type == ExpressionType.PHI and expr.value:
        branches = []
        changed = False
        for condition, value in expr.value:
            new_condition = condition
            if condition is not None:
                condition_expr = self._substitute_generated_loop_variable_aliases(
                    condition.expression,
                    placeholder,
                    replacement,
                )
                if condition_expr is not condition.expression:
                    new_condition = Condition(condition_expr, condition.negated)
                    changed = True
            new_value = self._substitute_generated_loop_variable_aliases(
                value,
                placeholder,
                replacement,
            )
            if new_value is not value:
                changed = True
            branches.append((new_condition, new_value))
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = expr.size
        return rebuilt
    if expr.expr_type in {ExpressionType.CALL, ExpressionType.INTRINSIC, ExpressionType.MEMORY} and expr.operands:
        new_operands = [
            self._substitute_generated_loop_variable_aliases(operand, placeholder, replacement)
            for operand in expr.operands
        ]
        if all(new is old for new, old in zip(new_operands, expr.operands)):
            return expr
        if expr.expr_type == ExpressionType.CALL:
            rebuilt = Expression.call(expr.name or "call", new_operands)
        elif expr.expr_type == ExpressionType.INTRINSIC:
            rebuilt = Expression.intrinsic(
                expr.name or "intrinsic",
                new_operands,
                size=expr.size,
                runtime_ref=expr.runtime_ref,
                opcode=expr.opcode,
            )
        else:
            rebuilt = Expression.memory(
                new_operands[0],
                size=expr.size,
                read_order_key=expr.read_order_key,
                runtime_ref=expr.runtime_ref,
            )
        rebuilt.size = expr.size
        return rebuilt
    return expr


def _impl__expr_matches_placeholder(self, expr: Optional[Expression], placeholder: Expression) -> bool:
    expr = self._canonicalize_expression(expr)
    if expr is None:
        return False
    try:
        return expr.structural_key() == placeholder.structural_key()
    except (AttributeError, TypeError, ValueError, RecursionError):
        return False


def _impl__extract_delta_from_possible_phi(
    self,
    expr: Expression,
    accumulator_placeholder: Expression,
    parameters: Sequence[dict],
) -> Tuple[Expression, ...]:
    if expr.expr_type == ExpressionType.PHI and expr.value:
        deltas = []
        for _condition, branch_value in expr.value:
            if branch_value is None:
                return ()
            branch_deltas = self._extract_delta_from_possible_phi(
                branch_value,
                accumulator_placeholder,
                parameters,
            )
            if not branch_deltas:
                return ()
            deltas.extend(branch_deltas)
        return tuple(deltas)
    delta = self._extract_additive_delta(expr, accumulator_placeholder, parameters)
    if delta is not None:
        return (delta,)
    multiplicative = self._extract_multiplicative_accumulator_transition(
        expr,
        accumulator_placeholder,
    )
    if multiplicative is not None:
        return (multiplicative,)
    return ()


def _impl__debug(self, message: str) -> None:
    if self.debug:
        print(f"[RecurrenceSummary] {message}")


def _impl__fp_denominator_is_count_parameter(
    self,
    expr: Optional[Expression],
    count_name: str,
) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands and expr.operator in {"INT2FLOAT", "CAST", "COPY"}:
        return self._fp_denominator_is_count_parameter(expr.operands[0], count_name)
    if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2 and expr.operator == "SUBPIECE":
        return self._fp_denominator_is_count_parameter(expr.operands[0], count_name)
    return (
        expr.expr_type == ExpressionType.PARAMETER
        and str(getattr(expr, "name", "") or "") == str(count_name)
    )


def _impl__counter_value_satisfies_relation(self, value: int, relation: str, constant: int) -> bool:
    if relation == ">":
        return int(value) > int(constant)
    if relation == ">=":
        return int(value) >= int(constant)
    if relation == "<":
        return int(value) < int(constant)
    if relation == "<=":
        return int(value) <= int(constant)
    return False


def _impl__analysis_parameter_declared_signedness(
    self,
    analysis,
    count_param: Optional[Dict[str, Any]],
) -> Optional[bool]:
    declared = None if count_param is None else count_param.get("is_signed")
    index = None if count_param is None else count_param.get("index")
    if index is None:
        return declared
    try:
        index_value = int(index)
    except (TypeError, ValueError):
        return declared
    for hypothesis_payload in list(getattr(analysis, "signature_hypotheses", []) or []):
        if not isinstance(hypothesis_payload, dict):
            continue
        resolved_overrides = dict(hypothesis_payload.get("resolved_parameter_overrides") or {})
        resolved_payload = resolved_overrides.get(index_value)
        if resolved_payload is None:
            resolved_payload = resolved_overrides.get(str(index_value))
        if isinstance(resolved_payload, dict) and "is_signed" in resolved_payload:
            raw_signed = resolved_payload.get("is_signed")
            declared = None if raw_signed is None else bool(raw_signed)
        parameter_overrides = dict(hypothesis_payload.get("parameter_type_overrides") or {})
        override_name = parameter_overrides.get(index_value)
        if override_name is None:
            override_name = parameter_overrides.get(str(index_value))
        if override_name:
            declared = get_declared_type_signedness(
                None,
                str(override_name),
                fallback_signed=bool(declared if declared is not None else True),
            )
    return declared


def _impl__parameter_names_from_expr(self, expr) -> Tuple[str, ...]:
    names = []
    queue = [expr]
    while queue:
        current = queue.pop()
        if current is None:
            continue
        if getattr(current, "expr_type", None) == ExpressionType.PARAMETER and current.name:
            names.append(current.name)
        for operand in getattr(current, "operands", ()):
            queue.append(operand)
    return tuple(dict.fromkeys(names))


def _impl__new_loop_variable_binder_scope(self) -> Dict[Tuple[str, Tuple[Any, ...]], int]:
    return {}


def _impl__loop_variable_binder_ordinal(
    self,
    scope: Optional[Dict[Tuple[str, Tuple[Any, ...]], int]],
    role: str,
    varnode,
) -> int:
    if scope is None:
        return 0
    key = self._varnode_cache_key(varnode)
    if key is None:
        return 0
    role_key = str(role or "loop_variable")
    scoped_key = (role_key, key)
    if scoped_key not in scope:
        scope[scoped_key] = sum(
            1 for existing_role, _existing_key in scope
            if existing_role == role_key
        )
    return int(scope[scoped_key])


def _impl__infer_loop_parameter_pair(self, analysis) -> Optional[Tuple[str, str]]:
    candidates: Counter[Tuple[str, str]] = Counter()
    all_conditions: List[Condition] = []
    for ret in analysis.returns or []:
        all_conditions.extend(ret.conditions or [])
    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is not None:
        for effect in effect_summary.effects or []:
            all_conditions.extend(effect.conditions or [])

    for cond in all_conditions:
        pair = self._match_less_parameter_pair(cond)
        if pair is not None:
            candidates[pair] += 1
    if not candidates:
        return None
    return candidates.most_common(1)[0][0]


def _impl__match_less_parameter_pair(self, condition: Condition) -> Optional[Tuple[str, str]]:
    relation = self._parameter_comparison_relation(condition)
    if relation is None:
        return None
    left_name, relation_name, right_name = relation
    if relation_name == "<":
        return left_name, right_name
    if relation_name == ">":
        return right_name, left_name
    return None


def _impl__parameter_name_from_expr(self, expr: Optional[Expression]) -> Optional[str]:
    if expr is None:
        return None
    if expr.expr_type == ExpressionType.PARAMETER and expr.name:
        return expr.name
    normalized = self._normalize_counter_view(expr, getattr(expr, "name", None) or "")
    if normalized is not None and normalized[0].name:
        return normalized[0].name
    return None


def _impl__param_expr(self, analysis, name: str) -> Expression:
    for param in analysis.parameters or []:
        if param.get("name") != name:
            continue
        return Expression.parameter(
            name,
            index=int(param.get("index", 0)),
            data_type=param.get("data_type"),
            data_type_obj=param.get("data_type_obj"),
            size=int(param.get("size", 4) or 4),
        )
    return Expression.parameter(name, size=4)


def _impl__find_no_loop_base_case(
    self,
    returns: Sequence[ReturnInfo],
    pointer_name: str,
    start_name: str,
    limit_name: str,
    *,
    require_pointer_nonnull: bool,
) -> Optional[ReturnInfo]:
    for ret in returns:
        if self._return_is_constant(ret):
            continue
        has_nonnull = any(self._condition_is_pointer_nonnull(cond, pointer_name) for cond in ret.conditions or [])
        has_not_less = any(self._condition_is_not_less(cond, start_name, limit_name) for cond in ret.conditions or [])
        if has_not_less and (has_nonnull or not require_pointer_nonnull):
            return ret
    return None


def _impl__find_one_step_cases(
    self,
    returns: Sequence[ReturnInfo],
    pointer_name: str,
    start_name: str,
    limit_name: str,
    *,
    require_pointer_nonnull: bool,
) -> Optional[Tuple[ReturnInfo, ReturnInfo]]:
    even_case = None
    odd_case = None
    for ret in returns:
        conditions = ret.conditions or []
        has_nonnull = any(self._condition_is_pointer_nonnull(cond, pointer_name) for cond in conditions)
        has_loop = any(self._condition_is_less(cond, start_name, limit_name) for cond in conditions)
        has_one_step = any(self._condition_is_step_equality(cond, start_name, limit_name) for cond in conditions)
        if not (has_loop and has_one_step and (has_nonnull or not require_pointer_nonnull)):
            continue
        parity = self._extract_counter_parity(conditions, start_name)
        if parity is True:
            even_case = ret
        elif parity is False:
            odd_case = ret
    if even_case is None or odd_case is None:
        return None
    return even_case, odd_case

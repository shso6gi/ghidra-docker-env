"""Recurrence summarisation entry point: counter/parameter candidates, loop bounds, placeholder matching and base-case discovery."""

from __future__ import annotations

from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple
from collections import Counter
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.signature import get_declared_type_signedness, is_integral_data_type
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    ParameterInfo,
    _runtime_expression_signature,
    parameter_identity_key_from_descriptor,
    parameter_identity_key_from_expression,
)
from ._shared import ConditionSimplifier
from ._shared import _reduce_expression_under_conditions
from ._shared import _runtime_conditions_signature
from ._shared import eval_constant_raw
from scripts.function_tracer_pcode.analysis.debug import summarize_conditions, summarize_expression


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


def _impl__debug_available(self) -> bool:
    """debug 出力が有効か。呼び出し側は message 構築ごとこれで囲む。

    recurrence family の debug guard の唯一の判定点。出力方針（抑止・件数上限
    など）を変えるときはここと :func:`_impl__debug` だけを触ればよい。
    """

    return bool(self.debug)


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


# ---- one-step case synthesis from effects
def _impl__synthesize_one_step_cases_from_effects(
    self,
    analysis,
    base_case: ReturnInfo,
    pointer_name: str,
    start_name: str,
    limit_name: str,
    *,
    require_pointer_nonnull: bool,
) -> List[ReturnInfo]:
    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is None:
        return []
    coeffs = self._extract_linear_location_coefficients(base_case.value, analysis.parameters or [])
    if not coeffs:
        return []

    grouped: Dict[Tuple[object, ...], List] = {}
    for effect in effect_summary.effects or []:
        conds = ConditionSimplifier.simplify_conditions_object_centric(effect.conditions or [])
        key = _runtime_conditions_signature(conds)
        grouped.setdefault(key, []).append((conds, effect))

    synthesized: List[ReturnInfo] = []
    for grouped_effects in grouped.values():
        conds = grouped_effects[0][0]
        has_nonnull = any(self._condition_is_pointer_nonnull(cond, pointer_name) for cond in conds)
        if require_pointer_nonnull and not has_nonnull:
            if self._debug_available():
                self._debug(
                    "Skipping effect-derived one-step candidate: missing local pointer-nonnull guard "
                    f"for conditions {summarize_conditions(conds)}"
                )
            continue
        if not any(self._condition_is_less(cond, start_name, limit_name) for cond in conds):
            if self._debug_available():
                self._debug(
                    "Skipping effect-derived one-step candidate: missing loop-progress guard "
                    f"for conditions {summarize_conditions(conds)}"
                )
            continue
        parity = self._extract_counter_parity(conds, start_name)
        if parity is None:
            if self._debug_available():
                self._debug(
                    "Skipping effect-derived one-step candidate: could not determine counter parity "
                    f"for conditions {summarize_conditions(conds)}"
                )
            continue
        step_eq = Condition(
            Expression.binary_op(
                "INT_EQUAL",
                self._param_expr(analysis, limit_name),
                Expression.binary_op(
                    "INT_ADD",
                    self._param_expr(analysis, start_name),
                    Expression.constant(1, self._param_expr(analysis, start_name).size or 4),
                ),
            ),
            False,
        )
        step_context = ConditionSimplifier.simplify_conditions_object_centric(list(conds) + [step_eq])
        if ConditionSimplifier.object_centric_is_contradiction(step_context):
            if self._debug_available():
                self._debug(
                    "Skipping effect-derived one-step candidate: one-step context is contradictory "
                    f"for conditions {summarize_conditions(conds)}"
                )
            continue

        delta_terms: List[Expression] = []
        for _conds, effect in grouped_effects:
            coeff = coeffs.get(effect.location)
            if coeff in (None, 0):
                continue
            delta_expr = self._extract_store_delta_expr(
                effect,
                analysis.parameters or [],
                step_context,
            )
            if delta_expr is None:
                if self._debug_available():
                    self._debug(
                        "Aborting effect-derived one-step synthesis: could not isolate store delta "
                        f"for location={effect.location} value={summarize_expression(effect.value)} "
                        f"conditions={summarize_conditions(step_context)}"
                    )
                return []
            reduced_delta = _reduce_expression_under_conditions(delta_expr, step_context)
            scaled = self._scale_expression(reduced_delta, coeff)
            if scaled is not None:
                delta_terms.append(scaled)
        if not delta_terms:
            if self._debug_available():
                self._debug(
                    "Skipping effect-derived one-step candidate: no additive delta terms matched "
                    f"for conditions {summarize_conditions(conds)}"
                )
            continue

        delta_sum = self._sum_expression_terms(delta_terms)
        if delta_sum is None:
            continue
        value = Expression.binary_op("INT_ADD", base_case.value, delta_sum)
        value.size = base_case.value.size
        synthesized.append(
            ReturnInfo(
                address=base_case.address,
                value=value,
                conditions=step_context,
                branch_index=9_000 if parity else 9_001,
                pcode_identity=base_case.pcode_identity,
                pcode_order=base_case.pcode_order,
                pcode_time=base_case.pcode_time,
                pcode_op_ref=getattr(base_case, "pcode_op_ref", None),
                return_value_pcode_op_refs=tuple(
                    getattr(base_case, "return_value_pcode_op_refs", ()) or ()
                ),
            )
        )
    return synthesized


def _impl__extract_store_delta_expr(
    self,
    effect,
    parameters: Sequence[dict],
    conditions: Optional[Sequence[Condition]] = None,
) -> Optional[Expression]:
    active_conditions = list(conditions or [])
    reduced_value = _reduce_expression_under_conditions(effect.value, active_conditions)
    current_read = Expression.memory(
        self._address_expr_for_location(effect.location, parameters),
        size=effect.location.size,
    )
    reduced_current_read = _reduce_expression_under_conditions(current_read, active_conditions)
    delta = self._extract_additive_delta(reduced_value, reduced_current_read, parameters)
    if delta is not None:
        return delta
    if reduced_value.equals(reduced_current_read):
        return Expression.constant(0, size=effect.location.size)
    return None


def _impl__extract_additive_delta(
    self,
    expr: Expression,
    base_expr: Expression,
    parameters: Sequence[dict],
) -> Optional[Expression]:
    expr_terms = self._flatten_add_terms(expr)
    base_terms = self._flatten_add_terms(base_expr)
    remaining = list(expr_terms)
    for sign, term in base_terms:
        matched = False
        for index, (cand_sign, cand_term) in enumerate(remaining):
            if cand_sign != sign:
                continue
            if not self._terms_equivalent(cand_term, term, parameters):
                continue
            del remaining[index]
            matched = True
            break
        if not matched:
            return None
    return self._sum_expression_terms(
        [self._scale_expression(term, sign) for sign, term in remaining if self._scale_expression(term, sign) is not None]
    )


def _impl__flatten_add_terms(
    self,
    expr: Expression,
    sign: int = 1,
) -> List[Tuple[int, Expression]]:
    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_ADD" and len(expr.operands) == 2:
        return self._flatten_add_terms(expr.operands[0], sign) + self._flatten_add_terms(expr.operands[1], sign)
    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_SUB" and len(expr.operands) == 2:
        return self._flatten_add_terms(expr.operands[0], sign) + self._flatten_add_terms(expr.operands[1], -sign)
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "INT_2COMP" and expr.operands:
        return self._flatten_add_terms(expr.operands[0], -sign)
    return [(sign, expr)]


def _impl__build_parity_split_loop_value(
    self,
    base_expr: Expression,
    start_name: str,
    limit_name: str,
    even_affine: Tuple[int, int],
    odd_affine: Tuple[int, int],
    start_is_even: bool,
) -> Optional[Expression]:
    start_expr = self._param_expr_placeholder(start_name, base_expr.size or 4)
    limit_expr = self._param_expr_placeholder(limit_name, base_expr.size or 4)
    size = start_expr.size or 4
    n_expr = Expression.binary_op("INT_SUB", limit_expr, start_expr)
    n_expr.size = size
    one = Expression.constant(1, size)
    two = Expression.constant(2, size)

    if start_is_even:
        n_even = Expression.binary_op("INT_SDIV", Expression.binary_op("INT_ADD", n_expr, one), two)
        n_odd = Expression.binary_op("INT_SDIV", n_expr, two)
        first_even = start_expr
        first_odd = Expression.binary_op("INT_ADD", start_expr, one)
    else:
        n_even = Expression.binary_op("INT_SDIV", n_expr, two)
        n_odd = Expression.binary_op("INT_SDIV", Expression.binary_op("INT_ADD", n_expr, one), two)
        first_even = Expression.binary_op("INT_ADD", start_expr, one)
        first_odd = start_expr
    for item in (n_even, n_odd, first_even, first_odd):
        item.size = size

    sum_even = self._build_arithmetic_progression_sum(first_even, n_even, size)
    sum_odd = self._build_arithmetic_progression_sum(first_odd, n_odd, size)
    contrib_terms: List[Expression] = []
    even_sum_term = self._scale_expression(sum_even, even_affine[0])
    odd_sum_term = self._scale_expression(sum_odd, odd_affine[0])
    if even_sum_term is not None:
        contrib_terms.append(even_sum_term)
    if odd_sum_term is not None:
        contrib_terms.append(odd_sum_term)
    even_count_term = self._scale_expression(n_even, even_affine[1])
    odd_count_term = self._scale_expression(n_odd, odd_affine[1])
    if even_count_term is not None:
        contrib_terms.append(even_count_term)
    if odd_count_term is not None:
        contrib_terms.append(odd_count_term)
    contrib = self._sum_expression_terms(contrib_terms)
    if contrib is None:
        return None
    total = Expression.binary_op("INT_ADD", base_expr, contrib)
    total.size = base_expr.size
    return total


def _impl__param_expr_placeholder(self, name: str, size: int) -> Expression:
    return Expression.parameter(name, size=size)


def _impl__expr_is_add_one_of_param(self, expr: Expression, param_name: str) -> bool:
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_ADD" or len(expr.operands) != 2:
        return False
    left_name = self._parameter_name_from_expr(expr.operands[0])
    right_name = self._parameter_name_from_expr(expr.operands[1])
    left_const = self._constant_value(expr.operands[0])
    right_const = self._constant_value(expr.operands[1])
    return (
        (left_name == param_name and right_const == 1)
        or (right_name == param_name and left_const == 1)
    )


def _impl__extract_counter_parity(
    self,
    conditions: Sequence[Condition],
    counter_name: str,
) -> Optional[bool]:
    for condition in conditions or []:
        expr = getattr(condition, "expression", None)
        if (
            expr is None
            or expr.expr_type != ExpressionType.BINARY_OP
            or expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}
            or len(expr.operands) != 2
        ):
            continue
        bitand = None
        parity_const = None
        if self._constant_value(expr.operands[0]) in {0, 1}:
            bitand = expr.operands[1]
            parity_const = self._constant_value(expr.operands[0])
        elif self._constant_value(expr.operands[1]) in {0, 1}:
            bitand = expr.operands[0]
            parity_const = self._constant_value(expr.operands[1])
        if bitand is None or parity_const is None:
            continue
        if bitand.expr_type != ExpressionType.BINARY_OP or bitand.operator != "INT_AND" or len(bitand.operands) != 2:
            continue
        if self._constant_value(bitand.operands[0]) == 1:
            counter_expr = bitand.operands[1]
        elif self._constant_value(bitand.operands[1]) == 1:
            counter_expr = bitand.operands[0]
        else:
            continue
        if self._parameter_name_from_expr(counter_expr) != counter_name:
            continue
        is_equal = expr.operator == "INT_EQUAL"
        if condition.negated:
            is_equal = not is_equal
        is_even = is_equal if parity_const == 0 else not is_equal
        return is_even
    return None


def _impl__iter_pcode_ops(self, high_function) -> Iterable:
    for basic_block in high_function.getBasicBlocks():
        pcode_iter = basic_block.getIterator()
        while pcode_iter.hasNext():
            yield pcode_iter.next()


def _impl__parameter_can_be_counter(self, param_info: dict) -> bool:
    size = int(param_info.get("size") or 0)
    if size not in {1, 2, 4, 8}:
        return False
    data_type_obj = param_info.get("data_type_obj")
    if data_type_obj is None:
        return True
    return is_integral_data_type(
        data_type_obj,
        param_info.get("data_type"),
        program=getattr(self.tracer, "program", None),
    )


def _impl__is_direct_self_call(self, op, function_name: str) -> bool:
    resolver = getattr(self.tracer, "resolve_call_target_ref", None)
    if not callable(resolver):
        return False
    target_ref = resolver(
        op.getInput(0),
        allow_containing=True,
        allow_code_address=False,
    )
    return bool(target_ref is not None and target_ref.function_name == function_name)


def _impl__constant_value(self, expr: Optional[Expression]) -> Optional[int]:
    raw = self._raw_constant_value(expr)
    if raw is None:
        return None
    return raw


def _impl__raw_constant_value(self, expr: Optional[Expression]) -> Optional[int]:
    if expr is None:
        return None
    if expr.expr_type == ExpressionType.CONSTANT:
        return int(expr.value)
    evaluated = eval_constant_raw(expr)
    if evaluated is None:
        return None
    return int(evaluated[0])


def _impl__signed_constant_value(
    self,
    expr: Optional[Expression],
    bit_width_hint: Optional[int] = None,
) -> Optional[int]:
    raw_value = self._raw_constant_value(expr)
    if raw_value is None:
        return None
    assert expr is not None
    bit_width = int(bit_width_hint or ((expr.size or 0) * 8))
    if bit_width <= 0:
        return raw_value
    modulus = 1 << bit_width
    signed = raw_value % modulus
    if signed >= (1 << (bit_width - 1)):
        signed -= modulus
    return signed


def _impl__extract_unit_step_from_call_argument(self, expr: Expression, param_name: str) -> Optional[int]:
    bit_width_hint = self._infer_counter_bit_width(expr, param_name)
    affine = self._extract_affine_term(expr, param_name, bit_width_hint=bit_width_hint)
    if affine is None:
        return None
    coeff, bias = affine
    if coeff != 1:
        return None
    if bias in {-1, 1}:
        return bias
    return None


def _impl__normalize_counter_view(
    self,
    expr: Optional[Expression],
    param_name: str,
) -> Optional[Tuple[Expression, Optional[int]]]:
    if expr is None:
        return None
    if expr.expr_type == ExpressionType.PARAMETER and expr.name == param_name:
        return expr, (expr.size * 8) if expr.size else None
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_ZEXT", "INT_SEXT"} and len(expr.operands) == 1:
        return self._normalize_counter_view(expr.operands[0], param_name)
    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "SUBPIECE" and len(expr.operands) == 2:
        source, offset = expr.operands
        offset_value = self._raw_constant_value(offset)
        if offset_value == 0:
            source_counter = self._normalize_counter_view(source, param_name)
            if source_counter is not None:
                expr_bits = (expr.size * 8) if expr.size else None
                if expr_bits is not None and expr_bits > 0:
                    return source_counter[0], expr_bits
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_AND" or len(expr.operands) != 2:
        return None

    left_counter = self._normalize_counter_view(expr.operands[0], param_name)
    right_counter = self._normalize_counter_view(expr.operands[1], param_name)
    left_const = self._raw_constant_value(expr.operands[0])
    right_const = self._raw_constant_value(expr.operands[1])

    if left_counter is not None and right_const is not None:
        mask_bits = self._bit_width_from_low_bit_mask(right_const)
        if mask_bits is not None:
            return left_counter[0], mask_bits
    if right_counter is not None and left_const is not None:
        mask_bits = self._bit_width_from_low_bit_mask(left_const)
        if mask_bits is not None:
            return right_counter[0], mask_bits
    return None


def _impl__infer_counter_bit_width(self, expr: Optional[Expression], param_name: str) -> Optional[int]:
    normalized = self._normalize_counter_view(expr, param_name)
    if normalized is not None:
        return normalized[1]
    if expr is None:
        return None
    for operand in expr.operands or []:
        operand_bit_width = self._infer_counter_bit_width(operand, param_name)
        if operand_bit_width is not None:
            return operand_bit_width
    return None


def _impl__bit_width_from_low_bit_mask(self, value: int) -> Optional[int]:
    if value <= 0:
        return None
    if (value & (value + 1)) != 0:
        return None
    bit_width = value.bit_length()
    if bit_width < 8 or bit_width % 8 != 0:
        return None
    return bit_width


def _impl__parameter_comparison_relation(self, condition: Condition) -> Optional[Tuple[str, str, str]]:
    expr = getattr(condition, "expression", None)
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None
    relation = self._comparison_to_relation(expr.operator, swapped=False)
    if relation is None:
        return None
    left_name = self._parameter_name_from_expr(expr.operands[0])
    right_name = self._parameter_name_from_expr(expr.operands[1])
    if not left_name or not right_name or left_name == right_name:
        return None
    if condition.negated:
        relation = self._negate_relation(relation)
        if relation is None:
            return None
    return left_name, relation, right_name


def _impl__matches_shifted_high_reconstruction(
    self,
    high_expr: Optional[Expression],
    low_expr: Optional[Expression],
    param_name: str,
) -> bool:
    low_counter = self._normalize_counter_view(low_expr, param_name)
    if low_counter is None:
        return False
    if high_expr is None:
        return False
    if high_expr.expr_type != ExpressionType.BINARY_OP or high_expr.operator != "INT_LEFT" or len(high_expr.operands) != 2:
        return False
    shift_bits = self._raw_constant_value(high_expr.operands[1])
    if shift_bits is None:
        return False
    low_bits = low_counter[1]
    if low_bits is None:
        return False
    return shift_bits == low_bits


def _impl__comparison_to_relation(self, operator: str, swapped: bool) -> Optional[str]:
    mapping = {
        "INT_SLESS": "<",
        "INT_SLESSEQUAL": "<=",
        "INT_LESS": "<",
        "INT_LESSEQUAL": "<=",
    }
    relation = mapping.get(operator)
    if relation is None:
        return None
    if not swapped:
        return relation
    if relation == "<":
        return ">"
    if relation == "<=":
        return ">="
    return None


def _impl__negate_relation(self, relation: str) -> Optional[str]:
    return {
        "<": ">=",
        "<=": ">",
        ">": "<=",
        ">=": "<",
    }.get(relation)


def _impl__build_closed_form(
    self,
    param_expr: Expression,
    lower_bound: int,
    coeff: int,
    bias: int,
    base_value: int,
) -> Optional[Expression]:
    size = param_expr.size or 4
    wide_size = self._summary_working_size(size)
    lower_const = Expression.constant(lower_bound, size)
    wide_param = self._zero_extend_bitpattern(param_expr, wide_size)
    wide_lower = self._zero_extend_bitpattern(lower_const, wide_size)
    shift_amount = Expression.constant(1, wide_size)

    triangular_n = self._triangular(wide_param, wide_size, shift_amount)
    if lower_bound == 0:
        triangular_delta = triangular_n
    else:
        triangular_lower = self._triangular(wide_lower, wide_size, shift_amount)
        triangular_delta = Expression.binary_op("INT_SUB", triangular_n, triangular_lower)
        triangular_delta.size = wide_size

    term_exprs: List[Expression] = []
    coeff_term = self._scale_term(triangular_delta, coeff, wide_size)
    if coeff_term is not None:
        term_exprs.append(coeff_term)
    if bias != 0:
        distance = Expression.binary_op("INT_SUB", wide_param, wide_lower)
        distance.size = wide_size
        bias_term = self._scale_term(distance, bias, wide_size)
        if bias_term is not None:
            term_exprs.append(bias_term)

    total = self._sum_terms(term_exprs, base_value, size, wide_size)
    return self._truncate_to_width(total, size)


def _impl__triangular(self, expr: Expression, size: int, shift_amount: Expression) -> Expression:
    one = Expression.constant(1, size)
    incremented = Expression.binary_op("INT_ADD", expr, one)
    incremented.size = size
    product = Expression.binary_op("INT_MULT", expr, incremented)
    product.size = size
    tri = Expression.binary_op("INT_RIGHT", product, shift_amount)
    tri.size = size
    return tri


def _impl__zero_extend_bitpattern(self, expr: Expression, target_size: int) -> Expression:
    source_size = expr.size or 0
    if source_size <= 0 or source_size >= target_size:
        copied = expr
        copied.size = max(source_size, target_size)
        if source_size > target_size:
            return self._truncate_to_width(copied, target_size)
        return copied
    widened = Expression.unary_op("INT_ZEXT", expr)
    widened.size = target_size
    return widened


def _impl__truncate_to_width(self, expr: Expression, target_size: int) -> Expression:
    if (expr.size or 0) <= target_size:
        expr.size = target_size
        return expr
    truncated = Expression.binary_op("SUBPIECE", expr, Expression.constant(0, 4))
    truncated.size = target_size
    return truncated


def _impl__scale_term(
    self,
    expr: Expression,
    factor: int,
    wide_size: int,
) -> Optional[Expression]:
    if factor == 0:
        return None
    if factor == 1:
        expr.size = wide_size
        return expr
    if factor == -1:
        negated = Expression.unary_op("INT_2COMP", expr)
        negated.size = wide_size
        return negated
    factor_const = self._zero_extend_bitpattern(Expression.constant(factor, expr.size or wide_size), wide_size)
    scaled = Expression.binary_op("INT_MULT", factor_const, expr)
    scaled.size = wide_size
    return scaled


def _impl__sum_terms(
    self,
    term_exprs: Sequence[Expression],
    base_value: int,
    size: int,
    wide_size: int,
) -> Expression:
    total: Optional[Expression] = None
    if base_value != 0:
        total = self._zero_extend_bitpattern(Expression.constant(base_value, size), wide_size)
    for term in term_exprs:
        if total is None:
            total = term
            continue
        total = Expression.binary_op("INT_ADD", total, term)
        total.size = wide_size
    if total is None:
        total = self._zero_extend_bitpattern(Expression.constant(0, size), wide_size)
    total.size = wide_size
    return total

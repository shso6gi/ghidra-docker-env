"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence.summarizer``."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    ReturnInfo,
)
from scripts.function_tracer_pcode.smt.interface import SolverStatus
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver
from scripts.function_tracer_pcode.analysis.recurrence._shared import (
    ConditionConstraintSet,
    ConditionNormalizer,
    ConditionSMTOracle,
    ConditionSimplifier,
    CountedLoopGuard,
    StateTransitionLoopModel,
    _runtime_conditions_signature,
    _runtime_expression_signature,
)
from scripts.function_tracer_pcode.analysis.debug import summarize_conditions

def _impl__condition_conjunction_unsat_with_solver(
    self,
    conditions: Sequence[Condition],
    *,
    timeout: int = 2,
) -> Optional[bool]:
    try:
        is_unsat = ConditionSMTOracle.conjunction_is_unsat(conditions)
    except Exception:
        is_unsat = None
    if is_unsat is True or is_unsat is False:
        return bool(is_unsat)
    try:
        usable, script = ConditionSMTOracle._build_script(conditions)
    except Exception:
        return None
    if not usable or not script:
        return None
    try:
        result = Z3Solver(timeout=timeout, debug=False).check_equivalence_direct(script)
    except Exception:
        return None
    if result.status == SolverStatus.UNSAT:
        return True
    if result.status == SolverStatus.SAT:
        return False
    return None

def _impl__positive_counter_conditions_for_return(
    self,
    conditions: Sequence[Condition],
    counter_param: dict,
    *,
    signed_counter_guard: bool = True,
) -> Optional[Tuple[Tuple[Condition, Expression], ...]]:
    positives: List[Tuple[Condition, Expression]] = []
    candidates = self._counter_guard_parameter_candidates(counter_param, conditions)
    if not candidates:
        return None
    operator = "INT_SLESS" if bool(signed_counter_guard) else "INT_LESS"
    for counter_expr in candidates:
        positive = Condition(
            Expression.binary_op(
                operator,
                Expression.constant(0, size=counter_expr.size or 4),
                counter_expr,
            ),
            False,
        )
        try:
            is_unsat = ConditionSMTOracle.conjunction_is_unsat(list(conditions) + [positive])
        except Exception:
            return None
        if is_unsat is False:
            positives.append((positive, counter_expr))
        elif is_unsat is not True:
            return None
    return tuple(positives)

def _impl__zero_base_guard_cover_for_positive_counter_guard(
    self,
    analysis,
    counter_param: dict,
    counter_expr: Expression,
    positive_guard: Condition,
) -> Optional[Condition]:
    zero_return_count = 0
    zero_guard_clauses: List[Expression] = []
    for ret in getattr(analysis, "returns", None) or ():
        if self._raw_constant_value(getattr(ret, "value", None)) != 0:
            continue
        zero_return_count += 1
        conditions = ConditionSimplifier.simplify_conditions_object_centric(
            self._normalize_counter_parameter_conditions(
                list(getattr(ret, "conditions", None) or []),
                counter_param,
                counter_expr,
            )
        )
        if ConditionSimplifier.object_centric_is_contradiction(conditions):
            continue
        clause = self._condition_clause_expression(conditions)
        if clause is not None:
            zero_guard_clauses.append(clause)
    if not zero_guard_clauses:
        self._debug(
            "Declined vectorized affine progression summary: zero base guard check failed "
            f"(zero_returns={zero_return_count}, zero_guard_clauses=0)"
        )
        return None
    covered_expr = zero_guard_clauses[0]
    for clause in zero_guard_clauses[1:]:
        covered_expr = Expression.binary_op("BOOL_OR", covered_expr, clause)
        covered_expr.size = 1
    base_guard = Condition(covered_expr, False)
    try:
        uncovered_is_unsat = ConditionSMTOracle.conjunction_is_unsat(
            [positive_guard.negate(), base_guard.negate()]
        )
    except Exception:
        uncovered_is_unsat = None
    if uncovered_is_unsat is True:
        return base_guard
    self._debug(
        "Declined vectorized affine progression summary: zero base guard check failed "
        f"(zero_returns={zero_return_count}, zero_guard_clauses={len(zero_guard_clauses)})"
    )
    return None

def _impl__nonzero_returns_are_disjoint_from_base_guard(
    self,
    analysis,
    base_guard: Condition,
    counter_param: Optional[dict] = None,
    counter_expr: Optional[Expression] = None,
) -> bool:
    for ret in getattr(analysis, "returns", None) or ():
        if self._raw_constant_value(getattr(ret, "value", None)) == 0:
            continue
        raw_conditions = list(getattr(ret, "conditions", None) or [])
        if counter_param is not None and counter_expr is not None:
            raw_conditions = self._normalize_counter_parameter_conditions(
                raw_conditions,
                counter_param,
                counter_expr,
            )
        conditions = ConditionSimplifier.simplify_conditions_object_centric(
            raw_conditions
        )
        if ConditionSimplifier.object_centric_is_contradiction(conditions):
            continue
        try:
            is_unsat = ConditionSMTOracle.conjunction_is_unsat(list(conditions) + [base_guard])
        except Exception:
            is_unsat = None
        if is_unsat is not True:
            if self._debug_available():
                self._debug(
                    "Declined vectorized affine progression summary: nonzero return/base overlap proof failed "
                    f"(branch_index={getattr(ret, 'branch_index', None)}, "
                    f"conditions={summarize_conditions(conditions)})"
                )
            return False
    return True

def _impl__normalize_counter_parameter_conditions(
    self,
    conditions: Sequence[Condition],
    counter_param: dict,
    counter_expr: Expression,
) -> List[Condition]:
    normalized: List[Condition] = []
    for condition in conditions or ():
        expr = self._normalize_counter_parameter_expression(
            getattr(condition, "expression", None),
            counter_param,
            counter_expr,
        )
        if expr is getattr(condition, "expression", None):
            normalized.append(condition)
        else:
            normalized.append(Condition(expr, bool(getattr(condition, "negated", False))))
    return normalized

def _impl__counter_guard_signedness_from_condition(
    self,
    condition: Condition,
    counter_candidates: Sequence[Expression],
) -> Optional[bool]:
    expr = getattr(condition, "expression", None)
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    operator = getattr(expr, "operator", None)
    if operator not in {"INT_LESS", "INT_SLESS"}:
        return None
    operands = list(getattr(expr, "operands", None) or [])
    if len(operands) != 2:
        return None
    left, right = operands
    mentions_counter = any(
        self._same_counter_expression(left, candidate)
        or self._same_counter_expression(right, candidate)
        for candidate in counter_candidates or ()
    )
    if not mentions_counter:
        return None
    left_const = self._raw_constant_value(left)
    right_const = self._raw_constant_value(right)
    if left_const not in {0, 1} and right_const not in {0, 1}:
        return None
    return operator == "INT_SLESS"

def _impl__condition_clause_expression(self, conditions: Sequence[Condition]) -> Optional[Expression]:
    if not conditions:
        return Expression.constant(1, size=1)
    combined = Condition.combine_and(list(conditions))
    if combined is None:
        return Expression.constant(1, size=1)
    if bool(getattr(combined, "negated", False)):
        expr = Expression.unary_op("BOOL_NEGATE", combined.expression)
        expr.size = 1
        return expr
    return combined.expression

def _impl__counter_guard_parameter_candidates(
    self,
    counter_param: dict,
    conditions: Sequence[Condition],
) -> Tuple[Expression, ...]:
    primary = self._parameter_expression(counter_param)
    return self._parameter_expression_candidates(
        counter_param,
        [getattr(condition, "expression", None) for condition in conditions or ()],
        include_primary=True,
        primary=primary,
    )

def _impl__condition_for_cbranch_op(self, op) -> Optional[Condition]:
    if op is None or self._safe_pcode_input_count(op) < 2:
        return None
    try:
        expr = self._build_pcode_expression(op.getInput(1), placeholders={})
    except RecursionError:
        return None
    if expr is None or self._expression_is_unresolved(expr):
        return None
    return Condition(expr, False)

def _impl__summary_guard_constraints_key(
    self,
    guard_constraints: Sequence[Condition],
) -> Tuple[Any, ...]:
    guards = tuple(guard_constraints or ())
    if not guards:
        return ("guard_constraints", ())
    try:
        return ("guard_constraints", _runtime_conditions_signature(guards))
    except Exception:
        keys = []
        for guard in guards:
            key_fn = getattr(guard, "structural_key", None)
            if not callable(key_fn):
                return ("guard_constraints", "unavailable", len(guards))
            try:
                keys.append(key_fn(budget=256))
            except Exception:
                return ("guard_constraints", "unavailable", len(guards))
        return ("guard_constraints", tuple(sorted(keys, key=repr)))

def _impl__conditions_overlap_conditions(
    self,
    left: Sequence[Condition],
    right: Sequence[Condition],
) -> bool:
    try:
        return ConditionSMTOracle.conjunction_is_unsat(
            list(left or ()) + list(right or ())
        ) is not True
    except Exception:
        return False

def _impl__return_value_equals_under_conditions(
    self,
    left: Optional[Expression],
    right: Expression,
    conditions: Sequence[Condition],
) -> bool:
    if left is None:
        return False
    left_constant = self._raw_constant_value(left)
    right_constant = self._raw_constant_value(right)
    if left_constant is not None and right_constant is not None:
        return int(left_constant) == int(right_constant)
    parameters = self._collect_summary_parameter_specs(
        left,
        right,
        *(condition.expression for condition in conditions or () if condition is not None),
    )
    if parameters is None:
        return False
    return self._prove_expression_equivalence_under_conditions(
        left,
        right,
        conditions,
        parameters,
    )

def _impl__summary_return_conditions_key(self, conditions: Sequence[Condition]) -> Tuple[Any, ...]:
    keys = []
    for condition in conditions or ():
        try:
            keys.append(condition.structural_key(budget=256))
        except Exception:
            keys.append(("opaque_condition", type(condition).__name__))
    keys.sort(key=repr)
    return ("conditions", tuple(keys))

def _impl__prove_summary_conditions_plus_exact_returns_cover_active_precondition(
    self,
    *,
    active_preconditions: Sequence[Condition] = (),
    summary_conditions: Sequence[Condition],
    exact_returns: Sequence[ReturnInfo],
    parameters: Optional[Sequence[dict]] = None,
) -> Optional[Tuple[Any, ...]]:
    normalized_active_preconditions = self._canonicalize_condition_parameters_for_analysis(
        active_preconditions,
        parameters,
    )
    normalized_summary_conditions = self._canonicalize_condition_parameters_for_analysis(
        summary_conditions,
        parameters,
    )
    summary_clause = Condition.combine_and(list(normalized_summary_conditions or ()))
    if summary_clause is None:
        return None
    disjuncts: List[Expression] = []
    summary_expr = summary_clause.expression
    if bool(getattr(summary_clause, "negated", False)):
        summary_expr = Expression.unary_op("BOOL_NEGATE", summary_expr)
        summary_expr.size = 1
    disjuncts.append(summary_expr)
    disjoint_returns: List[ReturnInfo] = []
    positive_param_key = self._positive_summary_parameter_key(normalized_summary_conditions)
    excluded_counter_values = self._summary_excluded_counter_values(
        normalized_summary_conditions,
        parameters,
    )
    for ret in exact_returns or ():
        normalized_return_conditions = self._canonicalize_condition_parameters_for_analysis(
            getattr(ret, "conditions", None) or (),
            parameters,
        )
        if not (
            self._conditions_are_disjoint_from_conditions(
                normalized_return_conditions,
                normalized_summary_conditions,
            )
            or (
                positive_param_key is not None
                and self._conditions_cover_nonpositive_parameter_region(
                    normalized_return_conditions,
                    positive_param_key,
                )
            )
            or self._conditions_cover_summary_excluded_counter_value(
                normalized_return_conditions,
                excluded_counter_values,
                parameters,
            )
        ):
            continue
        disjoint_returns.append(ret)
        combined = Condition.combine_and(list(normalized_return_conditions or []))
        if combined is None:
            return None
        expr = combined.expression
        if bool(getattr(combined, "negated", False)):
            expr = Expression.unary_op("BOOL_NEGATE", expr)
            expr.size = 1
        disjuncts.append(expr)
    covered_expr = disjuncts[0]
    for disjunct in disjuncts[1:]:
        covered_expr = Expression.binary_op("BOOL_OR", covered_expr, disjunct)
        covered_expr.size = 1
    miss_condition = Condition(covered_expr, True)
    try:
        miss_unsat = ConditionSMTOracle.conjunction_is_unsat(
            list(normalized_active_preconditions or ()) + [miss_condition]
        )
    except Exception:
        miss_unsat = None
    if miss_unsat is not True:
        if self._debug_available():
            self._debug(
                "Declined summary-region coverage proof: summary plus disjoint exact returns is not total "
                f"(disjoint_returns={len(disjoint_returns)}, status={miss_unsat}, "
                f"summary_conditions={summarize_conditions(normalized_summary_conditions or ())}, "
                f"exact_return_conditions={[summarize_conditions(self._canonicalize_condition_parameters_for_analysis(getattr(ret, 'conditions', None) or (), parameters)) for ret in exact_returns or ()]})"
            )
        return None
    return (
        "return_region_coverage",
        "summary_conditions_plus_exact_returns",
        _runtime_conditions_signature(tuple(normalized_active_preconditions or ())),
        _runtime_conditions_signature(tuple(normalized_summary_conditions or ())),
        tuple(
            _runtime_conditions_signature(
                tuple(
                    self._canonicalize_condition_parameters_for_analysis(
                        getattr(ret, "conditions", None) or (),
                        parameters,
                    )
                )
            )
            for ret in disjoint_returns
        ),
    )

def _impl__conditions_cover_summary_excluded_counter_value(
    self,
    conditions: Sequence[Condition],
    excluded_counter_values: Sequence[Tuple[Tuple[Any, ...], int]],
    parameters: Optional[Sequence[dict]] = None,
) -> bool:
    if not excluded_counter_values:
        return False
    for param_key, value in excluded_counter_values or ():
        if self._conditions_imply_counter_identity_value(conditions or (), param_key, int(value), parameters):
            return True
    return False

def _impl__conditions_imply_counter_identity_value(
    self,
    conditions: Sequence[Condition],
    param_key: Tuple[Any, ...],
    value: int,
    parameters: Optional[Sequence[dict]] = None,
) -> bool:
    for condition in conditions or ():
        expr = getattr(condition, "expression", None)
        if (
            getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP
            or len(getattr(expr, "operands", ()) or ()) != 2
        ):
            continue
        operator = getattr(expr, "operator", None)
        if bool(getattr(condition, "negated", False)):
            if operator != "INT_NOTEQUAL":
                continue
        elif operator != "INT_EQUAL":
            continue
        left, right = expr.operands
        left_const = self._constant_value(left)
        right_const = self._constant_value(right)
        if right_const is not None and int(right_const) == int(value):
            left_key = self._counter_parameter_identity_key(left, parameters)
            if left_key == param_key:
                return True
        if left_const is not None and int(left_const) == int(value):
            right_key = self._counter_parameter_identity_key(right, parameters)
            if right_key == param_key:
                return True
    return False

def _impl__canonicalize_condition_parameters_for_analysis(
    self,
    conditions: Sequence[Condition],
    parameters: Optional[Sequence[dict]],
) -> Tuple[Condition, ...]:
    if not parameters:
        return tuple(conditions or ())
    by_index: Dict[int, dict] = {}
    by_name = self._unique_parameters_by_name(parameters)
    for param in parameters or ():
        if not isinstance(param, dict):
            continue
        try:
            by_index[int(param.get("index"))] = param
        except (TypeError, ValueError):
            pass
    if not by_index and not by_name:
        return tuple(conditions or ())
    return tuple(
        Condition(
            self._canonicalize_expression_parameters_for_analysis(
                condition.expression,
                by_index=by_index,
                by_name=by_name,
            ),
            bool(getattr(condition, "negated", False)),
        )
        for condition in conditions or ()
        if condition is not None
    )

def _impl__conditions_overlap_for_analysis_parameters(
    self,
    left: Sequence[Condition],
    right: Sequence[Condition],
    parameters: Optional[Sequence[dict]],
) -> bool:
    normalized_left = self._canonicalize_condition_parameters_for_analysis(left, parameters)
    normalized_right = self._canonicalize_condition_parameters_for_analysis(right, parameters)
    try:
        return ConditionSMTOracle.conjunction_is_unsat(
            list(normalized_left or ()) + list(normalized_right or ())
        ) is not True
    except Exception:
        return self._conditions_overlap_conditions(normalized_left, normalized_right)

def _impl__return_conditions_are_disjoint_from_conditions(
    self,
    ret: ReturnInfo,
    conditions: Sequence[Condition],
) -> bool:
    return self._conditions_are_disjoint_from_conditions(
        getattr(ret, "conditions", None) or (),
        conditions,
    )

def _impl__conditions_are_disjoint_from_conditions(
    self,
    left: Sequence[Condition],
    right: Sequence[Condition],
) -> bool:
    try:
        return ConditionSMTOracle.conjunction_is_unsat(
            list(left or []) + list(right or ())
        ) is True
    except Exception:
        pass
    for left_condition in left or ():
        if left_condition is None:
            continue
        for right_condition in right or ():
            if right_condition is None:
                continue
            try:
                if (
                    left_condition.negate().equals(right_condition)
                    or right_condition.negate().equals(left_condition)
                    or ConditionNormalizer.are_equivalent(left_condition.negate(), right_condition)
                    or ConditionNormalizer.are_equivalent(right_condition.negate(), left_condition)
                ):
                    return True
            except Exception:
                continue
    return False

def _impl__analysis_active_preconditions(self, analysis) -> Tuple[Condition, ...]:
    preconditions = getattr(analysis, "active_function_preconditions", None)
    if preconditions is None:
        preconditions = getattr(analysis, "active_preconditions", None)
    return tuple(condition for condition in (preconditions or ()) if isinstance(condition, Condition))

def _impl__conditions_cover_nonpositive_parameter_region(
    self,
    conditions: Sequence[Condition],
    positive_param_key: Tuple[Any, ...],
) -> bool:
    for condition in conditions or ():
        expr = getattr(condition, "expression", None)
        if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
            continue
        if getattr(expr, "operator", None) not in {"INT_SLESS", "INT_LESS", "INT_SLESSEQUAL", "INT_LESSEQUAL"}:
            continue
        operands = list(getattr(expr, "operands", ()) or ())
        if len(operands) != 2:
            continue
        left, right = operands
        if bool(getattr(condition, "negated", False)):
            if _runtime_expression_signature(right) != positive_param_key:
                continue
            left_value = self._raw_constant_value(left)
            if left_value is None:
                continue
            operator = getattr(expr, "operator", None)
            if operator in {"INT_SLESS", "INT_LESS"} and int(left_value) == 0:
                return True
            if operator in {"INT_SLESSEQUAL", "INT_LESSEQUAL"} and int(left_value) == 1:
                return True
            continue
        if _runtime_expression_signature(left) != positive_param_key:
            continue
        right_value = self._raw_constant_value(right)
        if right_value is None:
            continue
        operator = getattr(expr, "operator", None)
        if operator in {"INT_SLESS", "INT_LESS"} and int(right_value) == 1:
            return True
        if operator in {"INT_SLESSEQUAL", "INT_LESSEQUAL"} and int(right_value) == 0:
            return True
    return False

def _impl__prove_return_conditions_cover_region(
    self,
    *,
    region_conditions: Sequence[Condition],
    returns: Sequence[ReturnInfo],
) -> Optional[Tuple[Any, ...]]:
    region_clause = Condition.combine_and(list(region_conditions or ()))
    if region_clause is None:
        return None
    disjuncts: List[Expression] = []
    for ret in returns or ():
        combined = Condition.combine_and(list(getattr(ret, "conditions", None) or []))
        if combined is None:
            return None
        expr = combined.expression
        if bool(getattr(combined, "negated", False)):
            expr = Expression.unary_op("BOOL_NEGATE", expr)
            expr.size = 1
        disjuncts.append(expr)
    if not disjuncts:
        return None
    covered_expr = disjuncts[0]
    for disjunct in disjuncts[1:]:
        covered_expr = Expression.binary_op("BOOL_OR", covered_expr, disjunct)
        covered_expr.size = 1
    miss_condition = Condition(covered_expr, True)
    try:
        miss_unsat = ConditionSMTOracle.conjunction_is_unsat(
            list(region_conditions or ()) + [miss_condition]
        )
    except Exception:
        miss_unsat = None
    if miss_unsat is not True:
        return None
    return (
        "return_region_coverage",
        _runtime_conditions_signature(tuple(region_conditions or ())),
        tuple(
            _runtime_conditions_signature(tuple(getattr(ret, "conditions", None) or ()))
            for ret in returns or ()
        ),
    )

def _impl__first_return_overlapping_conditions(
    self,
    returns: Sequence[ReturnInfo],
    conditions: Sequence[Condition],
) -> Optional[ReturnInfo]:
    for ret in returns or ():
        if self._return_overlaps_conditions(ret, conditions):
            return ret
    return None

def _impl__canonicalize_zero_value_under_conditions(
    self,
    expr: Expression,
    conditions: Sequence[Condition],
) -> Expression:
    if expr is None:
        return expr
    zero = Expression.constant(0, size=max(1, int(getattr(expr, "size", 0) or 4)))
    if expr.equals(zero):
        return expr
    parameters = self._collect_summary_parameter_specs(
        expr,
        *(condition.expression for condition in conditions or [] if condition is not None),
    )
    if not self._prove_expression_equivalence_under_conditions(
        expr,
        zero,
        conditions,
        parameters,
    ):
        return expr
    self._debug(
        "Canonicalized counted loop summary base to zero under case conditions "
        f"(original={self._safe_expr_text(expr)})"
    )
    return zero

def _impl__prove_expression_equivalence_under_conditions(
    self,
    left: Expression,
    right: Expression,
    conditions: Sequence[Condition],
    parameters: Optional[Sequence[dict]],
) -> bool:
    if left.equals(right):
        return True
    query = self._build_expression_equivalence_query(left, right, conditions, parameters)
    if not query:
        return False
    solver = Z3Solver(timeout=2, debug=self.debug)
    result = solver.check_equivalence_direct(query)
    return result.status == SolverStatus.UNSAT

def _impl__negate_simple_condition_set(
    self,
    conditions: Sequence[Condition],
) -> Optional[List[Condition]]:
    simplified = ConditionSimplifier.simplify_conditions_object_centric(list(conditions or []))
    if len(simplified) != 1:
        return None
    return ConditionSimplifier.simplify_conditions_object_centric([simplified[0].negate()])

def _impl__repair_two_way_partition_conditions(
    self,
    base_conditions: Sequence[Condition],
    continue_conditions: Sequence[Condition],
) -> Tuple[List[Condition], List[Condition]]:
    base_simplified = ConditionSimplifier.simplify_conditions_object_centric(list(base_conditions or []))
    continue_simplified = ConditionSimplifier.simplify_conditions_object_centric(list(continue_conditions or []))

    if not base_simplified and continue_simplified:
        negated_continue = self._negate_simple_condition_set(continue_simplified)
        if negated_continue is not None:
            base_simplified = negated_continue
    elif not continue_simplified and base_simplified:
        negated_base = self._negate_simple_condition_set(base_simplified)
        if negated_base is not None:
            continue_simplified = negated_base

    return base_simplified, continue_simplified

def _impl__two_way_condition_partition_is_total(
    self,
    base_conditions: Sequence[Condition],
    continue_conditions: Sequence[Condition],
) -> bool:
    base = ConditionSimplifier.simplify_conditions_object_centric(list(base_conditions or []))
    cont = ConditionSimplifier.simplify_conditions_object_centric(list(continue_conditions or []))
    if not base or not cont:
        return False
    try:
        overlap_unsat = ConditionSMTOracle.conjunction_is_unsat(list(base) + list(cont))
    except Exception:
        overlap_unsat = None
    if overlap_unsat is not True:
        return False
    base_clause = Condition.combine_and(list(base))
    cont_clause = Condition.combine_and(list(cont))
    if base_clause is None or cont_clause is None:
        return False
    base_expr = base_clause.expression
    if bool(getattr(base_clause, "negated", False)):
        base_expr = Expression.unary_op("BOOL_NEGATE", base_expr)
        base_expr.size = 1
    cont_expr = cont_clause.expression
    if bool(getattr(cont_clause, "negated", False)):
        cont_expr = Expression.unary_op("BOOL_NEGATE", cont_expr)
        cont_expr.size = 1
    disjunction = Expression.binary_op("BOOL_OR", base_expr, cont_expr)
    disjunction.size = 1
    try:
        coverage_unsat = ConditionSMTOracle.conjunction_is_unsat([Condition(disjunction, True)])
    except Exception:
        coverage_unsat = None
    return coverage_unsat is True

def _impl__condition_sets_equivalent(
    self,
    left_conditions: Sequence[Condition],
    right_conditions: Sequence[Condition],
) -> bool:
    left = ConditionSimplifier.simplify_conditions_object_centric(list(left_conditions or []))
    right = ConditionSimplifier.simplify_conditions_object_centric(list(right_conditions or []))
    left_clause = Condition.combine_and(list(left))
    right_clause = Condition.combine_and(list(right))
    if left_clause is None or right_clause is None:
        return False
    left_expr = left_clause.expression
    if bool(getattr(left_clause, "negated", False)):
        left_expr = Expression.unary_op("BOOL_NEGATE", left_expr)
        left_expr.size = 1
    right_expr = right_clause.expression
    if bool(getattr(right_clause, "negated", False)):
        right_expr = Expression.unary_op("BOOL_NEGATE", right_expr)
        right_expr.size = 1
    left_and_not_right = Expression.binary_op(
        "BOOL_AND",
        left_expr,
        Expression.unary_op("BOOL_NEGATE", right_expr),
    )
    left_and_not_right.size = 1
    right_and_not_left = Expression.binary_op(
        "BOOL_AND",
        right_expr,
        Expression.unary_op("BOOL_NEGATE", left_expr),
    )
    right_and_not_left.size = 1
    try:
        left_implies_right = ConditionSMTOracle.conjunction_is_unsat(
            [Condition(left_and_not_right, False)]
        )
        right_implies_left = ConditionSMTOracle.conjunction_is_unsat(
            [Condition(right_and_not_left, False)]
        )
    except Exception:
        return False
    return left_implies_right is True and right_implies_left is True

def _impl__common_conditions_across_paths(
    self,
    path_sets: Sequence[Sequence[Condition]],
) -> List[Condition]:
    if not path_sets:
        return []
    normalized_sets = [
        ConditionSimplifier.simplify_conditions_object_centric(list(conditions or []))
        for conditions in path_sets
    ]
    common = list(normalized_sets[0])
    for conditions in normalized_sets[1:]:
        condition_map = {
            _runtime_conditions_signature([condition]): condition
            for condition in conditions
        }
        common = [
            condition
            for condition in common
            if _runtime_conditions_signature([condition]) in condition_map
        ]
        if not common:
            break
    return ConditionSimplifier.simplify_conditions_object_centric(common)

def _impl__guard_handoff_key(
    self,
    *,
    prior_guard: CountedLoopGuard,
    current_guard: CountedLoopGuard,
    continue_conditions: Sequence[Condition],
) -> Optional[Tuple[Any, ...]]:
    prior_entry = prior_guard.entry_condition_expr or prior_guard.condition_expr
    current_entry = current_guard.entry_condition_expr or current_guard.condition_expr
    prior_continue = prior_guard.condition_expr
    current_continue = current_guard.condition_expr
    prior_entry_sig = _runtime_expression_signature(prior_entry)
    current_entry_sig = _runtime_expression_signature(current_entry)
    prior_continue_sig = _runtime_expression_signature(prior_continue)
    current_continue_sig = _runtime_expression_signature(current_continue)
    active_sig = _runtime_conditions_signature(tuple(continue_conditions or ()))
    if prior_entry_sig == current_entry_sig and prior_continue_sig == current_continue_sig:
        return (
            "guard_handoff_proof",
            "identical_guard_domain",
            prior_entry_sig,
            current_entry_sig,
            "proved",
            active_sig,
        )
    try:
        not_current_entry = Expression.unary_op("BOOL_NEGATE", current_entry)
        not_current_entry.size = 1
        implication_obligation = list(continue_conditions or ()) + [
            Condition(prior_continue, True),
            Condition(not_current_entry, False),
        ]
        implication_unsat = ConditionSMTOracle.conjunction_is_unsat(implication_obligation)
    except Exception:
        return None
    if implication_unsat is not True:
        return None
    return (
        "guard_handoff_proof",
        "smt_implication",
        prior_continue_sig,
        current_entry_sig,
        "proved",
        active_sig,
    )

def _impl__loop_block_guard_conditions(
    self,
    *,
    header_block,
    guard: CountedLoopGuard,
    loop_blocks: Sequence[object],
) -> Dict[object, Tuple[Condition, ...]]:
    return {
        block_key: tuple(info.get("common", ()))
        for block_key, info in self._loop_block_guard_effect_info(
            header_block=header_block,
            guard=guard,
            loop_blocks=loop_blocks,
        ).items()
    }

def _impl__loop_block_guard_effect_info(
    self,
    *,
    header_block,
    guard: CountedLoopGuard,
    loop_blocks: Sequence[object],
) -> Dict[object, Dict[str, Any]]:
    if guard is None or guard.body_block is None:
        return {}
    result: Dict[object, Dict[str, Any]] = {}
    header_key = self._block_key(header_block)
    body_key = self._block_key(guard.body_block)
    for block in loop_blocks or ():
        block_key = self._block_key(block)
        if block_key in {header_key, body_key}:
            result[block_key] = {
                "common": (),
                "paths": ((),),
                "incomplete": False,
            }
            continue
        paths, incomplete = self._enumerate_paths_with_conditions_result(
            start_block=guard.body_block,
            target_block=block,
            header_block=header_block,
            placeholders={},
            stop_block=guard.exit_block,
            limit=16,
        )
        if not paths:
            result[block_key] = {
                "common": (),
                "paths": (),
                "incomplete": incomplete,
            }
            continue
        result[block_key] = {
            "common": tuple(self._common_conditions_across_paths(paths)),
            "paths": tuple(tuple(path) for path in paths),
            "incomplete": incomplete,
        }
    return result

def _impl__enumerate_paths_with_conditions(
    self,
    *,
    start_block,
    target_block,
    header_block,
    placeholders: Dict[object, Expression],
    stop_block=None,
    limit: int = 8,
) -> List[List[Condition]]:
    paths, _incomplete = self._enumerate_paths_with_conditions_result(
        start_block=start_block,
        target_block=target_block,
        header_block=header_block,
        placeholders=placeholders,
        stop_block=stop_block,
        limit=limit,
    )
    return paths

def _impl__enumerate_paths_with_conditions_result(
    self,
    *,
    start_block,
    target_block,
    header_block,
    placeholders: Dict[object, Expression],
    stop_block=None,
    limit: int = 8,
) -> Tuple[List[List[Condition]], bool]:
    if start_block is None or target_block is None:
        return [[]], False
    target_key = self._block_key(target_block)
    header_key = self._block_key(header_block)
    stop_key = self._block_key(stop_block)
    paths: List[List[Condition]] = []
    incomplete = False

    def dfs(current, active_conditions: List[Condition], visited: set) -> None:
        nonlocal incomplete
        if len(paths) >= limit:
            incomplete = True
            return
        current_key = self._block_key(current)
        if current_key == target_key:
            paths.append(list(active_conditions))
            return
        if current_key == stop_key:
            return
        visited = set(visited)
        visited.add(current_key)
        for successor in self._collect_block_successors(current):
            successor_key = self._block_key(successor)
            if successor_key in visited or successor_key == header_key:
                continue
            branch_condition = self._build_block_edge_condition(
                current,
                successor,
                placeholders=placeholders,
            )
            next_conditions = list(active_conditions)
            if branch_condition is not None:
                next_conditions.append(branch_condition)
            dfs(successor, next_conditions, visited)

    dfs(start_block, [], set())
    return paths, incomplete

def _impl__build_block_edge_condition(
    self,
    block,
    successor,
    *,
    placeholders: Dict[object, Expression],
) -> Optional[Condition]:
    from scripts.function_tracer_pcode.analysis.recurrence.proof_utils import (
        _PcodeExpressionTraversalContext,
        _build_block_edge_condition_with_context,
    )

    return _build_block_edge_condition_with_context(
        self,
        block,
        successor,
        placeholders=placeholders,
        context=_PcodeExpressionTraversalContext(),
    )

def _impl__normalize_loop_continue_guard(
    self,
    raw_expr: Expression,
    counter_placeholder: Expression,
    body_on_true: bool,
    step: int,
) -> Optional[Tuple[Expression, Expression, Expression, bool]]:
    counter_name = counter_placeholder.name or "__loop_iv"
    parsed = self._parse_counter_comparison(raw_expr, counter_name)
    if parsed is None:
        return None
    relation, other_expr, signed = parsed
    if not self._is_counted_loop_bound_expr(other_expr):
        return None
    if not body_on_true:
        relation = {
            "<": ">=",
            "<=": ">",
            ">": "<=",
            ">=": "<",
        }.get(relation)
    if step > 0:
        entry_relation = relation
        entry_bound_expr = other_expr
        if relation == "<=":
            other_expr = self._adjust_loop_bound_for_strict_relation(other_expr, +1)
            relation = "<"
        if relation != "<":
            return None
        operator = "INT_SLESS" if signed else "INT_LESS"
        condition_expr = Expression.binary_op(operator, counter_placeholder, other_expr)
        condition_expr.size = 1
        entry_operator = operator if entry_relation == "<" else ("INT_SLESSEQUAL" if signed else "INT_LESSEQUAL")
        entry_condition_expr = Expression.binary_op(entry_operator, counter_placeholder, entry_bound_expr)
        entry_condition_expr.size = 1
        return condition_expr, entry_condition_expr, other_expr, signed

    entry_relation = relation
    entry_bound_expr = other_expr
    if relation == ">=":
        other_expr = self._adjust_loop_bound_for_strict_relation(other_expr, -1)
        relation = ">"
    if relation != ">":
        return None
    operator = "INT_SLESS" if signed else "INT_LESS"
    condition_expr = Expression.binary_op(operator, other_expr, counter_placeholder)
    condition_expr.size = 1
    entry_operator = operator if entry_relation == ">" else ("INT_SLESSEQUAL" if signed else "INT_LESSEQUAL")
    entry_condition_expr = Expression.binary_op(entry_operator, entry_bound_expr, counter_placeholder)
    entry_condition_expr.size = 1
    return condition_expr, entry_condition_expr, other_expr, signed

def _impl__normalize_latch_continue_guard(
    self,
    raw_expr: Expression,
    counter_placeholder: Expression,
    continue_on_true: bool,
    step: int,
) -> Optional[Tuple[Expression, Expression, Expression, bool]]:
    counter_name = counter_placeholder.name or "__loop_iv"
    if raw_expr.expr_type != ExpressionType.BINARY_OP or len(raw_expr.operands) != 2:
        return None
    operator = raw_expr.operator
    left, right = raw_expr.operands

    counter_side = None
    bound_expr = None
    signed = operator.startswith("INT_S")
    affine_left = self._extract_affine_term(left, counter_name)
    affine_right = self._extract_affine_term(right, counter_name)
    if affine_left is not None and affine_left[0] == 1 and affine_right is None:
        counter_side = "left"
        bound_expr = right
        bias = affine_left[1]
    elif affine_right is not None and affine_right[0] == 1 and affine_left is None:
        counter_side = "right"
        bound_expr = left
        bias = affine_right[1]
    else:
        return None

    if bias != abs(step):
        return None
    if not self._is_counted_loop_bound_expr(bound_expr):
        return None

    continue_when_equal = operator == "INT_EQUAL"
    if raw_expr.operator not in {"INT_EQUAL", "INT_NOTEQUAL"}:
        return None
    keep_looping = continue_when_equal if continue_on_true else not continue_when_equal
    if keep_looping:
        return None

    compare_op = "INT_SLESS" if signed else "INT_LESS"
    if step > 0:
        condition_expr = Expression.binary_op(compare_op, counter_placeholder, bound_expr)
    else:
        condition_expr = Expression.binary_op(compare_op, bound_expr, counter_placeholder)
    condition_expr.size = 1
    entry_op = "INT_NOTEQUAL" if counter_side == "left" else "INT_NOTEQUAL"
    entry_condition_expr = Expression.binary_op(entry_op, counter_placeholder, bound_expr)
    entry_condition_expr.size = 1
    return condition_expr, entry_condition_expr, bound_expr, signed

def _impl__condition_mentions_counter(
    self,
    condition: Condition,
    counter_name: str,
) -> bool:
    expr = getattr(condition, "expression", None)
    if expr is None:
        return False
    return any(
        self._expr_matches_counter_placeholder(node, counter_name)
        for node in self._iter_expression_nodes(expr)
    )

def _impl__progress_guarded_unit_entry_guard_expression(
    self,
    *,
    model: StateTransitionLoopModel,
    progress_guard_expr: Expression,
    analysis,
) -> Optional[Expression]:
    if self._state_guard_proves_signed_positive_placeholder(
        model.state_guard_expr,
        model.state_placeholder,
    ):
        return self._positive_state_init_guard_expression(model)
    if not self._state_guard_is_positive_after_progress_step(
        model.state_guard_expr,
        model.state_placeholder,
        progress_guard_expr,
    ):
        return None
    positive_entry_guard = self._positive_state_init_guard_expression(model)
    if positive_entry_guard is None:
        return None
    if not self._progress_guarded_stop_one_anchor_is_proved(
        analysis=analysis,
        model=model,
        positive_entry_guard=positive_entry_guard,
        progress_guard_expr=progress_guard_expr,
    ):
        return None
    return positive_entry_guard

def _impl__positive_state_init_guard_expression(
    self,
    model: StateTransitionLoopModel,
) -> Optional[Expression]:
    positive_guard = self._positive_state_guard_expression(model.state_placeholder)
    entry_guard = self._substitute_exact_expression(
        positive_guard,
        model.state_placeholder,
        model.state_init_expr,
    )
    if entry_guard is None or self._expression_is_unresolved(entry_guard):
        return None
    return self._canonicalize_expression(entry_guard)

def _impl__state_guard_is_positive_after_progress_step(
    self,
    state_guard: Optional[Expression],
    state_placeholder: Expression,
    progress_guard_expr: Expression,
) -> bool:
    if state_guard is None or getattr(state_guard, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    if getattr(state_guard, "operator", None) != "INT_SLESS":
        return False
    operands = tuple(getattr(state_guard, "operands", ()) or ())
    if len(operands) != 2 or self._raw_constant_value(operands[0]) != 0:
        return False
    right = operands[1]
    if getattr(right, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    if getattr(right, "operator", None) != "INT_SUB":
        return False
    right_operands = tuple(getattr(right, "operands", ()) or ())
    if len(right_operands) != 2:
        return False
    return (
        self._expressions_have_same_structural_key(right_operands[0], state_placeholder)
        and self._expressions_have_same_structural_key(right_operands[1], progress_guard_expr)
    )

def _impl__progress_guarded_stop_one_anchor_is_proved(
    self,
    *,
    analysis,
    model: StateTransitionLoopModel,
    positive_entry_guard: Expression,
    progress_guard_expr: Expression,
) -> bool:
    if analysis is None:
        return False
    entry_continue_guard = self._substitute_exact_expression(
        model.state_guard_expr,
        model.state_placeholder,
        model.state_init_expr,
    )
    if entry_continue_guard is None or self._expression_is_unresolved(entry_continue_guard):
        return False
    anchor_region = (
        Condition(positive_entry_guard, False),
        Condition(progress_guard_expr, False),
        Condition(self._canonicalize_expression(entry_continue_guard), True),
    )
    for ret in getattr(analysis, "returns", ()) or ():
        ret_conditions = tuple(getattr(ret, "conditions", ()) or ())
        if not self._conditions_equivalent_object_centric(ret_conditions, anchor_region):
            continue
        if self._return_value_equals_under_conditions(
            getattr(ret, "value", None),
            model.state_init_expr,
            ret_conditions + anchor_region,
        ):
            return True
    return False

def _impl__progress_guarded_unit_step_expression(
    self,
    model: StateTransitionLoopModel,
) -> Optional[Expression]:
    transition = getattr(model, "state_transition_expr", None)
    if transition is None or getattr(transition, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    if getattr(transition, "operator", None) != "INT_SUB":
        return None
    operands = tuple(getattr(transition, "operands", ()) or ())
    if len(operands) != 2:
        return None
    state_expr, step_expr = operands
    if not self._expressions_have_same_structural_key(state_expr, model.state_placeholder):
        return None
    if self._expression_mentions_placeholder(step_expr, model.state_placeholder):
        return None
    if self._expression_mentions_placeholder(step_expr, model.accumulator_placeholder):
        return None
    accumulator_delta = getattr(model, "accumulator_delta_expr", None)
    if not self._expressions_have_same_structural_key(accumulator_delta, step_expr):
        return None
    if not self._expression_is_boolean_condition_value(step_expr):
        return None
    return self._canonicalize_expression(step_expr)

def _impl__expression_is_boolean_condition_value(self, expr: Optional[Expression]) -> bool:
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    if int(getattr(expr, "size", 0) or 1) != 1:
        return False
    return getattr(expr, "operator", None) in {
        "INT_EQUAL",
        "INT_NOTEQUAL",
        "INT_LESS",
        "INT_SLESS",
        "INT_LESSEQUAL",
        "INT_SLESSEQUAL",
        "BOOL_AND",
        "BOOL_OR",
        "BOOL_XOR",
    }

def _impl__negated_return_region_condition(
    self,
    conditions: Sequence[Condition],
) -> Optional[Condition]:
    region_expr = None
    for condition in conditions or ():
        expr = getattr(condition, "expression", None)
        if expr is None:
            return None
        if getattr(condition, "negated", False):
            expr = Expression.unary_op("BOOL_NEGATE", expr)
            expr.size = 1
        region_expr = expr if region_expr is None else Expression.binary_op("BOOL_AND", region_expr, expr)
        region_expr.size = 1
    if region_expr is None:
        return None
    negated = Expression.unary_op("BOOL_NEGATE", self._canonicalize_expression(region_expr))
    negated.size = 1
    return Condition(self._canonicalize_expression(negated), False)

def _impl__state_guard_is_placeholder_not_equal_one(
    self,
    state_guard: Optional[Expression],
    state_placeholder: Expression,
) -> bool:
    guard = self._canonicalize_expression(state_guard)
    if guard is None or guard.expr_type != ExpressionType.BINARY_OP or len(guard.operands) != 2:
        return False
    if guard.operator != "INT_NOTEQUAL":
        return False
    return self._binary_comparison_matches_affine_constant(
        guard,
        state_placeholder,
        coeff=1,
        bias=-1,
        constant=0,
    ) or self._binary_comparison_matches_affine_constant(
        guard,
        state_placeholder,
        coeff=1,
        bias=0,
        constant=1,
    )

def _impl__conditions_include_positive_state(
    self,
    conditions: Sequence[Condition],
    state_expr: Expression,
) -> bool:
    return any(self._condition_is_positive_state(condition, state_expr) for condition in conditions or ())

def _impl__conditions_include_nonpositive_state(
    self,
    conditions: Sequence[Condition],
    state_expr: Expression,
) -> bool:
    return any(self._condition_is_nonpositive_state(condition, state_expr) for condition in conditions or ())

def _impl__conditions_include_state_equals_one(
    self,
    conditions: Sequence[Condition],
    state_expr: Expression,
) -> bool:
    return any(self._condition_is_state_equals_one(condition, state_expr) for condition in conditions or ())

def _impl__condition_is_positive_state(
    self,
    condition: Condition,
    state_expr: Expression,
) -> bool:
    expr = self._canonicalize_expression(getattr(condition, "expression", None))
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return False
    if bool(getattr(condition, "negated", False)):
        return False
    if expr.operator == "INT_SLESS":
        left, right = expr.operands
        return self._raw_constant_value(left) == 0 and self._expr_matches_placeholder(right, state_expr)
    if expr.operator == "INT_SLESSEQUAL":
        left, right = expr.operands
        return self._raw_constant_value(left) == 1 and self._expr_matches_placeholder(right, state_expr)
    return False

def _impl__condition_is_nonpositive_state(
    self,
    condition: Condition,
    state_expr: Expression,
) -> bool:
    expr = self._canonicalize_expression(getattr(condition, "expression", None))
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return False
    negated = bool(getattr(condition, "negated", False))
    left, right = expr.operands
    if not negated and expr.operator == "INT_SLESSEQUAL":
        return self._expr_matches_placeholder(left, state_expr) and self._raw_constant_value(right) == 0
    if not negated and expr.operator == "INT_SLESS":
        return self._expr_matches_placeholder(left, state_expr) and self._raw_constant_value(right) == 1
    if negated and expr.operator == "INT_SLESS":
        return self._raw_constant_value(left) == 0 and self._expr_matches_placeholder(right, state_expr)
    return False

def _impl__condition_is_state_equals_one(
    self,
    condition: Condition,
    state_expr: Expression,
) -> bool:
    expr = self._canonicalize_expression(getattr(condition, "expression", None))
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return False
    negated = bool(getattr(condition, "negated", False))
    if expr.operator == "INT_EQUAL" and not negated:
        return self._binary_comparison_matches_affine_constant(
            expr,
            state_expr,
            coeff=1,
            bias=0,
            constant=1,
        ) or self._binary_comparison_matches_affine_constant(
            expr,
            state_expr,
            coeff=1,
            bias=-1,
            constant=0,
        )
    if expr.operator == "INT_NOTEQUAL" and negated:
        return self._binary_comparison_matches_affine_constant(
            expr,
            state_expr,
            coeff=1,
            bias=0,
            constant=1,
        ) or self._binary_comparison_matches_affine_constant(
            expr,
            state_expr,
            coeff=1,
            bias=-1,
            constant=0,
        )
    return False

def _impl__condition_term_to_expression(self, expr: Expression, negated: bool) -> Expression:
    expr = self._canonicalize_expression(expr)
    if not negated:
        return expr
    result = Expression.unary_op("BOOL_NEGATE", expr)
    result.size = 1
    return self._canonicalize_expression(result)

def _impl__state_guard_proves_signed_positive_placeholder(
    self,
    state_guard: Optional[Expression],
    state_placeholder: Expression,
) -> bool:
    guard = self._canonicalize_expression(state_guard)
    if guard is None or guard.expr_type != ExpressionType.BINARY_OP or len(guard.operands) != 2:
        return False
    left, right = guard.operands
    placeholder_key = state_placeholder.structural_key()

    def is_placeholder(value: Expression) -> bool:
        try:
            return value.structural_key() == placeholder_key
        except (AttributeError, TypeError, ValueError, RecursionError):
            return False

    if guard.operator == "INT_SLESS":
        return self._raw_constant_value(left) == 0 and is_placeholder(right)
    if guard.operator == "INT_SLESSEQUAL":
        return self._raw_constant_value(left) == 1 and is_placeholder(right)
    return False

def _impl__positive_state_guard_expression(self, state_placeholder: Expression) -> Expression:
    zero = Expression.constant(0, max(1, int(getattr(state_placeholder, "size", 0) or 4)))
    guard = Expression.binary_op("INT_SLESS", zero, state_placeholder)
    guard.size = 1
    return self._canonicalize_expression(guard)

def _impl__conditions_equivalent_object_centric(
    self,
    left: Sequence[Condition],
    right: Sequence[Condition],
) -> bool:
    left_set = ConditionConstraintSet.from_conditions(left or [])
    right_set = ConditionConstraintSet.from_conditions(right or [])
    if left_set.implies_all(right or []) and right_set.implies_all(left or []):
        return True
    return self._conditions_imply_with_smt(left or [], right or []) and self._conditions_imply_with_smt(
        right or [],
        left or [],
    )

def _impl__conditions_imply_with_smt(
    self,
    source: Sequence[Condition],
    target: Sequence[Condition],
) -> bool:
    for condition in target or []:
        unsat = ConditionSMTOracle.conjunction_is_unsat(
            list(source or []) + [condition.negate()]
        )
        if unsat is not True:
            return False
    return True

def _impl__bounded_prefix_region_conditions_from_exact_anchor(
    self,
    conditions: Sequence[Condition],
    count_param: dict,
    *,
    exact_count: int,
    upper_bound: int,
) -> Optional[List[Condition]]:
    """Recover the bounded prefix region around an exact materialized witness.

    Some compilers expose only one exact return from a bounded prefix loop
    after PHI expansion, e.g. count==1 under 0<count<4.  The exact-count
    predicate is a witness selector, not part of the enclosing bounded
    region.  Drop only object-identified singleton counter predicates for
    the same count, then require SMT satisfiability for every synthesized
    count.  This keeps non-counter guards and non-singleton counter bounds
    intact.
    """

    if upper_bound <= 0 or exact_count <= 0 or exact_count > upper_bound:
        return None
    count_name = str(count_param.get("name") or "")
    if not count_name:
        return None
    retained: List[Condition] = []
    dropped_singleton = False
    for condition in ConditionSimplifier.simplify_conditions_object_centric(list(conditions or [])):
        if (
            self._condition_references_only_counter_parameter(condition, count_name)
            and self._exact_counter_value_from_conditions([condition], count_name) == int(exact_count)
        ):
            dropped_singleton = True
            continue
        retained.append(condition)
    if not dropped_singleton:
        return None
    retained = ConditionSimplifier.simplify_conditions_object_centric(retained)
    for count_value in range(1, int(upper_bound) + 1):
        if not self._conditions_allow_counter_value(retained, count_param, int(count_value)):
            return None
    return retained

def _impl__condition_references_only_counter_parameter(
    self,
    condition: Optional[Condition],
    param_name: str,
) -> bool:
    expr = getattr(condition, "expression", None)
    if expr is None or not param_name:
        return False
    saw_counter = False
    for node in self._iter_expression_nodes(expr):
        if getattr(node, "expr_type", None) != ExpressionType.PARAMETER:
            continue
        if getattr(node, "name", None) != param_name:
            return False
        saw_counter = True
    return saw_counter

def _impl__infer_upper_bound_from_conditions(
    self,
    conditions: Sequence[Condition],
    param_name: str,
) -> Optional[int]:
    upper_bounds: List[int] = []
    for condition in conditions or []:
        relation = self._condition_relation(condition, param_name)
        if relation is None:
            continue
        relation_name, constant = relation
        if relation_name == "<=":
            upper_bounds.append(int(constant))
        elif relation_name == "<":
            upper_bounds.append(int(constant) - 1)
    if not upper_bounds:
        return None
    return min(upper_bounds)

def _impl__counter_singleton_region_covers_return_conditions(
    self,
    conditions: Sequence[Condition],
    count_param: dict,
    exact_count: int,
) -> bool:
    count_name = str(count_param.get("name") or "")
    if not count_name or exact_count <= 0:
        return False
    equality = self._counter_equality_condition(count_param, int(exact_count))
    for condition in conditions or []:
        if not self._condition_references_only_counter_parameter(condition, count_name):
            return False
        singleton = self._exact_counter_value_from_conditions([condition], count_name)
        if singleton is not None:
            if int(singleton) != int(exact_count):
                return False
            continue
        relation = self._condition_relation(condition, count_name)
        if relation is not None:
            relation_name, constant = relation
            if self._counter_value_satisfies_relation(int(exact_count), relation_name, int(constant)):
                continue
            return False
        solver_unsat = ConditionSMTOracle.conjunction_is_unsat(
            [equality, condition.negate()]
        )
        if solver_unsat is True:
            continue
        return False
    return True

def _impl__return_overlaps_conditions(
    self,
    ret: ReturnInfo,
    conditions: Sequence[Condition],
) -> bool:
    ret_constraint_set = ConditionConstraintSet.from_conditions(ret.conditions or [])
    return ret_constraint_set.overlaps_with(conditions or [])

def _impl__return_conditions_imply_conditions(
    self,
    ret: ReturnInfo,
    conditions: Sequence[Condition],
) -> bool:
    return ConditionConstraintSet.from_conditions(ret.conditions or []).implies_all(
        conditions or []
    )

def _impl__analysis_mentions_parameter_in_conditions(
    self,
    analysis,
    param_name: str,
) -> bool:
    if not param_name:
        return False
    for ret in analysis.returns or []:
        for condition in ret.conditions or []:
            relation = self._condition_relation(condition, param_name)
            if relation is not None:
                return True
            relation = self._parameter_comparison_relation(condition)
            if relation is not None and param_name in relation[:3:2]:
                return True
    return False

def _impl__conditions_imply_counter_value(
    self,
    conditions: Sequence[Condition],
    count_param: dict,
    count_value: int,
) -> bool:
    equality = self._counter_equality_condition(count_param, count_value)
    constraint_set = ConditionConstraintSet.from_conditions(conditions or [])
    if constraint_set.implies_condition(equality):
        return True
    solver_unsat = ConditionSMTOracle.conjunction_is_unsat(
        list(conditions or []) + [equality.negate()]
    )
    return bool(solver_unsat) if solver_unsat is not None else False

def _impl__conditions_allow_counter_value(
    self,
    conditions: Sequence[Condition],
    count_param: dict,
    count_value: int,
) -> bool:
    equality = self._counter_equality_condition(count_param, count_value)
    constraint_set = ConditionConstraintSet.from_conditions(conditions or [])
    if not constraint_set.overlaps_with([equality]):
        solver_unsat = ConditionSMTOracle.conjunction_is_unsat(
            list(conditions or []) + [equality]
        )
        return bool(solver_unsat is False)
    return True

def _impl__counter_equality_condition(
    self,
    count_param: dict,
    count_value: int,
) -> Condition:
    count_expr = self._parameter_expression(count_param)
    return Condition(
        Expression.binary_op(
            "INT_EQUAL",
            count_expr,
            Expression.constant(int(count_value), count_expr.size or 4),
        ),
        False,
    )

def _impl__condition_is_less(self, condition: Condition, start_name: str, limit_name: str) -> bool:
    relation = self._parameter_comparison_relation(condition)
    if relation is None:
        return False
    left_name, relation_name, right_name = relation
    return (
        (left_name == start_name and right_name == limit_name and relation_name == "<")
        or (left_name == limit_name and right_name == start_name and relation_name == ">")
    )

def _impl__condition_is_not_less(self, condition: Condition, start_name: str, limit_name: str) -> bool:
    relation = self._parameter_comparison_relation(condition)
    if relation is None:
        return False
    left_name, relation_name, right_name = relation
    return (
        (left_name == start_name and right_name == limit_name and relation_name == ">=")
        or (left_name == limit_name and right_name == start_name and relation_name == "<=")
    )

def _impl__condition_is_step_equality(self, condition: Condition, start_name: str, limit_name: str) -> bool:
    expr = getattr(condition, "expression", None)
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_EQUAL" or len(expr.operands) != 2:
        return False
    left_name = self._parameter_name_from_expr(expr.operands[0])
    right_name = self._parameter_name_from_expr(expr.operands[1])
    if left_name == limit_name and self._expr_is_add_one_of_param(expr.operands[1], start_name):
        return not condition.negated
    if right_name == limit_name and self._expr_is_add_one_of_param(expr.operands[0], start_name):
        return not condition.negated
    return False

def _impl__infer_lower_bound_from_conditions(self, conditions: Sequence[Condition], param_name: str) -> Optional[int]:
    lower_bounds: List[int] = []
    for condition in conditions or []:
        relation = self._condition_relation(condition, param_name)
        if relation is None:
            continue
        relation_name, constant = relation
        if relation_name == ">":
            lower_bounds.append(constant)
        elif relation_name == ">=":
            lower_bounds.append(constant - 1)
    if not lower_bounds:
        return None
    return max(lower_bounds)

def _impl__infer_lower_bound_from_base_conditions(self, conditions: Sequence[Condition], param_name: str) -> Optional[int]:
    upper_bounds: List[int] = []
    for condition in conditions or []:
        relation = self._condition_relation(condition, param_name)
        if relation is None:
            continue
        relation_name, constant = relation
        if relation_name == "<=":
            upper_bounds.append(constant)
        elif relation_name == "<":
            upper_bounds.append(constant - 1)
    if not upper_bounds:
        return None
    return min(upper_bounds)

def _impl__condition_relation(self, condition: Condition, param_name: str) -> Optional[Tuple[str, int]]:
    expr = getattr(condition, "expression", None)
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None
    left, right = expr.operands
    right_const = self._constant_value(right)
    left_const = self._constant_value(left)

    op = expr.operator
    relation: Optional[str] = None

    if self._is_condition_counter_view(left, param_name) and right_const is not None:
        relation = self._comparison_to_relation(op, swapped=False)
        constant = right_const
    elif self._is_condition_counter_view(right, param_name) and left_const is not None:
        relation = self._comparison_to_relation(op, swapped=True)
        constant = left_const
    else:
        return None

    if relation is None:
        return None
    if condition.negated:
        relation = self._negate_relation(relation)
        if relation is None:
            return None
    return relation, constant

def _impl__exact_counter_value_from_conditions(
    self,
    conditions: Sequence[Condition],
    param_name: str,
) -> Optional[int]:
    lower_bounds: List[int] = []
    upper_bounds: List[int] = []
    for condition in conditions or []:
        expr = getattr(condition, "expression", None)
        if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            relation = self._condition_relation(condition, param_name)
            if relation is None:
                continue
            relation_name, constant = relation
        else:
            operator = getattr(expr, "operator", None)
            left, right = expr.operands
            right_const = self._constant_value(right)
            left_const = self._constant_value(left)
            if self._is_condition_counter_view(left, param_name) and right_const is not None:
                if operator == "INT_EQUAL" and not condition.negated:
                    return right_const
                if operator == "INT_NOTEQUAL" and condition.negated:
                    return right_const
            if self._is_condition_counter_view(right, param_name) and left_const is not None:
                if operator == "INT_EQUAL" and not condition.negated:
                    return left_const
                if operator == "INT_NOTEQUAL" and condition.negated:
                    return left_const
            affine_left = self._solve_counter_affine_equality(left, right_const, operator, condition.negated, param_name)
            if affine_left is not None:
                return affine_left
            affine_right = self._solve_counter_affine_equality(right, left_const, operator, condition.negated, param_name)
            if affine_right is not None:
                return affine_right
            relation = self._condition_relation(condition, param_name)
            if relation is None:
                continue
            relation_name, constant = relation

        if relation_name == ">":
            lower_bounds.append(constant + 1)
        elif relation_name == ">=":
            lower_bounds.append(constant)
        elif relation_name == "<":
            upper_bounds.append(constant - 1)
        elif relation_name == "<=":
            upper_bounds.append(constant)
    if not lower_bounds or not upper_bounds:
        return None
    exact_lower = max(lower_bounds)
    exact_upper = min(upper_bounds)
    if exact_lower == exact_upper:
        return exact_lower
    return None

def _impl__is_condition_counter_view(self, expr: Optional[Expression], param_name: str) -> bool:
    if expr is None:
        return False
    if self._normalize_counter_view(expr, param_name) is not None:
        return True
    if expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "PIECE" and len(expr.operands) == 2:
        return self._normalize_counter_view(expr.operands[1], param_name) is not None
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator not in {"INT_OR", "INT_ADD"} or len(expr.operands) != 2:
        return False
    left, right = expr.operands
    return self._matches_shifted_high_reconstruction(left, right, param_name) or self._matches_shifted_high_reconstruction(right, left, param_name)

def _impl__build_base_conditions(self, param_expr: Expression, lower_bound: int) -> Optional[List[Condition]]:
    size = param_expr.size or 4
    lower_const = Expression.constant(lower_bound, size)
    cond_expr = Expression.binary_op("INT_SLESSEQUAL", param_expr, lower_const)
    return [Condition(cond_expr, False)]

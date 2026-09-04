"""Case condition algebra: unsat/implication checks, parameter equality and affine forms, comparison widths."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.core import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.render_smt import expression_smt_bit_width
from scripts.function_tracer_pcode.smt import SolverStatus
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver
from scripts.function_tracer_pcode.proof.strategies.pairwise_services._shared import (
    ConditionSMTOracle,
    ConditionSimplifier,
    ReturnCase,
)


def _impl__case_pair_comparison_result_size(
    self,
    left_case: Optional[ReturnCase],
    right_case: Optional[ReturnCase],
) -> Optional[int]:
    left_bits = self._case_comparison_bit_width(left_case)
    right_bits = self._case_comparison_bit_width(right_case)
    if left_bits is None or right_bits is None:
        return None
    if left_bits <= 0 or right_bits <= 0 or left_bits % 8 != 0 or right_bits % 8 != 0:
        return None
    if left_bits == right_bits:
        return left_bits // 8
    return None


def _impl__case_comparison_bit_width(self, case: Optional[ReturnCase]) -> Optional[int]:
    if case is None:
        return None
    surface = getattr(case, "comparison_surface", None)
    bits = getattr(surface, "explicit_bit_width", None)
    try:
        if bits is not None and int(bits) > 0:
            return int(bits)
    except (TypeError, ValueError):
        return None
    return None


def _impl__replace_expression_node(
    self,
    expr: Expression,
    target: Expression,
    replacement: Expression,
) -> Expression:
    if expr.equals(target):
        return replacement
    if getattr(expr, "expr_type", None) == ExpressionType.PHI:
        branches = []
        for cond, value in getattr(expr, "value", None) or []:
            new_cond = cond
            if cond is not None and getattr(cond, "expression", None) is not None:
                new_cond = Condition(
                    self._replace_expression_node(cond.expression, target, replacement),
                    getattr(cond, "negated", False),
                )
            branches.append((new_cond, self._replace_expression_node(value, target, replacement)))
        return expr.clone_with(value=branches)
    operands = getattr(expr, "operands", None) or []
    if not operands:
        return expr
    return expr.clone_with(
        operands=[
            self._replace_expression_node(operand, target, replacement)
            for operand in operands
        ]
    )


def _impl__coerce_expression_to_size(
    self,
    expr: Expression,
    target_size: int,
    *,
    signed: bool = False,
) -> Expression:
    target_size = max(1, int(target_size or 0))
    expr_size = int(getattr(expr, "size", 0) or 0)
    if expr_size <= 0:
        expr_bits = int(expression_smt_bit_width(expr) or 0)
        expr_size = max(1, (expr_bits + 7) // 8) if expr_bits > 0 else target_size
    if expr_size == target_size:
        return expr
    if expr_size > target_size:
        narrowed = Expression.binary_op("SUBPIECE", expr, Expression.constant(0, size=4))
        narrowed.size = target_size
        return narrowed
    widened = Expression.unary_op("INT_SEXT" if signed else "INT_ZEXT", expr)
    widened.size = target_size
    return widened


def _impl__expression_prefers_signed_extension(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    data_type = str(getattr(expr, "data_type", "") or "").lower()
    if "unsigned" in data_type or data_type.startswith("u"):
        return False
    if any(token in data_type for token in ("signed", "int", "long", "short", "char")):
        return True
    return False


def _impl__extract_affine_limit_trip_count_candidate(
    self,
    start: Expression,
    limit: Expression,
    step: int,
) -> Optional[Expression]:
    if getattr(limit, "expr_type", None) != ExpressionType.BINARY_OP or getattr(limit, "operator", None) != "INT_ADD":
        return None
    left, right = list(getattr(limit, "operands", ()) or ())
    for maybe_start, maybe_scaled in ((left, right), (right, left)):
        if not self._expressions_same_shape_ignoring_runtime(maybe_start, start):
            continue
        candidate = self._extract_constant_scaled_expression(maybe_scaled, step)
        if candidate is not None:
            return candidate
    return None


def _impl__extract_constant_scaled_expression(self, expr: Expression, factor: int) -> Optional[Expression]:
    if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP or getattr(expr, "operator", None) != "INT_MULT":
        return None
    left, right = list(getattr(expr, "operands", ()) or ())
    for maybe_const, candidate in ((left, right), (right, left)):
        if getattr(maybe_const, "expr_type", None) != ExpressionType.CONSTANT:
            continue
        try:
            if int(getattr(maybe_const, "value", 0) or 0) == int(factor):
                return candidate
        except (TypeError, ValueError):
            continue
    return None


def _impl__expression_is_zero(self, expr: Expression) -> bool:
    if getattr(expr, "expr_type", None) != ExpressionType.CONSTANT:
        return False
    try:
        return int(getattr(expr, "value", 0) or 0) == 0
    except (TypeError, ValueError):
        return False


def _impl__expression_is_provably_nonnegative_under_conditions(
    self,
    expr: Expression,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> bool:
    width_bits = max(1, int(getattr(expr, "size", 0) or 4) * 8)
    if width_bits <= 1:
        return True
    if getattr(expr, "expr_type", None) == ExpressionType.CONSTANT:
        try:
            raw = int(getattr(expr, "value", 0) or 0) % (1 << width_bits)
            return raw < (1 << (width_bits - 1))
        except Exception:
            return False
    query = self._build_nonnegative_query(expr, conditions, parameters, width_bits)
    if not query:
        return False
    result = Z3Solver(timeout=1, debug=False).check_equivalence_direct(query)
    return result.status == SolverStatus.UNSAT


def _impl__combined_summary_conditions(
    self,
    left_case: ReturnCase,
    right_case: ReturnCase,
) -> List[Condition]:
    left_conditions = left_case.summary_conditions if left_case.summary_conditions is not None else left_case.conditions
    right_conditions = right_case.summary_conditions if right_case.summary_conditions is not None else right_case.conditions
    return ConditionSimplifier.simplify_conditions_object_centric(
        list(left_conditions or []) + list(right_conditions or [])
    )


def _impl__cases_have_equivalent_summary_conditions(
    self,
    left_case: ReturnCase,
    right_case: ReturnCase,
) -> bool:
    left_conditions = left_case.summary_conditions if left_case.summary_conditions is not None else left_case.conditions
    right_conditions = right_case.summary_conditions if right_case.summary_conditions is not None else right_case.conditions
    left_normalized = ConditionSimplifier.simplify_conditions_object_centric(list(left_conditions or []))
    right_normalized = ConditionSimplifier.simplify_conditions_object_centric(list(right_conditions or []))
    if not left_normalized and not right_normalized:
        return True
    parameters = list(getattr(left_case, "parameters", None) or []) + list(
        getattr(right_case, "parameters", None) or []
    )
    return self._condition_set_implies(
        left_normalized,
        right_normalized,
        parameters,
    ) and self._condition_set_implies(
        right_normalized,
        left_normalized,
        parameters,
    )


def _impl__cases_have_pair_local_summary_guard_compatibility(
    self,
    left_case: ReturnCase,
    right_case: ReturnCase,
) -> bool:
    if not self._cases_have_equivalent_summary_conditions(left_case, right_case):
        return False
    return self._case_conditions_cover_runtime_summary_guards(
        left_case,
    ) and self._case_conditions_cover_runtime_summary_guards(right_case)


def _impl__iter_expression_nodes(self, expr: Optional[Expression]):
    if expr is None:
        return
    yield expr
    if getattr(expr, "expr_type", None) == ExpressionType.PHI:
        for condition, value in getattr(expr, "value", None) or ():
            if condition is not None:
                yield from self._iter_expression_nodes(getattr(condition, "expression", None))
            yield from self._iter_expression_nodes(value)
        return
    for operand in getattr(expr, "operands", None) or ():
        yield from self._iter_expression_nodes(operand)


def _impl__condition_delta_region_is_covered_by_cases(
    self,
    domain_conditions: Sequence[Condition],
    excluded_conditions: Sequence[Condition],
    covering_cases: Sequence[ReturnCase],
    domain_case: ReturnCase,
    excluded_case: ReturnCase,
) -> bool:
    excluded_conjunction = Condition.combine_and(list(excluded_conditions or []))
    if excluded_conjunction is None:
        return True

    proof_conditions: List[Condition] = list(domain_conditions or [])
    proof_conditions.append(excluded_conjunction.negate())

    covering_condition = self._case_union_condition(covering_cases)
    if covering_condition is None:
        return self._condition_region_is_unsat_for_cases(
            proof_conditions,
            [domain_case, excluded_case, *list(covering_cases or [])],
        )
    proof_conditions.append(covering_condition.negate())
    return self._condition_region_is_unsat_for_cases(
        proof_conditions,
        [domain_case, excluded_case, *list(covering_cases or [])],
    )


def _impl__case_summary_condition_basis(self, case: ReturnCase) -> List[Condition]:
    return list(case.summary_conditions if case.summary_conditions is not None else case.conditions)


def _impl__case_union_condition(self, cases: Sequence[ReturnCase]) -> Optional[Condition]:
    disjuncts = []
    for case in cases or []:
        case_conditions = list(getattr(case, "conditions", None) or [])
        if not case_conditions:
            return Condition(
                Expression.binary_op(
                    "INT_EQUAL",
                    Expression.constant(1, size=1),
                    Expression.constant(1, size=1),
                )
            )
        conjunction = Condition.combine_and(case_conditions)
        if conjunction is not None:
            disjuncts.append(self._condition_as_bool_expression(conjunction))
    if not disjuncts:
        return None
    union_expr = disjuncts[0]
    for disjunct in disjuncts[1:]:
        union_expr = Expression.binary_op("BOOL_OR", union_expr, disjunct)
    return Condition(union_expr)


def _impl__condition_as_bool_expression(self, condition: Condition) -> Expression:
    if condition.negated:
        return Expression.unary_op("BOOL_NEGATE", condition.expression)
    return condition.expression


def _impl__condition_region_is_unsat_for_cases(
    self,
    conditions: Sequence[Condition],
    cases: Sequence[ReturnCase],
) -> bool:
    parameters: List[Dict[str, Any]] = []
    for case in cases or []:
        parameters.extend(list(getattr(case, "parameters", None) or []))
    identity_conditions = self._conditions_with_object_identity_parameter_symbols(
        conditions,
        parameters,
    )
    solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
    if solver_result is not None:
        return solver_result
    return ConditionSimplifier.object_centric_is_contradiction(identity_conditions)


def _impl__condition_set_implies(
    self,
    premises: Sequence[Condition],
    conclusions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> bool:
    if not conclusions:
        return True
    for conclusion in conclusions or []:
        implication_conditions = list(premises or []) + [conclusion.negate()]
        identity_conditions = self._conditions_with_object_identity_parameter_symbols(
            implication_conditions,
            parameters,
        )
        solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
        if solver_result is not None:
            if not solver_result:
                return False
            continue
        if not ConditionSimplifier.object_centric_is_contradiction(identity_conditions):
            return False
    return True


def _impl__condition_set_is_unsat(
    self,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> bool:
    if self._conditions_have_parameter_mask_constant_conflict(list(conditions or ())):
        return True
    identity_conditions = self._conditions_with_object_identity_parameter_symbols(
        list(conditions or []),
        parameters,
    )
    if self._conditions_have_parameter_mask_constant_conflict(identity_conditions):
        return True
    solver_result = ConditionSMTOracle.conjunction_is_unsat(identity_conditions)
    if solver_result is not None:
        return solver_result
    return ConditionSimplifier.object_centric_is_contradiction(identity_conditions)


def _impl__conditions_have_parameter_mask_constant_conflict(
    self,
    conditions: Sequence[Condition],
) -> bool:
    constants: Dict[Tuple[Any, ...], Tuple[int, int]] = {}
    mask_equalities: List[Tuple[Tuple[Any, ...], int, int, int]] = []
    for condition in conditions or ():
        equality = self._condition_positive_equality_operands(condition)
        if equality is None:
            continue
        left, right = equality
        constant_equality = self._parameter_constant_equality(left, right)
        if constant_equality is None:
            constant_equality = self._parameter_constant_equality(right, left)
        if constant_equality is not None:
            key, value, bits = constant_equality
            previous = constants.get(key)
            if previous is not None and previous != (value, bits):
                return True
            constants[key] = (value, bits)
            continue
        mask_equality = self._parameter_mask_equality(left, right)
        if mask_equality is None:
            mask_equality = self._parameter_mask_equality(right, left)
        if mask_equality is not None:
            mask_equalities.append(mask_equality)
    for key, mask, expected, bits in mask_equalities:
        known = constants.get(key)
        if known is None:
            continue
        known_value, known_bits = known
        width_bits = max(1, int(bits or known_bits or 0))
        width_mask = (1 << width_bits) - 1
        if (known_value & mask & width_mask) != (expected & width_mask):
            return True
    return False


def _impl__condition_positive_equality_operands(
    self,
    condition: Condition,
) -> Optional[Tuple[Expression, Expression]]:
    expr = getattr(condition, "expression", None)
    if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    operator = getattr(expr, "operator", None)
    negated = bool(getattr(condition, "negated", False))
    if operator == "INT_NOTEQUAL" and negated:
        pass
    elif operator == "INT_EQUAL" and not negated:
        pass
    else:
        return None
    operands = list(getattr(expr, "operands", ()) or ())
    if len(operands) != 2:
        return None
    return operands[0], operands[1]


def _impl__parameter_constant_equality(
    self,
    maybe_param_expr: Expression,
    maybe_const_expr: Expression,
) -> Optional[Tuple[Tuple[Any, ...], int, int]]:
    const_value = self._raw_constant_value(maybe_const_expr)
    if const_value is None:
        return None
    affine = self._parameter_plus_constant_affine(maybe_param_expr)
    if affine is None:
        return None
    key, offset, bits = affine
    width_mask = (1 << max(1, bits)) - 1
    return key, (int(const_value) - int(offset)) & width_mask, bits


def _impl__parameter_mask_equality(
    self,
    maybe_mask_expr: Expression,
    maybe_const_expr: Expression,
) -> Optional[Tuple[Tuple[Any, ...], int, int, int]]:
    const_value = self._raw_constant_value(maybe_const_expr)
    if const_value is None:
        return None
    mask_expr = maybe_mask_expr
    if (
        getattr(mask_expr, "expr_type", None) == ExpressionType.BINARY_OP
        and getattr(mask_expr, "operator", None) == "INT_SUB"
    ):
        operands = list(getattr(mask_expr, "operands", ()) or ())
        if len(operands) != 2:
            return None
        sub_const = self._raw_constant_value(operands[1])
        if sub_const is None:
            return None
        mask_expr = operands[0]
        const_value = int(const_value) + int(sub_const)
    if getattr(mask_expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    if getattr(mask_expr, "operator", None) != "INT_AND":
        return None
    operands = list(getattr(mask_expr, "operands", ()) or ())
    if len(operands) != 2:
        return None
    for maybe_mask, maybe_param in ((operands[0], operands[1]), (operands[1], operands[0])):
        mask_value = self._raw_constant_value(maybe_mask)
        key = self._parameter_expression_key(maybe_param)
        if mask_value is None or key is None:
            continue
        bits = max(1, int(getattr(maybe_param, "size", 0) or getattr(mask_expr, "size", 0) or 4) * 8)
        width_mask = (1 << bits) - 1
        return key, int(mask_value) & width_mask, int(const_value) & width_mask, bits
    return None


def _impl__parameter_plus_constant_affine(
    self,
    expr: Expression,
) -> Optional[Tuple[Tuple[Any, ...], int, int]]:
    key = self._parameter_expression_key(expr)
    if key is not None:
        bits = max(1, int(getattr(expr, "size", 0) or 4) * 8)
        return key, 0, bits
    if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    operator = getattr(expr, "operator", None)
    operands = list(getattr(expr, "operands", ()) or ())
    if len(operands) != 2:
        return None
    bits = max(1, int(getattr(expr, "size", 0) or 4) * 8)
    width_mask = (1 << bits) - 1
    if operator == "INT_ADD":
        for left, right in ((operands[0], operands[1]), (operands[1], operands[0])):
            affine = self._parameter_plus_constant_affine(left)
            const_value = self._raw_constant_value(right)
            if affine is None or const_value is None:
                continue
            key, offset, affine_bits = affine
            return key, (int(offset) + int(const_value)) & width_mask, max(bits, affine_bits)
    if operator == "INT_SUB":
        affine = self._parameter_plus_constant_affine(operands[0])
        const_value = self._raw_constant_value(operands[1])
        if affine is None or const_value is None:
            return None
        key, offset, affine_bits = affine
        return key, (int(offset) - int(const_value)) & width_mask, max(bits, affine_bits)
    return None


def _impl__parameter_expression_key(self, expr: Expression) -> Optional[Tuple[Any, ...]]:
    if getattr(expr, "expr_type", None) != ExpressionType.PARAMETER:
        return None
    return (
        "parameter",
        str(getattr(expr, "name", "") or ""),
        int(getattr(expr, "value", -1) or -1),
        max(1, int(getattr(expr, "size", 0) or 4)),
    )


def _impl__conditions_are_semantically_equivalent(
    self,
    left_condition: Condition,
    right_condition: Condition,
) -> bool:
    if left_condition.equals(right_condition):
        return True
    return self._condition_implies(left_condition, right_condition) and self._condition_implies(
        right_condition,
        left_condition,
    )


def _impl__condition_implies(
    self,
    premise: Condition,
    conclusion: Condition,
) -> bool:
    implication_conditions = [premise, conclusion.negate()]
    solver_result = ConditionSMTOracle.conjunction_is_unsat(implication_conditions)
    if solver_result is not None:
        return solver_result
    return ConditionSimplifier.object_centric_is_contradiction(implication_conditions)


def _impl__solve_affine_equality(
    self,
    left_affine: tuple[int, int],
    right_affine: tuple[int, int],
) -> Optional[int]:
    left_coeff, left_bias = left_affine
    right_coeff, right_bias = right_affine
    coeff_delta = int(left_coeff) - int(right_coeff)
    bias_delta = int(right_bias) - int(left_bias)
    if coeff_delta == 0:
        return None
    if bias_delta % coeff_delta != 0:
        return None
    solved = bias_delta // coeff_delta
    return int(solved) if solved > 0 else None

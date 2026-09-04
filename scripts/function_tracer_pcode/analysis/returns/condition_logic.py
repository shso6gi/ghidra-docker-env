"""Condition implication, contradiction, equivalence and parameter-assignment evaluation."""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple, cast
from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.expression import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.structural import StructuralKey, expression_key_safe
from scripts.function_tracer_pcode.analysis.returns._shared import (
    AnalysisFailure,
    ConditionNormalizer,
    ConditionSMTOracle,
    ConditionSimplifier,
    EffectSummary,
    PcodeTracer,
    _expressions_equivalent,
    _iter_expression_nodes,
)
from scripts.function_tracer_pcode.analysis.returns._api import StructuralRecurrenceSummarizer
from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.analysis.returns._shared import (
    ConditionNormalizer,
    ConditionSMTOracle,
    ConditionSimplifier,
    _expressions_equivalent_under_conditions,
    eval_constant_raw,
)
from typing import Any, List, Mapping, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.analysis.returns._shared import (
    eval_constant_raw,
)


def _impl__condition_mentions_param(self, condition: Condition, param_name: str) -> bool:
    """条件が指定パラメータ変数を参照するか判定（to_string 非依存）。"""
    expression = condition.expression
    if expression is None:
        return False
    try:
        return param_name in expression.get_all_variables()
    except Exception:
        return False


def _impl__expression_is_zero_constant(self, expr: Optional[Expression]) -> bool:
    """式が 0 定数、または同値なゼロ表現か判定（to_string 非依存）。"""
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.CONSTANT:
        try:
            return int(expr.value) == 0
        except Exception:
            return False
    if expr.expr_type == ExpressionType.LITERAL:
        try:
            return int(expr.value) == 0
        except Exception:
            return False
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operator in {"INT_2COMP", "INT_NEGATE"}:
        if not expr.operands:
            return False
        return self._expression_is_zero_constant(expr.operands[0])
    return False


def _impl__expression_has_param(expr: Optional[Expression], param_name: str) -> bool:
    """式の内部に指定パラメータが含まれるかを判定。"""
    if expr is None:
        return False
    try:
        return param_name in expr.get_all_variables()
    except Exception:
        return False


def _impl__classify_param_condition(
    self,
    condition: Condition,
    param_name: str,
) -> Tuple[bool, bool, bool]:
    """
    条件を零・正・負チェックへ分類（display 文字列不使用）。

    戻り値: (has_zero_check, has_positive_check, has_negative_check)
    """
    decompose = self._decompose_comparison_condition(condition)
    if decompose is None:
        return False, False, False

    negated, op, left, right = decompose
    has_pos = False
    has_neg = False
    has_zero = False

    left_param = self._expression_has_param(left, param_name)
    right_param = self._expression_has_param(right, param_name)
    left_zero = self._expression_is_zero_constant(left)
    right_zero = self._expression_is_zero_constant(right)

    if op in {"INT_EQUAL", "INT_NOTEQUAL"}:
        if (left_zero and right_param) or (right_zero and left_param):
            has_zero = True
        return has_zero, has_pos, has_neg

    if not (
        (left_param and right_zero) or (right_param and left_zero)
    ):
        return has_zero, has_pos, has_neg

    relation_positive_on_zero = op in {"INT_LESSEQUAL", "INT_SLESSEQUAL", "INT_LESS", "INT_SLESS"}
    if not relation_positive_on_zero:
        return has_zero, has_pos, has_neg

    # op が param < 0 系の場合
    if left_param and right_zero:
        if op in {"INT_LESS", "INT_SLESS"}:
            # param < 0
            has_neg = not negated
            has_pos = negated
        elif op in {"INT_LESSEQUAL", "INT_SLESSEQUAL"}:
            # param <= 0
            has_neg = not negated
            has_pos = False
    # op が 0 < param 系の場合
    elif left_zero and right_param:
        if op in {"INT_LESS", "INT_SLESS"}:
            # 0 < param
            has_pos = not negated
            has_neg = negated
        elif op in {"INT_LESSEQUAL", "INT_SLESSEQUAL"}:
            # 0 <= param
            has_pos = not negated
            has_neg = False

    if op in {"INT_NOTEQUAL"} and (left_zero and right_param or right_zero and left_param):
        has_zero = True

    return has_zero, has_pos, has_neg


def _impl__constant_expression_value(expr: Optional[Expression]) -> Optional[int]:
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.CONSTANT:
        return None
    try:
        return int(getattr(expr, "value", 0) or 0)
    except (TypeError, ValueError):
        return None


def _impl__conditions_are_unsat(self, conditions: Sequence[Condition]) -> bool:
    try:
        solver_result = ConditionSMTOracle.conjunction_is_unsat(list(conditions or []))
    except Exception:
        solver_result = None
    if solver_result is not None:
        return bool(solver_result)
    return ConditionSimplifier.object_centric_is_contradiction(list(conditions or []))


def _impl__expressions_same_key(self, left: Optional[Expression], right: Optional[Expression]) -> bool:
    if left is None or right is None:
        return False
    try:
        return left.structural_key() == right.structural_key()
    except Exception:
        return False


def _impl__conditions_overlap(
    self,
    left: Sequence[Condition],
    right: Sequence[Condition],
) -> bool:
    for left_condition in left or ():
        if left_condition is None:
            continue
        for right_condition in right or ():
            if right_condition is None:
                continue
            if (
                left_condition.equals(right_condition.negate())
                or ConditionNormalizer.are_equivalent(left_condition, right_condition.negate())
                or left_condition.negate().equals(right_condition)
                or ConditionNormalizer.are_equivalent(left_condition.negate(), right_condition)
            ):
                return False
    try:
        return ConditionSMTOracle.conjunction_is_unsat(list(left or ()) + list(right or ())) is not True
    except Exception:
        return False


def _impl__conditions_imply(
    self,
    left: Sequence[Condition],
    right: Sequence[Condition],
) -> bool:
    for condition in right or ():
        if any(
            existing is not None
            and (
                existing.equals(condition)
                or ConditionNormalizer.are_equivalent(existing, condition)
            )
            for existing in left or ()
        ):
            continue
        try:
            if ConditionSMTOracle.conjunction_is_unsat(list(left or ()) + [condition.negate()]) is not True:
                return False
        except Exception:
            return False
    return True


def _impl__expressions_equal_under_conditions_smt(
    self,
    left: Optional[Expression],
    right: Optional[Expression],
    conditions: Sequence[Condition],
    parameters: Sequence[Dict],
) -> bool:
    if _expressions_equivalent_under_conditions(left, right, conditions, parameters):
        return True
    if left is None or right is None:
        return False
    equality = Condition(Expression.binary_op("INT_NOTEQUAL", left, right), False)
    try:
        return ConditionSMTOracle.conjunction_is_unsat(list(conditions or ()) + [equality]) is True
    except Exception:
        return False


def _impl__condition_contradicts_any(
    self,
    condition: Condition,
    others: Sequence[Condition],
) -> bool:
    if condition is None:
        return False
    for other in others or ():
        if other is None:
            continue
        try:
            if (
                condition.equals(other.negate())
                or condition.negate().equals(other)
                or ConditionNormalizer.are_equivalent(condition, other.negate())
                or ConditionNormalizer.are_equivalent(condition.negate(), other)
            ):
                return True
        except Exception:
            continue
    try:
        return ConditionSMTOracle.conjunction_is_unsat(list(others or ()) + [condition]) is True
    except Exception:
        return False


def _impl__signed_positive_condition(self, expr: Expression) -> Condition:
    zero = Expression.constant(0, max(1, int(expr.size or 4)))
    return Condition(Expression.binary_op("INT_SLESS", zero, expr), False)


def _impl__condition_is_signed_nonpositive_of_param(self, condition: Condition, param: Expression) -> bool:
    if condition is None or not getattr(condition, "negated", False):
        return False
    expr = getattr(condition, "expression", None)
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_SLESS":
        return False
    operands = list(getattr(expr, "operands", None) or ())
    if len(operands) != 2:
        return False
    left, right = operands
    return self._constant_int_value(left) == 0 and self._expression_is_same_parameter_ignoring_subpiece(right, param)


def _impl__condition_is_signed_positive_of_param(self, condition: Condition, param: Expression) -> bool:
    if condition is None or getattr(condition, "negated", False):
        return False
    expr = getattr(condition, "expression", None)
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_SLESS":
        return False
    operands = list(getattr(expr, "operands", None) or ())
    if len(operands) != 2:
        return False
    left, right = operands
    return self._constant_int_value(left) == 0 and self._expression_is_same_parameter_ignoring_subpiece(right, param)


def _impl__condition_is_signed_less_than_one_of_param(self, condition: Condition, param: Expression) -> bool:
    if condition is None or getattr(condition, "negated", False):
        return False
    expr = getattr(condition, "expression", None)
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_SLESS":
        return False
    operands = list(getattr(expr, "operands", None) or ())
    if len(operands) != 2:
        return False
    left, right = operands
    return self._expression_is_same_parameter_ignoring_subpiece(left, param) and self._constant_int_value(right) == 1


def _impl__condition_is_param_equal_const(self, condition: Condition, param: Expression, value: int) -> bool:
    if condition is None:
        return False
    expr = getattr(condition, "expression", None)
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP:
        return False
    operator = getattr(expr, "operator", None)
    negated = bool(getattr(condition, "negated", False))
    if operator == "INT_NOTEQUAL" and negated:
        pass
    elif operator == "INT_EQUAL" and not negated:
        pass
    else:
        return False
    operands = list(getattr(expr, "operands", None) or ())
    if len(operands) != 2:
        return False
    left, right = operands
    if (
        self._expression_is_same_parameter_ignoring_subpiece(left, param)
    ) and self._constant_int_value(right) == value:
        return True
    if (
        self._expression_is_same_parameter_ignoring_subpiece(right, param)
    ) and self._constant_int_value(left) == value:
        return True
    return False


def _impl__coerce_expression_size(self, expr: Expression, size: int) -> Expression:
    if int(getattr(expr, "size", 0) or 0) == int(size or 0):
        return expr
    return expr.clone_with(size=max(1, int(size or getattr(expr, "size", 0) or 4)))


def _impl__expression_is_same_parameter(self, expr: Expression, param: Expression) -> bool:
    if expr is None or param is None:
        return False
    if expr.expr_type != ExpressionType.PARAMETER or param.expr_type != ExpressionType.PARAMETER:
        return False
    expr_index = getattr(expr, "value", None)
    param_index = getattr(param, "value", None)
    if isinstance(expr_index, int) and isinstance(param_index, int) and expr_index >= 0 and param_index >= 0:
        return expr_index == param_index
    return (getattr(expr, "name", None) or "") == (getattr(param, "name", None) or "")


def _impl__expression_is_same_parameter_ignoring_subpiece(self, expr: Expression, param: Expression) -> bool:
    current = expr
    if (
        current is not None
        and current.expr_type == ExpressionType.BINARY_OP
        and current.operator == "SUBPIECE"
        and current.operands
    ):
        current = current.operands[0]
    return self._expression_is_same_parameter(current, param)


def _impl__conditions_equivalent(
    self,
    left: Sequence[Condition],
    right: Sequence[Condition],
) -> bool:
    left_conditions = tuple(left or ())
    right_conditions = tuple(right or ())
    left_implies_right = ConditionSMTOracle.conjunction_is_unsat(
        list(left_conditions) + [condition.negate() for condition in right_conditions]
    )
    right_implies_left = ConditionSMTOracle.conjunction_is_unsat(
        list(right_conditions) + [condition.negate() for condition in left_conditions]
    )
    return left_implies_right is True and right_implies_left is True


def _impl__coerce_order_key(self, value: object) -> Optional[int]:
    if value is None:
        return None
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, int):
        return value
    try:
        return int(cast(Any, value))
    except Exception:
        return None


def _impl__build_condition_signature_set(self, conditions: List[Condition]) -> Set[object]:
    signatures: Set[object] = set()
    for condition in conditions:
        try:
            signatures.add(condition.structural_key(budget=256))
        except Exception:
            try:
                signatures.add(ConditionNormalizer.normalize_for_contradiction(condition))
            except Exception:
                continue
    return signatures


def _impl__condition_set_conjunction_expression(
    self,
    conditions: Sequence[Condition],
) -> Optional[Expression]:
    terms = [self._condition_to_expression(condition) for condition in conditions or ()]
    terms = [term for term in terms if term is not None]
    if not terms:
        one = Expression.constant(1, size=1)
        return one
    result = terms[0]
    for term in terms[1:]:
        result = Expression.binary_op("BOOL_AND", result, term)
        result.size = 1
    return result


def _impl__condition_to_expression(self, condition: Condition) -> Optional[Expression]:
    expr = getattr(condition, "expression", None)
    if expr is None:
        return None
    if not bool(getattr(condition, "negated", False)):
        return expr
    negated = Expression.unary_op("BOOL_NEGATE", expr)
    negated.size = 1
    return negated


def _impl__condition_is_constant_equality_guard(self, condition: Condition) -> bool:
    if condition is None:
        return False
    expr = getattr(condition, "expression", None)
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    if self._condition_logical_operator(condition) != "INT_EQUAL" or len(getattr(expr, "operands", ()) or ()) != 2:
        return False
    left, right = expr.operands
    left_is_const = getattr(left, "expr_type", None) == ExpressionType.CONSTANT
    right_is_const = getattr(right, "expr_type", None) == ExpressionType.CONSTANT
    return left_is_const != right_is_const


def _impl__condition_logical_operator(
    self,
    condition: Condition,
) -> Optional[str]:
    expr = getattr(condition, "expression", None)
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    operator = getattr(expr, "operator", None)
    if not getattr(condition, "negated", False):
        return operator
    if operator == "INT_EQUAL":
        return "INT_NOTEQUAL"
    if operator == "INT_NOTEQUAL":
        return "INT_EQUAL"
    return operator


def _impl__pruning_conditions_signature(
    self,
    conditions: List[Condition],
):
    parts = [
        ConditionNormalizer.normalize_for_contradiction(condition)
        for condition in (conditions or [])
    ]
    parts.sort()
    return tuple(parts)


def _impl__condition_sets_are_complementary(
    self,
    left_conditions: List[Condition],
    right_conditions: List[Condition],
) -> bool:
    if not left_conditions or not right_conditions:
        return False
    if len(left_conditions) != len(right_conditions):
        return False

    unmatched = list(right_conditions)
    for left_condition in left_conditions:
        match_index = None
        for index, right_condition in enumerate(unmatched):
            if left_condition.equals(right_condition.negate()) or left_condition.negate().equals(right_condition):
                match_index = index
                break
        if match_index is None:
            return False
        unmatched.pop(match_index)
    return not unmatched


def _impl__substitute_parameter_constants_under_conditions(
    self,
    expr: Optional[Expression],
    conditions: Sequence[Condition],
) -> Optional[Expression]:
    assignments = self._parameter_constant_assignments_from_conditions(conditions)
    if not assignments:
        return expr
    substituted = self._substitute_parameter_constants(expr, assignments)
    if substituted is None:
        return expr
    folded = self._fold_constant_expression(substituted, fallback_expr=expr)
    return folded if folded is not None else substituted


def _impl__parameter_constant_assignments_from_conditions(
    self,
    conditions: Sequence[Condition],
) -> Dict[Tuple[Any, ...], Tuple[Expression, int]]:
    assignments: Dict[Tuple[Any, ...], Tuple[Expression, int]] = {}
    for condition in conditions or ():
        if getattr(condition, "negated", False):
            continue
        expr = getattr(condition, "expression", None)
        if getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
            continue
        if getattr(expr, "operator", None) != "INT_EQUAL":
            continue
        operands = list(getattr(expr, "operands", None) or [])
        if len(operands) != 2:
            continue
        for parameter, constant in ((operands[0], operands[1]), (operands[1], operands[0])):
            if getattr(parameter, "expr_type", None) != ExpressionType.PARAMETER:
                continue
            if getattr(constant, "expr_type", None) != ExpressionType.CONSTANT:
                continue
            try:
                key = parameter.structural_key()
                value = int(getattr(constant, "value", 0) or 0)
            except Exception:
                continue
            existing = assignments.get(key)
            if existing is not None and existing[1] != value:
                assignments.pop(key, None)
                continue
            assignments[key] = (parameter, value)
    return assignments


def _impl__substitute_parameter_constants(
    self,
    expr: Optional[Expression],
    assignments: Mapping[Tuple[Any, ...], Tuple[Expression, int]],
) -> Optional[Expression]:
    if expr is None:
        return expr
    if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
        try:
            key = expr.structural_key()
        except Exception:
            key = None
        assigned = assignments.get(key) if key is not None else None
        if assigned is None:
            return expr
        parameter, value = assigned
        return Expression.constant(
            int(value),
            size=max(1, int(getattr(parameter, "size", 0) or getattr(expr, "size", 0) or 4)),
        )
    if getattr(expr, "expr_type", None) == ExpressionType.PHI:
        changed = False
        branches = []
        for condition, value in getattr(expr, "value", None) or []:
            rewritten_condition = condition
            if condition is not None:
                rewritten_condition_expr = self._substitute_parameter_constants(
                    getattr(condition, "expression", None),
                    assignments,
                )
                if rewritten_condition_expr is not getattr(condition, "expression", None):
                    rewritten_condition = Condition(
                        rewritten_condition_expr,
                        getattr(condition, "negated", False),
                    )
                    changed = True
            rewritten_value = self._substitute_parameter_constants(value, assignments)
            if rewritten_value is not value:
                changed = True
            branches.append((rewritten_condition, rewritten_value if rewritten_value is not None else value))
        if not changed:
            return expr
        rebuilt = Expression.phi(branches)
        rebuilt.size = getattr(expr, "size", 0)
        return rebuilt
    operands = list(getattr(expr, "operands", None) or [])
    if not operands:
        return expr
    rewritten_operands = []
    changed = False
    for operand in operands:
        rewritten = self._substitute_parameter_constants(operand, assignments)
        if rewritten is None:
            rewritten = operand
        rewritten_operands.append(rewritten)
        changed = changed or rewritten is not operand
    if not changed:
        return expr
    rebuilt = expr.clone_with(operands=rewritten_operands)
    folded = self._fold_constant_expression(rebuilt, fallback_expr=expr)
    return folded if folded is not None else rebuilt


def _impl__reduce_phi_expression_under_conditions_with_smt(
    self,
    expr: Optional[Expression],
    conditions: Sequence[Condition],
    *,
    _active_ids: Optional[Set[int]] = None,
) -> Optional[Expression]:
    """Reduce PHI branches whose selector reachability is SMT-proved.

    PHI rendering is ordered: the first true condition wins, and the final
    branch is the fallback.  A branch can be selected only when active
    return reachability proves all earlier selectors false and proves this
    selector true.  Ambiguous selectors are preserved.
    """

    if expr is None:
        return expr
    active_ids = set() if _active_ids is None else set(_active_ids)
    expr_id = id(expr)
    if expr_id in active_ids:
        return expr
    active_ids.add(expr_id)

    expr_type = getattr(expr, "expr_type", None)
    if expr_type == ExpressionType.PHI:
        branches = list(getattr(expr, "value", None) or [])
        if not branches:
            return expr

        prior_conditions: List[Condition] = []
        surviving: List[Tuple[Optional[Condition], Expression]] = []
        changed = False
        active_conditions = list(conditions or [])
        assignments = self._parameter_constant_assignments_from_conditions(active_conditions)

        for branch_condition, branch_value in branches:
            branch_reachability = [
                prior.negate()
                for prior in prior_conditions
                if prior is not None
            ]
            if branch_condition is not None:
                branch_reachability.append(branch_condition)

            if branch_reachability and (
                self._conditions_conjunction_is_false_under_assignments(
                    branch_reachability,
                    assignments,
                )
                or self._conditions_are_unsat(active_conditions + branch_reachability)
            ):
                changed = True
                if branch_condition is not None:
                    prior_conditions.append(branch_condition)
                continue

            if self._active_conditions_imply_all(
                active_conditions,
                branch_reachability,
                assignments=assignments,
            ):
                return self._reduce_phi_expression_under_conditions_with_smt(
                    branch_value,
                    active_conditions + branch_reachability,
                    _active_ids=active_ids,
                )

            reduced_branch = self._reduce_phi_expression_under_conditions_with_smt(
                branch_value,
                active_conditions + branch_reachability,
                _active_ids=active_ids,
            )
            if reduced_branch is None:
                reduced_branch = branch_value
            if reduced_branch is not branch_value:
                changed = True
            surviving.append((branch_condition, reduced_branch))
            if branch_condition is not None:
                prior_conditions.append(branch_condition)

        if not surviving:
            return expr
        if len(surviving) == 1:
            return surviving[0][1]
        if not changed:
            return expr
        rebuilt = Expression.phi(surviving)
        rebuilt.size = getattr(expr, "size", 0)
        return rebuilt

    operands = list(getattr(expr, "operands", None) or [])
    if not operands:
        return expr
    rewritten_operands = []
    changed = False
    for operand in operands:
        rewritten = self._reduce_phi_expression_under_conditions_with_smt(
            operand,
            conditions,
            _active_ids=active_ids,
        )
        if rewritten is None:
            rewritten = operand
        rewritten_operands.append(rewritten)
        changed = changed or rewritten is not operand
    if not changed:
        return expr
    return expr.clone_with(operands=rewritten_operands)


def _impl__active_conditions_imply_all(
    self,
    active_conditions: Sequence[Condition],
    conclusions: Sequence[Condition],
    *,
    assignments: Optional[Mapping[Tuple[Any, ...], Tuple[Expression, int]]] = None,
) -> bool:
    for conclusion in conclusions or ():
        truth = self._condition_truth_under_parameter_assignments(
            conclusion,
            assignments or {},
        )
        if truth is True:
            continue
        if truth is False:
            return False
        try:
            negated = conclusion.negate()
        except Exception:
            return False
        if not self._conditions_are_unsat(list(active_conditions or []) + [negated]):
            return False
    return True


def _impl__conditions_conjunction_is_false_under_assignments(
    self,
    conditions: Sequence[Condition],
    assignments: Mapping[Tuple[Any, ...], Tuple[Expression, int]],
) -> bool:
    if not assignments:
        return False
    for condition in conditions or ():
        truth = self._condition_truth_under_parameter_assignments(condition, assignments)
        if truth is False:
            return True
    return False


def _impl__condition_truth_under_parameter_assignments(
    self,
    condition: Optional[Condition],
    assignments: Mapping[Tuple[Any, ...], Tuple[Expression, int]],
    *,
    _active_ids: Optional[Set[int]] = None,
) -> Optional[bool]:
    if condition is None or not assignments:
        return None
    substituted = self._evaluate_expression_under_parameter_assignments(
        getattr(condition, "expression", None),
        assignments,
        _active_ids=_active_ids,
    )
    evaluated = eval_constant_raw(substituted) if substituted is not None else None
    if evaluated is None:
        return None
    raw_value, _bits = evaluated
    truth = bool(raw_value)
    if getattr(condition, "negated", False):
        truth = not truth
    return truth


def _impl__evaluate_expression_under_parameter_assignments(
    self,
    expr: Optional[Expression],
    assignments: Mapping[Tuple[Any, ...], Tuple[Expression, int]],
    *,
    _active_ids: Optional[Set[int]] = None,
) -> Optional[Expression]:
    if expr is None or not assignments:
        return expr
    active_ids = set() if _active_ids is None else set(_active_ids)
    expr_id = id(expr)
    if expr_id in active_ids:
        return expr
    active_ids.add(expr_id)

    if getattr(expr, "expr_type", None) == ExpressionType.PARAMETER:
        try:
            key = expr.structural_key()
        except Exception:
            key = None
        assigned = assignments.get(key) if key is not None else None
        if assigned is None:
            return expr
        parameter, value = assigned
        return Expression.constant(
            int(value),
            size=max(1, int(getattr(parameter, "size", 0) or getattr(expr, "size", 0) or 4)),
        )

    if getattr(expr, "expr_type", None) == ExpressionType.PHI:
        branches = list(getattr(expr, "value", None) or [])
        if not branches:
            return expr
        rewritten_branches: List[Tuple[Optional[Condition], Expression]] = []
        changed = False
        for condition, value in branches:
            if condition is None:
                selected = self._evaluate_expression_under_parameter_assignments(
                    value,
                    assignments,
                    _active_ids=active_ids,
                )
                if not rewritten_branches:
                    return selected if selected is not None else value
                if selected is not None and selected is not value:
                    changed = True
                rewritten_branches.append((None, selected if selected is not None else value))
                continue
            truth = self._condition_truth_under_parameter_assignments(
                condition,
                assignments,
                _active_ids=active_ids,
            )
            if truth is True:
                selected = self._evaluate_expression_under_parameter_assignments(
                    value,
                    assignments,
                    _active_ids=active_ids,
                )
                return selected if selected is not None else value
            if truth is False:
                changed = True
                continue
            rewritten_condition = condition
            rewritten_condition_expr = self._evaluate_expression_under_parameter_assignments(
                getattr(condition, "expression", None),
                assignments,
                _active_ids=active_ids,
            )
            if rewritten_condition_expr is not None and rewritten_condition_expr is not getattr(condition, "expression", None):
                rewritten_condition = Condition(
                    rewritten_condition_expr,
                    bool(getattr(condition, "negated", False)),
                )
                changed = True
            rewritten_value = self._evaluate_expression_under_parameter_assignments(
                value,
                assignments,
                _active_ids=active_ids,
            )
            if rewritten_value is not None and rewritten_value is not value:
                changed = True
            rewritten_branches.append((rewritten_condition, rewritten_value if rewritten_value is not None else value))
        if not rewritten_branches:
            return expr
        if len(rewritten_branches) == 1:
            return rewritten_branches[0][1]
        if not changed:
            return expr
        rebuilt = Expression.phi(rewritten_branches)
        rebuilt.size = getattr(expr, "size", 0)
        return rebuilt

    operands = list(getattr(expr, "operands", None) or [])
    if not operands:
        return expr
    rewritten_operands = []
    changed = False
    for operand in operands:
        rewritten = self._evaluate_expression_under_parameter_assignments(
            operand,
            assignments,
            _active_ids=active_ids,
        )
        if rewritten is None:
            rewritten = operand
        rewritten_operands.append(rewritten)
        changed = changed or rewritten is not operand
    if not changed:
        return expr
    rebuilt = expr.clone_with(operands=rewritten_operands)
    folded = self._fold_constant_expression(rebuilt, fallback_expr=expr)
    return folded if folded is not None else rebuilt

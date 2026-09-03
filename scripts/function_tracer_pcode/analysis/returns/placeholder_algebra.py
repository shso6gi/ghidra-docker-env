"""Placeholder +/- unit and zero recognition under conditions."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.analysis.returns._shared import (
    AnalysisFailure,
    CallTargetRef,
    Condition,
    ConditionNormalizer,
    ConditionSMTOracle,
    ConditionSimplifier,
    EffectSummary,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    Mapping,
    PcodeTracer,
    ReturnInfo,
    StructuralKey,
    _expressions_equivalent,
    _iter_expression_nodes,
    cast,
    expression_key_safe,
)
from scripts.function_tracer_pcode.analysis.returns._api import StructuralRecurrenceSummarizer
from typing import Any, List, Mapping, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.analysis.returns._shared import (
    Condition,
    ConditionNormalizer,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    eval_constant_raw,
)
from typing import Any, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.analysis.returns._shared import (
    Condition,
    Expression,
    ExpressionType,
)


def _impl__expression_is_placeholder_plus_one(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
) -> bool:
    return self._expression_is_placeholder_plus_constant(expr, placeholder, 1)


def _impl__expression_is_placeholder_minus_one(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
) -> bool:
    return self._expression_is_placeholder_plus_constant(expr, placeholder, -1)


def _impl__expression_is_placeholder_plus_one_under_conditions(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    conditions: Sequence[Condition],
) -> bool:
    if self._expression_is_placeholder_plus_one(expr, placeholder):
        return True
    if self._expression_is_placeholder_plus_unit_condition(expr, placeholder, conditions):
        return True
    expected = Expression.binary_op(
        "INT_ADD",
        placeholder,
        Expression.constant(1, size=max(1, int(getattr(placeholder, "size", 0) or 4))),
    )
    expected.size = max(1, int(getattr(placeholder, "size", 0) or 4))
    return self._expressions_equal_under_conditions_smt(
        expr,
        expected,
        tuple(conditions or ()),
        getattr(self, "_current_parameters", ()) or (),
    )


def _impl__expression_is_placeholder_minus_one_under_conditions(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    conditions: Sequence[Condition],
) -> bool:
    if self._expression_is_placeholder_minus_one(expr, placeholder):
        return True
    if self._expression_is_placeholder_minus_one_unit_condition(expr, placeholder, conditions):
        return True
    expected = Expression.binary_op(
        "INT_SUB",
        placeholder,
        Expression.constant(1, size=max(1, int(getattr(placeholder, "size", 0) or 4))),
    )
    expected.size = max(1, int(getattr(placeholder, "size", 0) or 4))
    return self._expressions_equal_under_conditions_smt(
        expr,
        expected,
        tuple(conditions or ()),
        getattr(self, "_current_parameters", ()) or (),
    )


def _impl__expression_is_placeholder_plus_zero_under_conditions(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    conditions: Sequence[Condition],
) -> bool:
    current = self._strip_transparent_unary(expr)
    if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    if getattr(current, "operator", None) not in {"INT_ADD", "INT_SUB"}:
        return False
    operands = tuple(getattr(current, "operands", ()) or ())
    if len(operands) != 2:
        return False
    left, right = operands
    if self._expressions_same_key(left, placeholder):
        delta = right
        if getattr(current, "operator", None) == "INT_ADD":
            return self._expression_is_zero_under_conditions(delta, conditions)
        return self._expression_is_zero_under_conditions(delta, conditions)
    if getattr(current, "operator", None) == "INT_ADD" and self._expressions_same_key(right, placeholder):
        return self._expression_is_zero_under_conditions(left, conditions)
    return False


def _impl__expression_is_zero_under_conditions(
    self,
    expr: Optional[Expression],
    conditions: Sequence[Condition],
) -> bool:
    if self._constant_int_value(expr) == 0:
        return True
    current = self._strip_transparent_unary(expr)
    if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    as_condition = Condition(current, False)
    if self._conditions_imply(tuple(conditions or ()), (as_condition.negate(),)):
        return True
    operator = getattr(current, "operator", None)
    operands = tuple(getattr(current, "operands", ()) or ())
    if len(operands) != 2:
        return False
    if operator == "INT_SLESS":
        left, right = operands
        if self._constant_int_value(right) == 1 and getattr(left, "expr_type", None) == ExpressionType.PARAMETER:
            if any(
                self._condition_is_signed_positive_of_param(condition, left)
                for condition in conditions or ()
            ):
                return True
    if operator == "INT_SUB":
        left, right = operands
        if self._expression_is_one_under_conditions(left, conditions) and self._constant_int_value(right) == 1:
            return True
    return self._expressions_equal_under_conditions_smt(
        current,
        Expression.constant(0, size=max(1, int(getattr(current, "size", 0) or 4))),
        tuple(conditions or ()),
        getattr(self, "_current_parameters", ()) or (),
    )


def _impl__expression_is_placeholder_minus_one_unit_condition(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    conditions: Sequence[Condition],
) -> bool:
    return self._placeholder_minus_one_unit_condition_guard_key(expr, placeholder, conditions) is not None


def _impl__placeholder_minus_one_unit_condition_guard_key(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    conditions: Sequence[Condition],
) -> Optional[Tuple[Any, ...]]:
    current = self._strip_transparent_unary(expr)
    if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    if getattr(current, "operator", None) == "INT_ADD":
        operands = tuple(getattr(current, "operands", ()) or ())
        if len(operands) != 2:
            return None
        left, right = operands
        if self._expressions_same_key(left, placeholder):
            return self._negated_unit_condition_key_for_expression(right, conditions)
        if self._expressions_same_key(right, placeholder):
            return self._negated_unit_condition_key_for_expression(left, conditions)
        return None
    if getattr(current, "operator", None) != "INT_SUB":
        return None
    operands = tuple(getattr(current, "operands", ()) or ())
    if len(operands) != 2:
        return None
    if not self._expressions_same_key(operands[0], placeholder):
        return None
    return (
        self._unit_condition_key_for_expression(operands[1], conditions)
        or self._negated_unit_condition_key_for_expression(operands[1], conditions)
    )


def _impl__expression_is_placeholder_plus_unit_condition(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    conditions: Sequence[Condition],
) -> bool:
    return self._placeholder_plus_unit_condition_guard_key(expr, placeholder, conditions) is not None


def _impl__placeholder_plus_unit_condition_guard_key(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    conditions: Sequence[Condition],
) -> Optional[Tuple[Any, ...]]:
    current = self._strip_transparent_unary(expr)
    if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    if getattr(current, "operator", None) != "INT_ADD":
        return None
    operands = tuple(getattr(current, "operands", ()) or ())
    if len(operands) != 2:
        return None
    left, right = operands
    if self._expressions_same_key(left, placeholder):
        return self._unit_condition_key_for_expression(right, conditions)
    if self._expressions_same_key(right, placeholder):
        return self._unit_condition_key_for_expression(left, conditions)
    return None


def _impl__unit_condition_key_for_expression(
    self,
    expr: Optional[Expression],
    conditions: Sequence[Condition],
) -> Optional[Tuple[Any, ...]]:
    current = self._strip_transparent_unary(expr)
    if current is None:
        return None
    for condition in conditions or ():
        if condition is None:
            continue
        if self._expression_is_one_under_conditions(current, (condition,)):
            return self._condition_identity_key(condition)
    return None


def _impl__negated_unit_condition_key_for_expression(
    self,
    expr: Optional[Expression],
    conditions: Sequence[Condition],
) -> Optional[Tuple[Any, ...]]:
    current = self._strip_transparent_unary(expr)
    if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
        return None
    if getattr(current, "operator", None) != "INT_SUB":
        return None
    operands = tuple(getattr(current, "operands", ()) or ())
    if len(operands) != 2 or self._constant_int_value(operands[1]) != 1:
        return None
    flag_expr = self._strip_transparent_unary(operands[0])
    if flag_expr is None:
        return None
    for condition in conditions or ():
        if condition is None:
            continue
        if self._expression_is_zero_under_conditions(flag_expr, (condition,)) and self._expression_is_one_under_conditions(
            flag_expr,
            (condition.negate(),),
        ):
            return self._condition_identity_key(condition)
    return None


def _impl__strip_transparent_unary(expr: Optional[Expression]) -> Optional[Expression]:
    current = expr
    while (
        current is not None
        and getattr(current, "expr_type", None) == ExpressionType.UNARY_OP
        and getattr(current, "operator", None) in {"COPY", "CAST", "SUBPIECE", "INT_ZEXT", "INT_SEXT"}
        and len(tuple(getattr(current, "operands", ()) or ())) == 1
    ):
        current = tuple(getattr(current, "operands", ()) or ())[0]
    return current


def _impl__expression_is_placeholder_plus_constant(
    self,
    expr: Optional[Expression],
    placeholder: Expression,
    constant: int,
) -> bool:
    current = expr
    while (
        current is not None
        and getattr(current, "expr_type", None) == ExpressionType.UNARY_OP
        and getattr(current, "operator", None) in {"COPY", "CAST", "SUBPIECE", "INT_ZEXT", "INT_SEXT"}
        and len(tuple(getattr(current, "operands", ()) or ())) == 1
    ):
        current = tuple(getattr(current, "operands", ()) or ())[0]
    if current is None or getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    operands = tuple(getattr(current, "operands", ()) or ())
    if len(operands) != 2:
        return False
    operator = getattr(current, "operator", None)
    left, right = operands
    if operator == "INT_ADD":
        if self._expressions_same_key(left, placeholder) and self._constant_int_value(right) == constant:
            return True
        if self._expressions_same_key(right, placeholder) and self._constant_int_value(left) == constant:
            return True
        wrapped = self._constant_int_value(right)
        if self._expressions_same_key(left, placeholder) and wrapped is not None:
            return self._signed_unit_constant_matches(wrapped, constant, getattr(current, "size", None))
    if operator == "INT_SUB":
        if self._expressions_same_key(left, placeholder) and self._constant_int_value(right) == -constant:
            return True
    return False


def _impl__signed_unit_constant_matches(self, value: int, expected: int, size: Optional[int]) -> bool:
    if value == expected:
        return True
    bits = max(1, int(size or 4)) * 8
    mask = (1 << bits) - 1
    return (int(value) & mask) == (int(expected) & mask)


def _impl__condition_is_param_minus_one_nonpositive(
    self,
    condition: Condition,
    param: Expression,
    target_conditions: Sequence[Condition] = (),
) -> bool:
    if condition is None:
        return False
    expr = getattr(condition, "expression", None)
    if expr is None or getattr(expr, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    operands = tuple(getattr(expr, "operands", ()) or ())
    if len(operands) != 2:
        return False
    operator = getattr(expr, "operator", None)
    if operator == "INT_SLESSEQUAL" and not getattr(condition, "negated", False):
        return self._branch_guarded_expression_is_param_minus_one(operands[0], param, target_conditions) and self._constant_int_value(operands[1]) == 0
    if operator == "INT_SLESS" and getattr(condition, "negated", False):
        return self._constant_int_value(operands[0]) == 0 and self._branch_guarded_expression_is_param_minus_one(operands[1], param, target_conditions)
    return False


def _impl__expression_is_one_under_conditions(
    self,
    expr: Optional[Expression],
    target_conditions: Sequence[Condition],
) -> bool:
    if self._constant_int_value(expr) == 1:
        return True
    current = expr
    while (
        current is not None
        and getattr(current, "expr_type", None) == ExpressionType.UNARY_OP
        and getattr(current, "operator", None) in {"INT_ZEXT", "INT_SEXT", "CAST", "COPY"}
        and len(tuple(getattr(current, "operands", ()) or ())) == 1
    ):
        current = tuple(getattr(current, "operands", ()) or ())[0]
    if current is None:
        return False
    if getattr(current, "expr_type", None) != ExpressionType.BINARY_OP:
        return False
    if getattr(current, "operator", None) == "INT_SLESS":
        operands = tuple(getattr(current, "operands", ()) or ())
        if (
            len(operands) == 2
            and self._constant_int_value(operands[1]) == 1
            and getattr(operands[0], "expr_type", None) == ExpressionType.PARAMETER
            and any(
                self._condition_is_signed_nonpositive_of_param(condition, operands[0])
                for condition in target_conditions or ()
            )
        ):
            return True
    as_condition = Condition(current, False)
    if any(
        existing is not None
        and (
            existing.equals(as_condition)
            or ConditionNormalizer.are_equivalent(existing, as_condition)
        )
        for existing in target_conditions or ()
    ):
        return True
    return self._conditions_imply(tuple(target_conditions or ()), (as_condition,))


def _impl__expression_is_param_minus_one(self, expr: Expression, param: Expression) -> bool:
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or expr.operator not in {"INT_ADD", "INT_SUB"}:
        return False
    if len(expr.operands or ()) != 2:
        return False
    left, right = expr.operands
    if not self._expression_is_same_parameter(left, param):
        return False
    if right.expr_type != ExpressionType.CONSTANT:
        return False
    try:
        value = int(right.value)
    except (TypeError, ValueError):
        return False
    bits = max(1, int(getattr(left, "size", 0) or getattr(expr, "size", 0) or 4)) * 8
    mask = (1 << bits) - 1
    if expr.operator == "INT_SUB":
        return value == 1
    return (value & mask) == mask

"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence_summary``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    Condition,
    Expression,
    ExpressionType,
    ReturnInfo,
    UnknownValueRef,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__try_summarize_linear_self_recursion(self, function, high_function, analysis) -> Optional[Tuple[List[ReturnInfo], str]]:
    function_name = function.getName()
    recursive_returns = [
        ret for ret in (analysis.returns or [])
        if self._expression_contains_recursive_unknown(ret.value, function_name)
    ]
    if len(recursive_returns) != 1:
        self._debug(
            f"Declined '{function_name}': expected exactly one recursive return, found {len(recursive_returns)}"
        )
        return None

    base_returns = [
        ret for ret in (analysis.returns or [])
        if ret not in recursive_returns and self._is_constant_expression(ret.value)
    ]
    if len(base_returns) != 1:
        self._debug(
            f"Declined '{function_name}': expected exactly one constant base return, found {len(base_returns)}"
        )
        return None

    param_info = dict(analysis.parameters[0])
    if not self._parameter_can_be_counter(param_info):
        self._debug(f"Declined '{function_name}': parameter is not a scalar counter candidate")
        return None

    param_expr = self._parameter_expression(param_info)
    param_name = param_expr.name
    if not param_name:
        self._debug(f"Declined '{function_name}': parameter name is unavailable")
        return None
    recursive_ret = recursive_returns[0]
    base_ret = base_returns[0]

    lower_bound = self._infer_lower_bound_from_conditions(recursive_ret.conditions, param_name)
    if lower_bound is None:
        lower_bound = self._infer_lower_bound_from_base_conditions(base_ret.conditions, param_name)
    if lower_bound is None:
        self._debug(f"Declined '{function_name}': could not infer recursion/base split bound")
        return None

    self_call_ops = [
        op for op in self._iter_pcode_ops(high_function)
        if op.getMnemonic() == "CALL"
        and op.getNumInputs() >= 2
        and self._is_direct_self_call(op, function_name)
    ]
    if len(self_call_ops) != 1:
        self._debug(
            f"Declined '{function_name}': expected exactly one direct self-call, found {len(self_call_ops)}"
        )
        return None

    call_arg_expr = self.tracer.trace_varnode(self_call_ops[0].getInput(1), use_cache=False)
    step = self._extract_unit_step_from_call_argument(call_arg_expr, param_name)
    if step != -1:
        self._debug(
            f"Declined '{function_name}': recursive call argument is not a unit decrement "
            f"({call_arg_expr.to_string()})"
        )
        return None

    addend_expr = self._extract_addend_expression(recursive_ret.value, function_name)
    if addend_expr is None:
        self._debug(
            f"Declined '{function_name}': could not isolate non-recursive addend from "
            f"{recursive_ret.value.to_string()}"
        )
        return None

    affine = self._extract_affine_term(addend_expr, param_name)
    if affine is None:
        self._debug(
            f"Declined '{function_name}': addend is not affine in the counter "
            f"({addend_expr.to_string()})"
        )
        return None
    coeff, bias = affine

    base_value = self._constant_value(base_ret.value)
    if base_value is None:
        self._debug(f"Declined '{function_name}': base value is not a concrete constant")
        return None

    recursive_value = self._build_closed_form(
        param_expr=param_expr,
        lower_bound=lower_bound,
        coeff=coeff,
        bias=bias,
        base_value=base_value,
    )
    if recursive_value is None:
        self._debug(f"Declined '{function_name}': failed to construct closed-form summary")
        return None

    recursive_conditions = self._build_recursive_conditions(param_expr, lower_bound)
    base_conditions = self._build_base_conditions(param_expr, lower_bound)
    if recursive_conditions is None or base_conditions is None:
        self._debug(f"Declined '{function_name}': failed to build guard conditions for summary")
        return None

    summarized_returns = [
        ReturnInfo(
            address=base_ret.address,
            value=Expression.constant(base_value, recursive_value.size or param_expr.size or 4),
            conditions=base_conditions,
            branch_index=base_ret.branch_index,
            pcode_identity=base_ret.pcode_identity,
            pcode_order=base_ret.pcode_order,
            pcode_time=base_ret.pcode_time,
            pcode_op_ref=getattr(base_ret, "pcode_op_ref", None),
            return_value_pcode_op_refs=tuple(
                getattr(base_ret, "return_value_pcode_op_refs", ()) or ()
            ),
        ),
        ReturnInfo(
            address=recursive_ret.address,
            value=recursive_value,
            conditions=recursive_conditions,
            branch_index=recursive_ret.branch_index,
            pcode_identity=recursive_ret.pcode_identity,
            pcode_order=recursive_ret.pcode_order,
            pcode_time=recursive_ret.pcode_time,
            pcode_op_ref=getattr(recursive_ret, "pcode_op_ref", None),
            return_value_pcode_op_refs=tuple(
                getattr(recursive_ret, "return_value_pcode_op_refs", ()) or ()
            ),
        ),
    ]

    self._debug(
        f"Recovered linear self-recursive summary for '{function_name}' "
        f"(lower_bound={lower_bound}, coeff={coeff}, bias={bias}, base={base_value})"
    )
    return summarized_returns, "linear_self_recursion_summary"

def _impl__expression_contains_recursive_unknown(self, expr: Optional[Expression], function_name: str) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.UNKNOWN:
        runtime_ref = getattr(expr, "runtime_ref", None)
        if not isinstance(runtime_ref, UnknownValueRef):
            return False
        target_ref = runtime_ref.target_ref
        return bool(
            target_ref is not None
            and target_ref.function_name == function_name
        )
    if expr.expr_type == ExpressionType.PHI and expr.value:
        return any(
            (cond is not None and self._expression_contains_recursive_unknown(cond.expression, function_name))
            or self._expression_contains_recursive_unknown(value, function_name)
            for cond, value in expr.value
        )
    return any(self._expression_contains_recursive_unknown(operand, function_name) for operand in expr.operands or [])

def _impl__build_recursive_conditions(self, param_expr: Expression, lower_bound: int) -> Optional[List[Condition]]:
    size = param_expr.size or 4
    lower_const = Expression.constant(lower_bound, size)
    cond_expr = Expression.binary_op("INT_SLESS", lower_const, param_expr)
    return [Condition(cond_expr, False)]

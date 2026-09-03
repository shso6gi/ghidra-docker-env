"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.recurrence_summary``."""

from __future__ import annotations

from typing import Any, List, Optional, Tuple
from ._shared import (
    Condition,
    Expression,
    ExpressionType,
    ReturnInfo,
    UnknownValueRef,
    _expressions_equivalent_under_conditions,
)
from ...model.recurrence_contracts import (
    ImmutableRecurrenceCondition,
    ImmutableRecurrenceExpression,
)

def _recurrence_semantic_expression_key(expr):
    if expr is None:
        return ("none",)
    if expr.expr_type == ExpressionType.UNKNOWN:
        ref = getattr(expr, "runtime_ref", None)
        target = getattr(ref, "target_ref", None)
        return ("recursive_unknown", getattr(target, "function_name", None))
    if expr.expr_type == ExpressionType.PHI:
        return (
            "phi",
            tuple(
                (
                    bool(getattr(cond, "negated", False)),
                    _recurrence_semantic_expression_key(
                        getattr(cond, "expression", None)
                    ),
                    _recurrence_semantic_expression_key(value),
                )
                for cond, value in (expr.value or ())
            ),
        )
    return (
        expr.expr_type.name,
        expr.operator,
        expr.value,
        int(expr.size or 0),
        tuple(
            _recurrence_semantic_expression_key(item)
            for item in (expr.operands or ())
        ),
    )


def _recurrence_semantic_conditions_key(conditions):
    return tuple(
        (
            bool(condition.negated),
            _recurrence_semantic_expression_key(condition.expression),
        )
        for condition in (conditions or ())
    )


def _recurrence_expression_node_count(expr):
    if expr is None:
        return 0
    if expr.expr_type == ExpressionType.PHI:
        return 1 + sum(
            _recurrence_expression_node_count(getattr(cond, "expression", None))
            + _recurrence_expression_node_count(value)
            for cond, value in (expr.value or ())
        )
    return 1 + sum(
        _recurrence_expression_node_count(item) for item in (expr.operands or ())
    )

def _impl__try_summarize_linear_self_recursion(self, function, high_function, analysis) -> Optional[Tuple[List[ReturnInfo], str]]:
    function_name = function.getName()
    recursive_returns = [
        ret for ret in (analysis.returns or [])
        if self._expression_contains_recursive_unknown(ret.value, function_name)
    ]
    if len(recursive_returns) > 1:
        # Bounded refinement may retain peeled recursive cases in addition to
        # the direct recurrence.  Select the unique shallow semantic member;
        # later candidate acceptance still proves overlap and full coverage.
        scores = tuple(
            (_recurrence_expression_node_count(ret.value) + len(ret.conditions or ()), ret)
            for ret in recursive_returns
        )
        minimum = min(score for score, _ret in scores)
        shallow = tuple(ret for score, ret in scores if score == minimum)
        semantic_members = {}
        for ret in shallow:
            member_key = (
                    _recurrence_semantic_expression_key(ret.value),
                    _recurrence_semantic_conditions_key(ret.conditions),
                )
            semantic_members.setdefault(member_key, ret)
        recursive_returns = list(semantic_members.values())
    if len(recursive_returns) != 1:
        self._debug(
            f"Declined '{function_name}': expected exactly one recursive return, found {len(recursive_returns)}"
        )
        for index, ret in enumerate(recursive_returns):
            self._debug(
                f"  recursive[{index}] value={ret.value.to_string()} "
                f"guards={[condition.to_string() for condition in ret.conditions]}"
            )
        return None

    base_returns = [
        ret for ret in (analysis.returns or [])
        if ret not in recursive_returns
        and not self._expression_contains_recursive_unknown(ret.value, function_name)
    ]

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
    affine_base_returns = []
    for ret in base_returns:
        if self._constant_value(ret.value) is not None:
            affine_base_returns.append(ret)
            continue
        if self._extract_affine_term(ret.value, param_name) is not None:
            affine_base_returns.append(ret)
    if affine_base_returns:
        minimum_base_score = min(
            _recurrence_expression_node_count(ret.value)
            + len(ret.conditions or ())
            for ret in affine_base_returns
        )
        affine_base_returns = [
            ret
            for ret in affine_base_returns
            if _recurrence_expression_node_count(ret.value)
            + len(ret.conditions or ())
            == minimum_base_score
        ]
    base_members = {}
    for ret in affine_base_returns:
        base_members.setdefault(
            (
                _recurrence_semantic_expression_key(ret.value),
                _recurrence_semantic_conditions_key(ret.conditions),
            ),
            ret,
        )
    if len(base_members) > 1:
        representative = next(iter(base_members.values()))
        if all(
            _expressions_equivalent_under_conditions(
                representative.value,
                item.value,
                tuple(representative.conditions or ()) + tuple(item.conditions or ()),
                analysis.parameters,
            )
            for item in tuple(base_members.values())[1:]
        ):
            base_members = {"object_equivalent": representative}
    if len(base_members) != 1:
        self._debug(
            f"Declined '{function_name}': expected exactly one affine base return, found {len(base_members)}"
        )
        return None
    base_ret = next(iter(base_members.values()))

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
        base_affine = self._extract_affine_term(base_ret.value, param_name)
        if base_affine is None:
            self._debug(f"Declined '{function_name}': base value is not affine")
            return None
        base_coeff, base_bias = base_affine
        width = int((base_ret.value.size or param_expr.size or 4) * 8)
        base_value = (base_coeff * lower_bound + base_bias) & ((1 << width) - 1)

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

    self_call_ref = self._make_pcode_op_ref(self_call_ops[0])
    if self_call_ref is None:
        self._debug(f"Declined '{function_name}': self-call identity is unavailable")
        return None
    function_key = (
        analysis.function_ref.stable_key()
        if callable(getattr(analysis.function_ref, "stable_key", None))
        else None
    )
    if function_key is None:
        self._debug(f"Declined '{function_name}': function identity is unavailable")
        return None
    base_affine = self._extract_affine_term(base_ret.value, param_name)
    if base_affine is None:
        base_affine = (0, int(base_value))
    source_key = (
        "linear_self_recursion_summary_v1",
        ("function", function_key),
        ("counter", int(param_info.get("index", 0)), int(param_expr.size or 0)),
        ("step", -1),
        ("split_bound", int(lower_bound)),
        ("base_affine", tuple(base_affine)),
        ("addend_affine", int(coeff), int(bias)),
    )
    transition_evidence = (
        "linear_self_recursion_transition_evidence_v1",
        ("function", function_key),
        ("self_call", self_call_ref.stable_key()),
        ("counter", int(param_info.get("index", 0)), int(param_expr.size or 0)),
        ("step", -1),
        ("split_bound", int(lower_bound)),
        ("base_affine", tuple(base_affine)),
        ("addend_affine", int(coeff), int(bias)),
        ("effect_profile", "single_direct_self_call_no_store"),
        ("termination_measure", "signed_unit_decrement_to_bound"),
        ("width", int((recursive_value.size or param_expr.size or 0) * 8)),
        ("replacement_obligation", "not_required_without_phi_circular"),
    )
    retained_base_ref = None
    try:
        retained_conditions = tuple(
            ImmutableRecurrenceCondition.from_condition(condition).stable_key()
            for condition in (base_ret.conditions or ())
        )
        retained_value = ImmutableRecurrenceExpression.from_expression(
            base_ret.value
        ).stable_key()
        retained_base_identity = (
            "return_info",
            base_ret.address,
            base_ret.pcode_identity,
            base_ret.pcode_order,
            base_ret.pcode_time,
            base_ret.pcode_op_ref.stable_key()
            if callable(getattr(base_ret.pcode_op_ref, "stable_key", None))
            else None,
            retained_conditions,
            retained_value,
        )
        retained_base_ref = (
            "retained_exact_return_v1",
            retained_base_identity,
            (retained_conditions, retained_value, "exact"),
        )
    except (TypeError, ValueError):
        # The summary may still be representable even when the original base
        # guard contains a legacy VARIABLE node.  In that case it remains new
        # proposal payload; it is never mislabeled as retained exact evidence.
        retained_base_ref = None

    summarized_returns = [
        ReturnInfo(
            address=base_ret.address,
            value=base_ret.value,
            conditions=base_conditions,
            branch_index=base_ret.branch_index,
            pcode_identity=base_ret.pcode_identity,
            pcode_order=base_ret.pcode_order,
            pcode_time=base_ret.pcode_time,
            pcode_op_ref=getattr(base_ret, "pcode_op_ref", None),
            return_value_pcode_op_refs=tuple(
                getattr(base_ret, "return_value_pcode_op_refs", ()) or ()
            ),
            summary_candidate_source_key=source_key,
            summary_transition_evidence_key=transition_evidence,
            retained_exact_return_ref=retained_base_ref,
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
            summary_candidate_source_key=source_key,
            summary_transition_evidence_key=transition_evidence,
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

"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.analyzer``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    Condition,
    Expression,
    ExpressionType,
    eval_constant_raw,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

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

def _impl__expression_contains_unresolved_value(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return True

    expr_type = getattr(expr, "expr_type", None)
    if expr_type is None:
        return True

    if expr_type == ExpressionType.UNKNOWN:
        return True

    if expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            cond_expr = getattr(cond, "expression", None) if cond is not None else None
            if cond_expr is not None and self._expression_contains_unresolved_value(cond_expr):
                return True
            if self._expression_contains_unresolved_value(value):
                return True
        return False

    for operand in getattr(expr, "operands", []) or []:
        if self._expression_contains_unresolved_value(operand):
            return True

    return False

def _impl__contains_multiequal(self, varnode, depth: int = 0) -> bool:
    """Return値のチェーン内にMULTIEQUALが含まれるかチェック"""
    if depth > 15:
        return False

    if varnode is None:
        return False

    def_op = varnode.getDef()
    if def_op is None:
        return False

    mnemonic = def_op.getMnemonic()

    if mnemonic == "MULTIEQUAL":
        return True

    for i in range(def_op.getNumInputs()):
        input_vn = def_op.getInput(i)
        if self._contains_multiequal(input_vn, depth + 1):
            return True

    return False

def _impl_refresh_structural_recurrence_summary(
    self,
    analysis: Optional[FunctionReturnAnalysis],
    timeout: int = 60,
) -> Optional[FunctionReturnAnalysis]:
    """既存解析ビューに対して structural recurrence summary を再構築する。"""
    if analysis is None or not analysis.returns:
        return analysis

    function = self._find_function_by_name(analysis.function_name)
    if function is None:
        return analysis

    from ..decompilation_broker import (
        RECURRENCE_REFRESH_SOURCE_CONTRACT,
        decompile_function,
    )
    results = decompile_function(
        self, function, timeout, None,
        source_contract_id=RECURRENCE_REFRESH_SOURCE_CONTRACT,
        semantic_owner="subordinate",
    )
    if not results.decompileCompleted():
        self._debug_print(
            f"Structural summary refresh decompilation failed for '{analysis.function_name}'"
        )
        return analysis

    high_function = results.getHighFunction()
    if high_function is None:
        self._debug_print(
            f"Structural summary refresh HighFunction is None for '{analysis.function_name}'"
        )
        return analysis

    tracer = self._make_tracer(high_function)
    summary = self._apply_structural_recurrence_summary(
        function,
        high_function,
        analysis,
        tracer,
    )
    if summary is None:
        return analysis

    self._normalize_return_partition(summary)
    self._mark_incomplete_control_flow(summary)
    return summary

def _impl_get_last_function_lookup_error(self) -> Optional[str]:
    return self._last_function_lookup_error

def _impl_get_last_analysis_failure(self) -> Optional[AnalysisFailure]:
    return self._last_analysis_failure

def _impl_get_last_analysis_failure_status(self) -> Optional[str]:
    failure = self._last_analysis_failure
    return failure.status if failure is not None else None

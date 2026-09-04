"""Recognising and stripping stack-protector guard conditions."""

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
from typing import Any, List, Mapping, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.analysis.returns._shared import (
    ConditionNormalizer,
    ConditionSimplifier,
    eval_constant_raw,
)
from typing import List, Optional, Tuple


def _impl__strip_stack_protector_only_conditions(
    self,
    return_infos: List[ReturnInfo],
) -> List[ReturnInfo]:
    if not return_infos:
        return return_infos

    stripped_infos: List[ReturnInfo] = []
    changed = False

    for info in return_infos:
        if not info.conditions:
            stripped_infos.append(info)
            continue

        retained_conditions = [
            cond
            for cond in info.conditions
            if not self._condition_looks_like_stack_protector_guard(cond)
        ]
        if len(retained_conditions) == len(info.conditions):
            stripped_infos.append(info)
            continue

        changed = True
        if self.debug:
            removed_dump = [
                ConditionSimplifier.get_simplified_condition_string(cond)
                for cond in info.conditions
                if cond not in retained_conditions
            ]
            self._debug_print(
                "Dropped object-centric stack-protector guard conditions from "
                f"return case: {removed_dump}"
            )

        stripped_infos.append(
            self._make_return_info(
                address=info.address,
                value=info.value,
                conditions=retained_conditions,
                branch_index=info.branch_index,
                site_metadata=self._return_site_metadata_from_info(info),
            )
        )

    if not changed:
        return return_infos
    return stripped_infos


def _impl__condition_looks_like_stack_protector_guard(self, condition: Condition) -> bool:
    compared = self._extract_stack_protector_compare_pair(condition)
    if compared is None:
        return False
    left, right = compared
    return self._reads_share_stack_protector_probe(left, right)


def _impl__extract_stack_protector_compare_pair(
    self,
    condition: Optional[Condition],
) -> Optional[Tuple[Expression, Expression]]:
    if condition is None:
        return None

    decomposed = self._decompose_comparison_condition(condition)
    if decomposed is None:
        return None

    _negated, operator, left, right = decomposed
    if operator in {"INT_NOTEQUAL", "INT_EQUAL"}:
        if self._is_zero_constant(right):
            pair = self._extract_difference_pair(left)
            if pair is not None:
                return pair
        if self._is_zero_constant(left):
            pair = self._extract_difference_pair(right)
            if pair is not None:
                return pair
        return left, right
    return None


def _impl__extract_difference_pair(
    self,
    expr: Optional[Expression],
) -> Optional[Tuple[Expression, Expression]]:
    if expr is None or expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
        return None
    if expr.operator != "INT_SUB":
        return None
    return expr.operands[0], expr.operands[1]


def _impl__is_zero_constant(self, expr: Optional[Expression]) -> bool:
    return (
        expr is not None
        and expr.expr_type == ExpressionType.CONSTANT
        and int(expr.value) == 0
    )


def _impl__reads_share_stack_protector_probe(
    self,
    left: Expression,
    right: Expression,
) -> bool:
    left_probe = self._extract_stack_protector_memory_probe(left)
    right_probe = self._extract_stack_protector_memory_probe(right)
    if left_probe is None or right_probe is None:
        return False

    left_base_key, left_disp, left_deref_depth, left_size = left_probe
    right_base_key, right_disp, right_deref_depth, right_size = right_probe
    if left_size != right_size:
        return False
    if left_base_key != right_base_key or left_disp != right_disp:
        return False
    return {left_deref_depth, right_deref_depth} == {0, 1}


def _impl__extract_indirect_probe(
    self,
    expr: Optional[Expression],
) -> Optional[Tuple[StructuralKey, int, int]]:
    if expr is None:
        return None

    current = expr
    while (
        current.expr_type == ExpressionType.UNARY_OP
        and current.operator in {"INT_ZEXT", "INT_SEXT", "INT_2COMP"}
        and current.operands
    ):
        current = current.operands[0]

    if current.expr_type != ExpressionType.BINARY_OP or len(current.operands) != 2:
        return None
    if current.operator not in {"INDIRECT", "PTRADD", "PTRSUB", "INT_ADD"}:
        return None

    left, right = current.operands
    displacement = self._constant_int_value(right)
    base_expr = left
    if displacement is None:
        displacement = self._constant_int_value(left)
        base_expr = right
    if displacement is None:
        return None

    deref_depth = 0
    while base_expr.expr_type == ExpressionType.MEMORY and base_expr.operands:
        deref_depth += 1
        base_expr = base_expr.operands[0]

    return (
        ConditionNormalizer.expression_signature(
            base_expr,
            include_memory_read_order=False,
        ),
        displacement,
        deref_depth,
    )


def _impl__constant_int_value(self, expr: Optional[Expression]) -> Optional[int]:
    if expr is None or expr.expr_type != ExpressionType.CONSTANT:
        return None
    try:
        return int(expr.value)
    except (TypeError, ValueError):
        return None

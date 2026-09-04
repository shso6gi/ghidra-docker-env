"""PHI origin keys, phi-circular markers and finite fallback candidates."""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple, cast
from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.expression import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.runtime_refs import ReadonlyReductionRef, UnknownValueRef
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
    ConditionSimplifier,
    _iter_expression_nodes,
    eval_constant_raw,
)
from typing import Any, List, Optional, Sequence, Set, Tuple


def _impl__phi_circular_origin_stable_keys(self, expr: Optional[Expression]) -> Set[Tuple[Any, ...]]:
    keys: Set[Tuple[Any, ...]] = set()
    for node in _iter_expression_nodes(expr):
        if getattr(node, "expr_type", None) != ExpressionType.UNKNOWN:
            continue
        if not self._expression_contains_phi_circular_marker(node):
            continue
        runtime_ref = getattr(node, "runtime_ref", None)
        origin_ref = getattr(runtime_ref, "origin_ref", None)
        stable_key = getattr(origin_ref, "stable_key", None)
        if callable(stable_key):
            try:
                key = stable_key()
            except Exception:
                key = None
            if isinstance(key, tuple):
                keys.add(key)
    return keys


def _impl__candidate_phi_origin_keys_from_summary_source_key(self, value) -> Set[Tuple[Any, ...]]:
    keys: Set[Tuple[Any, ...]] = set()
    if not isinstance(value, tuple):
        return keys
    for item in value:
        if (
            isinstance(item, tuple)
            and len(item) == 2
            and item[0] == "candidate_phi_origin_keys"
        ):
            raw_keys = item[1]
            for raw_key in tuple(raw_keys or ()):
                if isinstance(raw_key, tuple):
                    keys.add(raw_key)
            continue
        if isinstance(item, tuple):
            keys.update(self._candidate_phi_origin_keys_from_summary_source_key(item))
    return keys


def _impl__phi_circular_additive_signature(self, expr: Optional[Expression]) -> Optional[Tuple[int, int]]:
    if expr is None:
        return None
    if self._expression_contains_phi_circular_marker(expr):
        if getattr(expr, "expr_type", None) == ExpressionType.UNKNOWN:
            return (1, 0)
    expr_type = getattr(expr, "expr_type", None)
    if expr_type == ExpressionType.CONSTANT:
        value = self._constant_int_value(expr)
        if value is None:
            return None
        return (0, int(value))
    if expr_type == ExpressionType.UNARY_OP and getattr(expr, "operator", None) in {"COPY", "CAST", "SUBPIECE", "INT_ZEXT", "INT_SEXT"}:
        operands = tuple(getattr(expr, "operands", ()) or ())
        if len(operands) != 1:
            return None
        return self._phi_circular_additive_signature(operands[0])
    if expr_type != ExpressionType.BINARY_OP:
        return None
    operands = tuple(getattr(expr, "operands", ()) or ())
    if len(operands) != 2:
        return None
    left = self._phi_circular_additive_signature(operands[0])
    right = self._phi_circular_additive_signature(operands[1])
    if left is None or right is None:
        return None
    operator = getattr(expr, "operator", None)
    if operator == "INT_ADD":
        return (left[0] + right[0], left[1] + right[1])
    if operator == "INT_SUB":
        return (left[0] - right[0], left[1] - right[1])
    return None


def _impl__expression_contains_phi_circular(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.UNKNOWN and "phi_circular" in str(getattr(expr, "value", "")):
        return True
    runtime_ref = getattr(expr, "runtime_ref", None)
    if getattr(runtime_ref, "reason", None) == "phi_circular" or getattr(runtime_ref, "kind", None) == "phi_circular":
        return True
    return any(self._expression_contains_phi_circular(operand) for operand in getattr(expr, "operands", []) or [])


def _impl__expression_contains_phi(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.PHI:
        return True
    for operand in getattr(expr, "operands", []) or []:
        if self._expression_contains_phi(operand):
            return True
    return False


def _impl__phi_origin_keys_from_varnode_defs(
    self,
    varnode,
    *,
    max_depth: int = 8,
) -> Set[Tuple[Any, ...]]:
    keys: Set[Tuple[Any, ...]] = set()
    seen: Set[int] = set()

    def visit(current, depth: int) -> None:
        if current is None or depth > int(max_depth):
            return
        marker = id(current)
        if marker in seen:
            return
        seen.add(marker)
        try:
            op = current.getDef()
        except Exception:
            op = None
        if op is None:
            return
        if getattr(op, "getMnemonic", lambda: None)() == "MULTIEQUAL":
            key = self._pcode_op_stable_key(op)
            if isinstance(key, tuple):
                keys.add(key)
        try:
            input_count = int(op.getNumInputs())
        except Exception:
            input_count = 0
        for index in range(input_count):
            try:
                visit(op.getInput(index), depth + 1)
            except Exception:
                continue

    visit(varnode, 0)
    return keys


def _impl__phi_free_finite_fallback_candidates(
    self,
    fallback_value: Expression,
    conditions: Sequence[Condition],
) -> List[Tuple[List[Condition], Expression]]:
    finite_condition_sets = self._split_small_finite_parameter_reachability_conditions(
        conditions,
    )
    if len(finite_condition_sets) <= 1:
        return []
    candidates: List[Tuple[List[Condition], Expression]] = []
    skipped_phi = 0
    skipped_none = 0
    for finite_conditions in finite_condition_sets:
        finite_value = self._normalize_expanded_return_value(
            fallback_value,
            finite_conditions,
        )
        if finite_value is None:
            skipped_none += 1
            continue
        if self._expression_contains_phi(finite_value):
            skipped_phi += 1
            continue
        candidates.append((finite_conditions, finite_value))
    if self.debug and (skipped_phi or skipped_none):
        self._debug_print(
            "Finite PHI fallback split retained "
            f"{len(candidates)}/{len(finite_condition_sets)} cases "
            f"(skipped_phi={skipped_phi}, skipped_none={skipped_none})"
        )
    return candidates


def _impl__split_small_finite_parameter_reachability_conditions(
    self,
    conditions: Sequence[Condition],
    *,
    search_min: int = -8,
    search_max: int = 64,
    max_cases: int = 16,
) -> List[List[Condition]]:
    parameter = self._single_parameter_expression_in_conditions(conditions)
    if parameter is None:
        return [list(conditions or [])]
    feasible_values: List[int] = []
    for value in range(int(search_min), int(search_max) + 1):
        equality = self._parameter_equals_condition(parameter, value)
        if not self._conditions_are_unsat(list(conditions or []) + [equality]):
            feasible_values.append(value)
            if len(feasible_values) > int(max_cases):
                return [list(conditions or [])]
    if len(feasible_values) <= 1:
        return [list(conditions or [])]
    uncovered_conditions = list(conditions or [])
    for value in feasible_values:
        uncovered_conditions.append(self._parameter_equals_condition(parameter, value).negate())
    if not self._conditions_are_unsat(uncovered_conditions):
        return [list(conditions or [])]
    result: List[List[Condition]] = []
    for value in feasible_values:
        split_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            list(conditions or []) + [self._parameter_equals_condition(parameter, value)]
        )
        if ConditionSimplifier.object_centric_is_contradiction(split_conditions):
            continue
        result.append(split_conditions)
    return result or [list(conditions or [])]


def _impl__single_parameter_expression_in_conditions(
    self,
    conditions: Sequence[Condition],
) -> Optional[Expression]:
    parameters: Dict[Tuple[Any, ...], Expression] = {}
    for condition in conditions or []:
        for node in _iter_expression_nodes(getattr(condition, "expression", None), include_phi_conditions=True):
            if getattr(node, "expr_type", None) != ExpressionType.PARAMETER:
                continue
            try:
                key = node.structural_key()
            except Exception:
                continue
            parameters[key] = node
            if len(parameters) > 1:
                return None
    return next(iter(parameters.values()), None)


def _impl__parameter_equals_condition(self, parameter: Expression, value: int) -> Condition:
    size = max(1, int(getattr(parameter, "size", 0) or 4))
    expr = Expression.binary_op("INT_EQUAL", parameter, Expression.constant(int(value), size=size))
    expr.size = 1
    return Condition(expr)


def _impl__phi_expression_key_set(
    self,
    expr: Optional[Expression],
) -> Set[Tuple[Any, ...]]:
    keys: Set[Tuple[Any, ...]] = set()

    def visit(node: Optional[Expression]) -> None:
        if node is None:
            return
        if getattr(node, "expr_type", None) == ExpressionType.PHI:
            try:
                keys.add(node.structural_key(budget=256))
            except Exception:
                pass
            for condition, value in getattr(node, "value", None) or []:
                if condition is not None:
                    visit(getattr(condition, "expression", None))
                visit(value)
            return
        for operand in getattr(node, "operands", None) or []:
            visit(operand)

    visit(expr)
    return keys


def _impl__expression_contains_phi_circular_marker(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if getattr(expr, "expr_type", None) == ExpressionType.UNKNOWN:
        if str(getattr(expr, "name", "") or getattr(expr, "value", "") or "") == "phi_circular":
            return True
        runtime_ref = getattr(expr, "runtime_ref", None)
        if (
            isinstance(runtime_ref, UnknownValueRef)
            and getattr(runtime_ref, "reason", None) == "phi_circular"
        ):
            return True
        if getattr(runtime_ref, "kind", None) == "phi_circular":
            return True
    return any(
        self._expression_contains_phi_circular_marker(operand)
        for operand in (getattr(expr, "operands", None) or ())
    )


def _impl__readonly_reduction_contract_priority_score(
    self,
    info: ReturnInfo,
) -> int:
    best_score = 0
    for node in _iter_expression_nodes(info.value, include_phi_conditions=False):
        runtime_ref = getattr(node, "runtime_ref", None)
        if isinstance(runtime_ref, ReadonlyReductionRef):
            best_score = max(
                best_score,
                self._readonly_reduction_ref_contract_priority_score(runtime_ref),
            )
    return best_score


def _impl__readonly_reduction_ref_contract_priority_score(
    self,
    runtime_ref: ReadonlyReductionRef,
) -> int:
    proof = getattr(runtime_ref, "accumulator_proof", None)
    if proof is None:
        return 0
    if not bool(getattr(proof, "return_region_value_proven", False)):
        return 0
    contract_key = None
    contract_key_fn = getattr(runtime_ref, "readonly_term_sequence_contract_key", None)
    if callable(contract_key_fn):
        try:
            contract_key = contract_key_fn()
        except (AttributeError, TypeError, ValueError):
            contract_key = None
    if contract_key is None:
        return 0

    semantic_witnesses = tuple(getattr(runtime_ref, "semantic_witnesses", ()) or ())
    exact_return_witnesses = tuple(getattr(proof, "exact_return_witnesses", ()) or ())
    loop_body_witnesses = tuple(getattr(proof, "loop_body_witnesses", ()) or ())
    seed_terms = tuple(getattr(proof, "seed_terms", ()) or ())
    return 1 + len(semantic_witnesses) + len(exact_return_witnesses) + len(loop_body_witnesses) + len(seed_terms)

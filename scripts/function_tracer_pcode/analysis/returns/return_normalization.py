"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.returns.analyzer``."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Tuple
from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.expression import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.structural import StructuralKey
from scripts.function_tracer_pcode.analysis.returns._shared import (
    ConditionSimplifier,
    ConditionTracker,
    PcodeTracer,
    _PCODE_CALL_OPCODES,
    _PCODE_OPCODE_BY_MNEMONIC,
    _PCODE_VALUE_PASSTHROUGH_OPCODES,
    _SIGNED_COMPARE_TO_UNSIGNED,
    _TrackedReturnValue,
    _UNSIGNED_COMPARE_TO_SIGNED,
    _expressions_equivalent,
    _reduce_expression_under_conditions,
    canonicalize_expr_read_location,
    expression_contains_post_state_reads,
    expression_matches_stale_post_state_replay,
    locations_match,
    promote_effect_value_match_to_post_state_read,
)

def _impl__normalize_return_partition(self, analysis: FunctionReturnAnalysis) -> None:
    if analysis is None:
        return
    self._normalize_return_callother_userops(analysis)
    analysis.returns = self._strip_stack_protector_only_conditions(analysis.returns)
    if "control_region_return_recovery" not in analysis.analysis_notes:
        analysis.returns = self._exclusivize_return_regions(analysis.returns)
    analysis.returns = self._merge_equivalent_return_infos(analysis.returns)

def _impl__rewrite_expression_signedness(
    self,
    expr: Optional[Expression],
    preferred: Dict[Tuple[StructuralKey, int], str],
) -> Tuple[Optional[Expression], bool]:
    if expr is None:
        return None, False

    changed = False
    rebuilt = expr

    if expr.expr_type == ExpressionType.PHI and expr.value:
        rewritten_branches = []
        branch_changed = False
        for cond, value in expr.value:
            rewritten_cond = cond
            if cond is not None:
                cond_expr, cond_changed = self._rewrite_expression_signedness(
                    cond.expression,
                    preferred,
                )
                rewritten_cond = Condition(cond_expr, cond.negated)
                branch_changed = branch_changed or cond_changed
            rewritten_value, value_changed = self._rewrite_expression_signedness(
                value,
                preferred,
            )
            branch_changed = branch_changed or value_changed
            rewritten_branches.append((rewritten_cond, rewritten_value))
        if branch_changed:
            rebuilt = expr.clone_with(value=rewritten_branches)
            changed = True
    elif getattr(expr, "operands", None):
        rewritten_operands = []
        operand_changed = False
        for operand in expr.operands:
            rewritten_operand, child_changed = self._rewrite_expression_signedness(
                operand,
                preferred,
            )
            rewritten_operands.append(rewritten_operand)
            operand_changed = operand_changed or child_changed
        if operand_changed:
            rebuilt = expr.clone_with(operands=rewritten_operands)
            changed = True

    if (
        rebuilt.expr_type == ExpressionType.BINARY_OP
        and rebuilt.operator in set(_UNSIGNED_COMPARE_TO_SIGNED) | set(_SIGNED_COMPARE_TO_UNSIGNED)
    ):
        fact = ConditionSimplifier.extract_scalar_constraint(Condition(rebuilt, False))
        if fact is not None:
            desired = preferred.get(fact.key)
            if desired == "signed" and rebuilt.operator in _UNSIGNED_COMPARE_TO_SIGNED:
                rebuilt = rebuilt.clone_with(operator=_UNSIGNED_COMPARE_TO_SIGNED[rebuilt.operator])
                changed = True
            elif desired == "unsigned" and rebuilt.operator in _SIGNED_COMPARE_TO_UNSIGNED:
                rebuilt = rebuilt.clone_with(operator=_SIGNED_COMPARE_TO_UNSIGNED[rebuilt.operator])
                changed = True

    return rebuilt, changed

def _impl__rewrite_tracked_return_values_for_op(
    self,
    tracked_values: List[_TrackedReturnValue],
    pcode_op,
    *,
    tracer: Optional[PcodeTracer],
    condition_tracker: Optional[ConditionTracker],
    path_conditions: Optional[List[Condition]] = None,
    current_function=None,
) -> Optional[List[_TrackedReturnValue]]:
    rewritten: List[_TrackedReturnValue] = []
    for tracked in tracked_values:
        updated = self._rewrite_single_tracked_return_value_for_op(
            tracked,
            pcode_op,
            tracer=tracer,
            condition_tracker=condition_tracker,
            path_conditions=path_conditions,
            current_function=current_function,
        )
        if updated is None:
            return None
        rewritten.extend(updated)
    return self._deduplicate_tracked_return_values(rewritten)

def _impl__rewrite_single_tracked_return_value_for_op(
    self,
    tracked: _TrackedReturnValue,
    pcode_op,
    *,
    tracer: Optional[PcodeTracer],
    condition_tracker: Optional[ConditionTracker],
    path_conditions: Optional[List[Condition]] = None,
    current_function=None,
) -> Optional[List[_TrackedReturnValue]]:
    if not self._tracked_return_value_is_affected_by_op(
        tracked,
        pcode_op,
        tracer=tracer,
        current_function=current_function,
    ):
        return [tracked]

    opcode = self._get_pcode_opcode(pcode_op)
    if opcode in _PCODE_CALL_OPCODES:
        return None

    if opcode in _PCODE_VALUE_PASSTHROUGH_OPCODES:
        propagated = self._propagate_passthrough_input_from_op(pcode_op, tracer)
        return propagated if propagated else None

    if opcode == _PCODE_OPCODE_BY_MNEMONIC["MULTIEQUAL"]:
        propagated = self._propagate_multiequal_input_for_return_path(
            pcode_op,
            tracer=tracer,
            condition_tracker=condition_tracker,
            path_conditions=path_conditions,
        )
        return propagated if propagated else None

    if opcode == _PCODE_OPCODE_BY_MNEMONIC["INDIRECT"]:
        propagated = self._propagate_indirect_return_effect(
            tracked,
            pcode_op,
            tracer=tracer,
        )
        return propagated if propagated else None

    return None

def _impl__normalize_bound_parameter_values(
    self,
    bound_parameter_values: Optional[Dict[int, Expression]],
) -> Dict[int, Expression]:
    normalized: Dict[int, Expression] = {}
    for index, expr in (bound_parameter_values or {}).items():
        try:
            normalized_index = int(index)
        except Exception:
            continue
        if normalized_index < 0 or expr is None:
            continue
        normalized[normalized_index] = self._clone_expression(expr)
    return normalized

def _impl__normalize_bound_parameter_storage_values(
    self,
    bound_parameter_storage_values: Optional[Dict[Tuple[Any, ...], Expression]],
) -> Dict[Tuple[Any, ...], Expression]:
    normalized: Dict[Tuple[Any, ...], Expression] = {}
    for key, expr in (bound_parameter_storage_values or {}).items():
        if key is None or expr is None:
            continue
        try:
            normalized_key = tuple(key)
        except Exception:
            continue
        if not normalized_key:
            continue
        normalized[normalized_key] = self._clone_expression(expr)
    return normalized

def _impl__rewrite_drops_composite_location_wrapper(
    self,
    original: Optional[Expression],
    rewritten: Optional[Expression],
    conditions: List[Condition],
) -> bool:
    if original is None or rewritten is None:
        return False
    if original.expr_type not in {
        ExpressionType.BINARY_OP,
        ExpressionType.UNARY_OP,
        ExpressionType.CALL,
        ExpressionType.INTRINSIC,
    }:
        return False

    original_location = canonicalize_expr_read_location(
        original,
        self._current_parameters,
    )
    rewritten_location = canonicalize_expr_read_location(
        rewritten,
        self._current_parameters,
    )
    if (
        original_location is None
        or rewritten_location is None
        or not locations_match(original_location, rewritten_location, conditions)
    ):
        return False
    if not self._is_direct_location_carrier(rewritten):
        return False
    current_effect_summary = self._current_effect_summary
    if (
        current_effect_summary is not None
        and (
            (
                promote_effect_value_match_to_post_state_read(
                    original,
                    original_location,
                    conditions,
                    current_effect_summary.effects,
                    self._current_parameters,
                    symbolic_post_state=True,
                )
                is not None
            )
            or expression_matches_stale_post_state_replay(
                original,
                rewritten,
                conditions,
                current_effect_summary.effects,
                self._current_parameters,
            )
        )
    ):
        return False
    return self._expression_has_nontrivial_location_wrapper(
        original,
        original_location,
    )

def _impl__normalize_expanded_return_value(
    self,
    value: Expression,
    conditions: List[Condition],
) -> Expression:
    normalized_value = value
    started_with_phi = self._expression_contains_phi(value)
    effect_summary = self._current_effect_summary
    has_effects = effect_summary is not None and bool(effect_summary.effects)

    if started_with_phi:
        reduced_value = _reduce_expression_under_conditions(value, conditions)
        reduced_value = self._reduce_phi_expression_under_conditions_with_smt(
            reduced_value if reduced_value is not None else value,
            conditions,
        )
        if reduced_value is not None:
            normalized_value = reduced_value
        if self.debug and normalized_value is not value:
            self._debug_print(
                "Reduced PHI-bearing expanded return under active conditions: "
                f"{self._debug_expr_summary(value)} -> {self._debug_expr_summary(normalized_value)}"
            )

    substituted_value = self._substitute_parameter_constants_under_conditions(
        normalized_value,
        conditions,
    )
    if substituted_value is not None and substituted_value is not normalized_value:
        normalized_value = substituted_value
        if self.debug:
            self._debug_print(
                "Specialized expanded return under exact parameter conditions: "
                f"{self._debug_expr_summary(value)} -> {self._debug_expr_summary(normalized_value)}"
            )
    assignments = self._parameter_constant_assignments_from_conditions(conditions)
    evaluated_value = self._evaluate_expression_under_parameter_assignments(
        normalized_value,
        assignments,
    )
    if evaluated_value is not None and evaluated_value is not normalized_value:
        normalized_value = evaluated_value
        if self.debug:
            self._debug_print(
                "Evaluated expanded return PHI selectors under exact parameter conditions: "
                f"{self._debug_expr_summary(value)} -> {self._debug_expr_summary(normalized_value)}"
            )

    if has_effects:
        assert effect_summary is not None
        canonicalized = self._normalize_return_value_with_effect_summary(
            normalized_value,
            conditions,
            effect_summary,
        )
        if canonicalized is not None:
            if self.debug and canonicalized is not normalized_value:
                self._debug_print(
                    "Normalized expanded return with definite post-state replay: "
                    f"{self._debug_expr_summary(normalized_value)} -> "
                    f"{self._debug_expr_summary(canonicalized)}"
                )
            normalized_value = canonicalized

    return normalized_value

def _impl__should_replay_canonicalized_return(
    self,
    canonicalized: Optional[Expression],
    original: Expression,
) -> bool:
    return (
        canonicalized is not None
        and not _expressions_equivalent(canonicalized, original)
        and not expression_contains_post_state_reads(canonicalized)
        and self._count_memory_reads(canonicalized) > self._count_memory_reads(original)
    )

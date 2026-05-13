# -*- coding: utf-8 -*-
"""Bounded fallback refinement for unresolved recursive call sites."""

from __future__ import annotations

import inspect
from typing import Callable, Dict, List, Optional, Sequence, Set, Tuple

from ..model import (
    CallTargetRef,
    Condition,
    DeferredCallInfo,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from .condition import ConditionSimplifier, ConditionNormalizer
from .effect_summary import (
    StoreEffect,
    _build_parameter_replacements,
    _call_arguments_width_safe_for_callee_analysis,
    _coerce_argument_to_callee_parameter,
    _coerce_storage_info,
    _enumerate_constant_expression_branches,
    _resolve_parameter_descriptor,
    _storage_infos_match,
    lower_post_state_expression_for_smt_if_needed,
    substitute_condition,
    substitute_expression,
)


ExpressionExpansion = Tuple[Expression, List[Condition]]


def _runtime_expression_signature(expr: Optional[Expression]):
    if expr is None:
        return ("none",)
    return ConditionNormalizer.expression_signature(expr)


def _runtime_conditions_signature(conditions: Sequence[Condition]):
    return ConditionNormalizer.conditions_signature(conditions)


def _expression_is_fully_resolved(expr: Optional[Expression]) -> bool:
    if expr is None:
        return True
    if expr.expr_type in {ExpressionType.UNKNOWN, ExpressionType.CALL}:
        return False
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and not _expression_is_fully_resolved(cond.expression):
                return False
            if not _expression_is_fully_resolved(value):
                return False
        return True
    for operand in getattr(expr, "operands", []) or []:
        if not _expression_is_fully_resolved(operand):
            return False
    return True


def _callable_accepts_positional_args(fn: Callable, count: int) -> bool:
    try:
        signature = inspect.signature(fn)
    except (TypeError, ValueError):
        return True
    positional_count = 0
    for param in signature.parameters.values():
        if param.kind == inspect.Parameter.VAR_POSITIONAL:
            return True
        if param.kind in {
            inspect.Parameter.POSITIONAL_ONLY,
            inspect.Parameter.POSITIONAL_OR_KEYWORD,
        }:
            positional_count += 1
    return positional_count >= count


def _return_info_is_concrete_fallback(ret: Optional[ReturnInfo]) -> bool:
    if ret is None or not _expression_is_fully_resolved(getattr(ret, "value", None)):
        return False
    for condition in getattr(ret, "conditions", []) or []:
        if condition is None or not _expression_is_fully_resolved(condition.expression):
            return False
    return True


class BoundedCallRefiner:
    """
    未解決 CALL プレースホルダを、有限回の inlining で保守的に展開する。

    - fuel により無限再帰を防止
    - max_cases により分岐爆発を防止
    - 解けない部分は UNKNOWN のまま保持
    """

    def __init__(
        self,
        analysis_provider: Callable[..., Optional[FunctionReturnAnalysis]],
        *,
        max_unroll: int = 2,
        max_cases: int = 128,
        debug: bool = False,
    ):
        self.analysis_provider = analysis_provider
        self.max_unroll = max(0, int(max_unroll))
        self.max_cases = max(1, int(max_cases))
        self.debug = debug
        self._analysis_provider_accepts_args = _callable_accepts_positional_args(
            analysis_provider,
            2,
        )

    def _debug(self, message: str) -> None:
        if self.debug:
            print(f"[BoundedCallRefiner] {message}")

    def _record_note(self, analysis: Optional[FunctionReturnAnalysis], note: str) -> None:
        if analysis is None or not note:
            return
        if note not in analysis.analysis_notes:
            analysis.analysis_notes.append(note)

    def _provide_analysis(
        self,
        target: object,
        args: Optional[Sequence[Expression]] = None,
    ) -> Optional[FunctionReturnAnalysis]:
        if self._analysis_provider_accepts_args:
            return self.analysis_provider(target, args)
        return self.analysis_provider(target)

    def refine_analysis(self, analysis: FunctionReturnAnalysis) -> bool:
        if analysis is None or not analysis.returns or not analysis.deferred_calls or self.max_unroll <= 0:
            return False
        analysis.normalize_deferred_calls()

        original_signature = self._analysis_signature(analysis.returns)
        refined_returns: List[ReturnInfo] = []

        for ret in analysis.returns:
            refined_returns.extend(self._expand_return_info(ret, analysis, self.max_unroll, set()))
            if len(refined_returns) >= self.max_cases:
                refined_returns = refined_returns[: self.max_cases]
                break

        if analysis.unknown_event_count or analysis.incomplete_control_flow:
            refined_returns.extend(
                ret
                for ret in (analysis.returns or [])
                if _return_info_is_concrete_fallback(ret)
            )

        deduped = self._deduplicate_return_infos(refined_returns)
        if not deduped:
            return False

        analysis.returns = deduped
        analysis.deferred_calls = self._filter_deferred_calls_in_use(analysis)

        changed = original_signature != self._analysis_signature(analysis.returns)
        if changed and "bounded_call_refinement" not in analysis.analysis_notes:
            analysis.analysis_notes.append("bounded_call_refinement")
        return changed

    def _analysis_signature(self, return_infos: Sequence[ReturnInfo]) -> Tuple[Tuple[object, object], ...]:
        signature = []
        for ret in return_infos or []:
            signature.append(
                (
                    _runtime_expression_signature(ret.value),
                    _runtime_conditions_signature(ret.conditions),
                )
            )
        return tuple(signature)

    def _expand_return_info(
        self,
        ret: ReturnInfo,
        analysis: FunctionReturnAnalysis,
        fuel: int,
        trail: Set[Tuple[object, ...]],
    ) -> List[ReturnInfo]:
        condition_states = self._expand_conditions(ret.conditions, analysis, fuel, trail)
        value_states = self._expand_expression(ret.value, analysis, fuel, trail)

        results: List[ReturnInfo] = []
        for conds in condition_states:
            for value_expr, extra_conditions in value_states:
                merged_conditions = ConditionSimplifier.simplify_conditions(
                    list(conds) + list(extra_conditions)
                )
                if ConditionSimplifier.is_contradiction(merged_conditions):
                    continue
                results.append(
                    ReturnInfo(
                        address=ret.address,
                        value=value_expr,
                        conditions=merged_conditions,
                        branch_index=ret.branch_index,
                        pcode_identity=ret.pcode_identity,
                        pcode_order=ret.pcode_order,
                        pcode_time=ret.pcode_time,
                        pcode_op_ref=getattr(ret, "pcode_op_ref", None),
                    )
                )
                if len(results) >= self.max_cases:
                    return results[: self.max_cases]
        return results

    def _expand_conditions(
        self,
        conditions: Sequence[Condition],
        analysis: FunctionReturnAnalysis,
        fuel: int,
        trail: Set[Tuple[object, ...]],
    ) -> List[List[Condition]]:
        states: List[List[Condition]] = [[]]

        for condition in conditions or []:
            next_states: List[List[Condition]] = []
            expansions = self._expand_expression(condition.expression, analysis, fuel, trail)
            for prefix in states:
                for expr, extra_conditions in expansions:
                    merged = ConditionSimplifier.simplify_conditions(
                        prefix + extra_conditions + [Condition(expr, condition.negated)]
                    )
                    if ConditionSimplifier.is_contradiction(merged):
                        continue
                    next_states.append(merged)
                    if len(next_states) >= self.max_cases:
                        break
                if len(next_states) >= self.max_cases:
                    break
            if not next_states:
                return []
            states = self._deduplicate_condition_sets(next_states)
        return states

    def _expand_expression(
        self,
        expr: Expression,
        analysis: FunctionReturnAnalysis,
        fuel: int,
        trail: Set[Tuple[object, ...]],
    ) -> List[ExpressionExpansion]:
        deferred = self._lookup_deferred_call(expr, analysis)
        if deferred is not None:
            deferred_key = deferred.identity_key()
            if fuel <= 0 or deferred_key in trail:
                return [(expr, [])]
            unfolded = self._expand_deferred_call(
                deferred,
                analysis,
                fuel - 1,
                trail | {deferred_key},
            )
            return unfolded or [(expr, [])]

        if expr is None:
            return [(expr, [])]

        if expr.expr_type in {
            ExpressionType.CONSTANT,
            ExpressionType.PARAMETER,
            ExpressionType.VARIABLE,
            ExpressionType.UNKNOWN,
            ExpressionType.LITERAL,
        }:
            return [(expr, [])]

        if expr.expr_type == ExpressionType.PHI and expr.value:
            return self._expand_phi_expression(expr, analysis, fuel, trail)

        if not expr.operands:
            return [(expr, [])]

        states: List[Tuple[List[Expression], List[Condition]]] = [([], [])]
        for operand in expr.operands:
            operand_expansions = self._expand_expression(operand, analysis, fuel, trail)
            next_states: List[Tuple[List[Expression], List[Condition]]] = []
            for built_operands, built_conditions in states:
                for new_operand, extra_conditions in operand_expansions:
                    next_states.append(
                        (
                            built_operands + [new_operand],
                            built_conditions + extra_conditions,
                        )
                    )
                    if len(next_states) >= self.max_cases:
                        break
                if len(next_states) >= self.max_cases:
                    break
            states = next_states
            if not states:
                return [(expr, [])]

        results: List[ExpressionExpansion] = []
        for operands, extra_conditions in states[: self.max_cases]:
            rebuilt = self._clone_expression_with_operands(expr, operands)
            merged_conditions = ConditionSimplifier.simplify_conditions(extra_conditions)
            if ConditionSimplifier.is_contradiction(merged_conditions):
                continue
            results.append((rebuilt, merged_conditions))

        return results or [(expr, [])]

    def _expand_phi_expression(
        self,
        expr: Expression,
        analysis: FunctionReturnAnalysis,
        fuel: int,
        trail: Set[Tuple[object, ...]],
    ) -> List[ExpressionExpansion]:
        states: List[Tuple[List[Tuple[Optional[Condition], Expression]], List[Condition]]] = [([], [])]
        for branch_condition, branch_value in expr.value or []:
            condition_expansions: List[Tuple[Optional[Condition], List[Condition]]]
            if branch_condition is None:
                condition_expansions = [(None, [])]
            else:
                condition_expansions = [
                    (Condition(condition_expr, branch_condition.negated), extra_conditions)
                    for condition_expr, extra_conditions in self._expand_expression(
                        branch_condition.expression,
                        analysis,
                        fuel,
                        trail,
                    )
                ]
            value_expansions = self._expand_expression(branch_value, analysis, fuel, trail)
            next_states: List[Tuple[List[Tuple[Optional[Condition], Expression]], List[Condition]]] = []
            for built_branches, built_conditions in states:
                for new_condition, condition_extra in condition_expansions:
                    for new_value, value_extra in value_expansions:
                        merged_extra = ConditionSimplifier.simplify_conditions(
                            list(built_conditions) + list(condition_extra) + list(value_extra)
                        )
                        if ConditionSimplifier.is_contradiction(merged_extra):
                            continue
                        next_states.append(
                            (
                                built_branches + [(new_condition, new_value)],
                                merged_extra,
                            )
                        )
                        if len(next_states) >= self.max_cases:
                            break
                    if len(next_states) >= self.max_cases:
                        break
                if len(next_states) >= self.max_cases:
                    break
            states = next_states
            if not states:
                return [(expr, [])]

        results: List[ExpressionExpansion] = []
        for branches, extra_conditions in states[: self.max_cases]:
            rebuilt = Expression.phi(branches)
            rebuilt.size = expr.size
            results.append((rebuilt, list(extra_conditions)))
        return self._deduplicate_expression_expansions(results) or [(expr, [])]

    def _expand_deferred_call(
        self,
        deferred: DeferredCallInfo,
        caller_analysis: FunctionReturnAnalysis,
        fuel: int,
        trail: Set[Tuple[object, ...]],
    ) -> List[ExpressionExpansion]:
        results: List[ExpressionExpansion] = []
        candidates = self._resolve_deferred_call_candidates(
            deferred
        )
        if not candidates:
            self._record_note(caller_analysis, "bounded_call_refinement_deferred_target_unresolved")
            self._debug(
                f"Skipped deferred call '{deferred.deferred_call_ref.display_name()}': "
                "no resolved callee analysis"
            )
            return []

        had_alignment_failure = False
        had_return_expansion = False
        for _target_ref, target_conditions, callee_analysis in candidates:
            already_specialized = self._analysis_is_fully_argument_specialized(callee_analysis)
            if already_specialized:
                aligned_arguments = []
                replacements = {}
            else:
                aligned_arguments = self._align_deferred_arguments_to_callee(
                    deferred,
                    caller_analysis.parameters,
                    callee_analysis.parameters,
                )
                if len(aligned_arguments) < len(callee_analysis.parameters):
                    had_alignment_failure = True
                    self._debug(
                        f"Skipped deferred call '{deferred.deferred_call_ref.display_name()}': expected "
                        f"{len(callee_analysis.parameters)} args, got {len(aligned_arguments)}"
                    )
                    continue
                if not _call_arguments_width_safe_for_callee_analysis(
                    callee_analysis,
                    aligned_arguments,
                ):
                    had_alignment_failure = True
                    self._debug(
                        f"Skipped deferred call '{deferred.deferred_call_ref.display_name()}': "
                        "partial-width argument is used as a full-width callee value"
                    )
                    continue

                replacements = _build_parameter_replacements(
                    callee_analysis.parameters,
                    aligned_arguments,
                )
            substituted_effects = self._substitute_effects_for_deferred_call(
                callee_analysis,
                replacements,
            )

            for ret in callee_analysis.returns:
                substituted_value = substitute_expression(ret.value, replacements, callee_analysis.parameters)
                substituted_conditions = [
                    substitute_condition(cond, replacements, callee_analysis.parameters)
                    for cond in ret.conditions
                ]
                substituted_value = self._lower_symbolic_post_state_after_substitution(
                    substituted_value,
                    substituted_conditions,
                    substituted_effects,
                    caller_analysis.parameters,
                )
                substituted_conditions = [
                    self._lower_symbolic_post_state_in_condition_after_substitution(
                        cond,
                        substituted_conditions,
                        substituted_effects,
                        caller_analysis.parameters,
                    )
                    for cond in substituted_conditions
                ]

                condition_sets = self._expand_conditions(
                    substituted_conditions,
                    callee_analysis,
                    fuel,
                    trail,
                )
                value_states = self._expand_expression(
                    substituted_value,
                    callee_analysis,
                    fuel,
                    trail,
                )

                for conds in condition_sets or [[]]:
                    for value_expr, extra_conditions in value_states:
                        merged_conditions = ConditionSimplifier.simplify_conditions(
                            list(target_conditions) + list(conds) + list(extra_conditions)
                        )
                        if ConditionSimplifier.is_contradiction(merged_conditions):
                            continue
                        had_return_expansion = True
                        results.append((value_expr, merged_conditions))
                        if len(results) >= self.max_cases:
                            self._record_note(
                                caller_analysis,
                                "bounded_call_refinement_deferred_expanded",
                            )
                            return results[: self.max_cases]

        if results:
            self._record_note(caller_analysis, "bounded_call_refinement_deferred_expanded")
        elif had_alignment_failure:
            self._record_note(caller_analysis, "bounded_call_refinement_argument_alignment_failed")
        elif not had_return_expansion:
            self._record_note(caller_analysis, "bounded_call_refinement_return_summary_unusable")
        return self._deduplicate_expression_expansions(results)

    def _resolve_deferred_call_candidates(
        self,
        deferred: DeferredCallInfo,
    ) -> List[Tuple[CallTargetRef, List[Condition], FunctionReturnAnalysis]]:
        candidates: List[Tuple[CallTargetRef, List[Condition], FunctionReturnAnalysis]] = []
        seen = set()

        def add_candidate(target_ref: CallTargetRef, conditions: Sequence[Condition]) -> None:
            call_arguments = list(getattr(deferred, "arguments", ()) or ())
            callee_analysis = None
            if call_arguments:
                callee_analysis = self._provide_analysis(target_ref, call_arguments)
            if callee_analysis is None:
                callee_analysis = self._provide_analysis(target_ref, None)
            if callee_analysis is None or not callee_analysis.returns:
                return
            key = (
                target_ref.stable_key(),
                _runtime_conditions_signature(conditions),
            )
            if key in seen:
                return
            seen.add(key)
            candidates.append((target_ref, list(conditions), callee_analysis))

        if deferred.call_target_expr is not None:
            for branch_conditions, address_value in _enumerate_constant_expression_branches(
                deferred.call_target_expr
            ):
                add_candidate(
                    CallTargetRef.from_code_address(address_value),
                    ConditionSimplifier.simplify_conditions(branch_conditions),
                )

        if deferred.target_ref is not None and not deferred.target_ref.is_unknown():
            add_candidate(deferred.target_ref, [])

        return candidates

    def _analysis_is_fully_argument_specialized(
        self,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> bool:
        if analysis is None:
            return False
        parameter_count = len(getattr(analysis, "parameters", ()) or ())
        if parameter_count <= 0:
            return False
        scope_key = getattr(analysis, "analysis_scope_key", None)
        if not isinstance(scope_key, tuple) or len(scope_key) < 4:
            return False
        bound_by_index = scope_key[2] if isinstance(scope_key[2], tuple) else ()
        bound_by_storage = scope_key[3] if isinstance(scope_key[3], tuple) else ()
        return max(len(bound_by_index), len(bound_by_storage)) >= parameter_count

    def _align_deferred_arguments_to_callee(
        self,
        deferred: DeferredCallInfo,
        caller_parameters: Sequence[Dict],
        callee_parameters: Sequence[Dict],
    ) -> List[Expression]:
        arguments = list(getattr(deferred, "arguments", []) or [])
        if not callee_parameters:
            return arguments

        if self._deferred_arguments_are_pcode_callsite_ordered(deferred):
            if len(arguments) < len(callee_parameters):
                return []
            aligned: List[Expression] = []
            for argument, callee_param in zip(arguments, callee_parameters):
                coerced = _coerce_argument_to_callee_parameter(argument, callee_param)
                aligned.append(coerced if coerced is not None else argument)
            return aligned

        if len(arguments) == 1 and len(callee_parameters) == 1:
            return list(arguments)
        aligned: List[Expression] = []
        used_argument_indexes: Set[int] = set()
        for callee_param in callee_parameters:
            best_index = None
            best_score = 0
            ambiguous_best = False
            for index, argument in enumerate(arguments):
                if index in used_argument_indexes:
                    continue
                score = self._callee_argument_match_score(
                    argument,
                    caller_parameters,
                    callee_param,
                )
                if score > best_score:
                    best_score = score
                    best_index = index
                    ambiguous_best = False
                elif score == best_score and score > 0:
                    ambiguous_best = True
            if best_index is not None and best_score >= 50 and not ambiguous_best:
                used_argument_indexes.add(best_index)
                aligned.append(arguments[best_index])
                continue

        return aligned

    def _deferred_arguments_are_pcode_callsite_ordered(
        self,
        deferred: Optional[DeferredCallInfo],
    ) -> bool:
        deferred_ref = getattr(deferred, "deferred_call_ref", None)
        pcode_ref = getattr(deferred_ref, "pcode_op_ref", None)
        if pcode_ref is None:
            return False
        mnemonic = getattr(pcode_ref, "mnemonic", None)
        if mnemonic is None:
            return False
        return str(mnemonic).upper() in {"CALL", "CALLIND"}

    def _callee_argument_match_score(
        self,
        argument: Optional[Expression],
        caller_parameters: Sequence[Dict],
        callee_param: Dict,
    ) -> int:
        if argument is None:
            return 0

        caller_param = _resolve_parameter_descriptor(argument, caller_parameters)
        if caller_param is None:
            return 0
        caller_storage = _coerce_storage_info(caller_param.get("storage")) if caller_param is not None else None
        callee_storage = _coerce_storage_info(callee_param.get("storage"))
        if caller_storage is not None and callee_storage is not None and _storage_infos_match(
            caller_storage,
            callee_storage,
        ):
            return 100
        return 0

    def _substitute_effects_for_deferred_call(
        self,
        callee_analysis: FunctionReturnAnalysis,
        replacements: Dict[Tuple[object, ...], Expression],
    ) -> List[StoreEffect]:
        effect_summary = getattr(callee_analysis, "effect_summary", None)
        if effect_summary is None or not getattr(effect_summary, "effects", None):
            return []

        substituted: List[StoreEffect] = []
        for effect in effect_summary.effects:
            substituted.append(
                StoreEffect(
                    location=effect.location,
                    value=substitute_expression(effect.value, replacements, callee_analysis.parameters),
                    conditions=[
                        substitute_condition(cond, replacements, callee_analysis.parameters)
                        for cond in (effect.conditions or [])
                    ],
                    order_key=effect.order_key,
                )
            )
        return substituted

    def _lower_symbolic_post_state_after_substitution(
        self,
        expr: Expression,
        conditions: Sequence[Condition],
        effects: Sequence[StoreEffect],
        parameters: Sequence[Dict],
    ) -> Expression:
        lowered = lower_post_state_expression_for_smt_if_needed(
            expr,
            conditions,
            effects,
            parameters,
        )
        return lowered if lowered is not None else expr

    def _lower_symbolic_post_state_in_condition_after_substitution(
        self,
        condition: Condition,
        conditions: Sequence[Condition],
        effects: Sequence[StoreEffect],
        parameters: Sequence[Dict],
    ) -> Condition:
        lowered_expr = self._lower_symbolic_post_state_after_substitution(
            condition.expression,
            conditions,
            effects,
            parameters,
        )
        if lowered_expr is condition.expression:
            return condition
        return Condition(lowered_expr, condition.negated)

    def _lookup_deferred_call(
        self,
        expr: Optional[Expression],
        analysis: FunctionReturnAnalysis,
    ) -> Optional[DeferredCallInfo]:
        if expr is None or expr.expr_type != ExpressionType.UNKNOWN:
            return None
        runtime_ref = getattr(expr, "runtime_ref", None)
        deferred_call_ref = getattr(runtime_ref, "deferred_call_ref", None)
        deferred_key = (
            deferred_call_ref.stable_key()
            if hasattr(deferred_call_ref, "stable_key")
            else None
        )
        if deferred_key is not None:
            return (analysis.deferred_calls or {}).get(deferred_key)
        return None

    def _clone_expression_with_operands(
        self,
        expr: Expression,
        operands: Sequence[Expression],
    ) -> Expression:
        cloned = Expression(
            expr.expr_type,
            value=expr.value,
            operator=expr.operator,
            operands=list(operands),
            size=expr.size,
            name=expr.name,
            data_type=expr.data_type,
            data_type_obj=getattr(expr, "data_type_obj", None),
            storage_info=expr.storage_info,
            read_order_key=getattr(expr, "read_order_key", None),
            runtime_ref=getattr(expr, "runtime_ref", None),
        )
        return cloned

    def _deduplicate_condition_sets(
        self,
        condition_sets: Sequence[Sequence[Condition]],
    ) -> List[List[Condition]]:
        seen = set()
        result: List[List[Condition]] = []
        for conditions in condition_sets:
            key = _runtime_conditions_signature(conditions)
            if key in seen:
                continue
            seen.add(key)
            result.append(list(conditions))
            if len(result) >= self.max_cases:
                break
        return result

    def _deduplicate_expression_expansions(
        self,
        expansions: Sequence[ExpressionExpansion],
    ) -> List[ExpressionExpansion]:
        seen = set()
        result: List[ExpressionExpansion] = []
        for expr, conditions in expansions:
            key = (
                _runtime_expression_signature(expr),
                _runtime_conditions_signature(conditions),
            )
            if key in seen:
                continue
            seen.add(key)
            result.append((expr, list(conditions)))
            if len(result) >= self.max_cases:
                break
        return result

    def _deduplicate_return_infos(
        self,
        return_infos: Sequence[ReturnInfo],
    ) -> List[ReturnInfo]:
        seen = set()
        result: List[ReturnInfo] = []
        for ret in return_infos:
            key = (
                ret.pcode_identity or ret.address,
                ret.branch_index,
                _runtime_expression_signature(ret.value),
                _runtime_conditions_signature(ret.conditions),
            )
            if key in seen:
                continue
            seen.add(key)
            result.append(ret)
            if len(result) >= self.max_cases:
                break
        return result

    def _filter_deferred_calls_in_use(
        self,
        analysis: FunctionReturnAnalysis,
    ) -> Dict[Tuple[object, ...], DeferredCallInfo]:
        used: Set[Tuple[object, ...]] = set()

        def visit_expression(expr: Optional[Expression]) -> None:
            if expr is None:
                return
            if expr.expr_type == ExpressionType.UNKNOWN:
                runtime_ref = getattr(expr, "runtime_ref", None)
                deferred_call_ref = getattr(runtime_ref, "deferred_call_ref", None)
                deferred_key = (
                    deferred_call_ref.stable_key()
                    if hasattr(deferred_call_ref, "stable_key")
                    else None
                )
                if deferred_key is not None:
                    used.add(deferred_key)
                    return
                return
            if expr.expr_type == ExpressionType.PHI and expr.value:
                for cond, value in expr.value:
                    if cond is not None:
                        visit_expression(cond.expression)
                    visit_expression(value)
                return
            for operand in expr.operands or []:
                visit_expression(operand)

        for ret in analysis.returns:
            visit_expression(ret.value)
            for cond in ret.conditions:
                visit_expression(cond.expression)

        return {
            key: info
            for key, info in analysis.deferred_calls.items()
            if key in used
        }

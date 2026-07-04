# -*- coding: utf-8 -*-
"""Bounded fallback refinement for unresolved recursive call sites."""

from __future__ import annotations

import inspect
from typing import Any, Callable, Dict, List, Mapping, Optional, Sequence, Set, Tuple

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
from .summary_returns import (
    _return_region_summary_proof_id_from_evidence,
    summary_return_acceptance_proof_id_from_evidence,
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


def _expression_contains_deferred_call_ref(expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if expr.expr_type == ExpressionType.UNKNOWN:
        runtime_ref = getattr(expr, "runtime_ref", None)
        return getattr(runtime_ref, "deferred_call_ref", None) is not None
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None and _expression_contains_deferred_call_ref(cond.expression):
                return True
            if _expression_contains_deferred_call_ref(value):
                return True
        return False
    for operand in getattr(expr, "operands", []) or []:
        if _expression_contains_deferred_call_ref(operand):
            return True
    return False


def _return_info_contains_deferred_call_ref(ret: Optional[ReturnInfo]) -> bool:
    if ret is None:
        return False
    if _expression_contains_deferred_call_ref(getattr(ret, "value", None)):
        return True
    for condition in getattr(ret, "conditions", []) or []:
        if condition is not None and _expression_contains_deferred_call_ref(condition.expression):
            return True
    return False


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
            expanded = self._expand_return_info(ret, analysis, self.max_unroll, set())
            contains_deferred_call = _return_info_contains_deferred_call_ref(ret)
            if contains_deferred_call:
                concrete_expanded = [
                    candidate
                    for candidate in expanded
                    if _return_info_is_concrete_fallback(candidate)
                ]
                has_unresolved_expansion = (
                    len(concrete_expanded) != len(expanded)
                    or len(expanded) >= self.max_cases
                )
                if has_unresolved_expansion:
                    remaining_slots = max(0, self.max_cases - len(refined_returns))
                    concrete_limit = max(0, remaining_slots - 1)
                    refined_returns.extend(concrete_expanded[:concrete_limit])
                else:
                    refined_returns.extend(concrete_expanded)
            else:
                refined_returns.extend(expanded)
                has_unresolved_expansion = False

            if contains_deferred_call and has_unresolved_expansion:
                refined_returns.append(ret)
                self._record_note(
                    analysis,
                    "bounded_call_refinement_preserved_unresolved_deferred_call",
                )
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
                        return_value_pcode_op_refs=tuple(
                            getattr(ret, "return_value_pcode_op_refs", ()) or ()
                        ),
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
            candidate_result_count = 0

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
                        candidate_result_count += 1
                        results.append((value_expr, merged_conditions))
                        if len(results) >= self.max_cases:
                            self._record_note(
                                caller_analysis,
                                "bounded_call_refinement_deferred_expanded",
                            )
                            return results[: self.max_cases]
            if candidate_result_count:
                self._record_bounded_call_refinement_expansion_evidence(
                    caller_analysis=caller_analysis,
                    deferred=deferred,
                    target_ref=_target_ref,
                    target_conditions=target_conditions,
                    callee_analysis=callee_analysis,
                    aligned_arguments=aligned_arguments,
                    result_count=candidate_result_count,
                )

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
        used_targets: Set[Tuple[Any, ...]] = set()

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
                target_ref = getattr(runtime_ref, "target_ref", None)
                target_key = (
                    target_ref.stable_key()
                    if hasattr(target_ref, "stable_key")
                    else None
                )
                if target_key is not None:
                    used_targets.add(target_key)
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

        candidates: List[
            Tuple[
                Tuple[object, ...],
                Tuple[object, ...],
                DeferredCallInfo,
                Optional[Tuple[Any, ...]],
            ]
        ] = []
        target_candidate_counts: Dict[Tuple[Any, ...], int] = {}
        for key, info in analysis.deferred_calls.items():
            info_ref = getattr(info, "deferred_call_ref", None)
            info_key = (
                info_ref.stable_key()
                if hasattr(info_ref, "stable_key")
                else key
            )
            info_target_ref = getattr(info, "target_ref", None)
            info_target_key = (
                info_target_ref.stable_key()
                if hasattr(info_target_ref, "stable_key")
                else None
            )
            candidates.append((key, info_key, info, info_target_key))
            if info_target_key is not None:
                target_candidate_counts[info_target_key] = target_candidate_counts.get(info_target_key, 0) + 1

        filtered: Dict[Tuple[object, ...], DeferredCallInfo] = {}
        for key, info_key, info, info_target_key in candidates:
            if key in used or info_key in used or (
                info_target_key is not None
                and info_target_key in used_targets
                and target_candidate_counts.get(info_target_key, 0) == 1
            ):
                filtered[info_key] = info
        return filtered

    def _record_bounded_call_refinement_expansion_evidence(
        self,
        *,
        caller_analysis: FunctionReturnAnalysis,
        deferred: DeferredCallInfo,
        target_ref: CallTargetRef,
        target_conditions: Sequence[Condition],
        callee_analysis: FunctionReturnAnalysis,
        aligned_arguments: Sequence[Expression],
        result_count: int,
    ) -> None:
        if caller_analysis is None or deferred is None or callee_analysis is None:
            return
        if int(result_count or 0) <= 0:
            return
        callee_effect_summary = getattr(callee_analysis, "effect_summary", None)
        if callee_effect_summary is None:
            self._debug("Skipped bounded refinement evidence: callee effect summary missing")
            return
        callee_effect_clean = (
            not getattr(callee_effect_summary, "effects", None)
            and not getattr(callee_effect_summary, "has_unsupported_call", False)
            and not getattr(callee_effect_summary, "incomplete_reasons", None)
        )
        if not callee_effect_clean:
            self._debug("Skipped bounded refinement evidence: callee effect summary not clean")
            return
        callee_requires_completed_summary_proof = self._callee_requires_completed_summary_proof(
            callee_analysis
        )
        callee_completed_proof_ids = self._callee_summary_completion_proof_ids(
            callee_analysis
        )
        callee_completed_proof_evidence_ids = self._callee_summary_completion_evidence_ids(
            callee_analysis
        )
        if callee_requires_completed_summary_proof and not (
            callee_completed_proof_ids or callee_completed_proof_evidence_ids
        ):
            self._debug(
                "Skipped bounded refinement evidence: summary-derived callee lacks completed proof refs"
            )
            return
        pcode_key = self._deferred_call_pcode_key(deferred)
        callee_key = self._call_target_key_for_analysis(target_ref, caller_analysis)
        argument_exprs = tuple(aligned_arguments or getattr(deferred, "arguments", ()) or ())
        argument_signature = tuple(_runtime_expression_signature(arg) for arg in argument_exprs)
        callee_partition_key = self._analysis_signature(getattr(callee_analysis, "returns", ()) or ())
        object_target_key = (
            "bounded_call_refinement_expansion",
            self._analysis_entry_key(caller_analysis),
            self._normalize_nested_tuple(pcode_key),
            self._normalize_nested_tuple(callee_key),
            argument_signature,
            self._analysis_entry_key(callee_analysis),
            callee_partition_key,
            _runtime_conditions_signature(target_conditions),
            int(result_count),
            int(self.max_unroll),
        )
        existing = tuple(getattr(caller_analysis, "completed_recovery_proof_evidence", ()) or ())
        if any(
            isinstance(item, dict)
            and self._normalize_nested_tuple(item.get("object_target_key")) == object_target_key
            and item.get("evidence_kind") == "bounded_call_refinement_expansion"
            for item in existing
        ):
            return
        content = {
            "object_derived": True,
            "status": "complete",
            "object_target_key": object_target_key,
            "callsite_pcode_key": self._normalize_nested_tuple(pcode_key),
            "callee_identity": self._normalize_nested_tuple(callee_key),
            "argument_signature": argument_signature,
            "callee_analysis_entry": self._analysis_entry_key(callee_analysis),
            "callee_return_partition_key": callee_partition_key,
            "callee_return_case_count": len(getattr(callee_analysis, "returns", ()) or ()),
            "callee_summary_requires_completed_proof": callee_requires_completed_summary_proof,
            "callee_completed_proof_ids": callee_completed_proof_ids,
            "callee_completed_proof_evidence_ids": callee_completed_proof_evidence_ids,
            "callee_effect_summary_clean": True,
            "target_conditions_key": _runtime_conditions_signature(target_conditions),
            "result_count": int(result_count),
            "max_unroll": int(self.max_unroll),
            "dependency_cycle": False,
            "truncated": False,
        }
        record = {
            "object_derived": True,
            "status": "complete",
            "evidence_kind": "bounded_call_refinement_expansion",
            "proof_stage": "bounded_call_refinement",
            "object_target_key": object_target_key,
            "proof_source": "bounded_call_refinement_deferred_expanded",
            "proof_content": content,
        }
        caller_analysis.completed_recovery_proof_evidence = existing + (record,)
        self._debug("Recorded bounded refinement expansion evidence")

    @staticmethod
    def _callee_requires_completed_summary_proof(
        callee_analysis: FunctionReturnAnalysis,
    ) -> bool:
        for ret in getattr(callee_analysis, "returns", ()) or ():
            if str(getattr(ret, "return_kind", "exact") or "exact") == "summary_derived":
                return True
            if getattr(ret, "summary_transition_evidence_key", None) is not None:
                return True
            if getattr(ret, "summary_candidate_source_key", None) is not None:
                return True
        return False

    @classmethod
    def _callee_summary_completion_proof_ids(
        cls,
        callee_analysis: FunctionReturnAnalysis,
    ) -> Tuple[Any, ...]:
        return cls._callee_summary_completion_evidence_ids(callee_analysis)

    @classmethod
    def _callee_summary_completion_evidence_ids(
        cls,
        callee_analysis: FunctionReturnAnalysis,
    ) -> Tuple[Any, ...]:
        accepted = []
        for item in getattr(callee_analysis, "completed_recovery_proof_evidence", ()) or ():
            if not isinstance(item, Mapping):
                continue
            proof_id = cls._validated_summary_completion_proof_id(item)
            if proof_id is not None:
                accepted.append(proof_id)
        return tuple(accepted)

    @classmethod
    def _validated_summary_completion_proof_id(
        cls,
        evidence: Mapping[str, Any],
    ) -> Optional[Tuple[Any, ...]]:
        proof_id = _return_region_summary_proof_id_from_evidence(evidence)
        if proof_id is not None:
            return cls._normalize_nested_tuple(proof_id)
        proof_id = summary_return_acceptance_proof_id_from_evidence(evidence)
        if proof_id is not None:
            return cls._normalize_nested_tuple(proof_id)
        return None

    @staticmethod
    def _normalize_nested_tuple(value: Any) -> Any:
        if isinstance(value, list):
            return tuple(BoundedCallRefiner._normalize_nested_tuple(item) for item in value)
        if isinstance(value, tuple):
            return tuple(BoundedCallRefiner._normalize_nested_tuple(item) for item in value)
        return value

    @staticmethod
    def _stable_key_or_none(value: Any) -> Optional[Tuple[Any, ...]]:
        stable_key = getattr(value, "stable_key", None)
        if callable(stable_key):
            try:
                key = stable_key()
            except (AttributeError, TypeError, ValueError, RecursionError):
                return None
            return key if isinstance(key, tuple) else None
        return None

    def _deferred_call_pcode_key(self, deferred: DeferredCallInfo) -> Optional[Tuple[Any, ...]]:
        deferred_ref = getattr(deferred, "deferred_call_ref", None)
        return self._stable_key_or_none(getattr(deferred_ref, "pcode_op_ref", None))

    def _call_target_key_for_analysis(
        self,
        target_ref: Any,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> Any:
        key = self._stable_key_or_none(target_ref)
        binary_id = getattr(analysis, "binary_id", None) if analysis is not None else None
        if not binary_id or not isinstance(key, tuple) or not key:
            return key
        kind = key[0]
        if kind == "function" and len(key) >= 3 and key[2] is not None:
            return ("function", str(binary_id), key[2])
        if kind == "code_address" and len(key) >= 3 and key[2] is not None:
            return ("code_address", str(binary_id), key[2])
        if kind == "unknown":
            return ("unknown", str(binary_id))
        return key

    def _analysis_entry_key(self, analysis: Optional[FunctionReturnAnalysis]) -> Tuple[Any, ...]:
        if analysis is None:
            return ("analysis", None, None, None)
        function_ref_key = self._stable_key_or_none(getattr(analysis, "function_ref", None))
        if function_ref_key is not None:
            binary_id = getattr(analysis, "binary_id", None)
            if binary_id and function_ref_key[0] == "function" and len(function_ref_key) >= 3:
                return ("function", str(binary_id), function_ref_key[2])
            return function_ref_key
        return (
            "analysis",
            getattr(analysis, "binary_id", None),
            getattr(analysis, "function_name", None),
            getattr(analysis, "entry_point", None),
        )

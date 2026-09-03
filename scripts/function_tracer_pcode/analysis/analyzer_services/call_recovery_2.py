"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.analysis.analyzer``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    CallTargetRef,
    ExpressionType,
    _enumerate_constant_expression_branches,
    _expression_contains_observed_loads,
    _expressions_equivalent_under_conditions,
    _resolve_call_target_ref,
    canonicalize_expr_read_location,
    coerce_call_target_ref,
    expression_contains_post_state_reads,
    lower_post_state_expression_for_smt,
    promote_effect_value_match_to_post_state_read,
    promote_observed_loads_to_post_state_reads,
    rewrite_observed_loads_from_effects,
)
from ._api import resolve_call_targets

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__resolve_object_centric_transfer_targets(
    self,
    pcode_op,
    tracer: Optional[PcodeTracer],
) -> List[CallTargetRef]:
    if pcode_op is None or tracer is None:
        return []

    resolved: List[CallTargetRef] = []

    try:
        mnemonic = str(pcode_op.getMnemonic())
    except Exception:
        mnemonic = ""

    if mnemonic in {"CALL", "CALLIND"}:
        try:
            image_base = None
            if self.program is not None:
                image_base = self.program.getImageBase().getOffset()
            for target_ref, _conditions in resolve_call_targets(
                tracer,
                pcode_op,
                conditions=[],
                parameters=list(self._current_parameters or []),
                read_memory_value=self._read_memory_value if self.program is not None else None,
                image_base=image_base,
                debug=self.debug,
            ):
                if target_ref is not None:
                    resolved.append(target_ref)
        except Exception:
            pass
    elif mnemonic == "BRANCHIND":
        try:
            target_varnode = pcode_op.getInput(0)
        except Exception:
            target_varnode = None

        if target_varnode is not None:
            resolver = getattr(tracer, "resolve_call_target_ref", None)
            if callable(resolver):
                try:
                    direct_target = resolver(
                        target_varnode,
                        allow_containing=True,
                        allow_code_address=True,
                    )
                except Exception:
                    direct_target = None
                direct_target_ref = coerce_call_target_ref(direct_target)
                if direct_target_ref is not None:
                    resolved.append(direct_target_ref)

            try:
                target_expr = tracer.trace_varnode(target_varnode, use_cache=False)
            except Exception:
                target_expr = None
            if target_expr is not None:
                target_expr = self._concretize_readonly_loads(
                    target_expr,
                    [],
                    self._current_parameters,
                )
                for _branch_conditions, address_value in _enumerate_constant_expression_branches(target_expr):
                    target_function = self._resolve_function_from_program_offset(int(address_value))
                    if target_function is not None:
                        resolved.append(CallTargetRef.from_function(target_function))
                    else:
                        resolved.append(CallTargetRef.from_code_address(int(address_value)))

    if not resolved:
        fallback_target = _resolve_call_target_ref(tracer, pcode_op)
        if fallback_target is not None:
            resolved.append(fallback_target)

    deduped: List[CallTargetRef] = []
    seen_keys = set()
    for target_ref in resolved:
        stable_key = target_ref.stable_key()
        if stable_key in seen_keys:
            continue
        seen_keys.add(stable_key)
        deduped.append(target_ref)
    return deduped

def _impl__resolve_function_from_call_target_ref(
    self,
    target_ref: Optional[CallTargetRef],
):
    if target_ref is None or target_ref.is_unknown():
        return None

    function_obj = getattr(target_ref, "function_obj", None)
    if function_obj is not None:
        return function_obj

    if target_ref.entry_offset is not None:
        return self._resolve_function_from_program_offset(target_ref.entry_offset)

    if target_ref.address_offset is not None:
        return self._resolve_function_from_program_offset(target_ref.address_offset)

    return None

def _impl__find_terminal_call_before_return(
    self,
    return_op,
    condition_tracker: ConditionTracker,
    tracer: Optional[PcodeTracer] = None,
    current_function=None,
):
    """同一 basic block 内で wrapper return とみなせる末尾 CALL/CALLIND を探す。"""
    return_parent = getattr(return_op, "getParent", lambda: None)()
    return_block = condition_tracker.get_block_by_hash(return_parent)
    if return_block is None:
        return None

    linear_ops = self._collect_linear_ops_to_return([return_block], return_op)
    if not linear_ops:
        return None
    return self._find_terminal_call_from_linear_ops(
        linear_ops,
        return_op,
        tracer=tracer,
        condition_tracker=condition_tracker,
        current_function=current_function,
        block_path=[return_block],
        path_conditions=None,
    )

def _impl__recover_implicit_return_from_terminal_call(
    self,
    call_op,
    address: str,
    tracer: PcodeTracer,
    condition_tracker: ConditionTracker,
    path_conditions: List[Condition],
    return_index: int,
    all_path_conditions: Optional[List[List[Condition]]] = None,
    active_functions: Optional[Set[Tuple[Any, ...]]] = None,
    current_function=None,
    site_metadata: Optional[Dict[str, Optional[object]]] = None,
) -> Optional[List[ReturnInfo]]:
    """`call foo(...); return;` 形式の wrapper を callee summary から復元する。"""
    from ...transform import ExpressionExpander

    expander = ExpressionExpander(
        tracer,
        condition_tracker,
        debug=self.debug,
        call_resolver=self._make_call_resolver(active_functions or set(), current_function),
        effect_summary=self._current_effect_summary,
        parameters=self._current_parameters,
        resolve_callee_parameters=self._get_freshest_callee_parameters,
        read_memory_value=self._read_memory_value,
        image_base=self.program.getImageBase().getOffset(),
        record_deferred_call=self._make_deferred_call_recorder(current_function),
    )

    path_condition_sets = all_path_conditions or []
    if not path_condition_sets:
        path_condition_sets = [path_conditions] if path_conditions else [[]]

    expanded_values = []
    for conds in path_condition_sets:
        expanded_values.extend(
            expander._expand_call_operation(
                call_op,
                conds,
                depth=0,
                output_size=0,
            )
        )

    if not expanded_values:
        return None

    results = self._build_return_infos_from_expansions(
        address,
        expanded_values,
        return_index,
        site_metadata=site_metadata,
    )
    return results or None

def _impl__is_semantically_lossless_effect_sensitive_rewrite(
    self,
    original: Optional[Expression],
    rewritten: Optional[Expression],
    conditions: List[Condition],
    effect_summary: EffectSummary,
) -> bool:
    if original is None or rewritten is None:
        return False
    if not expression_contains_post_state_reads(rewritten):
        return False
    if not _expression_contains_observed_loads(original):
        return False
    rewritten_location = canonicalize_expr_read_location(
        rewritten,
        self._current_parameters,
    )
    if rewritten_location is not None:
        existing_effect_carrier = promote_effect_value_match_to_post_state_read(
            original,
            rewritten_location,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            symbolic_post_state=True,
        )
        if existing_effect_carrier is not None:
            return False

    comparison_targets: List[Expression] = [original]
    if _expression_contains_observed_loads(original):
        observed_post_state = promote_observed_loads_to_post_state_reads(
            original,
            conditions,
            effect_summary.effects,
            self._current_parameters,
            symbolic_post_state=True,
        )
        if observed_post_state is not None:
            comparison_targets.append(observed_post_state)
            lowered_observed_post_state = lower_post_state_expression_for_smt(
                observed_post_state,
                conditions,
                effect_summary.effects,
                self._current_parameters,
            )
            if lowered_observed_post_state is not None:
                comparison_targets.append(lowered_observed_post_state)
        observed_rewritten = rewrite_observed_loads_from_effects(
            original,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        )
        if observed_rewritten is not None:
            comparison_targets.append(observed_rewritten)

    lowered_rewritten = lower_post_state_expression_for_smt(
        rewritten,
        conditions,
        effect_summary.effects,
        self._current_parameters,
    )
    lowered_rewritten = lowered_rewritten if lowered_rewritten is not None else rewritten
    if expression_contains_post_state_reads(lowered_rewritten):
        return False

    for target in comparison_targets:
        lowered_target = lower_post_state_expression_for_smt(
            target,
            conditions,
            effect_summary.effects,
            self._current_parameters,
        )
        candidate = lowered_target if lowered_target is not None else target
        if _expressions_equivalent_under_conditions(
            lowered_rewritten,
            candidate,
            conditions,
            self._current_parameters,
        ):
            return True
    return False

def _impl__expression_contains_deferred_call_value(self, expr: Optional[Expression]) -> bool:
    if expr is None:
        return False
    if getattr(expr, "expr_type", None) == ExpressionType.UNKNOWN:
        runtime_ref = getattr(expr, "runtime_ref", None)
        if getattr(runtime_ref, "deferred_call_ref", None) is not None:
            return True
    if getattr(expr, "expr_type", None) == ExpressionType.PHI and getattr(expr, "value", None):
        for condition, value in expr.value or []:
            if condition is not None and self._expression_contains_deferred_call_value(condition.expression):
                return True
            if self._expression_contains_deferred_call_value(value):
                return True
        return False
    for operand in getattr(expr, "operands", None) or ():
        if self._expression_contains_deferred_call_value(operand):
            return True
    return False

def _impl__clear_resolved_call_effect_blockers(self, analysis: Optional[FunctionReturnAnalysis]) -> None:
    if analysis is None:
        return
    if getattr(analysis, "deferred_calls", None):
        return
    if any(
        self._expression_contains_deferred_call_value(getattr(ret, "value", None))
        or any(
            self._expression_contains_deferred_call_value(getattr(cond, "expression", None))
            for cond in (getattr(ret, "conditions", None) or [])
        )
        for ret in (getattr(analysis, "returns", None) or [])
    ):
        return
    blocking_notes = {
        "effect_call_argument_evidence",
        "effect_call_argument_evidence_incomplete",
    }
    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is not None and getattr(effect_summary, "call_argument_evidence", None):
        return
    if any(note in blocking_notes for note in getattr(analysis, "analysis_notes", []) or []):
        analysis.analysis_notes = [
            note
            for note in (analysis.analysis_notes or [])
            if note not in blocking_notes
        ]
        if "bounded_call_effect_resolved" not in analysis.analysis_notes:
            analysis.analysis_notes.append("bounded_call_effect_resolved")

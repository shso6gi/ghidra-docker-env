"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.equivalence.strategies.pairwise``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    Condition,
    CountedLoopSummaryRef,
    ExpressionType,
    ReadonlyReductionRef,
    _RuntimeShortcutDecision,
    compare_loop_summaries,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__intrinsic_runtime_values_equivalent(
    self,
    left: Expression,
    right: Expression,
    *,
    left_case: Optional[ReturnCase] = None,
    right_case: Optional[ReturnCase] = None,
    semantic_parameter_sources: Sequence[ParameterInfo] = (),
) -> bool:
    if left is None or right is None:
        return False
    if left.expr_type != ExpressionType.INTRINSIC or right.expr_type != ExpressionType.INTRINSIC:
        return False
    left_ref = getattr(left, "runtime_ref", None)
    right_ref = getattr(right, "runtime_ref", None)
    comparison_result_size = self._case_pair_comparison_result_size(left_case, right_case)
    loop_contract_decision = self._runtime_loop_contract_shortcut_decision(
        left_ref,
        right_ref,
        result_size=comparison_result_size,
    )
    if loop_contract_decision.equivalent:
        if loop_contract_decision.requires_guard_equivalence and (
            left_case is None
            or right_case is None
            or not self._case_pair_has_runtime_guard_coverage_or_equivalence(left_case, right_case)
        ):
            return False
        return True
    if getattr(left, "opcode", None) != getattr(right, "opcode", None):
        return False
    if (getattr(left, "name", None) or "") != (getattr(right, "name", None) or ""):
        return False
    shortcut_decision = self._runtime_refs_shortcut_decision(
        left_ref,
        right_ref,
        result_size=comparison_result_size,
    )
    if not shortcut_decision.equivalent:
        if (
            isinstance(left_ref, ReadonlyReductionRef)
            or isinstance(right_ref, ReadonlyReductionRef)
        ) and str(getattr(shortcut_decision, "reason", "") or "").startswith("readonly_contract_"):
            return False
        if self._case_pair_loop_summaries_solver_equivalent(
            left_ref,
            right_ref,
            left_case=left_case,
            right_case=right_case,
            semantic_parameter_sources=semantic_parameter_sources,
        ):
            return True
        if self._counted_loop_values_are_provably_equivalent(
            left,
            right,
            left_case=left_case,
            right_case=right_case,
            semantic_parameter_sources=semantic_parameter_sources,
        ):
            return True
        return False
    if shortcut_decision.requires_guard_equivalence and (
        left_case is None
        or right_case is None
        or not self._case_pair_has_runtime_guard_coverage_or_equivalence(left_case, right_case)
    ):
        return False
    if len(left.operands) != len(right.operands):
        return False
    return all(
        self._expressions_share_object_centric_structure(left_operand, right_operand)
        for left_operand, right_operand in zip(left.operands, right.operands)
    )

def _impl__runtime_refs_share_shortcut_semantics(self, left_ref, right_ref) -> tuple[bool, bool]:
    decision = self._runtime_refs_shortcut_decision(left_ref, right_ref)
    return decision.equivalent, decision.requires_guard_equivalence

def _impl__runtime_refs_shortcut_decision(
    self,
    left_ref,
    right_ref,
    *,
    result_size: Optional[int] = None,
) -> _RuntimeShortcutDecision:
    if left_ref is None or right_ref is None:
        return _RuntimeShortcutDecision(False, False, reason="missing_runtime_ref")

    left_loop_summary = getattr(left_ref, "loop_summary", None)
    right_loop_summary = getattr(right_ref, "loop_summary", None)
    if left_loop_summary is not None or right_loop_summary is not None:
        if isinstance(left_ref, ReadonlyReductionRef) and isinstance(right_ref, ReadonlyReductionRef):
            exact_readonly_decision = self._runtime_refs_exact_shortcut_decision(
                left_ref,
                right_ref,
                requires_guard_equivalence=(
                    self._runtime_ref_has_guard_constraints(left_ref)
                    or self._runtime_ref_has_guard_constraints(right_ref)
                ),
            )
            if exact_readonly_decision.equivalent:
                return exact_readonly_decision
        readonly_decision = self._readonly_reduction_contract_shortcut_decision(
            left_ref,
            right_ref,
            requires_guard_equivalence=True,
            result_size=result_size,
        )
        if readonly_decision.equivalent:
            return readonly_decision
        if readonly_decision.reason in {
            "readonly_contract_type_mismatch",
            "readonly_contract_result_width_mismatch",
            "readonly_contract_mismatch",
        } and (
            isinstance(left_ref, ReadonlyReductionRef)
            or isinstance(right_ref, ReadonlyReductionRef)
        ):
            return readonly_decision
        loop_result = compare_loop_summaries(left_loop_summary, right_loop_summary)
        decisive = loop_result.is_equivalent()
        if decisive is not None:
            return _RuntimeShortcutDecision(
                bool(decisive),
                True,
                reason=f"loop_summary_{loop_result.status}",
            )
        if loop_result.blocks_shortcut():
            return _RuntimeShortcutDecision(
                False,
                True,
                reason=f"loop_summary_{loop_result.status}",
            )
        exact_decision = self._runtime_refs_exact_shortcut_decision(
            left_ref,
            right_ref,
            requires_guard_equivalence=True,
        )
        if exact_decision.equivalent:
            return exact_decision
        semantic_decision = self._runtime_refs_semantic_shortcut_decision(left_ref, right_ref)
        if semantic_decision.equivalent:
            return _RuntimeShortcutDecision(
                True,
                True,
                reason=semantic_decision.reason,
            )
        return _RuntimeShortcutDecision(
            False,
            True,
            reason="loop_summary_unproven",
        )

    exact_decision = self._runtime_refs_exact_shortcut_decision(
        left_ref,
        right_ref,
        requires_guard_equivalence=self._runtime_refs_require_guard_equivalence(left_ref, right_ref),
    )
    if exact_decision.equivalent:
        return exact_decision

    semantic_decision = self._runtime_refs_semantic_shortcut_decision(left_ref, right_ref)
    if semantic_decision.equivalent:
        return semantic_decision
    return _RuntimeShortcutDecision(False, False, reason="no_shortcut")

def _impl__runtime_refs_require_guard_equivalence(self, left_ref, right_ref) -> bool:
    left_guard_fn = getattr(left_ref, "pairwise_requires_guard_equivalence", None)
    right_guard_fn = getattr(right_ref, "pairwise_requires_guard_equivalence", None)
    return bool(callable(left_guard_fn) and left_guard_fn()) or bool(
        callable(right_guard_fn) and right_guard_fn()
    )

def _impl__runtime_ref_has_guard_constraints(self, runtime_ref) -> bool:
    for owner in (
        runtime_ref,
        getattr(runtime_ref, "accumulator_proof", None),
        getattr(runtime_ref, "loop_summary", None),
    ):
        if tuple(getattr(owner, "guard_constraints", ()) or ()):
            return True
    return False

def _impl__runtime_refs_exact_shortcut_decision(
    self,
    left_ref,
    right_ref,
    *,
    requires_guard_equivalence: bool,
) -> _RuntimeShortcutDecision:
    left_exact_key_fn = getattr(left_ref, "pairwise_exact_key", None)
    right_exact_key_fn = getattr(right_ref, "pairwise_exact_key", None)
    if callable(left_exact_key_fn) and callable(right_exact_key_fn):
        try:
            left_exact_key = left_exact_key_fn()
            right_exact_key = right_exact_key_fn()
            if left_exact_key is not None and right_exact_key is not None and left_exact_key == right_exact_key:
                return _RuntimeShortcutDecision(
                    True,
                    requires_guard_equivalence,
                    reason="exact_runtime_key",
                )
        except (AttributeError, TypeError, ValueError):
            return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="exact_key_unavailable")
    return _RuntimeShortcutDecision(False, requires_guard_equivalence, reason="exact_key_mismatch")

def _impl__method_b_summary_runtime_ref(self, expr: Optional[Expression]):
    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, (ReadonlyReductionRef, CountedLoopSummaryRef)) and getattr(
        runtime_ref,
        "loop_summary",
        None,
    ) is not None:
        return runtime_ref
    return None

def _impl__method_b_expression_runtime_object_key(self, expr: Any) -> Tuple[Any, ...]:
    runtime_ref = getattr(expr, "runtime_ref", None)
    if runtime_ref is not None:
        return ("runtime_ref", self._semantic_key_or_stable_key_or_none(runtime_ref))
    return self._expression_runtime_object_key(expr)

def _impl__runtime_refs_semantic_shortcut_decision(self, left_ref, right_ref) -> _RuntimeShortcutDecision:
    left_semantic_key_fn = getattr(left_ref, "pairwise_semantic_key", None)
    right_semantic_key_fn = getattr(right_ref, "pairwise_semantic_key", None)
    if not callable(left_semantic_key_fn) or not callable(right_semantic_key_fn):
        return _RuntimeShortcutDecision(False, False, reason="semantic_key_missing")
    try:
        left_semantic_key = left_semantic_key_fn()
        right_semantic_key = right_semantic_key_fn()
    except (AttributeError, TypeError, ValueError):
        return _RuntimeShortcutDecision(False, False, reason="semantic_key_unavailable")
    if left_semantic_key is None or right_semantic_key is None:
        return _RuntimeShortcutDecision(False, False, reason="semantic_key_none")
    if left_semantic_key != right_semantic_key:
        return _RuntimeShortcutDecision(False, False, reason="semantic_key_mismatch")

    left_guard_fn = getattr(left_ref, "pairwise_requires_guard_equivalence", None)
    right_guard_fn = getattr(right_ref, "pairwise_requires_guard_equivalence", None)
    requires_guard_equivalence = bool(callable(left_guard_fn) and left_guard_fn()) or bool(
        callable(right_guard_fn) and right_guard_fn()
    )
    return _RuntimeShortcutDecision(
        True,
        requires_guard_equivalence,
        reason="semantic_runtime_key",
    )

def _impl__expressions_same_shape_ignoring_runtime(self, left: Expression, right: Expression) -> bool:
    if left is None or right is None:
        return False
    return left.structural_key(include_semantic_runtime_refs=False) == right.structural_key(
        include_semantic_runtime_refs=False
    )

def _impl__clone_auxiliary_runtime_ref_for_smt(
    self,
    runtime_ref: Any,
    identity_to_spec: Dict[Tuple[object, ...], Dict[str, Any]],
) -> Any:
    if runtime_ref is None:
        return None
    if isinstance(runtime_ref, CountedLoopSummaryRef):
        return self._clone_auxiliary_counted_loop_summary_ref(runtime_ref, identity_to_spec)
    return runtime_ref

def _impl__case_pair_has_runtime_guard_coverage_or_equivalence(
    self,
    left_case: ReturnCase,
    right_case: ReturnCase,
) -> bool:
    left_guards, left_complete = self._runtime_summary_guard_conditions_from_expression(
        left_case.value_expr,
    )
    right_guards, right_complete = self._runtime_summary_guard_conditions_from_expression(
        right_case.value_expr,
    )
    if not left_complete or not right_complete:
        return False
    if not left_guards and not right_guards:
        return self._cases_have_equivalent_summary_conditions(left_case, right_case)
    if self._cases_have_pair_local_summary_guard_compatibility(left_case, right_case):
        return True
    if not left_guards or not right_guards:
        return False
    return self._case_conditions_cover_runtime_summary_guards(
        left_case,
    ) and self._case_conditions_cover_runtime_summary_guards(
        right_case,
    )

def _impl__case_conditions_cover_runtime_summary_guards(
    self,
    case: ReturnCase,
) -> bool:
    guards, complete = self._runtime_summary_guard_conditions_from_expression(case.value_expr)
    if not complete:
        return False
    if not guards:
        return False
    return self._condition_set_implies(
        list(getattr(case, "conditions", None) or []),
        guards,
        list(getattr(case, "parameters", None) or []),
    )

def _impl__runtime_summary_guard_conditions_from_expression(
    self,
    expr: Optional[Expression],
) -> tuple[List[Condition], bool]:
    guards: List[Condition] = []
    seen: set[tuple] = set()
    complete = True
    for node in self._iter_expression_nodes(expr):
        runtime_ref = getattr(node, "runtime_ref", None)
        for owner in (
            runtime_ref,
            getattr(runtime_ref, "accumulator_proof", None),
            getattr(runtime_ref, "loop_summary", None),
        ):
            for guard in tuple(getattr(owner, "guard_constraints", ()) or ()):
                if not isinstance(guard, Condition):
                    complete = False
                    continue
                key = guard.structural_key(budget=256)
                if key in seen:
                    continue
                seen.add(key)
                guards.append(guard)
    return guards, complete

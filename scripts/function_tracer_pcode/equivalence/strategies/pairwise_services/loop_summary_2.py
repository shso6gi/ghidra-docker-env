"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.equivalence.strategies.pairwise``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    CountedLoopSummaryRef,
    ExpressionType,
    LoopSummaryRef,
    LoopTermDescriptorRef,
    compare_loop_summaries,
    expression_smt_bit_width,
    replace,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__counted_loop_refs_allow_value_proof(self, left_ref, right_ref) -> bool:
    if left_ref is None or right_ref is None:
        return False
    if not isinstance(left_ref, CountedLoopSummaryRef) or not isinstance(right_ref, CountedLoopSummaryRef):
        return False
    left_loop_summary = getattr(left_ref, "loop_summary", None)
    right_loop_summary = getattr(right_ref, "loop_summary", None)
    if left_loop_summary is None and right_loop_summary is None:
        return True
    for loop_summary in (left_loop_summary, right_loop_summary):
        requires_effect_proof = getattr(loop_summary, "requires_effect_proof", None)
        if callable(requires_effect_proof) and requires_effect_proof():
            return False
        requires_path_proof = getattr(loop_summary, "requires_path_proof", None)
        if callable(requires_path_proof) and requires_path_proof():
            return False
    loop_result = compare_loop_summaries(left_loop_summary, right_loop_summary)
    if loop_result.blocks_shortcut():
        return False
    return loop_result.is_equivalent() is True

def _impl__counted_loop_refs_match_ignoring_signedness(self, left_ref, right_ref) -> bool:
    if left_ref is None or right_ref is None:
        return False
    if not isinstance(left_ref, CountedLoopSummaryRef) or not isinstance(right_ref, CountedLoopSummaryRef):
        return False
    try:
        return (
            int(getattr(left_ref, "induction_step", 0) or 0)
            == int(getattr(right_ref, "induction_step", 0) or 0)
            and max(1, int(getattr(left_ref, "result_size", 0) or 0))
            == max(1, int(getattr(right_ref, "result_size", 0) or 0))
            and tuple(getattr(left_ref, "residue_cases", ()) or ())
            == tuple(getattr(right_ref, "residue_cases", ()) or ())
            and getattr(left_ref, "source", None) == getattr(right_ref, "source", None)
        )
    except Exception:
        return False

def _impl__counted_loop_signedness_difference_is_guarded(
    self,
    left: Expression,
    right: Expression,
    conditions: Sequence[Condition],
    parameters: Sequence[Dict[str, Any]],
) -> bool:
    left_ref = getattr(left, "runtime_ref", None)
    right_ref = getattr(right, "runtime_ref", None)
    if bool(getattr(left_ref, "signed_loop", False)) == bool(getattr(right_ref, "signed_loop", False)):
        return True
    operands = list(getattr(left, "operands", None) or [])
    if len(operands) != 3:
        return False
    # Signed and unsigned COUNTED_LOOP_SUM lowerings differ in how start/limit
    # are extended to the wide arithmetic domain. If both are non-negative
    # under the current pair guard, the two interpretations coincide.
    return all(
        self._expression_is_provably_nonnegative_under_conditions(expr, conditions, parameters)
        for expr in operands[1:3]
    )

def _impl__clone_auxiliary_counted_loop_summary_ref(
    self,
    runtime_ref: CountedLoopSummaryRef,
    identity_to_spec: Dict[Tuple[object, ...], Dict[str, Any]],
) -> Optional[CountedLoopSummaryRef]:
    cloned_bias_terms = self._clone_auxiliary_residue_bias_terms(
        tuple(getattr(runtime_ref, "residue_bias_terms", ()) or ()),
        identity_to_spec,
    )
    if cloned_bias_terms is None:
        return None
    loop_summary = getattr(runtime_ref, "loop_summary", None)
    cloned_loop_summary = loop_summary
    if isinstance(loop_summary, LoopSummaryRef):
        cloned_loop_summary = self._clone_auxiliary_loop_summary_ref(loop_summary, identity_to_spec)
        if cloned_loop_summary is None:
            return None
    return replace(
        runtime_ref,
        residue_bias_terms=cloned_bias_terms,
        loop_summary=cloned_loop_summary,
    )

def _impl__clone_auxiliary_loop_summary_ref(
    self,
    loop_summary: LoopSummaryRef,
    identity_to_spec: Dict[Tuple[object, ...], Dict[str, Any]],
) -> Optional[LoopSummaryRef]:
    term_descriptor = getattr(loop_summary, "term_descriptor", None)
    if not isinstance(term_descriptor, LoopTermDescriptorRef):
        return loop_summary
    cloned_bias_terms = self._clone_auxiliary_residue_bias_terms(
        tuple(getattr(term_descriptor, "residue_bias_terms", ()) or ()),
        identity_to_spec,
    )
    if cloned_bias_terms is None:
        return None
    return replace(
        loop_summary,
        term_descriptor=replace(term_descriptor, residue_bias_terms=cloned_bias_terms),
    )

def _impl__case_pair_can_defer_loop_summary_proof(
    self,
    left_case: ReturnCase,
    right_case: ReturnCase,
    reason: str,
) -> bool:
    if reason == "loop_summary_guard_mismatch":
        return self._loop_summary_contracts_match_without_guard(
            left_case.value_expr,
            right_case.value_expr,
        )
    return False

def _impl__loop_summary_contracts_match_without_guard(
    self,
    left: Optional[Expression],
    right: Optional[Expression],
) -> bool:
    if left is None or right is None:
        return False
    left_has_loop = self._expression_contains_loop_summary_runtime(left)
    right_has_loop = self._expression_contains_loop_summary_runtime(right)
    if not left_has_loop or not right_has_loop:
        return False
    if left.expr_type == ExpressionType.INTRINSIC and right.expr_type == ExpressionType.INTRINSIC:
        decision = self._runtime_loop_contract_shortcut_decision(
            getattr(left, "runtime_ref", None),
            getattr(right, "runtime_ref", None),
        )
        if decision.equivalent and decision.requires_guard_equivalence:
            return True
    if left.expr_type != right.expr_type:
        return False
    left_operands = list(getattr(left, "operands", []) or [])
    right_operands = list(getattr(right, "operands", []) or [])
    if len(left_operands) != len(right_operands):
        return False
    return any(
        self._loop_summary_contracts_match_without_guard(left_operand, right_operand)
        for left_operand, right_operand in zip(left_operands, right_operands)
    )

def _impl__resolve_pending_loop_summary_pairs_with_partition_proof(
    self,
    pending_pairs: Sequence[_PendingLoopSummaryPair],
    cases1: Sequence[ReturnCase],
    cases2: Sequence[ReturnCase],
    resolved_pairs: set[tuple[int, int]],
) -> set[tuple[int, int]]:
    resolved_pending: set[tuple[int, int]] = set()
    progress = True
    while progress:
        progress = False
        known_resolved = set(resolved_pairs) | resolved_pending
        for pending in pending_pairs:
            pair_key = (pending.i, pending.j)
            if pair_key in resolved_pending:
                continue
            if not self._pending_loop_summary_pair_has_exact_delta_coverage(
                pending,
                cases1,
                cases2,
                known_resolved,
            ):
                continue
            resolved_pending.add(pair_key)
            progress = True
    return resolved_pending

def _impl__pending_loop_summary_pair_has_exact_delta_coverage(
    self,
    pending: _PendingLoopSummaryPair,
    cases1: Sequence[ReturnCase],
    cases2: Sequence[ReturnCase],
    resolved_pairs: set[tuple[int, int]],
) -> bool:
    left_cover_cases = [
        cases1[left_index]
        for left_index, _right_index in sorted(resolved_pairs)
        if _right_index == pending.j
        and left_index != pending.i
        and 0 <= left_index < len(cases1)
        and not self._expression_contains_loop_summary_runtime(cases1[left_index].value_expr)
    ]
    right_cover_cases = [
        cases2[right_index]
        for _left_index, right_index in sorted(resolved_pairs)
        if _left_index == pending.i
        and right_index != pending.j
        and 0 <= right_index < len(cases2)
        and not self._expression_contains_loop_summary_runtime(cases2[right_index].value_expr)
    ]
    return self._condition_delta_region_is_covered_by_cases(
        self._case_summary_condition_basis(pending.left_case),
        self._case_summary_condition_basis(pending.right_case),
        right_cover_cases,
        pending.left_case,
        pending.right_case,
    ) and self._condition_delta_region_is_covered_by_cases(
        self._case_summary_condition_basis(pending.right_case),
        self._case_summary_condition_basis(pending.left_case),
        left_cover_cases,
        pending.right_case,
        pending.left_case,
    )

def _impl__phi_circular_case_shape_and_unknowns(
    self,
    case: ReturnCase,
) -> Tuple[Optional[Tuple[Any, ...]], Tuple[Any, ...]]:
    unknowns: List[Any] = []
    value_shape = self._phi_circular_expression_shape_key(
        getattr(case, "value_expr", None),
        unknowns,
    )
    if value_shape is None:
        return None, ()
    condition_shapes: List[Tuple[Any, ...]] = []
    for condition in getattr(case, "conditions", None) or ():
        expression = getattr(condition, "expression", None)
        condition_shape = self._phi_circular_expression_shape_key(expression, unknowns)
        if condition_shape is None:
            return None, ()
        condition_shapes.append(
            (
                "condition",
                bool(getattr(condition, "negated", False)),
                condition_shape,
            )
        )
    return (
        (
            "phi_circular_case_shape",
            ("value", value_shape),
            ("conditions", tuple(condition_shapes)),
        ),
        tuple(unknowns),
    )

def _impl__phi_circular_expression_shape_key(
    self,
    expr: Any,
    unknowns: List[Any],
) -> Optional[Tuple[Any, ...]]:
    if expr is None or getattr(expr, "expr_type", None) is None:
        return None
    expr_type = expr.expr_type
    if expr_type == ExpressionType.UNKNOWN:
        if not self._unknown_expression_is_originated_phi_circular(expr):
            return None
        bits = int(expression_smt_bit_width(expr) or 0)
        if bits <= 0:
            return None
        unknowns.append(expr)
        return ("unknown", "phi_circular", bits)
    if self._expression_node_is_unsupported_smt_op(expr):
        return None
    bits = int(expression_smt_bit_width(expr) or 0)
    if expr_type == ExpressionType.CONSTANT:
        return ("const", int(getattr(expr, "value", 0) or 0), bits)
    if expr_type == ExpressionType.LITERAL:
        return ("literal", repr(getattr(expr, "value", None)), bits)
    if expr_type == ExpressionType.PARAMETER:
        raw_value = getattr(expr, "value", None)
        return (
            "parameter",
            str(getattr(expr, "name", "") or ""),
            -1 if raw_value is None else int(raw_value),
            bits,
        )
    if expr_type == ExpressionType.VARIABLE:
        return None
    if expr_type == ExpressionType.UNARY_OP:
        operands = getattr(expr, "operands", None) or ()
        if len(operands) != 1:
            return None
        operand = self._phi_circular_expression_shape_key(operands[0], unknowns)
        if operand is None:
            return None
        return ("unary", str(getattr(expr, "operator", "") or ""), bits, operand)
    if expr_type == ExpressionType.BINARY_OP:
        operands = getattr(expr, "operands", None) or ()
        if len(operands) != 2:
            return None
        left = self._phi_circular_expression_shape_key(operands[0], unknowns)
        right = self._phi_circular_expression_shape_key(operands[1], unknowns)
        if left is None or right is None:
            return None
        return (
            "binary",
            str(getattr(expr, "operator", "") or ""),
            bits,
            left,
            right,
        )
    if expr_type == ExpressionType.INTRINSIC:
        operands = []
        for operand_expr in getattr(expr, "operands", None) or ():
            operand = self._phi_circular_expression_shape_key(operand_expr, unknowns)
            if operand is None:
                return None
            operands.append(operand)
        return (
            "intrinsic",
            str(getattr(expr, "name", "") or ""),
            None if getattr(expr, "opcode", None) is None else int(getattr(expr, "opcode")),
            bits,
            tuple(operands),
        )
    return None

def _impl__unknown_expression_is_originated_phi_circular(cls, expr: Any) -> bool:
    if getattr(expr, "expr_type", None) != ExpressionType.UNKNOWN:
        return False
    runtime_ref = getattr(expr, "runtime_ref", None)
    if getattr(runtime_ref, "kind", None) != "opaque_unknown":
        return False
    if getattr(runtime_ref, "reason", None) != "phi_circular":
        return False
    if getattr(runtime_ref, "origin_kind", None) != "multiequal_pcode_op":
        return False
    return cls._stable_key_or_none(getattr(runtime_ref, "origin_ref", None)) is not None

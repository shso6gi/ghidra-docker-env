"""Blocking UNKNOWN reasons, unresolved-expression detection, evidence accessors and query normalisation."""

from __future__ import annotations

from typing import Any, List, Mapping, Optional, Sequence, Set, Tuple
from types import SimpleNamespace
from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
)
from scripts.function_tracer_pcode.core.render_smt import expression_contains_unsupported_smt_ops
from scripts.function_tracer_pcode.proof.strategies.proof_gates._shared import (
    UnknownReasonId,
    UnknownReasonRecord,
)


def _impl__debug_print(self, msg: str):
    """デバッグ出力"""
    if self.debug:
        print(f"[{self.__class__.__name__}] {msg}")


def _impl__summary_return_candidate_blocker_reason_ids(
    cls,
    analysis: Optional[FunctionReturnAnalysis],
) -> Tuple[str, ...]:
    if analysis is None:
        return ()
    known = {
        UnknownReasonId.SUMMARY_RETURN_CANDIDATE_INVALID.value,
        UnknownReasonId.SUMMARY_RETURN_OVERLAP_UNPROVEN.value,
        UnknownReasonId.SUMMARY_EFFECT_UNMODELED.value,
        UnknownReasonId.SUMMARY_PRECONDITION_INCOMPLETE.value,
        UnknownReasonId.SUMMARY_PARTITION_NOT_TOTAL.value,
        UnknownReasonId.PHI_CIRCULAR_REPLACEMENT_UNPROVEN.value,
    }
    reasons: List[str] = []
    for candidate in getattr(analysis, "summary_return_candidates", ()) or ():
        for blocker in getattr(candidate, "validation_blockers", ()) or ():
            reason_id = cls._summary_return_blocker_reason_id(str(blocker))
            if reason_id in known:
                reasons.append(reason_id)
    for note in getattr(analysis, "analysis_notes", ()) or ():
        text = str(note)
        if not text.startswith("summary_return_blocker:"):
            continue
        blocker = text[len("summary_return_blocker:"):]
        reason_id = cls._summary_return_blocker_reason_id(blocker)
        if reason_id in known:
            reasons.append(reason_id)
    return tuple(dict.fromkeys(reasons))


def _impl__summary_return_blocker_reason_id(blocker: str) -> str:
    text = str(blocker or "")
    if text == "return_coverage_gap:summary_partition_not_total":
        return UnknownReasonId.SUMMARY_PARTITION_NOT_TOTAL.value
    if text.startswith("return_coverage_gap:summary_partition_not_total:"):
        return UnknownReasonId.SUMMARY_PARTITION_NOT_TOTAL.value
    return text.split(":", 1)[0]


def _impl__return_case_smt_disjunctions(
    cases: Sequence[Any],
    replace_fn,
) -> Optional[Tuple[str, ...]]:
    disjuncts: List[str] = []
    for case in cases:
        if not getattr(case, "conditions", None):
            disjuncts.append("true")
            continue
        conditions = list(case.get_conditions_smt(replace_fn))
        if not conditions:
            return None
        if len(conditions) == 1:
            disjuncts.append(conditions[0])
        else:
            disjuncts.append(f"(and {' '.join(conditions)})")
    return tuple(disjuncts)


def _impl__normalize_query(query: Optional[str]) -> Optional[str]:
    if not query or not isinstance(query, str):
        return None
    lines = [line.strip() for line in query.splitlines() if line.strip()]
    normalized = [line for line in lines if not line.startswith("; Return coverage")]
    return "\n".join(normalized)


def _impl__iter_expression_nodes_for_metadata(cls, expr: Any):
    stack = [expr]
    seen: Set[int] = set()
    while stack:
        current = stack.pop()
        if current is None:
            continue
        current_id = id(current)
        if current_id in seen:
            continue
        seen.add(current_id)
        yield current
        for operand in getattr(current, "operands", ()) or ():
            stack.append(operand)
        if getattr(current, "expr_type", None) == ExpressionType.PHI:
            for cond, value in getattr(current, "value", ()) or ():
                if cond is not None:
                    stack.append(getattr(cond, "expression", None))
                stack.append(value)


def _impl__expression_contains_runtime_ref(cls, expr: Any, needle: Tuple[Any, ...]) -> bool:
    if expr is None:
        return False
    stack = [expr]
    seen: Set[int] = set()
    while stack:
        current = stack.pop()
        if current is None:
            continue
        current_id = id(current)
        if current_id in seen:
            continue
        seen.add(current_id)
        runtime_ref = cls._stable_key_or_none(getattr(current, "runtime_ref", None))
        if runtime_ref == needle or cls._normalize_nested_tuple(runtime_ref) == needle:
            return True
        for operand in getattr(current, "operands", ()) or ():
            stack.append(operand)
        if getattr(current, "expr_type", None) == ExpressionType.PHI:
            for condition, value in getattr(current, "value", ()) or ():
                stack.append(getattr(condition, "expression", None))
                stack.append(value)
    return False


def _impl__unresolved_equivalence_blocking_unknown_reasons(
    self,
    blocking_reasons: Sequence[str],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    stage: str,
) -> List[UnknownReasonRecord]:
    unresolved: List[UnknownReasonRecord] = []
    for blocking_reason in blocking_reasons:
        reason_record = self._make_blocking_unsafety_unknown_reason(
            blocking_reason,
            analysis1,
            analysis2,
            stage=stage,
        )
        self._record_completed_call_effect_summary_proof_if_safe(
            reason_record,
            analysis1,
            analysis2,
        )
        if self._recovery_proof_is_complete(
            reason_record,
            analysis1,
            analysis2,
        ):
            continue
        unresolved.append(reason_record)
    return unresolved


def _impl__evidence_required_evidence_matches(cls, evidence: Any, expected_required: Sequence[str]) -> bool:
    required_evidence = tuple(
        str(item)
        for item in (cls._evidence_get(evidence, "required_evidence") or ())
    )
    return required_evidence == tuple(expected_required)


def _impl__query_cases_are_nonempty(cls, value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) > 0
        and all(isinstance(item, str) for item in value)
    )


def _impl__evidence_get(evidence: Any, key: str) -> Any:
    if isinstance(evidence, Mapping):
        return evidence.get(key)
    return getattr(evidence, key, None)


def _impl__evidence_text(cls, evidence: Any, key: str) -> str:
    value = cls._evidence_get(evidence, key)
    return "" if value is None else str(value)


def _impl__evidence_bool(cls, evidence: Any, key: str) -> bool:
    return bool(cls._evidence_get(evidence, key))


def _impl__evidence_has_any(cls, evidence: Any, keys: Sequence[str]) -> bool:
    for key in keys:
        value = cls._evidence_get(evidence, key)
        if value:
            return True
    return False


def _impl__evidence_has_any_recursive(cls, evidence: Any, keys: Sequence[str]) -> bool:
    if isinstance(evidence, Mapping):
        if cls._evidence_has_any(evidence, keys):
            return True
        return any(cls._evidence_has_any_recursive(value, keys) for value in evidence.values())
    if isinstance(evidence, Sequence) and not isinstance(evidence, (str, bytes, bytearray)):
        return any(cls._evidence_has_any_recursive(item, keys) for item in evidence)
    return False


def _impl__split_blocking_reason(blocking_reason: str) -> Tuple[str, str]:
    text = str(blocking_reason or "")
    if ":" not in text:
        return "", text
    label, reason = text.split(":", 1)
    return label, reason


def _impl__blocking_reason_kind(cls, blocking_reason: Optional[str]) -> str:
    _label, reason = cls._split_blocking_reason(str(blocking_reason or ""))
    return reason.split(":", 1)[0]


def _impl__blocking_reason_index(cls, reason_text: Optional[str]) -> Optional[int]:
    parts = str(reason_text or "").split(":")
    if len(parts) < 2:
        return None
    try:
        return int(parts[1])
    except (TypeError, ValueError):
        return None


def _impl__guard_union_miss_condition(
    self,
    guard_sets: Sequence[Sequence[Condition]],
) -> Optional[Condition]:
    guard_cases = [SimpleNamespace(conditions=tuple(guards or ())) for guards in guard_sets or ()]
    miss_terms = []
    for case in guard_cases:
        conditions = tuple(getattr(case, "conditions", ()) or ())
        if not conditions:
            return Condition(Expression.constant(0, 1), False)
        miss_expr = self._case_miss_expression(conditions)
        if miss_expr is None:
            return None
        miss_terms.append(miss_expr)
    if not miss_terms:
        return None
    expr = miss_terms[0]
    for term in miss_terms[1:]:
        expr = Expression.binary_op("BOOL_AND", expr, term)
    return Condition(expr, False)


def _impl__case_miss_expression(
    self,
    conditions: Sequence[Condition],
) -> Optional[Expression]:
    miss_terms = [self._negated_condition_expression(condition) for condition in conditions]
    miss_terms = [term for term in miss_terms if term is not None]
    if not miss_terms:
        return None
    result = miss_terms[0]
    for term in miss_terms[1:]:
        result = Expression.binary_op("BOOL_OR", result, term)
    return result


def _impl__negated_condition_expression(
    self,
    condition: Condition,
) -> Optional[Expression]:
    expr = getattr(condition, "expression", None)
    if expr is None:
        return None
    if bool(getattr(condition, "negated", False)):
        return expr
    return Expression.unary_op("BOOL_NEGATE", expr)


def _impl__case_conditions_contain_unresolved_expression(self, case: Any) -> bool:
    return any(
        self._expression_contains_unresolved(getattr(cond, "expression", None))
        for cond in getattr(case, "conditions", []) or []
    )


def _impl__expression_contains_unresolved(self, expr: Any) -> bool:
    if expr is None:
        return False

    expr_type = getattr(expr, "expr_type", None)
    if expr_type == ExpressionType.UNKNOWN:
        return True
    if expression_contains_unsupported_smt_ops(expr):
        return True

    if expr_type == ExpressionType.PHI and getattr(expr, "value", None):
        for cond, value in expr.value:
            if cond is not None and self._expression_contains_unresolved(getattr(cond, "expression", None)):
                return True
            if self._expression_contains_unresolved(value):
                return True
        return False

    for operand in getattr(expr, "operands", []) or []:
        if self._expression_contains_unresolved(operand):
            return True

    return False

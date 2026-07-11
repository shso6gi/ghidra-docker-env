"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.equivalence.strategies.base``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    Condition,
    Expression,
    ExpressionType,
    Mapping,
    Sequence,
    SimpleNamespace,
    UnknownReasonId,
    expression_contains_unsupported_smt_ops,
    expression_provenance_key,
    hashlib,
    json,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

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

def _impl__canonicalize_key_sequence(values: Sequence[Any]) -> Tuple[Any, ...]:
    return tuple(sorted(tuple(values or ()), key=repr))

def _impl__canonical_jsonable_for_digest(cls, value: Any) -> Optional[Any]:
    if value is None or isinstance(value, (str, bool, int, float)):
        return value
    if isinstance(value, Mapping):
        result = {}
        for key in sorted(value.keys(), key=lambda item: str(item)):
            if not isinstance(key, str):
                return None
            normalized = cls._canonical_jsonable_for_digest(value[key])
            if normalized is None and value[key] is not None:
                return None
            result[key] = normalized
        return result
    if isinstance(value, (tuple, list)):
        result = []
        for item in value:
            normalized = cls._canonical_jsonable_for_digest(item)
            if normalized is None and item is not None:
                return None
            result.append(normalized)
        return result
    return None

def _impl__canonical_json_digest(cls, value: Any) -> Optional[str]:
    canonical = cls._canonical_jsonable_for_digest(value)
    if canonical is None and value is not None:
        return None
    try:
        payload = json.dumps(
            canonical,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        )
    except (TypeError, ValueError):
        return None
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()

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

def _impl__readonly_identity_target_is_specific(cls, object_target_key: Any) -> bool:
    target = cls._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) != 5 or target[0] != "readonly_identity":
        return False
    return (
        cls._proof_target_pair_is_specific(target[1])
        and cls._readonly_identity_side_is_specific(target[2], "left")
        and cls._readonly_identity_side_is_specific(target[3], "right")
        and cls._readonly_identity_relation_is_specific(target[4])
    )

def _impl__method_b_closure_target_is_specific(cls, object_target_key: Any) -> bool:
    target = cls._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) != 5 or target[0] != "method_b_closure":
        return False
    return (
        cls._proof_target_pair_is_specific(target[1])
        and cls._method_b_closure_side_is_specific(target[2], "left")
        and cls._method_b_closure_side_is_specific(target[3], "right")
        and cls._method_b_closure_relation_is_specific(target[4])
    )

def _impl__readonly_identity_side_is_specific(cls, value: Any, expected_side: str) -> bool:
    side = cls._normalize_nested_tuple(value)
    return (
        isinstance(side, tuple)
        and len(side) == 7
        and side[0] == "readonly_identity_side"
        and side[1] == expected_side
        and not cls._proof_target_contains_diagnostic_value(side)
    )

def _impl__method_b_closure_side_is_specific(cls, value: Any, expected_side: str) -> bool:
    side = cls._normalize_nested_tuple(value)
    return (
        isinstance(side, tuple)
        and len(side) == 6
        and side[0] == "method_b_closure_side"
        and side[1] == expected_side
        and not cls._proof_target_contains_diagnostic_value(side)
    )

def _impl__readonly_identity_relation_is_specific(cls, value: Any) -> bool:
    relation = cls._normalize_nested_tuple(value)
    if (
        not isinstance(relation, tuple)
        or len(relation) != 3
        or relation[0] != "readonly_identity_relation"
        or cls._proof_target_contains_diagnostic_value(relation)
    ):
        return False
    shared = relation[1]
    storage = relation[2]
    return (
        isinstance(shared, tuple)
        and len(shared) == 2
        and shared[0] == "shared_count_identities"
        and isinstance(shared[1], tuple)
        and all(cls._readonly_component_key_is_specific(item) for item in shared[1])
        and isinstance(storage, tuple)
        and len(storage) == 2
        and storage[0] == "count_storage_relation"
        and cls._readonly_storage_relation_is_specific(storage[1])
    )

def _impl__readonly_storage_relation_is_specific(cls, value: Any) -> bool:
    relation = cls._normalize_nested_tuple(value)
    if not isinstance(relation, tuple) or not relation or not cls._proof_text_is_specific(relation[0]):
        return False
    kind = relation[0]
    if kind == "same_storage_identity":
        return len(relation) == 2 and cls._readonly_component_key_is_specific(relation[1])
    if kind in {"missing_storage_identity", "different_storage_identity", "different_register_base"}:
        return (
            len(relation) == 3
            and all(item is None or cls._readonly_component_key_is_specific(item) for item in relation[1:])
        )
    if kind == "same_register_base_projection":
        return (
            len(relation) == 5
            and cls._tag_payload_is_specific(relation[1], "base")
            and cls._readonly_bit_span_is_specific(relation[2], "left_bits")
            and cls._readonly_bit_span_is_specific(relation[3], "right_bits")
            and isinstance(relation[4], tuple)
            and len(relation[4]) == 2
            and relation[4][0] == "projection"
            and cls._proof_text_is_specific(relation[4][1])
        )
    return False

def _impl__tag_payload_is_specific(cls, value: Any, tag: str) -> bool:
    item = cls._normalize_nested_tuple(value)
    return (
        isinstance(item, tuple)
        and len(item) == 2
        and item[0] == tag
        and cls._object_leaf_is_specific(item[1])
    )

def _impl__object_leaf_is_specific(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    if normalized is None:
        return False
    if isinstance(normalized, str):
        return cls._proof_text_is_specific(normalized)
    if isinstance(normalized, bool):
        return True
    if isinstance(normalized, int):
        return True
    if isinstance(normalized, tuple):
        return bool(normalized) and not cls._proof_target_contains_missing_or_diagnostic(normalized)
    return False

def _impl__readonly_bit_span_is_specific(cls, value: Any, tag: str) -> bool:
    span = cls._normalize_nested_tuple(value)
    return (
        isinstance(span, tuple)
        and len(span) == 3
        and span[0] == tag
        and cls._proof_nonnegative_int_like(span[1])
        and cls._proof_positive_int_like(span[2])
    )

def _impl__readonly_component_key_is_specific(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or not normalized or not cls._proof_text_is_specific(normalized[0]):
        return False
    if cls._proof_target_contains_missing_or_diagnostic(normalized):
        return False
    root = normalized[0]
    if root in {"parameter", "parameter_index", "loop_limit_parameter"}:
        return len(normalized) == 2 and cls._proof_nonnegative_int_like(normalized[1])
    if root == "parameter_storage":
        return len(normalized) == 2 and cls._readonly_component_key_is_specific(normalized[1])
    if root == "register_storage":
        return len(normalized) == 6 and all(cls._proof_int_like(item) for item in normalized[1:])
    if root in {"binary", "kind"}:
        return len(normalized) == 2 and cls._proof_text_is_specific(normalized[1])
    if root in {"base", "count", "storage"}:
        return len(normalized) == 2 and cls._readonly_component_key_is_specific(normalized[1])
    if root in {"stride", "element_size", "result_size"}:
        return len(normalized) == 2 and cls._proof_nonnegative_int_like(normalized[1])
    if root in {"start_offset", "constant_bias"}:
        return len(normalized) == 2 and cls._proof_int_like(normalized[1])
    if root in {"expression", "condition"}:
        return len(normalized) >= 2 and not cls._proof_target_contains_missing_or_diagnostic(normalized)
    if root in {"const", "literal", "variable", "binary", "unary", "memory", "call", "intrinsic", "phi"}:
        return len(normalized) >= 2 and not cls._proof_target_contains_missing_or_diagnostic(normalized)
    return False

def _impl__method_b_closure_relation_is_specific(cls, value: Any) -> bool:
    relation = cls._normalize_nested_tuple(value)
    if (
        not isinstance(relation, tuple)
        or len(relation) < 2
        or relation[0] != "method_b_closure_relation"
        or cls._proof_target_contains_diagnostic_value(relation)
    ):
        return False
    fields = {
        item[0]: item[1:]
        for item in relation[1:]
        if isinstance(item, tuple) and len(item) >= 2 and isinstance(item[0], str)
    }
    kind = fields.get("kind", (None,))[0]
    if kind == "one_sided_summary":
        return (
            len(relation) == 7
            and fields.get("summary_side", (None,))[0] in {"left", "right"}
            and fields.get("exact_side", (None,))[0] in {"left", "right"}
            and fields.get("summary_side", (None,))[0] != fields.get("exact_side", (None,))[0]
            and cls._method_b_summary_profile_is_specific(fields.get("summary", (None,))[0])
            and cls._method_b_exact_terms_are_specific(fields.get("exact_terms", (None,))[0])
            and cls._proof_int_like(fields.get("exact_constant_bias", (None,))[0])
        )
    if kind == "dual_summary":
        return (
            len(relation) == 4
            and cls._method_b_summary_profile_is_specific(fields.get("left_summary", (None,))[0])
            and cls._method_b_summary_profile_is_specific(fields.get("right_summary", (None,))[0])
        )
    return False

def _impl__method_b_summary_profile_is_specific(cls, value: Any) -> bool:
    profile = cls._normalize_nested_tuple(value)
    if not isinstance(profile, tuple) or len(profile) != 5 or profile[0] != "method_b_summary_profile":
        return False
    fields = {
        item[0]: item[1]
        for item in profile[1:]
        if isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
    }
    return (
        cls._method_b_runtime_ref_key_is_specific(fields.get("runtime_ref"))
        and cls._method_b_loop_summary_key_is_specific(fields.get("loop_summary"))
        and cls._readonly_term_contract_is_specific(fields.get("term_contract"))
        and cls._method_b_count_identities_are_specific(fields.get("count_identities"))
    )

def _impl__method_b_runtime_ref_key_is_specific(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    return (
        isinstance(normalized, tuple)
        and len(normalized) >= 2
        and normalized[0]
        in {
            "readonly_reduction",
            "readonly_reduction_proof_semantic",
            "readonly_reduction_loop_semantic",
            "readonly_reduction_semantic",
            "counted_loop_summary",
            "counted_loop_summary_loop_semantic",
            "counted_loop_summary_semantic",
            "counted_loop_summary_profile_ref",
        }
        and not cls._proof_target_contains_missing_or_diagnostic(normalized)
    )

def _impl__method_b_loop_summary_key_is_specific(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    return (
        isinstance(normalized, tuple)
        and len(normalized) >= 2
        and normalized[0] in {"loop_summary", "loop_summary_method_b", "counted_loop_summary_loop_profile"}
        and not cls._proof_target_contains_missing_or_diagnostic(normalized)
    )

def _impl__readonly_term_contract_is_specific(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or len(normalized) < 2:
        return False
    if cls._proof_target_contains_missing_or_diagnostic(normalized):
        return False
    if normalized[0] == "readonly_reduction_term_sequence_contract":
        return (
            len(normalized) >= 14
            and cls._proof_text_is_specific(normalized[1])
            and cls._readonly_component_key_is_specific(normalized[2])
            and cls._readonly_component_key_is_specific(normalized[3])
            and cls._readonly_component_key_is_specific(normalized[4])
            and all(cls._proof_int_like(item) for item in normalized[5:10])
            and isinstance(normalized[10], bool)
            and isinstance(normalized[11], tuple)
            and cls._readonly_projection_key_is_specific(normalized[12])
            and cls._readonly_side_effect_profile_is_specific(normalized[13])
        )
    if normalized[0] == "affine_readonly_sum":
        return len(normalized) >= 4 and all(
            cls._readonly_component_key_is_specific(item) for item in normalized[1:]
        )
    if normalized[0] == "counted_loop_summary_contract":
        return (
            len(normalized) == 10
            and cls._method_b_runtime_ref_key_is_specific(normalized[1])
            and cls._method_b_loop_summary_key_is_specific(normalized[2])
            and cls._proof_positive_int_like(normalized[3])
            and cls._proof_int_like(normalized[4])
            and isinstance(normalized[5], bool)
            and isinstance(normalized[6], tuple)
            and isinstance(normalized[7], tuple)
            and cls._proof_int_like(normalized[8])
            and isinstance(normalized[9], tuple)
            and not cls._proof_target_contains_missing_or_diagnostic(normalized)
        )
    return False

def _impl__readonly_projection_key_is_specific(cls, value: Any) -> bool:
    projection = cls._normalize_nested_tuple(value)
    return (
        isinstance(projection, tuple)
        and len(projection) == 2
        and all(cls._proof_int_like(item) for item in projection)
    )

def _impl__method_b_count_identities_are_specific(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    return (
        isinstance(normalized, tuple)
        and bool(normalized)
        and all(isinstance(item, tuple) and bool(item) for item in normalized)
        and not cls._proof_target_contains_missing_or_diagnostic(normalized)
    )

def _impl__method_b_closure_relation_fields(cls, value: Any) -> Optional[Dict[str, Tuple[Any, ...]]]:
    relation = cls._normalize_nested_tuple(value)
    if not isinstance(relation, tuple) or len(relation) < 2 or relation[0] != "method_b_closure_relation":
        return None
    return {
        item[0]: item[1:]
        for item in relation[1:]
        if isinstance(item, tuple) and len(item) >= 2 and isinstance(item[0], str)
    }

def _impl__method_b_one_sided_relation_payload(
    cls,
    object_target_key: Tuple[Any, ...],
) -> Optional[Dict[str, Any]]:
    target = cls._normalize_nested_tuple(object_target_key)
    if not (
        isinstance(target, tuple)
        and len(target) == 5
        and cls._method_b_closure_relation_is_specific(target[4])
    ):
        return None
    fields = cls._method_b_closure_relation_fields(target[4])
    if not fields or fields.get("kind", (None,))[0] != "one_sided_summary":
        return None
    exact_bias = fields.get("exact_constant_bias", (None,))[0]
    if not cls._proof_int_like(exact_bias):
        return None
    return {
        "summary_side": fields.get("summary_side", (None,))[0],
        "exact_side": fields.get("exact_side", (None,))[0],
        "exact_terms": cls._normalize_nested_tuple(fields.get("exact_terms", (None,))[0]),
        "exact_constant_bias": int(exact_bias),
    }

def _impl__method_b_exact_terms_are_specific(cls, value: Any) -> bool:
    terms = cls._normalize_nested_tuple(value)
    return (
        isinstance(terms, tuple)
        and bool(terms)
        and all(cls._method_b_readonly_term_is_specific(term) for term in terms)
    )

def _impl__method_b_readonly_term_is_specific(cls, value: Any) -> bool:
    term = cls._normalize_nested_tuple(value)
    return (
        isinstance(term, tuple)
        and len(term) == 3
        and term[0] == "readonly_reduction_term"
        and cls._proof_nonnegative_int_like(term[1])
        and cls._proof_positive_int_like(term[2])
    )

def _impl__readonly_identity_storage_relation_from_target(cls, object_target_key: Any) -> Optional[Tuple[Any, ...]]:
    target = cls._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) != 5:
        return None
    relation = cls._normalize_nested_tuple(target[4])
    if not isinstance(relation, tuple) or len(relation) != 3:
        return None
    storage = cls._normalize_nested_tuple(relation[2])
    if not isinstance(storage, tuple) or len(storage) != 2 or storage[0] != "count_storage_relation":
        return None
    storage_relation = cls._normalize_nested_tuple(storage[1])
    return storage_relation if isinstance(storage_relation, tuple) else None

def _impl__method_b_guard_count_values(cls, proof_content: Mapping[str, Any]) -> Tuple[int, ...]:
    raw_values = proof_content.get("count_values")
    if raw_values is None:
        if not cls._proof_positive_int_like(proof_content.get("count_value")):
            return ()
        return (int(proof_content.get("count_value")),)
    values = cls._normalize_nested_tuple(raw_values)
    if not isinstance(values, tuple) or not values:
        return ()
    normalized: List[int] = []
    for value in values:
        if not cls._proof_positive_int_like(value):
            return ()
        normalized.append(int(value))
    if len(set(normalized)) != len(normalized):
        return ()
    if proof_content.get("count_value") is not None:
        if not cls._proof_positive_int_like(proof_content.get("count_value")):
            return ()
        if int(proof_content.get("count_value")) not in set(normalized):
            return ()
    return tuple(normalized)

def _impl__method_b_dual_summary_relation_payload(
    cls,
    object_target_key: Tuple[Any, ...],
) -> Optional[Dict[str, Any]]:
    target = cls._normalize_nested_tuple(object_target_key)
    if not (
        isinstance(target, tuple)
        and len(target) == 5
        and cls._method_b_closure_relation_is_specific(target[4])
    ):
        return None
    fields = cls._method_b_closure_relation_fields(target[4])
    if not fields or fields.get("kind", (None,))[0] != "dual_summary":
        return None
    left_summary = cls._normalize_nested_tuple(fields.get("left_summary", (None,))[0])
    right_summary = cls._normalize_nested_tuple(fields.get("right_summary", (None,))[0])
    if not (
        cls._method_b_summary_profile_is_specific(left_summary)
        and cls._method_b_summary_profile_is_specific(right_summary)
    ):
        return None
    return {
        "left_summary": left_summary,
        "right_summary": right_summary,
    }

def _impl__positive_int_like(value: Any) -> bool:
    if isinstance(value, bool):
        return False
    try:
        return int(value) > 0
    except (TypeError, ValueError):
        return False

def _impl__query_cases_are_nonempty(cls, value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) > 0
        and all(isinstance(item, str) for item in value)
    )

def _impl__nested_contains_tag(cls, value: Any, tag: str) -> bool:
    if isinstance(value, Mapping):
        return any(cls._nested_contains_tag(item, tag) for item in value.values())
    if isinstance(value, tuple):
        if value and value[0] == tag:
            return True
        return any(cls._nested_contains_tag(item, tag) for item in value)
    if isinstance(value, list):
        return any(cls._nested_contains_tag(item, tag) for item in value)
    return False

def _impl__normalization_policy_digest_from_target(cls, object_target_key: Any) -> Optional[str]:
    if isinstance(object_target_key, tuple):
        if (
            len(object_target_key) == 2
            and object_target_key[0] == "normalization_policy_digest"
            and isinstance(object_target_key[1], str)
        ):
            return object_target_key[1]
        for item in object_target_key:
            found = cls._normalization_policy_digest_from_target(item)
            if found is not None:
                return found
    return None

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

def _impl__normalize_nested_tuple(cls, value: Any):
    if value is None:
        return None
    if isinstance(value, (tuple, list)):
        return tuple(cls._normalize_nested_tuple(item) for item in value)
    return value

def _impl__return_value_extension_ops_object_key(self, return_info: Any) -> Tuple[Any, ...]:
    profiles: List[Tuple[Any, ...]] = []
    seen: Set[Tuple[Any, ...]] = set()
    for ref in (getattr(return_info, "return_value_pcode_op_refs", None) or ()):
        mnemonic = getattr(ref, "mnemonic", None)
        if mnemonic not in {"INT_SEXT", "INT_ZEXT"}:
            continue
        input_size = None
        try:
            input_size = ref.input_size(0)
        except Exception:
            input_size = None
        output_size = getattr(ref, "output_size", None)
        input_bits = int(input_size) * 8 if input_size else None
        output_bits = int(output_size) * 8 if output_size else None
        policy = "sign_extend" if mnemonic == "INT_SEXT" else "zero_extend"
        profile = (
            "extension_op",
            mnemonic,
            ("op_ref", self._stable_key_or_none(ref)),
            ("input_bits", input_bits),
            ("output_bits", output_bits),
            ("policy", policy),
        )
        if profile in seen:
            continue
        seen.add(profile)
        profiles.append(profile)
    return ("return_value_extension_ops", tuple(profiles))

def _impl__solver_timeout_object_target_key(
    self,
    *,
    analysis1: Optional[FunctionReturnAnalysis],
    analysis2: Optional[FunctionReturnAnalysis],
    stage: str,
    query: Optional[str],
    timeout_seconds: Any = None,
    pair_id: Optional[str] = None,
    solver_name: Optional[str] = None,
    parallel_result: Optional[ParallelResult] = None,
) -> Optional[Tuple[Any, ...]]:
    """Stable target for a timed-out solver query.

    The query hash identifies the generated SMT artifact while both side
    records keep the target anchored to Ghidra-derived function, return, and
    guard objects.  Program ids are normalized through binary ids.
    """

    query_text = query or ""
    query_hash = hashlib.sha256(query_text.encode("utf-8")).hexdigest() if query_text else None
    resolved_pair_id = pair_id or self._binary_pair_id_from_analyses(analysis1, analysis2)
    solver_options_key = self._solver_timeout_options_object_key(
        parallel_result=parallel_result,
        timeout_seconds=timeout_seconds,
        fallback_solver_name=solver_name,
    )
    if solver_options_key is None:
        return None
    return (
        "solver_timeout",
        ("pair", resolved_pair_id),
        ("stage", str(stage or "unknown")),
        ("query_hash", query_hash),
        ("timeout_budget_seconds", self._coerce_timeout_seconds(timeout_seconds)),
        solver_options_key,
        self._solver_timeout_side_object_key("left", analysis1),
        self._solver_timeout_side_object_key("right", analysis2),
    )

def _impl__solver_timeout_options_object_key(
    self,
    *,
    parallel_result: Optional[ParallelResult],
    timeout_seconds: Any,
    fallback_solver_name: Optional[str] = None,
) -> Optional[Tuple[Any, ...]]:
    timeout_key = ("timeout_seconds", self._coerce_timeout_seconds(timeout_seconds))
    solver_names = self._solver_names_from_parallel_result(parallel_result)
    if len(solver_names) == 1:
        return ("solver_options", ("solver", solver_names[0]), timeout_key)
    if solver_names:
        return ("solver_options", ("solvers", solver_names), timeout_key)
    if parallel_result is not None:
        return None
    fallback = str(fallback_solver_name).strip() if fallback_solver_name is not None else ""
    if not fallback:
        return None
    return ("solver_options", ("solver", fallback), timeout_key)

def _impl__solver_names_from_parallel_result(parallel_result: Optional[ParallelResult]) -> Tuple[str, ...]:
    results = getattr(parallel_result, "results", None)
    if not results:
        return ()
    names = {
        str(name).strip()
        for result in results
        for name in (getattr(result, "solver_name", None),)
        if name is not None and str(name).strip()
    }
    return tuple(sorted(names))

def _impl__coerce_timeout_seconds(value: Any) -> Optional[int]:
    try:
        seconds = int(value)
    except (TypeError, ValueError):
        return None
    return seconds if seconds >= 0 else None

def _impl__solver_timeout_side_object_key(
    self,
    side_label: str,
    analysis: Optional[FunctionReturnAnalysis],
) -> Tuple[Any, ...]:
    target = (
        "solver_timeout_side",
        side_label,
        self._analysis_entry_key(analysis) if analysis is not None else None,
        self._return_storage_object_key(analysis) if analysis is not None else None,
        self._return_partition_object_key(analysis) if analysis is not None else None,
        self._return_guard_disjunction_object_key(analysis) if analysis is not None else None,
    )
    if analysis is not None:
        return self._artifact_stable_key_for_analysis(target, analysis)
    return target

def _impl__binary_pair_id_from_analyses(
    cls,
    analysis1: Optional[FunctionReturnAnalysis],
    analysis2: Optional[FunctionReturnAnalysis],
) -> Optional[str]:
    left = cls._analysis_binary_id(analysis1)
    right = cls._analysis_binary_id(analysis2)
    if not left or not right:
        return None
    return "_".join(sorted((left, right)))

def _impl__analysis_binary_id(analysis: Optional[FunctionReturnAnalysis]) -> Optional[str]:
    if analysis is None:
        return None
    binary_id = getattr(analysis, "binary_id", None)
    if isinstance(binary_id, str) and binary_id.strip():
        return binary_id.strip()
    return None

def _impl__return_storage_object_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    surface = None
    surface_getter = getattr(analysis, "get_comparison_surface", None)
    if callable(surface_getter):
        try:
            surface = surface_getter()
        except (AttributeError, TypeError, ValueError, RecursionError):
            surface = None
    return (
        "return_storage",
        getattr(surface, "kind", None),
        getattr(surface, "explicit_bit_width", None),
        getattr(surface, "use_sign_extension", None),
        getattr(analysis, "return_type", None),
    )

def _impl__return_case_object_key(self, index: int, return_info: Any) -> Tuple[Any, ...]:
    pcode_op_ref = getattr(return_info, "pcode_op_ref", None)
    pcode_key = self._stable_key_or_none(pcode_op_ref)
    value = getattr(return_info, "value", None)
    return (
        "return_case",
        int(index),
        getattr(return_info, "address", None),
        pcode_key,
        getattr(return_info, "pcode_identity", None),
        getattr(return_info, "pcode_order", None),
        self._expression_runtime_object_key(value),
        tuple(
            self._return_condition_object_key(condition)
            for condition in (getattr(return_info, "conditions", None) or ())
        ),
    )

def _impl__return_guard_disjunction_object_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    return (
        "guard_disjunction",
        tuple(
            (
                int(index),
                tuple(
                    self._return_condition_object_key(condition)
                    for condition in (getattr(return_info, "conditions", None) or ())
                ),
            )
            for index, return_info in enumerate(getattr(analysis, "returns", ()) or ())
        ),
    )

def _impl__return_condition_object_key(self, condition: Any) -> Tuple[Any, ...]:
    expression = getattr(condition, "expression", None)
    structural_key = None
    key_fn = getattr(condition, "structural_key", None)
    if callable(key_fn):
        try:
            structural_key = key_fn(budget=256)
        except TypeError:
            try:
                structural_key = key_fn()
            except (AttributeError, TypeError, ValueError, RecursionError):
                structural_key = None
        except (AttributeError, ValueError, RecursionError):
            structural_key = None
    return (
        "return_guard",
        bool(getattr(condition, "negated", False)),
        structural_key,
        self._expression_runtime_object_key(expression),
    )

def _impl__conditions_runtime_object_key(self, conditions: Any) -> Tuple[Any, ...]:
    return (
        "conditions",
        tuple(
            self._return_condition_object_key(condition)
            for condition in (conditions or ())
        ),
    )

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

def _impl__artifact_stable_key_for_analysis(
    cls,
    value: Any,
    analysis: Optional[FunctionReturnAnalysis],
) -> Any:
    binary_id = getattr(analysis, "binary_id", None) if analysis is not None else None
    if binary_id is None:
        return value
    return cls._rewrite_program_identity_keys(value, str(binary_id))

def _impl__rewrite_program_identity_keys(cls, value: Any, binary_id: str) -> Any:
    if isinstance(value, list):
        value = tuple(value)
    if not isinstance(value, tuple):
        return value
    rewritten = tuple(cls._rewrite_program_identity_keys(item, binary_id) for item in value)
    if not rewritten:
        return rewritten
    tag = rewritten[0]
    atom_rewritten = cls._rewrite_atom_encoded_program_identity_key(rewritten, binary_id)
    if atom_rewritten is not None:
        return atom_rewritten
    if tag in {"function", "code_address"} and len(rewritten) >= 3 and cls._program_id_like(rewritten[1]):
        return (tag, binary_id, rewritten[2], *rewritten[3:])
    if tag == "parameter" and len(rewritten) >= 4 and cls._program_id_like(rewritten[1]):
        return (tag, binary_id, rewritten[2], *rewritten[3:])
    if tag == "deferred_call_site" and len(rewritten) == 6 and cls._program_id_like(rewritten[1]):
        caller_entry = rewritten[2]
        caller_key: Any = None
        try:
            caller_key = ("function_ref", ("function", binary_id, int(caller_entry)))
        except (TypeError, ValueError):
            caller_key = ("function_ref", ("function", binary_id, caller_entry))
        return (
            "deferred_call_site",
            caller_key,
            rewritten[3],
            rewritten[4],
            ("argument",),
            rewritten[5],
        )
    return rewritten

def _impl__rewrite_atom_encoded_program_identity_key(
    cls,
    rewritten: Tuple[Any, ...],
    binary_id: str,
) -> Optional[Tuple[Any, ...]]:
    """Normalize program ids inside structural._atom_key encoded tuples.

    expression_provenance_key() preserves runtime_ref.stable_key() through
    _atom_key(), so CallTargetRef / DeferredCallRef identities can appear as
    ("tuple", (("str", "function"), ("int", program_id), ...)) rather than
    raw ("function", program_id, ...).  These ids are Ghidra session-local
    and must not become proof target identity.
    """

    if len(rewritten) != 2 or rewritten[0] != "tuple" or not isinstance(rewritten[1], tuple):
        return None
    items = rewritten[1]
    if not items or not cls._atom_str_is(items[0], None):
        return None
    atom_tag = items[0][1]
    if atom_tag in {"function", "code_address"} and len(items) >= 3 and cls._atom_program_id_like(items[1]):
        return ("tuple", (items[0], ("str", binary_id), items[2], *items[3:]))
    if atom_tag == "parameter" and len(items) >= 4 and cls._atom_program_id_like(items[1]):
        return ("tuple", (items[0], ("str", binary_id), items[2], *items[3:]))
    if atom_tag == "unknown" and len(items) >= 2 and cls._atom_program_id_like(items[1]):
        return ("tuple", (items[0], ("str", binary_id), *items[2:]))
    if atom_tag == "deferred_call_site" and len(items) == 6 and cls._atom_program_id_like(items[1]):
        return ("tuple", (items[0], ("str", binary_id), items[2], items[3], items[4], items[5]))
    return None

def _impl__program_id_like(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)

def _impl__atom_program_id_like(cls, value: Any) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "int"
        and cls._program_id_like(value[1])
    )

def _impl__atom_str_is(value: Any, expected: Optional[str]) -> bool:
    return (
        isinstance(value, tuple)
        and len(value) == 2
        and value[0] == "str"
        and (expected is None or value[1] == expected)
    )

def _impl__typed_target_expression_key(cls, expr: Any) -> Optional[Tuple[Any, ...]]:
    if expr is None:
        return None
    return ("typed_target_expression", cls._expression_runtime_object_key(expr))

def _impl__analysis_entry_key(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    binary_id = getattr(analysis, "binary_id", None)
    function_ref = getattr(analysis, "function_ref", None)
    if binary_id and function_ref is not None:
        entry_offset = getattr(function_ref, "entry_offset", None)
        if entry_offset is None:
            entry_offset = getattr(function_ref, "address_offset", None)
        if entry_offset is not None:
            try:
                return ("function_ref", ("function", str(binary_id), int(entry_offset)))
            except (TypeError, ValueError):
                pass
    stable_key = getattr(function_ref, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
            if key is not None:
                return ("function_ref", key)
        except (AttributeError, TypeError, ValueError, RecursionError):
            pass
    return ("entry_point", getattr(analysis, "entry_point", None))

def _impl__deterministic_function_identity(
    cls,
    analysis: FunctionReturnAnalysis,
) -> Tuple[Any, ...]:
    binary_id = getattr(analysis, "binary_id", None)
    normalized_binary_id = str(binary_id).strip() if binary_id is not None and str(binary_id).strip() else "unknown_binary"
    binary_name = getattr(analysis, "binary_name", None)
    normalized_binary_name = str(binary_name).strip() if binary_name is not None and str(binary_name).strip() else "unknown_binary_name"
    language_id = (
        getattr(analysis, "language_id", None)
        or getattr(analysis, "program_language_id", None)
        or getattr(analysis, "architecture_language_id", None)
    )
    normalized_language_id = str(language_id).strip() if language_id is not None and str(language_id).strip() else "unknown_language"
    compiler_artifact = (
        getattr(analysis, "compiler_artifact_identity", None)
        or getattr(analysis, "compiler_spec_id", None)
        or getattr(analysis, "compiler_id", None)
    )
    normalized_compiler = (
        str(compiler_artifact).strip()
        if compiler_artifact is not None and str(compiler_artifact).strip()
        else "unknown_compiler_artifact"
    )
    calling_convention = (
        getattr(analysis, "calling_convention", None)
        or getattr(analysis, "calling_convention_name", None)
    )
    normalized_calling_convention = (
        str(calling_convention).strip()
        if calling_convention is not None and str(calling_convention).strip()
        else "unknown_calling_convention"
    )
    return (
        "function_identity",
        ("identity_schema_version", cls._RETURN_COVERAGE_TARGET_SCHEMA_VERSION),
        (
            "binary_identity",
            ("binary_id", normalized_binary_id),
            ("binary_name", normalized_binary_name),
            ("language_id", normalized_language_id),
            ("compiler_artifact", normalized_compiler),
        ),
        ("function_name", cls._identity_freeze(getattr(analysis, "function_name", None))),
        ("entry_offset", cls._analysis_entry_offset(analysis)),
        ("entry_point", cls._identity_freeze(getattr(analysis, "entry_point", None))),
        ("signature", cls._normalized_function_signature_key(analysis)),
        ("calling_convention", normalized_calling_convention),
    )

def _impl__analysis_entry_offset(cls, analysis: FunctionReturnAnalysis) -> Optional[int]:
    function_ref = getattr(analysis, "function_ref", None)
    for value in (
        getattr(function_ref, "entry_offset", None),
        getattr(function_ref, "address_offset", None),
        getattr(analysis, "entry_point", None),
    ):
        try:
            return int(str(value), 0)
        except (TypeError, ValueError):
            continue
    return None

def _impl__normalized_function_signature_key(
    cls,
    analysis: FunctionReturnAnalysis,
) -> Tuple[Any, ...]:
    parameters = []
    for param in getattr(analysis, "parameters", ()) or ():
        if isinstance(param, Mapping):
            param_index = param.get("index")
            try:
                param_index = int(param_index)
            except (TypeError, ValueError):
                param_index = None
            parameters.append(
                (
                    "parameter",
                    ("index", param_index),
                    ("name", cls._identity_freeze(param.get("name"))),
                    ("data_type", cls._identity_freeze(param.get("data_type"))),
                    ("size", cls._identity_freeze(param.get("size"))),
                    ("is_signed", cls._identity_freeze(param.get("is_signed"))),
                    ("storage", cls._identity_freeze(param.get("storage"))),
                )
            )
        else:
            parameters.append(("parameter", cls._identity_freeze(param)))
    parameters.sort(key=repr)
    return (
        "function_signature",
        ("return_type", cls._identity_freeze(getattr(analysis, "return_type", None))),
        ("return_storage", cls._identity_freeze(cls._return_storage_static_key(analysis))),
        ("parameters", tuple(parameters)),
    )

def _impl__return_storage_static_key(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
    surface = None
    surface_getter = getattr(analysis, "get_comparison_surface", None)
    if callable(surface_getter):
        try:
            surface = surface_getter()
        except (AttributeError, TypeError, ValueError, RecursionError):
            surface = None
    return (
        "return_storage",
        getattr(surface, "kind", None),
        getattr(surface, "explicit_bit_width", None),
        getattr(surface, "use_sign_extension", None),
        getattr(analysis, "return_type", None),
    )

def _impl__identity_freeze(cls, value: Any) -> Any:
    if isinstance(value, Mapping):
        return tuple(
            (str(key), cls._identity_freeze(item))
            for key, item in sorted(value.items(), key=lambda item: str(item[0]))
        )
    if isinstance(value, (tuple, list)):
        return tuple(cls._identity_freeze(item) for item in value)
    if isinstance(value, (set, frozenset)):
        return tuple(sorted((cls._identity_freeze(item) for item in value), key=repr))
    if isinstance(value, bool) or isinstance(value, int) or isinstance(value, str) or value is None:
        return value
    if isinstance(value, float):
        return ("float", repr(value))
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            return cls._identity_freeze(stable_key())
        except (AttributeError, TypeError, ValueError, RecursionError):
            pass
    return ("opaque", type(value).__module__, type(value).__qualname__)

def _impl__stable_key_or_none(value: Any):
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            return stable_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
    return None

def _impl__expression_runtime_object_key(cls, expr: Any) -> Tuple[Any, ...]:
    return expression_provenance_key(expr)

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

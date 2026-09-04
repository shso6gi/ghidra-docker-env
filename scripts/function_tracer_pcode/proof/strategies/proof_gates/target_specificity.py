"""Specificity predicates for readonly-identity and Method-B closure targets and relations."""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Optional, Tuple


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

"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.equivalence.strategies.base``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    Mapping,
    Sequence,
    UnknownReasonId,
    UnknownRecoveryProofKind,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__recovery_proof_is_complete(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> bool:
    if not self.enable_completed_recovery_proofs:
        return False
    return self._call_effect_summary_proof_is_complete(
        reason_record,
        analysis1,
        analysis2,
    ) or self._return_coverage_proof_is_complete(
        reason_record,
        analysis1,
        analysis2,
    ) or self._sat_unsafety_resolution_proof_is_complete(
        reason_record,
        analysis1,
        analysis2,
    ) or self._return_width_bridge_proof_is_complete(
        reason_record,
        analysis1,
        analysis2,
    ) or self._readonly_identity_proof_is_complete(
        reason_record,
        analysis1,
        analysis2,
    ) or self._method_b_closure_proof_is_complete(
        reason_record,
        analysis1,
        analysis2,
    )

def _impl__completed_recovery_proof_evidence(
    cls,
    *analyses: FunctionReturnAnalysis,
) -> Tuple[Mapping[str, Any], ...]:
    evidence_records: List[Mapping[str, Any]] = []
    for analysis in analyses:
        for evidence in getattr(analysis, "completed_recovery_proof_evidence", ()) or ():
            if isinstance(evidence, Mapping):
                evidence_records.append(evidence)
    return tuple(evidence_records)

def _impl__readonly_identity_proof_is_complete(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> bool:
    if reason_record.reason_id != UnknownReasonId.READONLY_IDENTITY_MISSING.value:
        return False
    if reason_record.recovery_proof_kind != UnknownRecoveryProofKind.STORAGE_BACKED_IDENTITY_PROPAGATION.value:
        return False
    return self._all_recovery_actions_have_completed_proofs(reason_record, analysis1, analysis2)

def _impl__method_b_closure_proof_is_complete(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> bool:
    if reason_record.reason_id != UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value:
        return False
    if reason_record.recovery_proof_kind not in {
        UnknownRecoveryProofKind.PROOF_BACKED_COVERING_CASE.value,
        UnknownRecoveryProofKind.GUARD_PARTITION_COMPLETION.value,
    }:
        return False
    return self._all_recovery_actions_have_completed_proofs(reason_record, analysis1, analysis2)

def _impl__all_recovery_actions_have_completed_proofs(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> bool:
    completed = set(self._completed_recovery_proof_ids(analysis1, analysis2))
    required_ids = tuple(
        self._normalize_nested_tuple(action.proof_obligation_id)
        for action in build_unknown_recovery_actions([reason_record])
    )
    if not required_ids or any(proof_id is None for proof_id in required_ids):
        return False
    return all(proof_id in completed for proof_id in required_ids)

def _impl__completed_recovery_proof_ids(
    cls,
    *analyses: FunctionReturnAnalysis,
) -> Tuple[Tuple[Any, ...], ...]:
    proof_ids: List[Tuple[Any, ...]] = []
    for analysis in analyses:
        proof_ids.extend(cls._produced_recovery_proof_ids(analysis))
    return tuple(proof_ids)

def _impl__produced_recovery_proof_ids(
    cls,
    analysis: FunctionReturnAnalysis,
) -> Tuple[Tuple[Any, ...], ...]:
    proof_ids: List[Tuple[Any, ...]] = []
    evidence_records = getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
    if not cls._analysis_has_active_call_effect_proof_blockers(analysis):
        for evidence in evidence_records:
            proof_id = cls._call_effect_summary_proof_id_from_evidence(evidence)
            if proof_id is not None:
                proof_ids.append(proof_id)
    for evidence in evidence_records:
        proof_id = cls._return_coverage_proof_id_from_evidence(evidence)
        if proof_id is not None:
            proof_ids.append(proof_id)
    for evidence in evidence_records:
        proof_id = cls._sat_unsafety_resolution_proof_id_from_evidence(evidence)
        if proof_id is not None:
            proof_ids.append(proof_id)
    for evidence in evidence_records:
        proof_id = cls._return_width_bridge_proof_id_from_evidence(evidence)
        if proof_id is not None:
            proof_ids.append(proof_id)
    for evidence in evidence_records:
        proof_id = cls._readonly_identity_proof_id_from_evidence(evidence)
        if proof_id is not None:
            proof_ids.append(proof_id)
    for evidence in evidence_records:
        proof_id = cls._method_b_closure_proof_id_from_evidence(evidence)
        if proof_id is not None:
            proof_ids.append(proof_id)
    return tuple(proof_ids)

def _impl__proof_section_payload_matches(
    cls,
    section: Any,
    payload_key: str,
    expected_payload: Tuple[Any, ...],
) -> bool:
    if not isinstance(section, Mapping):
        return False
    if not cls._completed_proof_section_is_clean(section):
        return False
    return cls._normalize_nested_tuple(section.get(payload_key)) == expected_payload

def _impl__readonly_identity_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
    if not cls._evidence_bool(evidence, "object_derived"):
        return None
    if cls._evidence_text(evidence, "status") not in {"complete", "completed", "proven"}:
        return None
    if cls._evidence_text(evidence, "reason_id") != UnknownReasonId.READONLY_IDENTITY_MISSING.value:
        return None
    proof_kind = cls._evidence_text(evidence, "proof_kind") or cls._evidence_text(
        evidence,
        "recovery_proof_kind",
    )
    if proof_kind != UnknownRecoveryProofKind.STORAGE_BACKED_IDENTITY_PROPAGATION.value:
        return None
    proof_stage = cls._evidence_text(evidence, "proof_stage")
    if proof_stage != "readonly_operand_identity":
        return None
    expected_evidence_kind, expected_required = cls._READONLY_IDENTITY_ACTION_REQUIREMENT
    evidence_kind = cls._evidence_text(evidence, "evidence_kind")
    if evidence_kind != expected_evidence_kind:
        return None
    if not cls._evidence_required_evidence_matches(evidence, expected_required):
        return None
    if cls._evidence_has_any(evidence, cls._COMPLETED_PROOF_BLOCKER_FIELDS):
        return None
    object_target_key = cls._normalize_nested_tuple(cls._evidence_get(evidence, "object_target_key"))
    if not cls._readonly_identity_target_is_specific(object_target_key):
        return None
    proof_id = build_proof_obligation_id(
        UnknownReasonId.READONLY_IDENTITY_MISSING.value,
        proof_stage,
        proof_kind,
        evidence_kind,
        object_target_key,
    )
    provided_id = cls._normalize_nested_tuple(cls._evidence_get(evidence, "proof_obligation_id"))
    if provided_id is None or provided_id != proof_id:
        return None
    proof_content = cls._evidence_get(evidence, "proof_content")
    if not cls._readonly_identity_proof_content_is_complete(proof_content, object_target_key):
        return None
    return proof_id

def _impl__method_b_closure_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
    if not cls._evidence_bool(evidence, "object_derived"):
        return None
    if cls._evidence_text(evidence, "status") not in {"complete", "completed", "proven"}:
        return None
    if cls._evidence_text(evidence, "reason_id") != UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value:
        return None
    proof_kind = cls._evidence_text(evidence, "proof_kind") or cls._evidence_text(
        evidence,
        "recovery_proof_kind",
    )
    proof_stage = cls._evidence_text(evidence, "proof_stage")
    requirement = cls._METHOD_B_ACTION_REQUIREMENTS.get((proof_kind, proof_stage))
    if requirement is None:
        return None
    expected_evidence_kind, expected_required = requirement
    evidence_kind = cls._evidence_text(evidence, "evidence_kind")
    if evidence_kind != expected_evidence_kind:
        return None
    if not cls._evidence_required_evidence_matches(evidence, expected_required):
        return None
    if cls._evidence_has_any(evidence, cls._COMPLETED_PROOF_BLOCKER_FIELDS):
        return None
    object_target_key = cls._normalize_nested_tuple(cls._evidence_get(evidence, "object_target_key"))
    if not cls._method_b_closure_target_is_specific(object_target_key):
        return None
    proof_id = build_proof_obligation_id(
        UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value,
        proof_stage,
        proof_kind,
        evidence_kind,
        object_target_key,
    )
    provided_id = cls._normalize_nested_tuple(cls._evidence_get(evidence, "proof_obligation_id"))
    if provided_id is None or provided_id != proof_id:
        return None
    proof_content = cls._evidence_get(evidence, "proof_content")
    if not cls._method_b_closure_proof_content_is_complete(
        proof_content,
        object_target_key,
        proof_stage=proof_stage,
    ):
        return None
    return proof_id

def _impl__proof_target_pair_is_specific(cls, value: Any) -> bool:
    pair = cls._normalize_nested_tuple(value)
    return (
        isinstance(pair, tuple)
        and len(pair) == 2
        and pair[0] == "pair"
        and cls._proof_text_is_specific(pair[1])
    )

def _impl__proof_target_contains_weak_value(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    if normalized is None:
        return True
    if isinstance(normalized, str):
        text = normalized.strip()
        return (
            not text
            or text == "<missing>"
            or text.startswith("missing_")
            or text.endswith("_unavailable")
            or text in {
                "missing_readonly_ref",
                "missing_method_b_summary",
                "exact_terms_unavailable",
                "loop_summary_shape_mismatch",
                "loop_summary_guard_mismatch",
                "loop_summary_unproven",
                "readonly_contract_mismatch",
                "readonly_contract_type_mismatch",
                "readonly_contract_missing_loop",
                "readonly_contract_effects_unproven",
                "readonly_contract_result_width_mismatch",
                "readonly_contract_term_sequence_mismatch",
            }
        )
    if isinstance(normalized, tuple):
        if not normalized:
            return True
        return any(cls._proof_target_contains_weak_value(item) for item in normalized)
    return False

def _impl__proof_target_contains_diagnostic_value(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    if isinstance(normalized, str):
        text = normalized.strip()
        return (
            text == "<missing>"
            or text.startswith("missing_")
            or text.endswith("_unavailable")
            or text in {
                "missing_readonly_ref",
                "missing_method_b_summary",
                "exact_terms_unavailable",
                "loop_summary_shape_mismatch",
                "loop_summary_guard_mismatch",
                "loop_summary_unproven",
                "readonly_contract_mismatch",
                "readonly_contract_type_mismatch",
                "readonly_contract_missing_loop",
                "readonly_contract_effects_unproven",
                "readonly_contract_result_width_mismatch",
                "readonly_contract_term_sequence_mismatch",
            }
        )
    if isinstance(normalized, tuple):
        return any(cls._proof_target_contains_diagnostic_value(item) for item in normalized)
    return False

def _impl__proof_target_contains_missing_or_diagnostic(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    if normalized is None:
        return True
    if isinstance(normalized, str):
        text = normalized.strip()
        return (
            not text
            or text == "<missing>"
            or text.startswith("missing_")
            or text.endswith("_unavailable")
            or text in {
                "missing_readonly_ref",
                "missing_method_b_summary",
                "exact_terms_unavailable",
                "loop_summary_shape_mismatch",
                "loop_summary_guard_mismatch",
                "loop_summary_unproven",
                "readonly_contract_mismatch",
                "readonly_contract_type_mismatch",
                "readonly_contract_missing_loop",
                "readonly_contract_effects_unproven",
                "readonly_contract_result_width_mismatch",
                "readonly_contract_term_sequence_mismatch",
            }
        )
    if isinstance(normalized, tuple):
        return any(cls._proof_target_contains_missing_or_diagnostic(item) for item in normalized)
    return False

def _impl__proof_text_is_specific(cls, value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip()) and not cls._proof_target_contains_weak_value(value)

def _impl__proof_int_like(cls, value: Any) -> bool:
    if isinstance(value, bool):
        return False
    try:
        int(value)
    except (TypeError, ValueError):
        return False
    return True

def _impl__proof_nonnegative_int_like(cls, value: Any) -> bool:
    return cls._proof_int_like(value) and int(value) >= 0

def _impl__proof_positive_int_like(cls, value: Any) -> bool:
    return cls._proof_int_like(value) and int(value) > 0

def _impl__readonly_identity_proof_content_is_complete(
    cls,
    proof_content: Any,
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not isinstance(proof_content, Mapping):
        return False
    if not cls._evidence_bool(proof_content, "object_derived"):
        return False
    if cls._normalize_nested_tuple(proof_content.get("object_target_key")) != object_target_key:
        return False
    if cls._evidence_has_any_recursive(proof_content, cls._COMPLETED_PROOF_BLOCKER_FIELDS):
        return False
    if cls._normalize_nested_tuple(proof_content.get("left_side")) != object_target_key[2]:
        return False
    if cls._normalize_nested_tuple(proof_content.get("right_side")) != object_target_key[3]:
        return False
    if not (
        cls._evidence_text(proof_content, "object_storage_identity") == "matched"
        and cls._evidence_text(proof_content, "count_identity") == "matched"
        and cls._evidence_text(proof_content, "guard_implication") in {"proven", "vacuous"}
        and cls._evidence_text(proof_content, "finite_witness") == "checked"
    ):
        return False
    storage_relation = cls._readonly_identity_storage_relation_from_target(object_target_key)
    if storage_relation is None:
        return False
    if storage_relation[0] == "same_register_base_projection":
        if cls._normalize_nested_tuple(proof_content.get("storage_relation")) != storage_relation:
            return False
        return cls._readonly_projection_extension_proof_content_is_complete(
            proof_content.get("parameter_extension"),
            storage_relation,
        )
    return True

def _impl__readonly_projection_extension_proof_content_is_complete(
    cls,
    extension: Any,
    storage_relation: Tuple[Any, ...],
) -> bool:
    if not isinstance(extension, Mapping):
        return False
    if extension.get("object_derived") is not True or extension.get("status") != "proven":
        return False
    if extension.get("relation") != "same_register_base_projection_semantic_extension":
        return False
    if cls._normalize_nested_tuple(extension.get("projection_relation")) != storage_relation:
        return False
    if extension.get("wide_side") not in {"left", "right"} or extension.get("narrow_side") not in {"left", "right"}:
        return False
    if extension.get("wide_side") == extension.get("narrow_side"):
        return False
    if extension.get("signedness") not in {"signed", "unsigned"}:
        return False
    if extension.get("extension") not in {"sign_extend", "zero_extend"}:
        return False
    if (extension.get("signedness") == "signed") != (extension.get("extension") == "sign_extend"):
        return False
    try:
        narrow_bits = int(extension.get("narrow_bits"))
        wide_bits = int(extension.get("wide_bits"))
        parameter_index = int(extension.get("parameter_index"))
    except (TypeError, ValueError):
        return False
    if parameter_index < 0 or narrow_bits <= 0 or wide_bits <= narrow_bits:
        return False
    relation_spans = {
        item[0]: item
        for item in storage_relation
        if isinstance(item, tuple) and len(item) == 3 and item[0] in {"left_bits", "right_bits"}
    }
    left_span = relation_spans.get("left_bits")
    right_span = relation_spans.get("right_bits")
    if left_span is None or right_span is None:
        return False
    try:
        left_size = int(left_span[2])
        right_size = int(right_span[2])
    except (TypeError, ValueError):
        return False
    expected_wide_side = "left" if left_size > right_size else "right"
    expected_narrow_side = "right" if expected_wide_side == "left" else "left"
    return (
        extension.get("wide_side") == expected_wide_side
        and extension.get("narrow_side") == expected_narrow_side
        and max(left_size, right_size) == wide_bits
        and min(left_size, right_size) == narrow_bits
        and extension.get("proof_source")
        in {"param_semantic_hint", "declared_parameter_narrow_type_on_wide_storage"}
    )

def _impl__method_b_closure_proof_content_is_complete(
    cls,
    proof_content: Any,
    object_target_key: Tuple[Any, ...],
    *,
    proof_stage: str,
) -> bool:
    if not isinstance(proof_content, Mapping):
        return False
    if not cls._evidence_bool(proof_content, "object_derived"):
        return False
    if cls._normalize_nested_tuple(proof_content.get("object_target_key")) != object_target_key:
        return False
    if cls._evidence_has_any_recursive(proof_content, cls._COMPLETED_PROOF_BLOCKER_FIELDS):
        return False
    if proof_stage == "method_b_covering_case":
        if not all(
            cls._proof_status_value_is_complete(proof_content.get(field))
            for field in ("seed_compensation", "term_sequence", "pure_side_effect_profile")
        ):
            return False
        if cls._method_b_dual_summary_proof_content_matches_relation(
            proof_content,
            object_target_key,
            proof_stage=proof_stage,
        ):
            return True
        return cls._method_b_covering_proof_content_matches_relation(proof_content, object_target_key)
    if proof_stage == "method_b_guard_partition":
        if not all(
            cls._proof_status_value_is_complete(proof_content.get(field))
            for field in ("guard_partition", "partition_coverage_proof")
        ):
            return False
        if cls._method_b_dual_summary_proof_content_matches_relation(
            proof_content,
            object_target_key,
            proof_stage=proof_stage,
        ):
            return True
        return cls._method_b_guard_proof_content_matches_relation(proof_content, object_target_key)
    return False

def _impl__method_b_proof_sides_match_relation(
    cls,
    proof_content: Mapping[str, Any],
    relation_payload: Mapping[str, Any],
) -> bool:
    return (
        cls._evidence_text(proof_content, "exact_side") == relation_payload.get("exact_side")
        and cls._evidence_text(proof_content, "summary_side") == relation_payload.get("summary_side")
    )

def _impl__method_b_covering_proof_content_matches_relation(
    cls,
    proof_content: Mapping[str, Any],
    object_target_key: Tuple[Any, ...],
) -> bool:
    relation_payload = cls._method_b_one_sided_relation_payload(object_target_key)
    if relation_payload is None or not cls._method_b_proof_sides_match_relation(proof_content, relation_payload):
        return False
    if not (
        cls._proof_positive_int_like(proof_content.get("count_value"))
        and cls._proof_positive_int_like(proof_content.get("result_size"))
        and cls._proof_int_like(proof_content.get("constant_bias"))
    ):
        return False
    exact_terms = cls._normalize_nested_tuple(proof_content.get("exact_terms"))
    expected_terms = cls._normalize_nested_tuple(proof_content.get("expected_terms"))
    relation_terms = relation_payload.get("exact_terms")
    if exact_terms != relation_terms or expected_terms != relation_terms:
        return False
    if int(proof_content.get("constant_bias")) != relation_payload.get("exact_constant_bias"):
        return False
    return cls._evidence_text(proof_content, "covering_evidence") == "method_b_covering_materialized_terms"

def _impl__method_b_guard_proof_content_matches_relation(
    cls,
    proof_content: Mapping[str, Any],
    object_target_key: Tuple[Any, ...],
) -> bool:
    relation_payload = cls._method_b_one_sided_relation_payload(object_target_key)
    if relation_payload is None or not cls._method_b_proof_sides_match_relation(proof_content, relation_payload):
        return False
    count_values = cls._method_b_guard_count_values(proof_content)
    if not count_values:
        return False
    guard_evidence = cls._evidence_text(proof_content, "guard_evidence")
    return guard_evidence in {
        "reduction_count_implication",
        "reduction_count_membership_implication",
    }

def _impl__method_b_dual_summary_proof_content_matches_relation(
    cls,
    proof_content: Mapping[str, Any],
    object_target_key: Tuple[Any, ...],
    *,
    proof_stage: str,
) -> bool:
    relation_payload = cls._method_b_dual_summary_relation_payload(object_target_key)
    if relation_payload is None:
        return False
    if cls._evidence_text(proof_content, "relation_kind") != "dual_summary":
        return False
    left_summary = cls._normalize_nested_tuple(proof_content.get("left_summary"))
    right_summary = cls._normalize_nested_tuple(proof_content.get("right_summary"))
    if (
        left_summary != relation_payload["left_summary"]
        or right_summary != relation_payload["right_summary"]
    ):
        return False
    if cls._evidence_text(proof_content, "summary_value_equivalence") != "unsat":
        return False
    if cls._evidence_text(proof_content, "guard_coverage") != "proven":
        return False
    if proof_stage == "method_b_covering_case":
        return cls._evidence_text(proof_content, "solver_equality_proof") == "unsat"
    if proof_stage == "method_b_guard_partition":
        return cls._evidence_text(proof_content, "partition_coverage_proof") == "covered"
    return False

def _impl__proof_status_value_is_complete(cls, value: Any) -> bool:
    return str(value or "") in {"complete", "completed", "covered", "matched", "proven", "checked", "vacuous"}

def _impl__completed_proof_section_is_clean(cls, section: Any) -> bool:
    if isinstance(section, Mapping):
        status = str(section.get("status") or "")
        if status not in {"complete", "completed", "proven", "discharged", "replayed"}:
            return False
        if cls._evidence_has_any_recursive(section, cls._COMPLETED_PROOF_BLOCKER_FIELDS):
            return False
        return any(key not in {"status", "detail"} for key in section)
    if isinstance(section, Sequence) and not isinstance(section, (str, bytes, bytearray)):
        return bool(section) and all(cls._completed_proof_section_is_clean(item) for item in section)
    return False

"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.proof.strategies.base``."""

from __future__ import annotations

from typing import Any, Optional, Tuple
from scripts.function_tracer_pcode.proof.strategies.proof_gates._shared import (
    FunctionReturnAnalysis,
    Mapping,
)

def _impl__unsupported_call_effect_proof_content_is_complete(
    cls,
    proof_content: Mapping[str, Any],
    object_target_key: Tuple[Any, ...],
) -> bool:
    proof_rule = cls._evidence_text(proof_content, "proof_rule")
    if proof_rule == "self_recursive_no_store_effect_summary":
        call_effect_summary = proof_content.get("call_effect_summary")
        if not isinstance(call_effect_summary, Mapping):
            return False
        if call_effect_summary.get("unsupported_reason") != "callee_effect_summary_missing":
            return False
        if call_effect_summary.get("local_store_effect_count") != 0:
            return False
        if proof_content.get("local_store_effect_count") != 0:
            return False
        if proof_content.get("recursive_call_effect") != "no_memory_effects_by_induction":
            return False
        recurrence_validation = proof_content.get("recurrence_validation")
        if not isinstance(recurrence_validation, Mapping):
            return False
        if not all(
            isinstance(recurrence_validation.get(key), str)
            and recurrence_validation.get(key)
            for key in (
                "proposal_digest",
                "function_recurrence_binding_digest",
                "semantic_closure_digest",
            )
        ):
            return False
        artifact_id = recurrence_validation.get("validated_unary_artifact_id")
        if not (
            isinstance(artifact_id, (tuple, list))
            and tuple(artifact_id)
            == (
                "validated_recurrence_artifact_v1",
                recurrence_validation["semantic_closure_digest"],
            )
        ):
            return False
        return True
    if proof_rule in {"matched_unknown_indirect_no_store_call_effect", "matched_unsupported_call_parameter_exposure_no_store_call_effect"}:
        unsupported_reason_signature = cls._unsupported_call_effect_reason_signature(
            object_target_key[6] if len(object_target_key) >= 7 else None
        )

        peer_object_target_key = cls._normalize_nested_tuple(
            proof_content.get("peer_object_target_key")
        )
        if not (
            isinstance(peer_object_target_key, tuple)
            and len(peer_object_target_key) >= 7
            and peer_object_target_key[0] == "unsupported_call_effect"
            and cls._unsupported_call_effect_reason_signature(
                peer_object_target_key[6]
            )
            == unsupported_reason_signature
        ):
            return False

        call_effect_summary = proof_content.get("call_effect_summary")
        if not isinstance(call_effect_summary, Mapping):
            return False
        if cls._normalize_nested_tuple(
            call_effect_summary.get("peer_object_target_key")
        ) != peer_object_target_key:
            return False
        if cls._unsupported_call_effect_reason_signature(
            call_effect_summary.get("unsupported_reason")
        ) != unsupported_reason_signature:
            return False
        if call_effect_summary.get("local_store_effect_count") != 0:
            return False
        if call_effect_summary.get("matching_local_unsupported_call_site_count") != 1:
            return False
        if call_effect_summary.get("matching_peer_unsupported_call_site_count") != 1:
            return False
        if proof_rule == "matched_unknown_indirect_no_store_call_effect":
            surface = proof_content.get("call_effect_surface")
            if not cls._matched_unknown_indirect_call_effect_surface_is_complete(
                surface,
                object_target_key,
                peer_object_target_key,
            ):
                return False

        runtime_ref = proof_content.get("runtime_ref")
        callsite_storage = proof_content.get("callsite_storage")
        if not isinstance(runtime_ref, Mapping) or not isinstance(callsite_storage, Mapping):
            return False
        if not cls._completed_proof_section_is_clean(runtime_ref):
            return False
        if not cls._completed_proof_section_is_clean(callsite_storage):
            return False
        if cls._normalize_nested_tuple(runtime_ref.get("peer_runtime_ref")) != peer_object_target_key[3]:
            return False
        if cls._normalize_nested_tuple(callsite_storage.get("peer_callsite_storage")) != peer_object_target_key[4]:
            return False

        target_expression_key = cls._cross_binary_call_effect_component_key(
            cls._unsupported_call_effect_target_expression_key(object_target_key)
        )
        peer_target_expression_key = cls._cross_binary_call_effect_component_key(
            cls._unsupported_call_effect_target_expression_key(peer_object_target_key)
        )
        if not (
            cls._call_effect_target_expression_key_is_present(target_expression_key)
            and cls._call_effect_target_expression_key_is_present(peer_target_expression_key)
        ):
            return False

        argument_keys = cls._cross_binary_call_effect_component_key(
            cls._unsupported_call_effect_argument_keys(object_target_key)
        )
        peer_argument_keys = cls._cross_binary_call_effect_component_key(
            cls._unsupported_call_effect_argument_keys(peer_object_target_key)
        )
        if cls._unsupported_call_effect_requires_exact_target_expression_match(
            object_target_key,
            peer_object_target_key,
        ) and target_expression_key != peer_target_expression_key:
            return False
        if argument_keys != peer_argument_keys:
            return False

        expected_policy = cls._unsupported_call_effect_compatibility_policy_evidence(
            object_target_key,
            peer_object_target_key,
        )
        if not cls._unsupported_call_effect_compatibility_policy_is_complete(expected_policy):
            return False
        provided_policy = proof_content.get("compatibility_policy")
        if not cls._unsupported_call_effect_compatibility_policy_is_complete(provided_policy):
            return False
        for key in (
            "reason_signature",
            "peer_reason_signature",
            "left_callee_identity_category",
            "right_callee_identity_category",
            "left_target_expression_key",
            "right_target_expression_key",
            "left_argument_keys",
            "right_argument_keys",
            "left_path_guard_key",
            "right_path_guard_key",
        ):
            if cls._normalize_nested_tuple(provided_policy.get(key)) != cls._normalize_nested_tuple(
                expected_policy.get(key)
            ):
                return False

        if cls._normalize_nested_tuple(runtime_ref.get("matched_target_expression_key")) != target_expression_key:
            return False
        if cls._normalize_nested_tuple(callsite_storage.get("matched_argument_keys")) != argument_keys:
            return False
        return True
    return False

def _impl__matched_unknown_indirect_call_effect_surface_is_complete(
    cls,
    surface: Any,
    object_target_key: Tuple[Any, ...],
    peer_object_target_key: Tuple[Any, ...],
) -> bool:
    if not isinstance(surface, Mapping):
        return False
    if cls._evidence_text(surface, "status") not in {"complete", "completed", "proven"}:
        return False
    if cls._evidence_text(surface, "guard_equivalence_mode") != "path_guard_equivalence":
        return False
    local_guard = cls._normalize_nested_tuple(surface.get("local_callsite_path_guard_key"))
    peer_guard = cls._normalize_nested_tuple(surface.get("peer_callsite_path_guard_key"))
    if not isinstance(local_guard, tuple) or not isinstance(peer_guard, tuple):
        return False
    if local_guard != cls._unsupported_call_effect_path_condition_key(object_target_key):
        return False
    if peer_guard != cls._unsupported_call_effect_path_condition_key(peer_object_target_key):
        return False
    if cls._cross_binary_call_effect_component_key(local_guard) != cls._cross_binary_call_effect_component_key(peer_guard):
        return False
    occurrence = surface.get("call_occurrence")
    peer_occurrence = surface.get("peer_call_occurrence")
    if not isinstance(occurrence, Mapping) or not isinstance(peer_occurrence, Mapping):
        return False
    if cls._evidence_text(occurrence, "status") not in {"complete", "completed", "proven"}:
        return False
    if cls._evidence_text(peer_occurrence, "status") not in {"complete", "completed", "proven"}:
        return False
    if cls._normalize_nested_tuple(occurrence.get("effect_ordinal")) != cls._normalize_nested_tuple(object_target_key[5]):
        return False
    if cls._normalize_nested_tuple(peer_occurrence.get("effect_ordinal")) != cls._normalize_nested_tuple(peer_object_target_key[5]):
        return False
    if occurrence.get("occurrence_index") != peer_occurrence.get("occurrence_index"):
        return False
    write = surface.get("caller_observed_memory_write")
    if not isinstance(write, Mapping):
        return False
    if cls._evidence_text(write, "status") not in {"complete", "completed", "proven"}:
        return False
    if cls._evidence_text(write, "scope") != "whole_function_effect_summary":
        return False
    for key in (
        "local_store_effect_count",
        "peer_store_effect_count",
        "local_incomplete_reason_count",
        "peer_incomplete_reason_count",
    ):
        if write.get(key) != 0:
            return False
    local_output = surface.get("call_output_use")
    peer_output = surface.get("peer_call_output_use")
    if not cls._call_output_use_surface_is_complete(local_output, object_target_key):
        return False
    if not cls._call_output_use_surface_is_complete(peer_output, peer_object_target_key):
        return False
    return True

def _impl__call_output_use_surface_is_complete(
    cls,
    section: Any,
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not isinstance(section, Mapping):
        return False
    if cls._evidence_text(section, "status") not in {"complete", "completed", "proven"}:
        return False
    if cls._evidence_text(section, "classification") != "not_exposed_to_return_or_call_effect_surface":
        return False
    if cls._evidence_text(section, "checked_surface") != "return_values_return_guards_and_call_effect_inputs":
        return False
    expected_pcode_ref = cls._unsupported_call_effect_pcode_ref_key(object_target_key)
    return (
        expected_pcode_ref is not None
        and cls._normalize_nested_tuple(section.get("pcode_op_ref")) == expected_pcode_ref
    )

def _impl__deferred_call_proof_content_is_complete(
    cls,
    proof_content: Mapping[str, Any],
    object_target_key: Tuple[Any, ...],
) -> bool:
    if cls._evidence_text(proof_content, "proof_rule") != "matched_deferred_call_argument_evidence":
        return False
    peer_object_target_key = cls._normalize_nested_tuple(
        proof_content.get("peer_object_target_key")
    )
    if not (
        isinstance(peer_object_target_key, tuple)
        and len(peer_object_target_key) >= 9
        and peer_object_target_key[0] == "deferred_call"
        and peer_object_target_key[-1] != "complete"
    ):
        return False
    call_effect_summary = proof_content.get("call_effect_summary")
    if not isinstance(call_effect_summary, Mapping):
        return False
    if cls._normalize_nested_tuple(
        call_effect_summary.get("peer_object_target_key")
    ) != peer_object_target_key:
        return False
    if call_effect_summary.get("local_store_effect_count") != 0:
        return False
    if call_effect_summary.get("matching_local_deferred_call_count") != 1:
        return False
    if call_effect_summary.get("matching_peer_deferred_call_count") != 1:
        return False
    runtime_ref = proof_content.get("runtime_ref")
    callsite_storage = proof_content.get("callsite_storage")
    if not isinstance(runtime_ref, Mapping) or not isinstance(callsite_storage, Mapping):
        return False
    if not cls._completed_proof_section_is_clean(runtime_ref):
        return False
    if not cls._completed_proof_section_is_clean(callsite_storage):
        return False
    peer_refs = cls._expected_deferred_call_proof_content_refs(peer_object_target_key)
    if peer_refs is None:
        return False
    peer_runtime_ref, peer_callsite_storage = peer_refs
    if cls._normalize_nested_tuple(runtime_ref.get("peer_runtime_ref")) != peer_runtime_ref:
        return False
    if cls._normalize_nested_tuple(callsite_storage.get("peer_callsite_storage")) != peer_callsite_storage:
        return False
    target_expression_key = cls._cross_binary_call_effect_component_key(
        cls._deferred_call_target_expression_key(object_target_key)
    )
    peer_target_expression_key = cls._cross_binary_call_effect_component_key(
        cls._deferred_call_target_expression_key(peer_object_target_key)
    )
    if not (
        cls._call_effect_target_expression_key_is_present(target_expression_key)
        and cls._call_effect_target_expression_key_is_present(peer_target_expression_key)
    ):
        return False
    argument_keys = cls._cross_binary_call_effect_component_key(
        cls._deferred_call_argument_keys(object_target_key)
    )
    peer_argument_keys = cls._cross_binary_call_effect_component_key(
        cls._deferred_call_argument_keys(peer_object_target_key)
    )
    if not (
        cls._call_effect_argument_keys_are_present(argument_keys)
        and cls._call_effect_argument_keys_are_present(peer_argument_keys)
    ):
        return False
    if target_expression_key != peer_target_expression_key:
        return False
    if argument_keys != peer_argument_keys:
        return False
    if cls._normalize_nested_tuple(runtime_ref.get("matched_target_expression_key")) != target_expression_key:
        return False
    if cls._normalize_nested_tuple(callsite_storage.get("matched_argument_keys")) != argument_keys:
        return False
    return True

def _impl__readonly_side_effect_profile_is_specific(cls, value: Any) -> bool:
    profile = cls._normalize_nested_tuple(value)
    return (
        isinstance(profile, tuple)
        and len(profile) >= 2
        and profile[0] == "loop_side_effect_profile"
        and cls._proof_text_is_specific(profile[1])
        and not cls._proof_target_contains_missing_or_diagnostic(profile)
    )

def _impl__analysis_has_active_call_effect_proof_blockers(
    cls,
    analysis: FunctionReturnAnalysis,
) -> bool:
    decisive_reasons = getattr(analysis, "get_decisive_sat_unsafety_reasons", lambda: ())()
    recoverable_call_effect_kinds = {
        cls._blocking_reason_kind(reason)
        for reason in cls._CALL_EFFECT_PROOF_RECOVERABLE_UNSAFETY_REASONS
    }
    for reason in decisive_reasons:
        if cls._blocking_reason_kind(str(reason)) not in recoverable_call_effect_kinds:
            return True
    for note in getattr(analysis, "analysis_notes", ()) or ():
        if cls._blocking_reason_kind(str(note)) in {
            "return_case_coverage_gap",
            "return_case_coverage_inconclusive",
        }:
            return True
    return False

def _impl__call_effect_blocking_object_target_key(
    self,
    blocking_reason: str,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Optional[Tuple[Any, ...]]:
    label, reason_text = self._split_blocking_reason(blocking_reason)
    reason_kind = self._blocking_reason_kind(blocking_reason)
    reason_index = self._blocking_reason_index(reason_text)
    if reason_kind not in {
        "unsupported_call_effect_summary",
        "effect_summary_path_coverage_incomplete",
        "effect_call_argument_evidence",
        "effect_call_argument_evidence_incomplete",
        "effect_call_target_resolution_evidence",
        "bounded_call_refinement_argument_alignment_failed",
        "bounded_call_refinement_deferred_target_unresolved",
        "bounded_call_refinement_return_summary_unusable",
    }:
        return None
    analysis = analysis1 if label == "function1" else analysis2 if label == "function2" else None
    if analysis is None:
        return None
    all_deferred_call_keys = tuple(
        self._deferred_call_object_target_key(info, analysis=analysis, side_label=label)
        for info in getattr(analysis, "deferred_calls", {}).values()
        if info is not None
    )
    deferred_call_keys = tuple(
        self._deferred_call_object_target_key(info, analysis=analysis, side_label=label)
        for info in getattr(analysis, "deferred_calls", {}).values()
        if self._deferred_call_is_blocking(info)
    )
    effect_summary = getattr(analysis, "effect_summary", None)
    evidence_keys = ()
    unsupported_call_site_keys = ()
    target_resolution_keys = ()
    if effect_summary is not None:
        evidence_keys = tuple(
            self._call_argument_evidence_object_key(
                evidence,
                analysis=analysis,
                side_label=label,
            )
            for evidence in getattr(effect_summary, "call_argument_evidence", {}).values()
            if evidence is not None
        )
        unsupported_call_site_keys = tuple(
            self._unsupported_call_effect_object_key(
                site,
                analysis=analysis,
                side_label=label,
            )
            for site in getattr(effect_summary, "unsupported_call_sites", ()) or ()
            if site is not None
        )
        target_resolution_keys = tuple(
            self._call_target_resolution_evidence_object_key(
                evidence,
                analysis=analysis,
                side_label=label,
            )
            for evidence in getattr(effect_summary, "call_target_resolution_evidence", ()) or ()
            if evidence is not None
        )
    selected_deferred_keys: Tuple[Any, ...] = ()
    selected_evidence_keys: Tuple[Any, ...] = ()
    selected_unsupported_keys: Tuple[Any, ...] = ()
    selected_target_resolution_keys: Tuple[Any, ...] = ()

    if reason_kind == "unsupported_call_effect_summary":
        selected_unsupported_keys = unsupported_call_site_keys
        if len(selected_unsupported_keys) == 1:
            return selected_unsupported_keys[0]
    elif reason_kind in {"effect_call_argument_evidence", "effect_call_argument_evidence_incomplete"}:
        selected_evidence_keys = evidence_keys
        if reason_index is not None and 0 <= reason_index < len(selected_evidence_keys):
            return selected_evidence_keys[reason_index]
        if len(selected_evidence_keys) == 1:
            return selected_evidence_keys[0]
        if not selected_evidence_keys:
            selected_deferred_keys = deferred_call_keys
            if len(selected_deferred_keys) == 1:
                return selected_deferred_keys[0]
    elif reason_kind == "effect_call_target_resolution_evidence":
        selected_target_resolution_keys = target_resolution_keys
        if (
            reason_index is not None
            and 0 <= reason_index < len(selected_target_resolution_keys)
        ):
            return selected_target_resolution_keys[reason_index]
        if len(selected_target_resolution_keys) == 1:
            return selected_target_resolution_keys[0]
    elif reason_kind in {
        "bounded_call_refinement_argument_alignment_failed",
        "bounded_call_refinement_deferred_target_unresolved",
        "bounded_call_refinement_return_summary_unusable",
    }:
        selected_deferred_keys = deferred_call_keys or all_deferred_call_keys
        if len(selected_deferred_keys) == 1:
            return selected_deferred_keys[0]
        selected_unsupported_keys = unsupported_call_site_keys
        if len(selected_unsupported_keys) == 1:
            return selected_unsupported_keys[0]
        selected_target_resolution_keys = target_resolution_keys
        if len(selected_target_resolution_keys) == 1:
            return selected_target_resolution_keys[0]
    elif reason_kind == "effect_summary_path_coverage_incomplete":
        selected_evidence_keys = evidence_keys
        selected_unsupported_keys = unsupported_call_site_keys

    return (
        "call_effect_blocker",
        label,
        self._analysis_entry_key(analysis),
        reason_kind,
        reason_text,
        selected_deferred_keys,
        selected_evidence_keys,
        selected_unsupported_keys,
        selected_target_resolution_keys,
    )

def _impl__deferred_call_is_blocking(info: Any) -> bool:
    status = getattr(info, "call_argument_recovery_status", None)
    return status != "complete"

def _impl__deferred_call_object_target_key(
    self,
    info: Any,
    *,
    analysis: Optional[FunctionReturnAnalysis] = None,
    side_label: Optional[str] = None,
) -> Tuple[Any, ...]:
    deferred_ref = getattr(info, "deferred_call_ref", None)
    target_ref = getattr(info, "target_ref", None)
    pcode_op_ref = getattr(deferred_ref, "pcode_op_ref", None)
    target_expr_key = self._typed_target_expression_key(
        getattr(info, "call_target_expr", None)
    )
    argument_keys = tuple(
        (
            "argument",
            index,
            self._expression_runtime_object_key(argument),
        )
        for index, argument in enumerate(getattr(info, "arguments", ()) or ())
    )
    target = (
        "deferred_call",
        side_label,
        self._analysis_entry_key(analysis) if analysis is not None else None,
        self._deferred_call_site_object_key(
            deferred_ref,
            analysis=analysis,
            target_ref=target_ref,
            target_expr_key=target_expr_key,
            argument_keys=argument_keys,
        ),
        self._stable_key_or_none(pcode_op_ref),
        self._call_target_key_for_analysis(target_ref, analysis),
        target_expr_key,
        argument_keys,
        getattr(info, "call_argument_recovery_status", None),
    )
    if analysis is not None:
        return self._artifact_stable_key_for_analysis(target, analysis)
    return target

def _impl__deferred_call_site_object_key(
    self,
    deferred_ref: Any,
    *,
    analysis: Optional[FunctionReturnAnalysis],
    target_ref: Any,
    target_expr_key: Optional[Tuple[Any, ...]],
    argument_keys: Tuple[Any, ...],
) -> Tuple[Any, ...]:
    pcode_op_ref = getattr(deferred_ref, "pcode_op_ref", None)
    caller_entry_offset = getattr(deferred_ref, "caller_entry_offset", None)
    caller_function_key: Any = None
    binary_id = getattr(analysis, "binary_id", None) if analysis is not None else None
    if binary_id is not None and caller_entry_offset is not None:
        try:
            caller_function_key = ("function_ref", ("function", str(binary_id), int(caller_entry_offset)))
        except (TypeError, ValueError):
            caller_function_key = None
    if caller_function_key is None and analysis is not None:
        caller_function_key = self._analysis_entry_key(analysis)
    return (
        "deferred_call_site",
        caller_function_key,
        self._stable_key_or_none(pcode_op_ref),
        self._call_target_key_for_analysis(target_ref, analysis),
        target_expr_key,
        tuple(("argument", key[1]) for key in argument_keys if isinstance(key, tuple) and len(key) >= 2),
        getattr(deferred_ref, "sequence", None),
    )

def _impl__call_argument_evidence_object_key(
    self,
    evidence: Any,
    *,
    analysis: Optional[FunctionReturnAnalysis] = None,
    side_label: Optional[str] = None,
) -> Tuple[Any, ...]:
    target = (
        "call_argument_evidence",
        side_label,
        self._analysis_entry_key(analysis) if analysis is not None else None,
        self._stable_key_or_none(evidence),
        self._call_target_key_for_analysis(getattr(evidence, "target_ref", None), analysis),
        tuple(
            (
                "argument",
                index,
                self._expression_runtime_object_key(argument),
            )
            for index, argument in enumerate(getattr(evidence, "arguments", ()) or ())
        ),
        bool(getattr(evidence, "coverage_complete", False)),
        getattr(evidence, "recovery_status", None),
    )
    if analysis is not None:
        return self._artifact_stable_key_for_analysis(target, analysis)
    return target

def _impl__call_target_resolution_evidence_object_key(
    self,
    evidence: Any,
    *,
    analysis: Optional[FunctionReturnAnalysis] = None,
    side_label: Optional[str] = None,
) -> Tuple[Any, ...]:
    pcode_key = self._stable_key_or_none(getattr(evidence, "pcode_op_ref", None))
    target_key = self._call_target_key_for_analysis(getattr(evidence, "target_ref", None), analysis)
    target_expr_key = self._typed_target_expression_key(getattr(evidence, "target_expr", None))
    callee_identity_key = self._call_effect_callee_identity_key(
        target_key,
        target_expr_key,
        analysis,
    )
    target = (
        "call_target_resolution_evidence",
        side_label,
        self._analysis_entry_key(analysis) if analysis is not None else None,
        (
            "runtime_ref",
            "call_target_resolution",
            ("pcode_op_ref", pcode_key),
            ("callee_identity", callee_identity_key),
            ("typed_target_expression", target_expr_key),
        ),
        (
            "callsite_storage",
            ("pcode_op_ref", pcode_key),
            ("callee_identity", callee_identity_key),
            ("target_expression", target_expr_key),
        ),
        ("resolution_kind", getattr(evidence, "resolution_kind", None)),
        ("path_conditions", tuple(getattr(evidence, "path_condition_keys", ()) or ())),
        ("target_conditions", tuple(getattr(evidence, "target_condition_keys", ()) or ())),
        ("effect_ordinal", int(getattr(evidence, "order_key", 0) or 0)),
    )
    if analysis is not None:
        return self._artifact_stable_key_for_analysis(target, analysis)
    return target

def _impl__unsupported_call_effect_object_key(
    self,
    site: Any,
    *,
    analysis: Optional[FunctionReturnAnalysis] = None,
    side_label: Optional[str] = None,
) -> Tuple[Any, ...]:
    pcode_key = self._stable_key_or_none(getattr(site, "pcode_op_ref", None))
    target_key = self._call_target_key_for_analysis(getattr(site, "target_ref", None), analysis)
    target_expr_key = self._typed_target_expression_key(getattr(site, "target_expr", None))
    argument_keys = tuple(
        (
            "argument",
            index,
            self._expression_runtime_object_key(argument),
        )
        for index, argument in enumerate(getattr(site, "arguments", ()) or ())
    )
    path_condition_keys = tuple(
        self._return_condition_object_key(condition)
        for condition in (getattr(site, "path_conditions", ()) or ())
    )
    callee_identity_key = self._call_effect_callee_identity_key(
        target_key,
        target_expr_key,
        analysis,
    )
    effect_ordinal = int(getattr(site, "order_key", 0) or 0)
    target = (
        "unsupported_call_effect",
        side_label,
        self._analysis_entry_key(analysis) if analysis is not None else None,
        (
            "runtime_ref",
            "unsupported_call_effect",
            ("pcode_op_ref", pcode_key),
            ("callee_identity", callee_identity_key),
            ("typed_target_expression", target_expr_key),
            ("argument_keys", argument_keys),
            ("path_conditions", path_condition_keys),
        ),
        (
            "callsite_storage",
            ("pcode_op_ref", pcode_key),
            ("callee_identity", callee_identity_key),
            ("target_expression", target_expr_key),
            ("argument_keys", argument_keys),
            ("path_conditions", path_condition_keys),
        ),
        ("effect_ordinal", effect_ordinal),
        getattr(site, "reason", None),
    )
    if analysis is not None:
        return self._artifact_stable_key_for_analysis(target, analysis)
    return target

def _impl__call_effect_callee_identity_key(
    target_key: Any,
    target_expr_key: Any,
    analysis: Optional[FunctionReturnAnalysis],
) -> Any:
    if target_key is not None:
        if isinstance(target_key, tuple) and target_key and target_key[0] == "unknown":
            binary_id = target_key[1] if len(target_key) >= 2 else None
            if binary_id is None and analysis is not None:
                binary_id = getattr(analysis, "binary_id", None)
            return (
                "unknown",
                str(binary_id) if binary_id is not None else None,
                ("target_expression", target_expr_key),
            )
        return target_key
    binary_id = getattr(analysis, "binary_id", None) if analysis is not None else None
    return (
        "unknown",
        str(binary_id) if binary_id is not None else None,
        ("target_expression", target_expr_key),
    )

def _impl__call_target_key_for_analysis(
    cls,
    target_ref: Any,
    analysis: Optional[FunctionReturnAnalysis],
):
    key = cls._stable_key_or_none(target_ref)
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

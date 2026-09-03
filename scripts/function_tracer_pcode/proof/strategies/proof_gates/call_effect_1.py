"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.proof.strategies.base``."""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Tuple
from scripts.function_tracer_pcode.proof.strategies.proof_gates._shared import (
    FunctionReturnAnalysis,
    Mapping,
    UnknownReasonRecord,
    UnknownRecoveryProofKind,
    build_proof_obligation_id,
)

def _impl__record_completed_call_effect_summary_proof_if_safe(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> None:
    if not self.enable_completed_recovery_proofs:
        return
    from scripts.function_tracer_pcode.authority.domains.call_effect import CALL_EFFECT_REASON_SPECS

    if reason_record.reason_id not in CALL_EFFECT_REASON_SPECS:
        return
    if reason_record.recovery_proof_kind != UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value:
        return
    proof_obligation_id = self._normalize_nested_tuple(reason_record.proof_obligation_id)
    object_target_key = self._normalize_nested_tuple(reason_record.object_target_key)
    if proof_obligation_id is None or not isinstance(object_target_key, tuple):
        return

    analysis = self._analysis_for_call_effect_object_target(
        object_target_key,
        analysis1,
        analysis2,
    )
    if analysis is None:
        return
    proof_content = (
        self._self_recursive_no_store_call_effect_proof_content(
            object_target_key,
            analysis,
        )
        or self._call_effect_blocker_proof_content(
            object_target_key,
            analysis,
            analysis1,
            analysis2,
        )
        or self._matched_unknown_indirect_call_effect_proof_content(
            object_target_key,
            analysis,
            analysis1,
            analysis2,
        )
        or self._matched_unsupported_call_effect_no_store_parameter_exposure_proof_content(
            object_target_key,
            analysis,
            analysis1,
            analysis2,
            reason="callee_unsupported_call_may_expose_parameter_memory",
        )
        or self._call_argument_evidence_phase15_proof_content(
            object_target_key,
            analysis,
        )
        or self._matched_deferred_call_argument_proof_content(
            object_target_key,
            analysis,
            analysis1,
            analysis2,
        )
    )
    if proof_content is None:
        return

    records: List[Dict[str, Any]] = [
        dict(item)
        for item in getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
        if isinstance(item, Mapping)
    ]
    existing_ids = {
        self._normalize_nested_tuple(item.get("proof_obligation_id"))
        for item in records
    }
    if proof_obligation_id in existing_ids:
        return

    proof_rule = str(proof_content.get("proof_rule") or "")
    proof_source = (
        "self_recursive_no_store_call_effect_summary"
        if proof_rule == "self_recursive_no_store_effect_summary"
        else "call_argument_evidence_phase15_complete"
        if proof_rule == "call_argument_evidence_phase15_complete"
        else "call_argument_evidence_complete"
        if proof_rule == "call_argument_evidence_complete"
        else "matched_deferred_call_argument_evidence"
        if proof_rule == "matched_deferred_call_argument_evidence"
        else "matched_unknown_indirect_no_store_call_effect"
        if proof_rule == "matched_unknown_indirect_no_store_call_effect"
        else "matched_unsupported_call_parameter_exposure_no_store_call_effect"
        if proof_rule == "matched_unsupported_call_parameter_exposure_no_store_call_effect"
        else "call_effect_summary_proof"
    )
    records.append(
        {
            "object_derived": True,
            "status": "complete",
            "reason_id": reason_record.reason_id,
            "recovery_proof_kind": UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value,
            "proof_stage": "object_evidence_collected",
            "evidence_kind": "call_effect_summary",
            "object_target_key": object_target_key,
            "proof_obligation_id": proof_obligation_id,
            "proof_source": proof_source,
            "proof_content": proof_content,
        }
    )
    analysis.completed_recovery_proof_evidence = tuple(records)

def _impl__iter_call_effect_blocker_candidates(
    cls,
    object_target_key: Tuple[Any, ...],
) -> Tuple[Tuple[Any, ...], ...]:
    if not isinstance(object_target_key, tuple) or len(object_target_key) < 9:
        return ()

    candidate_keys: List[Tuple[Any, ...]] = []
    for group in object_target_key[5:9]:
        if not isinstance(group, tuple) or not group:
            continue
        for candidate in group:
            candidate_tuple = cls._normalize_nested_tuple(candidate)
            if isinstance(candidate_tuple, tuple):
                candidate_keys.append(candidate_tuple)
    return tuple(candidate_keys)

def _impl__select_call_effect_blocker_candidate(
    cls,
    object_target_key: Tuple[Any, ...],
) -> Optional[Tuple[Any, ...]]:
    candidates = cls._iter_call_effect_blocker_candidates(object_target_key)
    if not candidates:
        return None
    return max(candidates, key=cls._call_effect_blocker_candidate_score)

def _impl__call_effect_blocker_proof_content(
    self,
    object_target_key: Tuple[Any, ...],
    analysis: FunctionReturnAnalysis,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Optional[Dict[str, Any]]:
    if not isinstance(object_target_key, tuple) or object_target_key[0] != "call_effect_blocker":
        return None
    best_candidate: Optional[Tuple[Tuple[Any, ...], Dict[str, Any]]] = None
    for candidate in self._iter_call_effect_blocker_candidates(object_target_key):
        if not candidate:
            continue
        candidate = self._normalize_nested_tuple(candidate)
        if not isinstance(candidate, tuple):
            continue
        candidate_kind = self._normalize_nested_tuple(candidate[0])
        if candidate_kind is None:
            continue

        candidate_content: Optional[Dict[str, Any]] = None
        if candidate_kind == "call_argument_evidence":
            candidate_content = self._call_argument_evidence_phase15_proof_content(
                candidate,
                analysis,
            )
        elif candidate_kind == "unsupported_call_effect":
            candidate_content = (
                self._self_recursive_no_store_call_effect_proof_content(
                    candidate,
                    analysis,
                )
                or self._matched_unknown_indirect_call_effect_proof_content(
                    candidate,
                    analysis,
                    analysis1,
                    analysis2,
                )
                or self._matched_unsupported_call_effect_no_store_parameter_exposure_proof_content(
                    candidate,
                    analysis,
                    analysis1,
                    analysis2,
                    reason="callee_unsupported_call_may_expose_parameter_memory",
                )
            )
        elif candidate_kind == "deferred_call":
            candidate_content = self._matched_deferred_call_argument_proof_content(
                candidate,
                analysis,
                analysis1,
                analysis2,
            )
        if candidate_content is None:
            continue

        expected_refs = self._expected_call_effect_proof_content_refs(
            object_target_key,
            candidate=candidate,
        )
        if expected_refs is None:
            continue

        runtime_ref, callsite_storage = expected_refs
        candidate_content_dict = {
            "object_derived": True,
            "status": "complete",
            "proof_rule": self._evidence_text(candidate_content, "proof_rule")
            or "call_effect_blocker_resolution",
            "object_target_key": object_target_key,
            "selected_candidate_key": self._normalize_nested_tuple(candidate),
            "selected_candidate_kind": candidate_kind,
            "selected_candidate_proof_content": candidate_content,
            "peer_object_target_key": self._evidence_get(
                candidate_content,
                "peer_object_target_key",
            ),
            "call_effect_summary": {
                "object_derived": True,
                "status": "complete",
                "summary_source": ("effect_summary", "call_effect_blocker"),
                "evidence_kind": "call_effect_summary",
                "object_target_key": object_target_key,
                "coverage_complete": True,
                "recovery_status": "complete",
            },
            "runtime_ref": {
                "status": "complete",
                "runtime_ref": runtime_ref,
            },
            "callsite_storage": {
                "status": "complete",
                "callsite_storage": callsite_storage,
            },
        }
        score = self._call_effect_blocker_candidate_score(candidate)
        if best_candidate is None or score > best_candidate[0]:
            best_candidate = (score, candidate_content_dict)
    return None if best_candidate is None else best_candidate[1]

def _impl__call_effect_blocker_candidate_score(cls, candidate: Any) -> Tuple[Any, ...]:
    normalized = cls._normalize_nested_tuple(candidate)
    if not isinstance(normalized, tuple) or not normalized:
        return (0, 0, 0, 0, ())
    candidate_kind = normalized[0]
    priority = cls._call_effect_blocker_candidate_priority(candidate_kind)
    if candidate_kind == "call_argument_evidence":
        coverage_complete = bool(normalized[6]) if len(normalized) >= 7 else False
        recovery_status = str(normalized[7]) if len(normalized) >= 8 else ""
        return (
            priority,
            3,
            1 if coverage_complete else 0,
            1 if recovery_status == "complete" else 0,
            cls._call_effect_blocker_semantic_tie_break(normalized),
        )
    if candidate_kind == "unsupported_call_effect":
        return (
            priority,
            2,
            1,
            1,
            cls._call_effect_blocker_semantic_tie_break(normalized),
        )
    if candidate_kind == "deferred_call":
        recovery_status = str(normalized[-1]) if normalized else ""
        return (
            priority,
            1,
            1 if recovery_status == "complete" else 0,
            0,
            cls._call_effect_blocker_semantic_tie_break(normalized),
        )
    return (
        priority,
        1,
        1,
        0,
        cls._call_effect_blocker_semantic_tie_break(normalized),
    )

def _impl__call_effect_blocker_semantic_tie_break(cls, candidate: Tuple[Any, ...]) -> Tuple[Any, ...]:
    candidate_kind = candidate[0] if candidate else None
    if candidate_kind == "call_argument_evidence":
        return (
            "call_argument_evidence",
            cls._call_effect_blocker_sort_token(candidate[3] if len(candidate) > 3 else None),
            cls._call_effect_blocker_sort_token(candidate[4] if len(candidate) > 4 else None),
            cls._call_effect_blocker_sort_token(candidate[5] if len(candidate) > 5 else None),
        )
    if candidate_kind == "unsupported_call_effect":
        return (
            "unsupported_call_effect",
            cls._unsupported_call_effect_reason_signature(candidate[6] if len(candidate) > 6 else None),
            cls._call_effect_blocker_sort_token(
                cls._unsupported_call_effect_argument_keys(candidate)
            ),
            cls._call_effect_blocker_sort_token(
                cls._unsupported_call_effect_target_expression_key(candidate)
            ),
        )
    if candidate_kind == "deferred_call":
        return (
            "deferred_call",
            cls._call_effect_blocker_sort_token(
                cls._deferred_call_argument_keys(candidate)
            ),
            cls._call_effect_blocker_sort_token(
                cls._deferred_call_target_expression_key(candidate)
            ),
            str(candidate[-1]) if candidate else "",
        )
    return (str(candidate_kind), cls._call_effect_blocker_sort_token(candidate))

def _impl__call_effect_blocker_sort_token(cls, value: Any) -> Tuple[Any, ...]:
    if value is None:
        return (0, "")
    if isinstance(value, bool):
        return (1, int(value))
    if isinstance(value, int):
        return (2, int(value))
    if isinstance(value, str):
        return (3, value)
    if isinstance(value, tuple):
        return (4, tuple(cls._call_effect_blocker_sort_token(item) for item in value))
    return (5, str(value))

def _impl__call_effect_blocker_candidate_priority(cls, candidate_kind: Any) -> int:
    if candidate_kind == "call_argument_evidence":
        return 3
    if candidate_kind == "unsupported_call_effect":
        return 2
    if candidate_kind == "deferred_call":
        return 1
    return 0

def _impl__analysis_for_call_effect_object_target(
    object_target_key: Tuple[Any, ...],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Optional[FunctionReturnAnalysis]:
    if len(object_target_key) < 2:
        return None
    if object_target_key[0] not in {
        "unsupported_call_effect",
        "call_argument_evidence",
        "call_target_resolution_evidence",
        "deferred_call",
        "call_effect_blocker",
    }:
        return None
    side_label = object_target_key[1]
    if side_label == "function1":
        return analysis1
    if side_label == "function2":
        return analysis2
    return None

def _impl__call_argument_evidence_phase15_proof_content(
    self,
    object_target_key: Tuple[Any, ...],
    analysis: FunctionReturnAnalysis,
) -> Optional[Dict[str, Any]]:
    if len(object_target_key) < 8 or object_target_key[0] != "call_argument_evidence":
        return None
    if getattr(analysis, "deferred_calls", None):
        return None
    side_label = object_target_key[1]
    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is None:
        return None
    if getattr(effect_summary, "effects", None):
        return None
    if getattr(effect_summary, "has_unsupported_call", False):
        return None
    if getattr(effect_summary, "incomplete_reasons", None):
        return None
    matching_evidence = None
    for evidence in getattr(effect_summary, "call_argument_evidence", {}).values():
        if evidence is None or not getattr(evidence, "is_usable", lambda: False)():
            continue
        if not bool(getattr(evidence, "coverage_complete", False)):
            continue
        if str(getattr(evidence, "recovery_status", "")) != "complete":
            continue
        evidence_key = self._normalize_nested_tuple(
            self._call_argument_evidence_object_key(
                evidence,
                analysis=analysis,
                side_label=side_label,
            )
        )
        if evidence_key == object_target_key:
            matching_evidence = evidence
            break
    if matching_evidence is None:
        return None
    bounded_refinement = self._bounded_call_refinement_evidence_for_call_argument_target(
        object_target_key,
        analysis,
        matching_evidence,
    )
    if bounded_refinement is None:
        return None
    argument_keys = object_target_key[5]
    expected_refs = self._expected_call_effect_proof_content_refs(object_target_key)
    if expected_refs is None:
        return None
    runtime_ref, callsite_storage = expected_refs
    return {
        "object_derived": True,
        "status": "complete",
        "proof_rule": "call_argument_evidence_phase15_complete",
        "object_target_key": object_target_key,
        "call_effect_summary": {
            "object_derived": True,
            "status": "complete",
            "summary_source": ("effect_summary", "call_argument_evidence"),
            "evidence_kind": "call_effect_summary",
            "object_target_key": object_target_key,
            "coverage_complete": True,
            "recovery_status": "complete",
            "argument_count": len(argument_keys),
        },
        "runtime_ref": {
            "status": "complete",
            "runtime_ref": runtime_ref,
        },
        "callsite_storage": {
            "status": "complete",
            "callsite_storage": callsite_storage,
        },
        "callee_summary_completion": {
            "object_derived": True,
            "status": "complete",
            "object_target_key": object_target_key,
            "callee_identity": object_target_key[4],
            "return_coverage_status": "complete",
            "effect_summary_status": "complete",
            "memory_policy_status": "complete",
            "unsupported_call_policy_status": "complete",
            "bounded_refinement_evidence_ref": bounded_refinement["object_target_key"],
            "callee_return_partition_key": bounded_refinement["callee_return_partition_key"],
        },
        "callee_precondition": {
            "object_derived": True,
            "status": "complete",
            "object_target_key": object_target_key,
            "caller_guard_implies_callee_precondition": True,
            "abi_coercion": {
                "object_derived": True,
                "status": "complete",
                "argument_widths": tuple(
                    (
                        "argument",
                        item[1],
                        self._expression_bit_width_from_object_key(item[2]),
                    )
                    for item in argument_keys
                    if isinstance(item, tuple) and len(item) >= 3
                ),
                "sign_zero_extension": "object_value_provenance_preserved",
                "abi_narrow_wide_coercion": "bounded_call_refinement_checked",
                "callee_parameter_interpretation": object_target_key[4],
            },
        },
        "argument_value_provenance": {
            "object_derived": True,
            "status": "complete",
            "object_target_key": object_target_key,
            "argument_keys": argument_keys,
            "value_provenance_equivalent": True,
            "sources": tuple(getattr(matching_evidence, "sources", ()) or ()),
            "path_condition_keys": tuple(
                self._conditions_runtime_object_key(conditions)
                for conditions in getattr(matching_evidence, "path_conditions", ()) or ()
            ),
        },
        "proof_dependency_graph": {
            "object_derived": True,
            "status": "complete",
            "object_target_key": object_target_key,
            "cycle_policy": "acyclic",
            "dependencies": (
                bounded_refinement["object_target_key"],
                "call_argument_evidence_usable",
                "callee_return_summary_expanded_into_caller",
            ),
        },
        "bounded_refinement": bounded_refinement,
    }

def _impl__bounded_call_refinement_evidence_for_call_argument_target(
    self,
    object_target_key: Tuple[Any, ...],
    analysis: FunctionReturnAnalysis,
    matching_evidence: Any,
) -> Optional[Dict[str, Any]]:
    expected_pcode_key = self._normalize_nested_tuple(
        self._stable_key_or_none(getattr(matching_evidence, "pcode_op_ref", None))
    )
    expected_callee_key = self._normalize_nested_tuple(
        self._call_target_key_for_analysis(getattr(matching_evidence, "target_ref", None), analysis)
    )
    if expected_pcode_key is None or expected_callee_key is None:
        return None
    if self._normalize_nested_tuple(object_target_key[3]) != expected_pcode_key:
        return None
    if self._normalize_nested_tuple(object_target_key[4]) != expected_callee_key:
        return None
    expected_argument_count = len(tuple(getattr(matching_evidence, "arguments", ()) or ()))
    records = tuple(getattr(analysis, "completed_recovery_proof_evidence", ()) or ())
    for record in records:
        if not isinstance(record, Mapping):
            continue
        if self._evidence_text(record, "evidence_kind") != "bounded_call_refinement_expansion":
            continue
        if self._evidence_text(record, "status") not in {"complete", "completed", "proven"}:
            continue
        if not self._evidence_bool(record, "object_derived"):
            continue
        content = record.get("proof_content")
        if not isinstance(content, Mapping):
            continue
        if not self._bounded_call_refinement_content_is_complete(
            content,
            expected_pcode_key=expected_pcode_key,
            expected_callee_key=expected_callee_key,
            expected_argument_count=expected_argument_count,
        ):
            continue
        evidence_ref = self._normalize_nested_tuple(content.get("object_target_key"))
        return {
            "object_derived": True,
            "status": "complete",
            "evidence_kind": "bounded_call_refinement_expansion",
            "object_target_key": evidence_ref,
            "call_argument_object_target_key": object_target_key,
            "callsite_pcode_key": expected_pcode_key,
            "callee_identity": expected_callee_key,
            "callee_return_partition_key": self._normalize_nested_tuple(
                content.get("callee_return_partition_key")
            ),
            "callee_summary_requires_completed_proof": bool(
                content.get("callee_summary_requires_completed_proof")
            ),
            "callee_completed_proof_ids": self._normalize_nested_tuple(
                content.get("callee_completed_proof_ids")
            ),
            "callee_completed_proof_evidence_ids": self._normalize_nested_tuple(
                content.get("callee_completed_proof_evidence_ids")
            ),
            "result_count": int(content.get("result_count") or 0),
            "dependency_cycle": bool(content.get("dependency_cycle")),
            "truncated": bool(content.get("truncated")),
        }
    return None

def _impl__bounded_call_refinement_content_is_complete(
    self,
    content: Mapping[str, Any],
    *,
    expected_pcode_key: Tuple[Any, ...],
    expected_callee_key: Tuple[Any, ...],
    expected_argument_count: int,
) -> bool:
    if self._evidence_text(content, "status") not in {"complete", "completed", "proven"}:
        return False
    if not self._evidence_bool(content, "object_derived"):
        return False
    if self._evidence_has_any_recursive(content, self._COMPLETED_PROOF_BLOCKER_FIELDS):
        return False
    if self._normalize_nested_tuple(content.get("callsite_pcode_key")) != expected_pcode_key:
        return False
    if self._normalize_nested_tuple(content.get("callee_identity")) != expected_callee_key:
        return False
    argument_signature = self._normalize_nested_tuple(content.get("argument_signature"))
    if not isinstance(argument_signature, tuple) or len(argument_signature) != int(expected_argument_count):
        return False
    if int(content.get("result_count") or 0) <= 0:
        return False
    if int(content.get("callee_return_case_count") or 0) <= 0:
        return False
    if content.get("callee_effect_summary_clean") is not True:
        return False
    if content.get("dependency_cycle") is True:
        return False
    if content.get("truncated") is True:
        return False
    if self._normalize_nested_tuple(content.get("callee_return_partition_key")) in {None, ()}:
        return False
    if self._normalize_nested_tuple(content.get("object_target_key")) in {None, ()}:
        return False
    if content.get("callee_summary_requires_completed_proof") is True:
        completed_ids = self._normalize_nested_tuple(content.get("callee_completed_proof_ids"))
        completed_evidence_ids = self._normalize_nested_tuple(
            content.get("callee_completed_proof_evidence_ids")
        )
        if completed_ids in {None, ()} and completed_evidence_ids in {None, ()}:
            return False
    return True

def _impl__self_recursive_no_store_call_effect_proof_content(
    self,
    object_target_key: Tuple[Any, ...],
    analysis: FunctionReturnAnalysis,
) -> Optional[Dict[str, Any]]:
    if len(object_target_key) < 7 or object_target_key[0] != "unsupported_call_effect":
        return None
    if object_target_key[-1] != "callee_effect_summary_missing":
        return None
    recurrence_receipts = tuple(
        item
        for item in getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
        if isinstance(item, Mapping)
        and item.get("status") == "complete"
        and item.get("proof_stage") == "recurrence_validation_complete"
        and item.get("evidence_kind") == "validated_unary_recurrence_artifact"
    )
    if len(recurrence_receipts) != 1:
        return None
    recurrence_receipt = recurrence_receipts[0]
    proposal_digest = str(recurrence_receipt.get("proposal_digest") or "")
    binding_digest = str(
        recurrence_receipt.get("function_recurrence_binding_digest") or ""
    )
    seed_digest = str(recurrence_receipt.get("seed_core_digest") or "")
    if not proposal_digest or not binding_digest or not seed_digest:
        return None
    proposals = tuple(
        proposal
        for proposal in getattr(analysis, "quarantined_recurrence_proposals", ()) or ()
        if str(getattr(proposal, "digest", "") or "") == proposal_digest
        and str(getattr(proposal, "seed_core_digest", "") or "") == seed_digest
    )
    if len(proposals) != 1:
        return None
    try:
        from scripts.function_tracer_pcode.checker.cause_identity import ProofRequirementId
        from scripts.function_tracer_pcode.proof.obligations.recurrence import (
            validate_recurrence_requirement_target,
        )

        requirement = ProofRequirementId.from_dict(
            recurrence_receipt.get("proof_requirement") or {}
        )
        target_fields = dict(requirement.proof_target_key[1:])
        validate_recurrence_requirement_target(
            requirement,
            seed_core_digest=seed_digest,
            proposal_digest=proposal_digest,
            function_recurrence_binding_digest=binding_digest,
            proof_stage="recurrence_validation_complete",
            proof_target_semantic_key=tuple(target_fields["proof_target"]),
        )
    except (KeyError, TypeError, ValueError):
        return None
    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is None:
        return None
    if getattr(effect_summary, "effects", None):
        return None
    if getattr(effect_summary, "incomplete_reasons", None):
        return None
    unsupported_sites = tuple(getattr(effect_summary, "unsupported_call_sites", ()) or ())
    if len(unsupported_sites) != 1:
        return None
    side_label = object_target_key[1]
    site = unsupported_sites[0]
    if getattr(site, "reason", None) != "callee_effect_summary_missing":
        return None
    site_key = self._normalize_nested_tuple(
        self._unsupported_call_effect_object_key(
            site,
            analysis=analysis,
            side_label=side_label,
        )
    )
    if site_key != object_target_key:
        return None
    target_key = self._call_target_key_for_analysis(getattr(site, "target_ref", None), analysis)
    if not self._call_target_is_analysis_entry(target_key, analysis):
        return None
    pcode_op_ref = self._stable_key_or_none(getattr(site, "pcode_op_ref", None))
    if pcode_op_ref is None:
        return None
    return {
        "object_derived": True,
        "status": "complete",
        "proof_rule": "self_recursive_no_store_effect_summary",
        "object_target_key": object_target_key,
        "caller_function": self._analysis_entry_key(analysis),
        "recursive_callee": target_key,
        "callsite_pcode_op_ref": pcode_op_ref,
        "unsupported_call_site": object_target_key,
        "local_store_effect_count": 0,
        "unsupported_call_site_count": 1,
        "recursive_call_effect": "no_memory_effects_by_induction",
        "recurrence_validation": {
            "proposal_digest": proposal_digest,
            "function_recurrence_binding_digest": binding_digest,
            "semantic_closure_digest": recurrence_receipt.get(
                "semantic_closure_digest"
            ),
            "validated_unary_artifact_id": recurrence_receipt.get(
                "validated_unary_artifact_id"
            ),
        },
        "call_effect_summary": {
            "status": "complete",
            "summary_source": ("effect_summary", "unsupported_call_effect"),
            "evidence_kind": "call_effect_summary",
            "object_target_key": object_target_key,
            "unsupported_reason": "callee_effect_summary_missing",
            "local_store_effect_count": 0,
            "unsupported_call_site_count": 1,
        },
        "runtime_ref": {
            "status": "complete",
            "runtime_ref": object_target_key[3],
        },
        "callsite_storage": {
            "status": "complete",
            "callsite_storage": object_target_key[4],
        },
    }

def _impl__matched_unknown_indirect_call_effect_proof_content(
    self,
    object_target_key: Tuple[Any, ...],
    analysis: FunctionReturnAnalysis,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Optional[Dict[str, Any]]:
    def reject(reason: str) -> Optional[Dict[str, Any]]:
        self._debug_print(
            "matched unknown-indirect call-effect proof unavailable: "
            f"{reason}"
        )
        return None

    if len(object_target_key) < 7 or object_target_key[0] != "unsupported_call_effect":
        return None
    if not self._unsupported_call_effect_reason_is_compatible(
        object_target_key[-1],
        "target_identity_unavailable",
    ):
        return None
    local_reason = object_target_key[6] if len(object_target_key) > 6 else None
    peer_compatible_reason = "target_identity_unavailable"
    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is None:
        return reject("missing local effect summary")
    if getattr(effect_summary, "effects", None):
        return reject("local store effects are present")
    if getattr(effect_summary, "incomplete_reasons", None):
        return reject(
            "local effect summary is incomplete: "
            f"{tuple(getattr(effect_summary, 'incomplete_reasons', ()) or ())}"
        )
    peer_analysis = analysis2 if analysis is analysis1 else analysis1 if analysis is analysis2 else None
    if peer_analysis is None:
        return reject("object target side did not map to either analysis")
    peer_summary = getattr(peer_analysis, "effect_summary", None)
    if peer_summary is None:
        return reject("missing peer effect summary")
    if getattr(peer_summary, "effects", None):
        return reject("peer store effects are present")
    if getattr(peer_summary, "incomplete_reasons", None):
        return reject(
            "peer effect summary is incomplete: "
            f"{tuple(getattr(peer_summary, 'incomplete_reasons', ()) or ())}"
        )
    local_label = "function1" if analysis is analysis1 else "function2"
    local_matches = [
        self._unsupported_call_effect_object_key(
            local_site,
            analysis=analysis,
            side_label=local_label,
        )
        for local_site in getattr(effect_summary, "unsupported_call_sites", ()) or ()
        if self._unsupported_call_effects_semantically_match(
            object_target_key,
            self._unsupported_call_effect_object_key(
                local_site,
                analysis=analysis,
                side_label=local_label,
            ),
        )
    ]
    if len(local_matches) != 1:
        return reject(
            "local unsupported call effect match count is "
            f"{len(local_matches)}"
        )
    peer_label = "function2" if analysis is analysis1 else "function1"
    matches = [
        self._unsupported_call_effect_object_key(
            peer_site,
            analysis=peer_analysis,
            side_label=peer_label,
        )
        for peer_site in getattr(peer_summary, "unsupported_call_sites", ()) or ()
        if self._unsupported_call_effects_semantically_match(
            object_target_key,
            self._unsupported_call_effect_object_key(
                peer_site,
                analysis=peer_analysis,
                side_label=peer_label,
            ),
        )
    ]
    if len(matches) != 1:
        return reject(
            "peer unsupported call effect match count is "
            f"{len(matches)}"
        )
    peer_object_target_key = self._normalize_nested_tuple(matches[0])
    peer_reason = peer_object_target_key[6] if len(peer_object_target_key) > 6 else None
    if (
        local_reason == "callee_unsupported_call_may_expose_parameter_memory"
        and peer_reason != peer_compatible_reason
    ):
        return reject(
            "parameter-exposure specific unsupported-call reason pair handled by "
            "parameter-exposure proof path"
        )
    if not self._unsupported_call_effect_reason_is_compatible(local_reason, peer_reason):
        return reject("mixed unsupported-call reason pair not supported by unknown-indirect proof")
    target_expression_key = self._cross_binary_call_effect_component_key(
        self._unsupported_call_effect_target_expression_key(object_target_key)
    )
    if not self._call_effect_target_expression_key_is_present(target_expression_key):
        return reject("missing local target expression key")
    argument_keys = self._cross_binary_call_effect_component_key(
        self._unsupported_call_effect_argument_keys(object_target_key)
    )
    effect_fingerprint = self._matched_unknown_indirect_call_effect_fingerprint(
        object_target_key,
        peer_object_target_key,
        analysis,
        peer_analysis,
        effect_summary,
        peer_summary,
    )
    if effect_fingerprint is None:
        return reject("call-effect surface fingerprint incomplete")
    return {
        "object_derived": True,
        "status": "complete",
        "proof_rule": "matched_unknown_indirect_no_store_call_effect",
        "object_target_key": object_target_key,
        "peer_object_target_key": peer_object_target_key,
        "call_effect_summary": {
            "status": "complete",
            "summary_source": ("effect_summary", "unsupported_call_effect"),
            "evidence_kind": "call_effect_summary",
            "object_target_key": object_target_key,
            "peer_object_target_key": peer_object_target_key,
            "unsupported_reason": object_target_key[6]
            if len(object_target_key) > 6
            else "target_identity_unavailable",
            "local_store_effect_count": 0,
            "unsupported_call_site_count": len(
                tuple(getattr(effect_summary, "unsupported_call_sites", ()) or ())
            ),
            "peer_unsupported_call_site_count": len(
                tuple(getattr(peer_summary, "unsupported_call_sites", ()) or ())
            ),
            "matching_local_unsupported_call_site_count": len(local_matches),
            "matching_peer_unsupported_call_site_count": len(matches),
        },
        "call_effect_surface": effect_fingerprint,
        "runtime_ref": {
            "status": "complete",
            "runtime_ref": object_target_key[3],
            "peer_runtime_ref": peer_object_target_key[3],
            "matched_target_expression_key": target_expression_key,
        },
        "callsite_storage": {
            "status": "complete",
            "callsite_storage": object_target_key[4],
            "peer_callsite_storage": peer_object_target_key[4],
            "matched_argument_keys": argument_keys,
        },
        "compatibility_policy": self._unsupported_call_effect_compatibility_policy_evidence(
            object_target_key,
            peer_object_target_key,
        ),
    }

def _impl__matched_unsupported_call_effect_no_store_parameter_exposure_proof_content(
    self,
    object_target_key: Tuple[Any, ...],
    analysis: FunctionReturnAnalysis,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    reason: str,
) -> Optional[Dict[str, Any]]:
    def reject(reason_text: str) -> Optional[Dict[str, Any]]:
        self._debug_print(
            "matched unsupported-call parameter-exposure proof unavailable: "
            f"{reason_text}"
        )
        return None

    if len(object_target_key) < 7 or object_target_key[0] != "unsupported_call_effect":
        return None
    if object_target_key[-1] != reason:
        return None
    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is None:
        return reject("missing local effect summary")
    if getattr(effect_summary, "effects", None):
        return reject("local store effects are present")
    if getattr(effect_summary, "incomplete_reasons", None):
        return reject(
            "local effect summary is incomplete: "
            f"{tuple(getattr(effect_summary, 'incomplete_reasons', ()) or ())}"
        )
    peer_analysis = analysis2 if analysis is analysis1 else analysis1 if analysis is analysis2 else None
    if peer_analysis is None:
        return reject("object target side did not map to either analysis")
    peer_summary = getattr(peer_analysis, "effect_summary", None)
    if peer_summary is None:
        return reject("missing peer effect summary")
    if getattr(peer_summary, "effects", None):
        return reject("peer store effects are present")
    if getattr(peer_summary, "incomplete_reasons", None):
        return reject(
            "peer effect summary is incomplete: "
            f"{tuple(getattr(peer_summary, 'incomplete_reasons', ()) or ())}"
        )

    local_label = "function1" if analysis is analysis1 else "function2"
    local_matches = [
        self._unsupported_call_effect_object_key(
            local_site,
            analysis=analysis,
            side_label=local_label,
        )
        for local_site in getattr(effect_summary, "unsupported_call_sites", ()) or ()
        if self._unsupported_call_effects_semantically_match(
            object_target_key,
            self._unsupported_call_effect_object_key(
                local_site,
                analysis=analysis,
                side_label=local_label,
            ),
        )
    ]
    if len(local_matches) != 1:
        return reject(
            "local unsupported call effect match count is "
            f"{len(local_matches)}"
        )
    peer_label = "function2" if analysis is analysis1 else "function1"
    matches = [
        self._unsupported_call_effect_object_key(
            peer_site,
            analysis=peer_analysis,
            side_label=peer_label,
        )
        for peer_site in getattr(peer_summary, "unsupported_call_sites", ()) or ()
        if self._unsupported_call_effects_semantically_match(
            object_target_key,
            self._unsupported_call_effect_object_key(
                peer_site,
                analysis=peer_analysis,
                side_label=peer_label,
            ),
        )
    ]
    if len(matches) != 1:
        return reject(
            "peer unsupported call effect match count is "
            f"{len(matches)}"
        )
    peer_object_target_key = self._normalize_nested_tuple(matches[0])
    target_expression_key = self._cross_binary_call_effect_component_key(
        self._unsupported_call_effect_target_expression_key(object_target_key)
    )
    if not self._call_effect_target_expression_key_is_present(target_expression_key):
        return reject("missing local target expression key")
    argument_keys = self._cross_binary_call_effect_component_key(
        self._unsupported_call_effect_argument_keys(object_target_key)
    )
    if not self._call_effect_argument_keys_are_present(argument_keys):
        return reject("missing local argument keys")
    return {
        "object_derived": True,
        "status": "complete",
        "proof_rule": "matched_unsupported_call_parameter_exposure_no_store_call_effect",
        "object_target_key": object_target_key,
        "peer_object_target_key": peer_object_target_key,
        "call_effect_summary": {
            "status": "complete",
            "summary_source": ("effect_summary", "unsupported_call_effect"),
            "evidence_kind": "call_effect_summary",
            "object_target_key": object_target_key,
            "peer_object_target_key": peer_object_target_key,
            "unsupported_reason": reason,
            "local_store_effect_count": 0,
            "unsupported_call_site_count": len(
                tuple(getattr(effect_summary, "unsupported_call_sites", ()) or ())
            ),
            "peer_unsupported_call_site_count": len(
                tuple(getattr(peer_summary, "unsupported_call_sites", ()) or ())
            ),
            "matching_local_unsupported_call_site_count": len(local_matches),
            "matching_peer_unsupported_call_site_count": len(matches),
        },
        "runtime_ref": {
            "status": "complete",
            "runtime_ref": object_target_key[3],
            "peer_runtime_ref": peer_object_target_key[3],
            "matched_target_expression_key": target_expression_key,
        },
        "callsite_storage": {
            "status": "complete",
            "callsite_storage": object_target_key[4],
            "peer_callsite_storage": peer_object_target_key[4],
            "matched_argument_keys": argument_keys,
        },
        "compatibility_policy": self._unsupported_call_effect_compatibility_policy_evidence(
            object_target_key,
            peer_object_target_key,
        ),
    }

def _impl__matched_deferred_call_argument_proof_content(
    self,
    object_target_key: Tuple[Any, ...],
    analysis: FunctionReturnAnalysis,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Optional[Dict[str, Any]]:
    def reject(reason: str) -> Optional[Dict[str, Any]]:
        self._debug_print(
            "matched deferred-call argument proof unavailable: "
            f"{reason}"
        )
        return None

    if len(object_target_key) < 9 or object_target_key[0] != "deferred_call":
        return None
    if object_target_key[-1] == "complete":
        return None
    peer_analysis = analysis2 if analysis is analysis1 else analysis1 if analysis is analysis2 else None
    if peer_analysis is None:
        return reject("object target side did not map to either analysis")
    local_summary = getattr(analysis, "effect_summary", None)
    peer_summary = getattr(peer_analysis, "effect_summary", None)
    if local_summary is None or peer_summary is None:
        return reject("missing effect summary")
    if getattr(local_summary, "effects", None):
        return reject("local store effects are present")
    if getattr(peer_summary, "effects", None):
        return reject("peer store effects are present")
    if getattr(local_summary, "incomplete_reasons", None):
        return reject(
            "local effect summary is incomplete: "
            f"{tuple(getattr(local_summary, 'incomplete_reasons', ()) or ())}"
        )
    if getattr(peer_summary, "incomplete_reasons", None):
        return reject(
            "peer effect summary is incomplete: "
            f"{tuple(getattr(peer_summary, 'incomplete_reasons', ()) or ())}"
        )

    local_label = "function1" if analysis is analysis1 else "function2"
    local_matches = [
        self._deferred_call_object_target_key(
            local_info,
            analysis=analysis,
            side_label=local_label,
        )
        for local_info in getattr(analysis, "deferred_calls", {}).values()
        if local_info is not None
        and self._deferred_calls_semantically_match(
            object_target_key,
            self._deferred_call_object_target_key(
                local_info,
                analysis=analysis,
                side_label=local_label,
            ),
        )
    ]
    if len(local_matches) != 1:
        return reject(f"local deferred-call match count is {len(local_matches)}")

    peer_label = "function2" if analysis is analysis1 else "function1"
    peer_matches = [
        self._deferred_call_object_target_key(
            peer_info,
            analysis=peer_analysis,
            side_label=peer_label,
        )
        for peer_info in getattr(peer_analysis, "deferred_calls", {}).values()
        if peer_info is not None
        and self._deferred_calls_semantically_match(
            object_target_key,
            self._deferred_call_object_target_key(
                peer_info,
                analysis=peer_analysis,
                side_label=peer_label,
            ),
        )
    ]
    if len(peer_matches) != 1:
        return reject(f"peer deferred-call match count is {len(peer_matches)}")

    peer_object_target_key = self._normalize_nested_tuple(peer_matches[0])
    target_expression_key = self._cross_binary_call_effect_component_key(
        self._deferred_call_target_expression_key(object_target_key)
    )
    if not self._call_effect_target_expression_key_is_present(target_expression_key):
        return reject("missing local target expression key")
    argument_keys = self._cross_binary_call_effect_component_key(
        self._deferred_call_argument_keys(object_target_key)
    )
    if not self._call_effect_argument_keys_are_present(argument_keys):
        return reject("missing local argument keys")
    expected_refs = self._expected_deferred_call_proof_content_refs(object_target_key)
    peer_refs = self._expected_deferred_call_proof_content_refs(peer_object_target_key)
    if expected_refs is None or peer_refs is None:
        return reject("missing deferred-call proof refs")
    runtime_ref, callsite_storage = expected_refs
    peer_runtime_ref, peer_callsite_storage = peer_refs
    return {
        "object_derived": True,
        "status": "complete",
        "proof_rule": "matched_deferred_call_argument_evidence",
        "object_target_key": object_target_key,
        "peer_object_target_key": peer_object_target_key,
        "call_effect_summary": {
            "status": "complete",
            "summary_source": ("effect_summary", "deferred_call"),
            "evidence_kind": "call_effect_summary",
            "object_target_key": object_target_key,
            "peer_object_target_key": peer_object_target_key,
            "local_store_effect_count": 0,
            "matching_local_deferred_call_count": len(local_matches),
            "matching_peer_deferred_call_count": len(peer_matches),
            "local_deferred_call_count": len(
                tuple(getattr(analysis, "deferred_calls", {}).values())
            ),
            "peer_deferred_call_count": len(
                tuple(getattr(peer_analysis, "deferred_calls", {}).values())
            ),
            "local_call_argument_recovery_status": object_target_key[-1],
            "peer_call_argument_recovery_status": peer_object_target_key[-1],
        },
        "runtime_ref": {
            "status": "complete",
            "runtime_ref": runtime_ref,
            "peer_runtime_ref": peer_runtime_ref,
            "matched_target_expression_key": target_expression_key,
        },
        "callsite_storage": {
            "status": "complete",
            "callsite_storage": callsite_storage,
            "peer_callsite_storage": peer_callsite_storage,
            "matched_argument_keys": argument_keys,
        },
    }

def _impl__unsupported_call_effects_semantically_match(
    self,
    object_target_key: Any,
    peer_object_target_key: Any,
) -> bool:
    left = self._normalize_nested_tuple(object_target_key)
    right = self._normalize_nested_tuple(peer_object_target_key)
    if not (
        isinstance(left, tuple)
        and isinstance(right, tuple)
        and len(left) >= 7
        and len(right) >= 7
        and left[0] == right[0] == "unsupported_call_effect"
    ):
        return False
    if not self._unsupported_call_effect_reason_is_compatible(left[-1], right[-1]):
        return False
    left_target = self._cross_binary_call_effect_component_key(
        self._unsupported_call_effect_target_expression_key(left)
    )
    right_target = self._cross_binary_call_effect_component_key(
        self._unsupported_call_effect_target_expression_key(right)
    )
    if not (
        self._call_effect_target_expression_key_is_present(left_target)
        and self._call_effect_target_expression_key_is_present(right_target)
    ):
        return False

    left_argument_keys = self._cross_binary_call_effect_component_key(
        self._unsupported_call_effect_argument_keys(left)
    )
    right_argument_keys = self._cross_binary_call_effect_component_key(
        self._unsupported_call_effect_argument_keys(right)
    )
    if not (
        self._unsupported_call_effect_argument_evidence_is_complete(left_argument_keys)
        and self._unsupported_call_effect_argument_evidence_is_complete(right_argument_keys)
    ):
        return False

    policy = self._unsupported_call_effect_compatibility_policy_evidence(left, right)
    return self._unsupported_call_effect_compatibility_policy_is_complete(policy)

def _impl__matched_unknown_indirect_call_effect_fingerprint(
    self,
    object_target_key: Tuple[Any, ...],
    peer_object_target_key: Tuple[Any, ...],
    analysis: FunctionReturnAnalysis,
    peer_analysis: FunctionReturnAnalysis,
    effect_summary: Any,
    peer_summary: Any,
) -> Optional[Dict[str, Any]]:
    if not (
        self._unsupported_call_effect_has_no_observed_writes(effect_summary)
        and self._unsupported_call_effect_has_no_observed_writes(peer_summary)
    ):
        return None
    local_guard_key = self._unsupported_call_effect_path_condition_key(object_target_key)
    peer_guard_key = self._unsupported_call_effect_path_condition_key(peer_object_target_key)
    if local_guard_key is None or peer_guard_key is None:
        return None
    if (
        self._cross_binary_call_effect_component_key(local_guard_key)
        != self._cross_binary_call_effect_component_key(peer_guard_key)
    ):
        return None
    local_output_use = self._unsupported_call_output_use_fingerprint(
        analysis,
        effect_summary,
        object_target_key,
    )
    peer_output_use = self._unsupported_call_output_use_fingerprint(
        peer_analysis,
        peer_summary,
        peer_object_target_key,
    )
    if local_output_use is None or peer_output_use is None:
        return None
    local_occurrence = self._unsupported_call_effect_occurrence_fingerprint(
        object_target_key,
        analysis,
        effect_summary,
    )
    peer_occurrence = self._unsupported_call_effect_occurrence_fingerprint(
        peer_object_target_key,
        peer_analysis,
        peer_summary,
    )
    if local_occurrence is None or peer_occurrence is None:
        return None
    if local_occurrence.get("occurrence_index") != peer_occurrence.get("occurrence_index"):
        return None
    return {
        "status": "complete",
        "guard_equivalence_mode": "path_guard_equivalence",
        "local_callsite_path_guard_key": local_guard_key,
        "peer_callsite_path_guard_key": peer_guard_key,
        "call_occurrence": local_occurrence,
        "peer_call_occurrence": peer_occurrence,
        "caller_observed_memory_write": {
            "status": "complete",
            "scope": "whole_function_effect_summary",
            "local_store_effect_count": 0,
            "peer_store_effect_count": 0,
            "local_incomplete_reason_count": 0,
            "peer_incomplete_reason_count": 0,
        },
        "call_output_use": local_output_use,
        "peer_call_output_use": peer_output_use,
    }

def _impl__unsupported_call_effect_has_no_observed_writes(cls, effect_summary: Any) -> bool:
    if effect_summary is None:
        return False
    return not (
        tuple(getattr(effect_summary, "effects", ()) or ())
        or tuple(getattr(effect_summary, "incomplete_reasons", ()) or ())
    )

def _impl__unsupported_call_effect_occurrence_fingerprint(
    self,
    object_target_key: Tuple[Any, ...],
    analysis: FunctionReturnAnalysis,
    effect_summary: Any,
) -> Optional[Dict[str, Any]]:
    sites = tuple(getattr(effect_summary, "unsupported_call_sites", ()) or ())
    if not sites:
        return None
    side_label = object_target_key[1] if len(object_target_key) >= 2 else None
    analysis_key = object_target_key[2] if len(object_target_key) >= 3 else None
    site_keys = tuple(
        self._normalize_nested_tuple(
            self._unsupported_call_effect_object_key(
                site,
                analysis=analysis,
                side_label=side_label,
            )
        )
        for site in sites
    )
    target_runtime = object_target_key[3] if len(object_target_key) >= 4 else None
    target_storage = object_target_key[4] if len(object_target_key) >= 5 else None
    target_ordinal = object_target_key[5] if len(object_target_key) >= 6 else None
    matching_indices = tuple(
        index
        for index, key in enumerate(site_keys)
        if (
            isinstance(key, tuple)
            and len(key) >= 6
            and key[3] == target_runtime
            and key[4] == target_storage
            and key[5] == target_ordinal
        )
    )
    if len(matching_indices) != 1:
        return None
    return {
        "status": "complete",
        "analysis_key": analysis_key,
        "effect_ordinal": target_ordinal,
        "occurrence_index": matching_indices[0],
        "unsupported_call_site_count": len(site_keys),
        "call_order_key_sequence": tuple(
            key[5] for key in site_keys if isinstance(key, tuple) and len(key) >= 6
        ),
    }

def _impl__unsupported_call_output_use_fingerprint(
    self,
    analysis: FunctionReturnAnalysis,
    effect_summary: Any,
    object_target_key: Tuple[Any, ...],
) -> Optional[Dict[str, Any]]:
    pcode_ref = self._unsupported_call_effect_pcode_ref_key(object_target_key)
    if pcode_ref is None:
        return None
    exposed_refs = []
    for return_index, return_info in enumerate(getattr(analysis, "returns", ()) or ()):
        if self._expression_contains_runtime_ref(getattr(return_info, "value", None), pcode_ref):
            exposed_refs.append(("return_value", return_index))
        for condition_index, condition in enumerate(getattr(return_info, "conditions", ()) or ()):
            if self._expression_contains_runtime_ref(
                getattr(condition, "expression", None),
                pcode_ref,
            ):
                exposed_refs.append(("return_guard", return_index, condition_index))
    for site_index, site in enumerate(getattr(effect_summary, "unsupported_call_sites", ()) or ()):
        if self._expression_contains_runtime_ref(getattr(site, "target_expr", None), pcode_ref):
            exposed_refs.append(("unsupported_call_target", site_index))
        for argument_index, argument in enumerate(getattr(site, "arguments", ()) or ()):
            if self._expression_contains_runtime_ref(argument, pcode_ref):
                exposed_refs.append(("unsupported_call_argument", site_index, argument_index))
    for evidence_index, evidence in enumerate(getattr(effect_summary, "call_target_resolution_evidence", ()) or ()):
        if self._expression_contains_runtime_ref(getattr(evidence, "target_expr", None), pcode_ref):
            exposed_refs.append(("call_target_resolution_target", evidence_index))
    if exposed_refs:
        return None
    return {
        "status": "complete",
        "classification": "not_exposed_to_return_or_call_effect_surface",
        "pcode_op_ref": pcode_ref,
        "checked_surface": "return_values_return_guards_and_call_effect_inputs",
    }

def _impl__unsupported_call_effect_pcode_ref_key(cls, object_target_key: Any) -> Optional[Tuple[Any, ...]]:
    target = cls._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) < 5:
        return None
    for section in (target[3], target[4]):
        if not isinstance(section, tuple):
            continue
        for item in section:
            if isinstance(item, tuple) and len(item) == 2 and item[0] == "pcode_op_ref":
                pcode_ref = cls._normalize_nested_tuple(item[1])
                return pcode_ref if isinstance(pcode_ref, tuple) else None
    return None

def _impl__unsupported_call_effect_path_condition_key(cls, object_target_key: Any) -> Optional[Tuple[Any, ...]]:
    target = cls._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) < 5:
        return None
    for section in (target[3], target[4]):
        if not isinstance(section, tuple):
            continue
        for item in section:
            if isinstance(item, tuple) and len(item) == 2 and item[0] == "path_conditions":
                value = cls._normalize_nested_tuple(item[1])
                return ("callsite_path_conditions", value if isinstance(value, tuple) else ())
    return ("callsite_path_conditions", ())

def _impl__unsupported_call_effect_requires_exact_target_expression_match(
    cls,
    object_target_key: Any,
    peer_object_target_key: Any,
) -> bool:
    return True

def _impl__unsupported_call_effect_callee_identity_key(cls, object_target_key: Any) -> Any:
    target = cls._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) < 5:
        return None
    for section in (target[3], target[4]):
        if not isinstance(section, tuple):
            continue
        for item in section:
            if isinstance(item, tuple) and len(item) == 2 and item[0] == "callee_identity":
                return cls._normalize_nested_tuple(item[1])
    return None

def _impl__unsupported_call_effect_callee_identity_category(cls, object_target_key: Any) -> Optional[str]:
    identity = cls._unsupported_call_effect_callee_identity_key(object_target_key)
    if isinstance(identity, tuple) and identity:
        return str(identity[0])
    if identity is None:
        return None
    return str(identity)

def _impl__unsupported_call_effect_callee_identity_is_reachable(cls, object_target_key: Any) -> bool:
    identity = cls._unsupported_call_effect_callee_identity_key(object_target_key)
    if not isinstance(identity, tuple) or not identity:
        return False
    category = str(identity[0])
    if category == "unknown":
        return cls._call_effect_target_expression_key_is_present(
            cls._cross_binary_call_effect_component_key(
                cls._unsupported_call_effect_target_expression_key(object_target_key)
            )
        )
    return category not in {"missing", "none", "unavailable"}

def _impl__unsupported_call_effect_compatibility_policy_evidence(
    cls,
    object_target_key: Any,
    peer_object_target_key: Any,
) -> Dict[str, Any]:
    left = cls._normalize_nested_tuple(object_target_key)
    right = cls._normalize_nested_tuple(peer_object_target_key)
    if not (
        isinstance(left, tuple)
        and isinstance(right, tuple)
        and len(left) >= 7
        and len(right) >= 7
        and left[0] == right[0] == "unsupported_call_effect"
    ):
        return {
            "status": "incomplete",
            "reason": "unsupported_call_effect_object_target_key_missing",
        }
    left_target = cls._cross_binary_call_effect_component_key(
        cls._unsupported_call_effect_target_expression_key(left)
    )
    right_target = cls._cross_binary_call_effect_component_key(
        cls._unsupported_call_effect_target_expression_key(right)
    )
    left_arguments = cls._cross_binary_call_effect_component_key(
        cls._unsupported_call_effect_argument_keys(left)
    )
    right_arguments = cls._cross_binary_call_effect_component_key(
        cls._unsupported_call_effect_argument_keys(right)
    )
    left_path_guard = cls._cross_binary_call_effect_component_key(
        cls._unsupported_call_effect_path_condition_key(left)
    )
    right_path_guard = cls._cross_binary_call_effect_component_key(
        cls._unsupported_call_effect_path_condition_key(right)
    )
    left_callee_category = cls._unsupported_call_effect_callee_identity_category(left)
    right_callee_category = cls._unsupported_call_effect_callee_identity_category(right)
    reason_signature_match = cls._unsupported_call_effect_reason_is_compatible(left[-1], right[-1])
    target_expression_match = (
        cls._call_effect_target_expression_key_is_present(left_target)
        and cls._call_effect_target_expression_key_is_present(right_target)
        and left_target == right_target
    )
    argument_keys_match = (
        cls._unsupported_call_effect_argument_evidence_is_complete(left_arguments)
        and cls._unsupported_call_effect_argument_evidence_is_complete(right_arguments)
        and left_arguments == right_arguments
    )
    path_guard_match = (
        left_path_guard is not None
        and right_path_guard is not None
        and left_path_guard == right_path_guard
    )
    callee_identity_category_match = (
        left_callee_category is not None
        and left_callee_category == right_callee_category
    )
    callee_identity_reachable = (
        cls._unsupported_call_effect_callee_identity_is_reachable(left)
        and cls._unsupported_call_effect_callee_identity_is_reachable(right)
    )
    unsupported_fact_evidence_complete = (
        cls._call_effect_target_expression_key_is_present(left_target)
        and cls._call_effect_target_expression_key_is_present(right_target)
        and cls._unsupported_call_effect_argument_evidence_is_complete(left_arguments)
        and cls._unsupported_call_effect_argument_evidence_is_complete(right_arguments)
        and left[-1] is not None
        and right[-1] is not None
    )
    flags = {
        "reason_signature_match": reason_signature_match,
        "target_expression_match": target_expression_match,
        "argument_keys_match": argument_keys_match,
        "path_guard_match": path_guard_match,
        "callee_identity_category_match": callee_identity_category_match,
        "callee_identity_reachable": callee_identity_reachable,
        "unsupported_fact_evidence_complete": unsupported_fact_evidence_complete,
    }
    return {
        "status": "complete" if all(flags.values()) else "incomplete",
        "reason_signature": cls._unsupported_call_effect_reason_signature(left[-1]),
        "peer_reason_signature": cls._unsupported_call_effect_reason_signature(right[-1]),
        "left_callee_identity_category": left_callee_category,
        "right_callee_identity_category": right_callee_category,
        "left_target_expression_key": left_target,
        "right_target_expression_key": right_target,
        "left_argument_keys": left_arguments,
        "right_argument_keys": right_arguments,
        "left_path_guard_key": left_path_guard,
        "right_path_guard_key": right_path_guard,
        **flags,
    }

def _impl__unsupported_call_effect_compatibility_policy_is_complete(
    cls,
    policy: Any,
) -> bool:
    if not isinstance(policy, Mapping):
        return False
    if cls._evidence_text(policy, "status") not in {"complete", "completed", "proven"}:
        return False
    return all(
        bool(policy.get(flag))
        for flag in cls._UNSUPPORTED_CALL_EFFECT_COMPATIBILITY_REQUIRED_FLAGS
    )

def _impl__unsupported_call_effect_callee_identity_is_unknown(cls, object_target_key: Any) -> bool:
    target = cls._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) < 4:
        return False
    runtime_ref = target[3]
    if not isinstance(runtime_ref, tuple):
        return False
    for item in runtime_ref:
        if not (isinstance(item, tuple) and len(item) == 2 and item[0] == "callee_identity"):
            continue
        callee_identity = item[1]
        normalized = cls._normalize_nested_tuple(callee_identity)
        return isinstance(normalized, tuple) and normalized and normalized[0] == "unknown"
    return False

def _impl__deferred_calls_semantically_match(
    self,
    object_target_key: Any,
    peer_object_target_key: Any,
) -> bool:
    left = self._normalize_nested_tuple(object_target_key)
    right = self._normalize_nested_tuple(peer_object_target_key)
    if not (
        isinstance(left, tuple)
        and isinstance(right, tuple)
        and len(left) >= 9
        and len(right) >= 9
        and left[0] == right[0] == "deferred_call"
        and left[-1] != "complete"
        and right[-1] != "complete"
    ):
        return False
    left_target = self._cross_binary_call_effect_component_key(
        self._deferred_call_target_expression_key(left)
    )
    right_target = self._cross_binary_call_effect_component_key(
        self._deferred_call_target_expression_key(right)
    )
    if not (
        self._call_effect_target_expression_key_is_present(left_target)
        and self._call_effect_target_expression_key_is_present(right_target)
    ):
        return False
    left_argument_keys = self._cross_binary_call_effect_component_key(
        self._deferred_call_argument_keys(left)
    )
    right_argument_keys = self._cross_binary_call_effect_component_key(
        self._deferred_call_argument_keys(right)
    )
    if not (
        self._call_effect_argument_keys_are_present(left_argument_keys)
        and self._call_effect_argument_keys_are_present(right_argument_keys)
    ):
        return False
    return (
        left_target == right_target
        and left_argument_keys == right_argument_keys
    )

def _impl__unsupported_call_effect_target_expression_key(cls, object_target_key: Any) -> Any:
    target = cls._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) < 5:
        return None
    callsite_storage = target[4]
    if isinstance(callsite_storage, tuple):
        for item in callsite_storage:
            if isinstance(item, tuple) and len(item) == 2 and item[0] == "target_expression":
                return item[1]
    runtime_ref = target[3]
    if isinstance(runtime_ref, tuple):
        for item in runtime_ref:
            if isinstance(item, tuple) and len(item) == 2 and item[0] == "typed_target_expression":
                return item[1]
    return None

def _impl__call_effect_target_expression_key_is_present(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    if normalized is None:
        return False
    if normalized == ():
        return False
    if isinstance(normalized, str):
        return normalized not in {"", "<missing>", "missing", "none", "None"}
    if isinstance(normalized, tuple):
        if not normalized:
            return False
        first = normalized[0]
        if cls._atom_str_is(first, "<missing>") or cls._atom_str_is(first, "missing"):
            return False
        return True
    return True

def _impl__unsupported_call_effect_argument_keys(cls, object_target_key: Any) -> Tuple[Any, ...]:
    target = cls._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) < 5:
        return ()
    callsite_storage = target[4]
    if isinstance(callsite_storage, tuple):
        for item in callsite_storage:
            if isinstance(item, tuple) and len(item) == 2 and item[0] == "argument_keys":
                value = cls._normalize_nested_tuple(item[1])
                return value if isinstance(value, tuple) else ()
    runtime_ref = target[3]
    if isinstance(runtime_ref, tuple):
        for item in runtime_ref:
            if isinstance(item, tuple) and len(item) == 2 and item[0] == "argument_keys":
                value = cls._normalize_nested_tuple(item[1])
                return value if isinstance(value, tuple) else ()
    return ()

def _impl__unsupported_call_effect_argument_evidence_is_complete(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    if not isinstance(normalized, tuple):
        return False
    if not normalized:
        return True
    return cls._call_effect_argument_keys_are_present(normalized)

def _impl__call_effect_argument_keys_are_present(cls, value: Any) -> bool:
    normalized = cls._normalize_nested_tuple(value)
    if not isinstance(normalized, tuple) or not normalized:
        return False
    for item in normalized:
        if not (
            isinstance(item, tuple)
            and len(item) >= 3
            and item[0] == "argument"
        ):
            return False
        if not cls._call_effect_target_expression_key_is_present(item[2]):
            return False
    return True

def _impl__deferred_call_target_expression_key(cls, object_target_key: Any) -> Any:
    target = cls._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) < 7:
        return None
    return target[6]

def _impl__deferred_call_argument_keys(cls, object_target_key: Any) -> Tuple[Any, ...]:
    target = cls._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) < 8:
        return ()
    value = cls._normalize_nested_tuple(target[7])
    return value if isinstance(value, tuple) else ()

def _impl__cross_binary_call_effect_component_key(cls, value: Any) -> Any:
    normalized = cls._normalize_nested_tuple(value)
    if isinstance(normalized, tuple):
        if normalized and normalized[0] == "parameter" and len(normalized) >= 4:
            if (
                isinstance(normalized[2], tuple)
                and len(normalized[2]) == 2
                and normalized[2][0] == "int"
            ):
                return ("parameter", normalized[2][1])
            return ("parameter", normalized[-1])
        if (
            len(normalized) == 2
            and normalized[0] == "tuple"
            and isinstance(normalized[1], tuple)
            and normalized[1]
            and cls._atom_str_is(normalized[1][0], "parameter")
            and len(normalized[1]) >= 4
        ):
            return ("tuple", (normalized[1][0], normalized[1][-1]))
        if (
            len(normalized) == 2
            and normalized[0] == "tuple"
            and isinstance(normalized[1], tuple)
            and normalized[1]
            and cls._atom_str_is(normalized[1][0], "unknown")
            and len(normalized[1]) >= 2
        ):
            return ("tuple", (normalized[1][0], *normalized[1][2:]))
        return tuple(cls._cross_binary_call_effect_component_key(item) for item in normalized)
    return normalized

def _impl__call_target_is_analysis_entry(
    cls,
    target_key: Any,
    analysis: FunctionReturnAnalysis,
) -> bool:
    if not isinstance(target_key, tuple) or len(target_key) < 3:
        return False
    if target_key[0] != "function":
        return False
    entry_key = cls._analysis_entry_key(analysis)
    if (
        not isinstance(entry_key, tuple)
        or len(entry_key) != 2
        or entry_key[0] != "function_ref"
        or not isinstance(entry_key[1], tuple)
        or len(entry_key[1]) < 3
    ):
        return False
    entry_ref = entry_key[1]
    try:
        return (
            str(target_key[1]) == str(entry_ref[1])
            and target_key[2] is not None
            and entry_ref[2] is not None
            and int(target_key[2]) == int(entry_ref[2])
        )
    except (TypeError, ValueError):
        return False

def _impl__unsupported_call_effect_reason_compatibility_group(cls, reason: Any) -> Tuple[str, ...]:
    reason_text = str(reason)
    for group in cls._UNSUPPORTED_CALL_EFFECT_REASON_COMPATIBILITY_GROUPS:
        if reason_text in group:
            return tuple(sorted(group))
    return (reason_text,)

def _impl__unsupported_call_effect_reason_signature(cls, reason: Any) -> str:
    return "|".join(cls._unsupported_call_effect_reason_compatibility_group(reason))

def _impl__unsupported_call_effect_reason_is_compatible(
    cls,
    left_reason: Any,
    right_reason: Any,
) -> bool:
    return cls._unsupported_call_effect_reason_signature(left_reason) == cls._unsupported_call_effect_reason_signature(
        right_reason
    )

def _impl__call_effect_blocking_object_evidence(
    self,
    blocking_reason: str,
    object_target_key: Optional[Tuple[Any, ...]],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Optional[Dict[str, Any]]:
    if not isinstance(object_target_key, tuple) or not object_target_key:
        return None
    target_kind = object_target_key[0]
    evidence: Dict[str, Any] = {
        "object_derived": True,
        "evidence_version": 1,
        "evidence_kind": "call_effect_summary",
        "blocker_reason": blocking_reason,
        "blocker_reason_kind": self._blocking_reason_kind(blocking_reason),
        "object_target_kind": target_kind,
        "left_function": getattr(analysis1, "function_name", None),
        "right_function": getattr(analysis2, "function_name", None),
    }
    if target_kind == "unsupported_call_effect" and len(object_target_key) >= 7:
        evidence.update(
            {
                "side": object_target_key[1],
                "analysis_key": object_target_key[2],
                "runtime_ref": object_target_key[3],
                "callsite_storage": object_target_key[4],
                "argument_storage": (
                    self._unsupported_call_effect_argument_keys(object_target_key)
                ),
                "effect_ordinal": object_target_key[5],
                "unsupported_reason": object_target_key[6],
                "call_effect_summary_status": object_target_key[6],
            }
        )
    elif target_kind == "call_target_resolution_evidence" and len(object_target_key) >= 9:
        evidence.update(
            {
                "side": object_target_key[1],
                "analysis_key": object_target_key[2],
                "runtime_ref": object_target_key[3],
                "callsite_storage": object_target_key[4],
                "resolution_kind": object_target_key[5],
                "path_conditions": object_target_key[6],
                "target_conditions": object_target_key[7],
                "effect_ordinal": object_target_key[8],
                "call_effect_summary_status": "target_resolution_pending_proof",
            }
        )
    elif target_kind == "call_argument_evidence" and len(object_target_key) >= 8:
        runtime_ref = (
            "runtime_ref",
            "call_argument",
            ("pcode_op_ref", object_target_key[3]),
            ("callee_identity", object_target_key[4]),
        )
        callsite_storage = (
            "callsite_storage",
            "call_argument",
            ("argument_keys", object_target_key[5]),
        )
        evidence.update(
            {
                "side": object_target_key[1],
                "analysis_key": object_target_key[2],
                "runtime_ref": runtime_ref,
                "callee_identity": object_target_key[4],
                "argument_storage": object_target_key[5],
                "coverage_complete": object_target_key[6],
                "recovery_status": object_target_key[7],
                "callsite_storage": callsite_storage,
                "call_effect_summary_status": object_target_key[7],
            }
        )
    elif target_kind == "deferred_call" and len(object_target_key) >= 9:
        evidence.update(
            {
                "side": object_target_key[1],
                "analysis_key": object_target_key[2],
                "deferred_call_site": object_target_key[3],
                "pcode_op_ref": object_target_key[4],
                "callee_identity": object_target_key[5],
                "target_expression": object_target_key[6],
                "argument_storage": object_target_key[7],
                "call_effect_summary_status": object_target_key[8],
            }
        )
    else:
        return None
    return evidence

def _impl__call_effect_summary_proof_is_complete(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> bool:
    from scripts.function_tracer_pcode.authority.domains.call_effect import CALL_EFFECT_REASON_SPECS

    if reason_record.reason_id not in CALL_EFFECT_REASON_SPECS:
        return False
    if reason_record.recovery_proof_kind != UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value:
        return False
    proof_obligation_id = self._normalize_nested_tuple(reason_record.proof_obligation_id)
    if proof_obligation_id is None:
        return False
    return proof_obligation_id in self._completed_call_effect_summary_proof_ids(
        analysis1,
        analysis2,
    )

def _impl__completed_call_effect_summary_proof_ids(
    cls,
    *analyses: FunctionReturnAnalysis,
) -> Tuple[Tuple[Any, ...], ...]:
    proof_ids: List[Tuple[Any, ...]] = []
    for analysis in analyses:
        evidence_records = getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
        for evidence in evidence_records:
            proof_id = cls._call_effect_summary_proof_id_from_evidence(evidence)
            if proof_id is not None:
                proof_ids.append(proof_id)
    return tuple(proof_ids)

def _impl__call_effect_summary_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
    if not cls._evidence_bool(evidence, "object_derived"):
        return None
    if cls._evidence_text(evidence, "status") not in {"complete", "completed", "proven"}:
        return None
    from scripts.function_tracer_pcode.authority.domains.call_effect import CALL_EFFECT_REASON_SPECS

    evidence_reason_id = cls._evidence_text(evidence, "reason_id")
    if evidence_reason_id not in CALL_EFFECT_REASON_SPECS:
        return None
    proof_kind = cls._evidence_text(evidence, "recovery_proof_kind")
    if proof_kind != UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value:
        return None
    proof_stage = cls._evidence_text(evidence, "proof_stage")
    if proof_stage != "object_evidence_collected":
        return None
    evidence_kind = cls._evidence_text(evidence, "evidence_kind")
    if evidence_kind != "call_effect_summary":
        return None
    if cls._evidence_has_any(evidence, cls._COMPLETED_PROOF_BLOCKER_FIELDS):
        return None
    object_target_key = cls._normalize_nested_tuple(cls._evidence_get(evidence, "object_target_key"))
    if not isinstance(object_target_key, tuple):
        return None
    proof_id = build_proof_obligation_id(
        evidence_reason_id,
        proof_stage,
        proof_kind,
        evidence_kind,
        object_target_key,
    )
    provided_id = cls._normalize_nested_tuple(cls._evidence_get(evidence, "proof_obligation_id"))
    if provided_id is None or provided_id != proof_id:
        return None
    if cls._call_effect_summary_proof_content_is_required(object_target_key):
        proof_content = cls._evidence_get(evidence, "proof_content")
        if not cls._call_effect_summary_proof_content_is_complete(
            proof_content,
            object_target_key,
        ):
            return None
    return proof_id

def _impl__call_effect_summary_proof_content_is_required(
    cls,
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not object_target_key:
        return False
    return str(object_target_key[0]) in cls._CALL_EFFECT_PROOF_CONTENT_REQUIRED_OBJECT_KINDS

def _impl__call_effect_summary_proof_content_is_complete(
    cls,
    proof_content: Any,
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not isinstance(proof_content, Mapping):
        return False
    if not cls._evidence_bool(proof_content, "object_derived"):
        return False
    if cls._evidence_text(proof_content, "status") not in {"complete", "completed", "proven"}:
        return False
    if cls._normalize_nested_tuple(proof_content.get("object_target_key")) != object_target_key:
        return False
    if cls._evidence_has_any_recursive(proof_content, cls._COMPLETED_PROOF_BLOCKER_FIELDS):
        return False
    if not cls._evidence_text(proof_content, "proof_rule"):
        return False
    required_sections = (
        "call_effect_summary",
        "runtime_ref",
        "callsite_storage",
    )
    if any(section not in proof_content for section in required_sections):
        return False
    if not cls._call_effect_summary_section_matches(
        proof_content.get("call_effect_summary"),
        object_target_key,
    ):
        return False
    selected_candidate = None
    if str(object_target_key[0]) == "call_effect_blocker":
        selected_candidate = cls._validated_call_effect_blocker_selected_candidate(
            proof_content,
            object_target_key,
        )
        if selected_candidate is None:
            return False
    expected_refs = cls._expected_call_effect_proof_content_refs(
        object_target_key,
        candidate=selected_candidate,
    )
    if expected_refs is None:
        return False
    expected_runtime_ref, expected_callsite_storage = expected_refs
    if not cls._proof_section_payload_matches(
        proof_content.get("runtime_ref"),
        "runtime_ref",
        expected_runtime_ref,
    ):
        return False
    if not cls._proof_section_payload_matches(
        proof_content.get("callsite_storage"),
        "callsite_storage",
        expected_callsite_storage,
    ):
        return False
    if (
        str(object_target_key[0]) == "unsupported_call_effect"
        and not cls._unsupported_call_effect_proof_content_is_complete(
            proof_content,
            object_target_key,
        )
    ):
        return False
    if (
        str(object_target_key[0]) == "deferred_call"
        and not cls._deferred_call_proof_content_is_complete(
            proof_content,
            object_target_key,
        )
    ):
        return False
    if (
        str(object_target_key[0]) == "call_argument_evidence"
        and not cls._call_argument_evidence_phase15_proof_content_is_complete(
            proof_content,
            object_target_key,
        )
    ):
        return False
    return True

def _impl__call_argument_evidence_phase15_proof_content_is_complete(
    cls,
    proof_content: Mapping[str, Any],
    object_target_key: Tuple[Any, ...],
) -> bool:
    """Validate Phase 1.5 obligations for call argument evidence.

    A recovered call argument is not enough to discharge a call/effect
    blocker. The proof must also pin the callee summary, preconditions/ABI
    coercion, and argument provenance to the same object target.
    """

    if cls._evidence_text(proof_content, "proof_rule") not in {
        "call_argument_evidence_phase15_complete",
        "call_effect_object_evidence_complete",
    }:
        return False

    callee_summary = proof_content.get("callee_summary_completion")
    if not cls._call_argument_callee_summary_section_is_complete(
        callee_summary,
        object_target_key,
    ):
        return False

    precondition = proof_content.get("callee_precondition")
    if not cls._call_argument_precondition_section_is_complete(
        precondition,
        object_target_key,
    ):
        return False

    provenance = proof_content.get("argument_value_provenance")
    if not cls._call_argument_value_provenance_section_is_complete(
        provenance,
        object_target_key,
    ):
        return False

    dependency_graph = proof_content.get("proof_dependency_graph")
    if not cls._call_argument_dependency_graph_section_is_complete(
        dependency_graph,
        object_target_key,
    ):
        return False

    bounded_refinement = proof_content.get("bounded_refinement")
    if not cls._call_argument_bounded_refinement_section_is_complete(
        bounded_refinement,
        object_target_key,
    ):
        return False
    if not cls._call_argument_phase15_sections_are_consistent(
        callee_summary,
        bounded_refinement,
    ):
        return False

    return True

def _impl__call_argument_phase15_sections_are_consistent(
    cls,
    callee_summary: Any,
    bounded_refinement: Any,
) -> bool:
    if not isinstance(callee_summary, Mapping) or not isinstance(bounded_refinement, Mapping):
        return False
    bounded_ref = cls._normalize_nested_tuple(
        callee_summary.get("bounded_refinement_evidence_ref")
    )
    bounded_key = cls._normalize_nested_tuple(
        bounded_refinement.get("object_target_key")
    )
    if bounded_ref in {None, ()} or bounded_ref != bounded_key:
        return False
    summary_partition = cls._normalize_nested_tuple(
        callee_summary.get("callee_return_partition_key")
    )
    bounded_partition = cls._normalize_nested_tuple(
        bounded_refinement.get("callee_return_partition_key")
    )
    if summary_partition in {None, ()} or summary_partition != bounded_partition:
        return False
    return True

def _impl__call_argument_callee_summary_section_is_complete(
    cls,
    section: Any,
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not isinstance(section, Mapping):
        return False
    if not cls._completed_proof_section_is_clean(section):
        return False
    if cls._evidence_text(section, "status") not in {"complete", "completed", "proven"}:
        return False
    if cls._normalize_nested_tuple(section.get("object_target_key")) != object_target_key:
        return False
    if cls._normalize_nested_tuple(section.get("callee_identity")) != object_target_key[4]:
        return False
    required_statuses = (
        "return_coverage_status",
        "effect_summary_status",
        "memory_policy_status",
        "unsupported_call_policy_status",
    )
    return all(cls._evidence_text(section, field) == "complete" for field in required_statuses)

def _impl__call_argument_precondition_section_is_complete(
    cls,
    section: Any,
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not isinstance(section, Mapping):
        return False
    if not cls._completed_proof_section_is_clean(section):
        return False
    if cls._evidence_text(section, "status") not in {"complete", "completed", "proven"}:
        return False
    if cls._normalize_nested_tuple(section.get("object_target_key")) != object_target_key:
        return False
    if section.get("caller_guard_implies_callee_precondition") is not True:
        return False
    abi = section.get("abi_coercion")
    if not isinstance(abi, Mapping):
        return False
    if not cls._completed_proof_section_is_clean(abi):
        return False
    if cls._evidence_text(abi, "status") not in {"complete", "completed", "proven"}:
        return False
    required_keys = (
        "argument_widths",
        "sign_zero_extension",
        "abi_narrow_wide_coercion",
        "callee_parameter_interpretation",
    )
    return all(key in abi for key in required_keys)

def _impl__call_argument_value_provenance_section_is_complete(
    cls,
    section: Any,
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not isinstance(section, Mapping):
        return False
    if not cls._completed_proof_section_is_clean(section):
        return False
    if cls._evidence_text(section, "status") not in {"complete", "completed", "proven"}:
        return False
    if cls._normalize_nested_tuple(section.get("object_target_key")) != object_target_key:
        return False
    if cls._normalize_nested_tuple(section.get("argument_keys")) != object_target_key[5]:
        return False
    return bool(section.get("value_provenance_equivalent"))

def _impl__call_argument_dependency_graph_section_is_complete(
    cls,
    section: Any,
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not isinstance(section, Mapping):
        return False
    if not cls._completed_proof_section_is_clean(section):
        return False
    if cls._evidence_text(section, "status") not in {"complete", "completed", "proven"}:
        return False
    if cls._normalize_nested_tuple(section.get("object_target_key")) != object_target_key:
        return False
    return cls._evidence_text(section, "cycle_policy") in {
        "acyclic",
        "fixed_point_proven",
        "induction_proven",
    }

def _impl__call_argument_bounded_refinement_section_is_complete(
    cls,
    section: Any,
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not isinstance(section, Mapping):
        return False
    if not cls._completed_proof_section_is_clean(section):
        return False
    if cls._evidence_text(section, "status") not in {"complete", "completed", "proven"}:
        return False
    if cls._evidence_text(section, "evidence_kind") != "bounded_call_refinement_expansion":
        return False
    if cls._normalize_nested_tuple(section.get("call_argument_object_target_key")) != object_target_key:
        return False
    if cls._normalize_nested_tuple(section.get("callsite_pcode_key")) != object_target_key[3]:
        return False
    if cls._normalize_nested_tuple(section.get("callee_identity")) != object_target_key[4]:
        return False
    if cls._normalize_nested_tuple(section.get("object_target_key")) in {None, ()}:
        return False
    if cls._normalize_nested_tuple(section.get("callee_return_partition_key")) in {None, ()}:
        return False
    if int(section.get("result_count") or 0) <= 0:
        return False
    if section.get("dependency_cycle") is True:
        return False
    if section.get("truncated") is True:
        return False
    if section.get("callee_summary_requires_completed_proof") is True:
        completed_ids = cls._normalize_nested_tuple(section.get("callee_completed_proof_ids"))
        completed_evidence_ids = cls._normalize_nested_tuple(
            section.get("callee_completed_proof_evidence_ids")
        )
        if completed_ids in {None, ()} and completed_evidence_ids in {None, ()}:
            return False
    return True

def _impl__validated_call_effect_blocker_selected_candidate(
    cls,
    proof_content: Mapping[str, Any],
    object_target_key: Tuple[Any, ...],
) -> Optional[Tuple[Any, ...]]:
    selected_candidate = cls._normalize_nested_tuple(
        proof_content.get("selected_candidate_key")
    )
    if not isinstance(selected_candidate, tuple) or not selected_candidate:
        return None
    if not any(
        selected_candidate == candidate
        for candidate in cls._iter_call_effect_blocker_candidates(object_target_key)
    ):
        return None
    selected_kind = str(selected_candidate[0])
    if cls._evidence_text(proof_content, "selected_candidate_kind") != selected_kind:
        return None
    selected_content = proof_content.get("selected_candidate_proof_content")
    if not isinstance(selected_content, Mapping):
        return None
    if not cls._call_effect_summary_proof_content_is_complete(
        selected_content,
        selected_candidate,
    ):
        return None
    return selected_candidate

def _impl__call_effect_summary_section_matches(
    cls,
    section: Any,
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not isinstance(section, Mapping):
        return False
    if not cls._completed_proof_section_is_clean(section):
        return False
    target_kind = str(object_target_key[0]) if object_target_key else ""
    if cls._normalize_nested_tuple(section.get("object_target_key")) != object_target_key:
        return False
    if cls._normalize_nested_tuple(section.get("summary_source")) != (
        "effect_summary",
        target_kind,
    ):
        return False
    if cls._evidence_text(section, "evidence_kind") != "call_effect_summary":
        return False
    return True

def _impl__expected_call_effect_proof_content_refs(
    cls,
    object_target_key: Tuple[Any, ...],
    candidate: Optional[Tuple[Any, ...]] = None,
    default_missing: Optional[Tuple[Any, ...]] = None,
) -> Optional[Tuple[Tuple[Any, ...], Tuple[Any, ...]]]:
    # Keep None as the sentinel for "missing references": callers must guard
    # before unpacking to avoid ValueError on empty tuples.
    target_kind = str(object_target_key[0]) if object_target_key else ""
    if target_kind == "call_argument_evidence":
        if len(object_target_key) < 6:
            return default_missing
        return (
            (
                "runtime_ref",
                "call_argument",
                ("pcode_op_ref", object_target_key[3]),
                ("callee_identity", object_target_key[4]),
            ),
            (
                "callsite_storage",
                "call_argument",
                ("argument_keys", object_target_key[5]),
            ),
        )
    if target_kind == "call_target_resolution_evidence":
        if len(object_target_key) < 5:
            return default_missing
        runtime_ref = cls._normalize_nested_tuple(object_target_key[3])
        callsite_storage = cls._normalize_nested_tuple(object_target_key[4])
        if not isinstance(runtime_ref, tuple) or not isinstance(callsite_storage, tuple):
            return default_missing
        return runtime_ref, callsite_storage
    if target_kind == "unsupported_call_effect":
        if len(object_target_key) < 5:
            return default_missing
        runtime_ref = cls._normalize_nested_tuple(object_target_key[3])
        callsite_storage = cls._normalize_nested_tuple(object_target_key[4])
        if not isinstance(runtime_ref, tuple) or not isinstance(callsite_storage, tuple):
            return default_missing
        return runtime_ref, callsite_storage
    if target_kind == "deferred_call":
        return cls._expected_deferred_call_proof_content_refs(object_target_key)
    if target_kind == "call_effect_blocker":
        if candidate is None:
            candidate = cls._select_call_effect_blocker_candidate(object_target_key)
        if candidate is None:
            return default_missing
        return cls._expected_call_effect_proof_content_refs(
            candidate,
            default_missing=default_missing,
        )
    return None

def _impl__expected_deferred_call_proof_content_refs(
    cls,
    object_target_key: Tuple[Any, ...],
) -> Optional[Tuple[Tuple[Any, ...], Tuple[Any, ...]]]:
    if len(object_target_key) < 8:
        return None
    deferred_call_site = cls._normalize_nested_tuple(object_target_key[3])
    pcode_op_ref = cls._normalize_nested_tuple(object_target_key[4])
    callee_identity = cls._normalize_nested_tuple(object_target_key[5])
    target_expression = cls._normalize_nested_tuple(object_target_key[6])
    argument_keys = cls._normalize_nested_tuple(object_target_key[7])
    if not isinstance(deferred_call_site, tuple):
        return None
    if not isinstance(argument_keys, tuple):
        return None
    return (
        (
            "runtime_ref",
            "deferred_call",
            ("deferred_call_site", deferred_call_site),
            ("pcode_op_ref", pcode_op_ref),
            ("callee_identity", callee_identity),
            ("typed_target_expression", target_expression),
            ("argument_keys", argument_keys),
        ),
        (
            "callsite_storage",
            "deferred_call",
            ("deferred_call_site", deferred_call_site),
            ("pcode_op_ref", pcode_op_ref),
            ("callee_identity", callee_identity),
            ("target_expression", target_expression),
            ("argument_keys", argument_keys),
        ),
    )

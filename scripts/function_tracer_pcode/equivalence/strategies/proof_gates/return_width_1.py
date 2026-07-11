"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.equivalence.strategies.base``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    ExpressionType,
    Mapping,
    ReadonlyReductionRef,
    UnknownReasonId,
    UnknownRecoveryProofKind,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
    expression_contains_unsupported_smt_ops,
    expression_provenance_key,
    expression_smt_bit_width,
    hashlib,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__collect_condition_width_sign_metadata(
    cls,
    condition: Any,
    bit_widths: Set[int],
    signedness: Set[str],
) -> None:
    expr = getattr(condition, "expression", None)
    for node in cls._iter_expression_nodes_for_metadata(expr):
        try:
            bit_width = int(expression_smt_bit_width(node) or 0)
        except (AttributeError, TypeError, ValueError, RecursionError):
            bit_width = 0
        if bit_width > 0:
            bit_widths.add(bit_width)
        operator = getattr(node, "operator", None)
        if operator in {"INT_SLESS", "INT_SLESSEQUAL"}:
            signedness.add("signed")
        elif operator in {"INT_LESS", "INT_LESSEQUAL"}:
            signedness.add("unsigned")
        elif operator in {"INT_EQUAL", "INT_NOTEQUAL"}:
            signedness.add("equality")

def _impl__expression_bit_width_from_object_key(cls, object_key: Any) -> Optional[int]:
    normalized = cls._normalize_nested_tuple(object_key)
    if not isinstance(normalized, tuple):
        return None
    stack = [normalized]
    seen: Set[int] = set()
    while stack:
        current = stack.pop()
        if id(current) in seen:
            continue
        seen.add(id(current))
        if isinstance(current, tuple):
            if len(current) >= 2 and current[0] in {"size", "size_bytes"}:
                try:
                    value = int(current[1])
                except Exception:
                    value = 0
                if current[0] == "size_bytes":
                    value *= 8
                if value > 0:
                    return value
            if len(current) >= 2 and str(current[0]).endswith("bits"):
                try:
                    value = int(current[1])
                except Exception:
                    value = 0
                if value > 0:
                    return value
            stack.extend(reversed(current))
    return None

def _impl__return_width_bridge_proof_is_complete(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    base_ctx: Optional[Mapping[str, Any]] = None,
    wide_param_replace_fn=None,
) -> bool:
    if reason_record.reason_id != UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value:
        return False
    if reason_record.recovery_proof_kind != UnknownRecoveryProofKind.ABI_RELATION_HIGH_BIT_PROOF.value:
        return False
    object_target_key = self._normalize_nested_tuple(reason_record.object_target_key)
    if not self._return_width_bridge_target_is_specific(object_target_key):
        return False
    completed_slots: Dict[Tuple[Any, ...], Mapping[str, Any]] = {}
    for evidence in self._completed_recovery_proof_evidence(analysis1, analysis2):
        slot_id = self._return_width_bridge_slot_id_from_evidence(evidence)
        if slot_id is None:
            continue
        if self._normalize_nested_tuple(self._evidence_get(evidence, "object_target_key")) != object_target_key:
            continue
        if not self._return_width_bridge_slot_evidence_matches_current_analyses(
            evidence,
            analysis1,
            analysis2,
            base_ctx=base_ctx,
            wide_param_replace_fn=wide_param_replace_fn,
        ):
            continue
        completed_slots[slot_id] = evidence
    return all(
        self._return_width_bridge_slot_obligation_id(
            slot_stage,
            object_target_key,
        )
        in completed_slots
        for slot_stage in ("abi_relation", "high_bit_relation")
    )

def _impl__return_width_bridge_slot_obligation_id(
    cls,
    slot_stage: str,
    object_target_key: Tuple[Any, ...],
) -> Optional[Tuple[Any, ...]]:
    slot_info = cls._RETURN_WIDTH_BRIDGE_ACCEPTED_DISCHARGES.get(str(slot_stage))
    if slot_info is None:
        return None
    target = cls._normalize_nested_tuple(object_target_key)
    if not cls._return_width_bridge_target_is_specific(target):
        return None
    return (
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value,
        str(slot_stage),
        str(slot_info["evidence_slot_kind"]),
        target,
    )

def _impl__return_width_bridge_discharge_proof_id(
    cls,
    *,
    slot_stage: str,
    discharge_proof_kind: str,
    evidence_kind: str,
    object_target_key: Tuple[Any, ...],
) -> Optional[Tuple[Any, ...]]:
    target = cls._normalize_nested_tuple(object_target_key)
    if not cls._return_width_bridge_target_is_specific(target):
        return None
    return (
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value,
        str(slot_stage),
        str(discharge_proof_kind),
        str(evidence_kind),
        target,
    )

def _impl__completed_return_width_bridge_slots(
    cls,
    *analyses: FunctionReturnAnalysis,
    object_target_key: Optional[Tuple[Any, ...]] = None,
) -> Dict[Tuple[Any, ...], Mapping[str, Any]]:
    completed: Dict[Tuple[Any, ...], Mapping[str, Any]] = {}
    expected_target = cls._normalize_nested_tuple(object_target_key)
    for evidence in cls._completed_recovery_proof_evidence(*analyses):
        slot_id = cls._return_width_bridge_slot_id_from_evidence(evidence)
        if slot_id is None:
            continue
        target = cls._normalize_nested_tuple(cls._evidence_get(evidence, "object_target_key"))
        if expected_target is not None and target != expected_target:
            continue
        completed[slot_id] = evidence
    return completed

def _impl__set_return_width_bridge_pending_evidence(
    self,
    *,
    object_target_key: Optional[Tuple[Any, ...]],
    subreason: str,
    detail: str,
    pair_id: Optional[str] = None,
    narrow_width: Optional[int] = None,
    query_stage: Optional[str] = None,
    extra: Optional[Mapping[str, Any]] = None,
) -> Dict[str, Any]:
    evidence: Dict[str, Any] = {
        "object_derived": True,
        "status": "pending_proof",
        "reason_id": UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value,
        "subreason": str(subreason),
        "detail": str(detail),
    }
    normalized_target = self._normalize_nested_tuple(object_target_key)
    if normalized_target is not None:
        evidence["object_target_key"] = normalized_target
    if pair_id is not None:
        evidence["pair_id"] = str(pair_id)
    if narrow_width is not None:
        evidence["narrow_width"] = int(narrow_width)
    if query_stage is not None:
        evidence["query_stage"] = str(query_stage)
    if extra:
        evidence.update(dict(extra))
    self._last_return_width_bridge_pending_evidence = evidence
    return evidence

def _impl__record_completed_return_width_bridge_proofs(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    query_stage: str,
    narrow_width: int,
    proof_source: str = "return_width_bridge_narrow_and_high_bit_queries_unsat",
) -> bool:
    if not self.enable_completed_recovery_proofs:
        self._debug_print("  return-width bridge proof record skipped: completed proofs disabled")
        return False
    if reason_record.reason_id != UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value:
        self._debug_print(
            "  return-width bridge proof record skipped: reason id mismatch "
            f"({reason_record.reason_id})"
        )
        return False
    object_target_key = self._normalize_nested_tuple(reason_record.object_target_key)
    if not self._return_width_bridge_target_is_specific(object_target_key):
        self._debug_print("  return-width bridge proof record skipped: weak object target")
        return False
    if self._return_width_bridge_target_narrow_width(object_target_key) != int(narrow_width):
        self._debug_print(
            "  return-width bridge proof record skipped: narrow width mismatch "
            f"({self._return_width_bridge_target_narrow_width(object_target_key)} vs {narrow_width})"
        )
        return False
    actions = tuple(build_unknown_recovery_actions([reason_record]))
    if len(actions) != len(self._RETURN_WIDTH_BRIDGE_ACTION_REQUIREMENTS):
        self._debug_print(
            "  return-width bridge proof record skipped: action count mismatch "
            f"({len(actions)})"
        )
        return False

    records: List[Dict[str, Any]] = [
        dict(item)
        for item in getattr(analysis1, "completed_recovery_proof_evidence", ()) or ()
        if isinstance(item, Mapping)
    ]
    existing_ids = {
        self._normalize_nested_tuple(item.get("proof_obligation_id"))
        for item in records
    }
    changed = False
    for action in actions:
        proof_id = self._normalize_nested_tuple(action.proof_obligation_id)
        if proof_id is None or proof_id in existing_ids:
            continue
        slot_obligation_id = self._return_width_bridge_slot_obligation_id(
            action.proof_stage,
            object_target_key,
        )
        proof_content = self._return_width_bridge_completed_proof_content(
            action.proof_kind,
            object_target_key,
            query_stage=query_stage,
            narrow_width=int(narrow_width),
        )
        if proof_content is None:
            self._debug_print(
                "  return-width bridge proof record skipped: proof content unavailable "
                f"({action.proof_kind})"
            )
            return False
        records.append(
            {
                "object_derived": True,
                "status": "complete",
                "reason_id": UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value,
                "proof_kind": action.proof_kind,
                "recovery_proof_kind": action.proof_kind,
                "proof_stage": action.proof_stage,
                "evidence_kind": action.evidence_kind,
                "required_evidence": tuple(action.required_evidence),
                "object_target_key": object_target_key,
                "proof_obligation_id": proof_id,
                "slot_stage": action.proof_stage,
                "slot_obligation_id": slot_obligation_id,
                "discharge_proof_kind": action.proof_kind,
                "discharge_proof_id": proof_id,
                "proof_source": proof_source,
                "proof_content": proof_content,
            }
        )
        existing_ids.add(proof_id)
        changed = True
    if changed:
        analysis1.completed_recovery_proof_evidence = tuple(records)
    return True

def _impl__record_completed_return_width_bridge_semantic_narrowing_proofs(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    narrow_width: int,
    base_ctx: Optional[Mapping[str, Any]] = None,
    wide_param_replace_fn=None,
) -> bool:
    if not self.enable_completed_recovery_proofs:
        self._debug_print("  return-width bridge semantic narrowing skipped: completed proofs disabled")
        return False
    if reason_record.reason_id != UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value:
        return False
    object_target_key = self._normalize_nested_tuple(reason_record.object_target_key)
    if not self._return_width_bridge_target_is_specific(object_target_key):
        self._debug_print("  return-width bridge semantic narrowing skipped: weak object target")
        return False
    if self._return_width_bridge_target_narrow_width(object_target_key) != int(narrow_width):
        self._debug_print("  return-width bridge semantic narrowing skipped: narrow width mismatch")
        return False

    actions = tuple(build_unknown_recovery_actions([reason_record]))
    action_by_stage = {str(action.proof_stage): action for action in actions}
    abi_action = action_by_stage.get("abi_relation")
    high_bit_action = action_by_stage.get("high_bit_relation")
    if abi_action is None or high_bit_action is None:
        return False

    semantic_content = self._return_width_bridge_semantic_narrowing_proof_content(
        object_target_key,
        analysis1,
        analysis2,
        narrow_width=int(narrow_width),
        base_ctx=base_ctx,
        wide_param_replace_fn=wide_param_replace_fn,
    )
    if semantic_content is None:
        self._set_return_width_bridge_pending_evidence(
            object_target_key=object_target_key,
            subreason="wide_surface_coverage_gap",
            detail="semantic return-width narrowing surface profile unavailable",
            narrow_width=int(narrow_width),
        )
        self._debug_print(
            "  return-width bridge semantic narrowing skipped: surface profile unavailable"
        )
        return False

    records: List[Dict[str, Any]] = [
        dict(item)
        for item in getattr(analysis1, "completed_recovery_proof_evidence", ()) or ()
        if isinstance(item, Mapping)
    ]
    existing_slot_ids = {
        self._normalize_nested_tuple(item.get("slot_obligation_id"))
        for item in records
    }
    existing_proof_ids = {
        self._normalize_nested_tuple(item.get("proof_obligation_id"))
        for item in records
    }
    changed = False

    abi_proof_id = self._normalize_nested_tuple(abi_action.proof_obligation_id)
    abi_slot_id = self._return_width_bridge_slot_obligation_id("abi_relation", object_target_key)
    if abi_proof_id is not None and abi_proof_id not in existing_proof_ids and abi_slot_id not in existing_slot_ids:
        abi_content = self._return_width_bridge_completed_proof_content(
            abi_action.proof_kind,
            object_target_key,
            query_stage="semantic-return-width-narrowing-object-evidence",
            narrow_width=int(narrow_width),
        )
        if abi_content is None:
            return False
        records.append(
            {
                "object_derived": True,
                "status": "complete",
                "reason_id": UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value,
                "proof_kind": abi_action.proof_kind,
                "recovery_proof_kind": abi_action.proof_kind,
                "proof_stage": abi_action.proof_stage,
                "evidence_kind": abi_action.evidence_kind,
                "required_evidence": tuple(abi_action.required_evidence),
                "object_target_key": object_target_key,
                "proof_obligation_id": abi_proof_id,
                "slot_stage": abi_action.proof_stage,
                "slot_obligation_id": abi_slot_id,
                "discharge_proof_kind": abi_action.proof_kind,
                "discharge_proof_id": abi_proof_id,
                "proof_source": self._RETURN_WIDTH_BRIDGE_SEMANTIC_NARROWING_SOURCE,
                "proof_content": abi_content,
            }
        )
        existing_slot_ids.add(abi_slot_id)
        existing_proof_ids.add(abi_proof_id)
        changed = True

    semantic_slot_id = self._return_width_bridge_slot_obligation_id(
        "high_bit_relation",
        object_target_key,
    )
    semantic_proof_id = self._return_width_bridge_discharge_proof_id(
        slot_stage="high_bit_relation",
        discharge_proof_kind="semantic_return_width_narrowing_proof",
        evidence_kind="producer_width",
        object_target_key=object_target_key,
    )
    if semantic_slot_id is not None and semantic_slot_id not in existing_slot_ids:
        records.append(
            {
                "object_derived": True,
                "status": "complete",
                "reason_id": UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value,
                "proof_kind": "semantic_return_width_narrowing_proof",
                "recovery_proof_kind": "semantic_return_width_narrowing_proof",
                "proof_stage": "high_bit_relation",
                "slot_stage": "high_bit_relation",
                "evidence_kind": "producer_width",
                "required_evidence": (
                    "wide_return_surface",
                    "return_type_provenance",
                    "partition_member_coverage",
                ),
                "object_target_key": object_target_key,
                "proof_obligation_id": semantic_slot_id,
                "slot_obligation_id": semantic_slot_id,
                "discharge_proof_kind": "semantic_return_width_narrowing_proof",
                "discharge_proof_id": semantic_proof_id,
                "discharges_action_proof_kind": high_bit_action.proof_kind,
                "proof_source": self._RETURN_WIDTH_BRIDGE_SEMANTIC_NARROWING_SOURCE,
                "proof_content": semantic_content,
            }
        )
        changed = True

    if changed:
        analysis1.completed_recovery_proof_evidence = tuple(records)
    return True

def _impl__record_completed_return_width_bridge_member_narrow_producer_proofs(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    narrow_width: int,
) -> bool:
    if not self.enable_completed_recovery_proofs:
        self._debug_print("  return-width bridge member producer proof skipped: completed proofs disabled")
        return False
    if reason_record.reason_id != UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value:
        return False
    object_target_key = self._normalize_nested_tuple(reason_record.object_target_key)
    if not self._return_width_bridge_target_is_specific(object_target_key):
        self._debug_print("  return-width bridge member producer proof skipped: weak object target")
        return False
    if self._return_width_bridge_target_narrow_width(object_target_key) != int(narrow_width):
        self._debug_print("  return-width bridge member producer proof skipped: narrow width mismatch")
        return False

    actions = tuple(build_unknown_recovery_actions([reason_record]))
    action_by_stage = {str(action.proof_stage): action for action in actions}
    abi_action = action_by_stage.get("abi_relation")
    high_bit_action = action_by_stage.get("high_bit_relation")
    if abi_action is None or high_bit_action is None:
        return False

    member_content = self._return_width_bridge_member_narrow_producer_proof_content(
        object_target_key,
        analysis1,
        analysis2,
        narrow_width=int(narrow_width),
    )
    if member_content is None:
        self._debug_print(
            "  return-width bridge member producer proof skipped: target member profile unavailable"
        )
        return False

    records: List[Dict[str, Any]] = [
        dict(item)
        for item in getattr(analysis1, "completed_recovery_proof_evidence", ()) or ()
        if isinstance(item, Mapping)
    ]
    existing_slot_ids = {
        self._normalize_nested_tuple(item.get("slot_obligation_id"))
        for item in records
    }
    existing_proof_ids = {
        self._normalize_nested_tuple(item.get("proof_obligation_id"))
        for item in records
    }
    changed = False

    abi_proof_id = self._normalize_nested_tuple(abi_action.proof_obligation_id)
    abi_slot_id = self._return_width_bridge_slot_obligation_id("abi_relation", object_target_key)
    if abi_proof_id is not None and abi_proof_id not in existing_proof_ids and abi_slot_id not in existing_slot_ids:
        abi_content = self._return_width_bridge_completed_proof_content(
            abi_action.proof_kind,
            object_target_key,
            query_stage="return-member-narrow-producer-object-evidence",
            narrow_width=int(narrow_width),
        )
        if abi_content is None:
            return False
        records.append(
            {
                "object_derived": True,
                "status": "complete",
                "reason_id": UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value,
                "proof_kind": abi_action.proof_kind,
                "recovery_proof_kind": abi_action.proof_kind,
                "proof_stage": abi_action.proof_stage,
                "evidence_kind": abi_action.evidence_kind,
                "required_evidence": tuple(abi_action.required_evidence),
                "object_target_key": object_target_key,
                "proof_obligation_id": abi_proof_id,
                "slot_stage": abi_action.proof_stage,
                "slot_obligation_id": abi_slot_id,
                "discharge_proof_kind": abi_action.proof_kind,
                "discharge_proof_id": abi_proof_id,
                "proof_source": self._RETURN_WIDTH_BRIDGE_MEMBER_NARROW_PRODUCER_SOURCE,
                "proof_content": abi_content,
            }
        )
        existing_slot_ids.add(abi_slot_id)
        existing_proof_ids.add(abi_proof_id)
        changed = True

    member_slot_id = self._return_width_bridge_slot_obligation_id(
        "high_bit_relation",
        object_target_key,
    )
    member_proof_id = self._return_width_bridge_discharge_proof_id(
        slot_stage="high_bit_relation",
        discharge_proof_kind="return_member_narrow_producer_high_bit_proof",
        evidence_kind="producer_width",
        object_target_key=object_target_key,
    )
    if member_slot_id is not None and member_slot_id not in existing_slot_ids:
        records.append(
            {
                "object_derived": True,
                "status": "complete",
                "reason_id": UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value,
                "subreason": "completed_member_narrow_producer_high_bit_proof",
                "result": "completed",
                "proof_kind": "return_member_narrow_producer_high_bit_proof",
                "recovery_proof_kind": "return_member_narrow_producer_high_bit_proof",
                "proof_stage": "high_bit_relation",
                "slot_stage": "high_bit_relation",
                "evidence_kind": "producer_width",
                "required_evidence": (
                    "target_return_member",
                    "producer_width",
                    "return_type_provenance",
                ),
                "object_target_key": object_target_key,
                "proof_obligation_id": member_slot_id,
                "slot_obligation_id": member_slot_id,
                "discharge_proof_kind": "return_member_narrow_producer_high_bit_proof",
                "discharge_proof_id": member_proof_id,
                "discharges_action_proof_kind": high_bit_action.proof_kind,
                "proof_source": self._RETURN_WIDTH_BRIDGE_MEMBER_NARROW_PRODUCER_SOURCE,
                "proof_content": member_content,
            }
        )
        changed = True

    if changed:
        analysis1.completed_recovery_proof_evidence = tuple(records)
    return True

def _impl__return_width_bridge_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
    if not cls._evidence_bool(evidence, "object_derived"):
        return None
    if cls._evidence_text(evidence, "status") not in {"complete", "completed", "proven"}:
        return None
    if cls._evidence_text(evidence, "reason_id") != UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value:
        return None
    proof_kind = cls._evidence_text(evidence, "proof_kind") or cls._evidence_text(
        evidence,
        "recovery_proof_kind",
    )
    proof_stage = cls._evidence_text(evidence, "proof_stage")
    requirement = cls._RETURN_WIDTH_BRIDGE_ACTION_REQUIREMENTS.get((proof_kind, proof_stage))
    if requirement is None:
        return None
    expected_evidence_kind, expected_required = requirement
    evidence_kind = cls._evidence_text(evidence, "evidence_kind")
    if evidence_kind != expected_evidence_kind:
        return None
    required_evidence = tuple(
        str(item)
        for item in (cls._evidence_get(evidence, "required_evidence") or ())
    )
    if required_evidence != tuple(expected_required):
        return None
    proof_source = cls._evidence_text(evidence, "proof_source")
    if proof_source not in {
        "return_width_bridge_narrow_and_high_bit_queries_unsat",
        "return_width_bridge_narrow_query_unsat_and_summary_parameter_extension",
        cls._RETURN_WIDTH_BRIDGE_SEMANTIC_NARROWING_SOURCE,
        cls._RETURN_WIDTH_BRIDGE_MEMBER_NARROW_PRODUCER_SOURCE,
    }:
        return None
    if cls._evidence_has_any(evidence, cls._COMPLETED_PROOF_BLOCKER_FIELDS):
        return None
    object_target_key = cls._normalize_nested_tuple(cls._evidence_get(evidence, "object_target_key"))
    if not cls._return_width_bridge_target_is_specific(object_target_key):
        return None
    proof_id = build_proof_obligation_id(
        UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value,
        proof_stage,
        proof_kind,
        evidence_kind,
        object_target_key,
    )
    provided_id = cls._normalize_nested_tuple(cls._evidence_get(evidence, "proof_obligation_id"))
    if provided_id is None or provided_id != proof_id:
        return None
    proof_content = cls._evidence_get(evidence, "proof_content")
    if not isinstance(proof_content, Mapping):
        return None
    if cls._evidence_has_any_recursive(proof_content, cls._COMPLETED_PROOF_BLOCKER_FIELDS):
        return None
    if proof_kind == "abi_relation_proof":
        if not cls._return_width_bridge_abi_relation_proof_content_is_complete(
            proof_content,
            object_target_key,
        ):
            return None
    elif proof_kind == "high_bit_proof":
        if not cls._return_width_bridge_high_bit_proof_content_is_complete(
            proof_content,
            object_target_key,
        ):
            return None
        if not cls._return_width_bridge_high_bit_proof_source_matches_content(
            proof_source,
            proof_content,
            object_target_key,
        ):
            return None
    else:
        return None
    return proof_id

def _impl__return_width_bridge_slot_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
    if not cls._evidence_bool(evidence, "object_derived"):
        return None
    if cls._evidence_text(evidence, "status") not in {"complete", "completed", "proven"}:
        return None
    if cls._evidence_text(evidence, "reason_id") != UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value:
        return None
    object_target_key = cls._normalize_nested_tuple(cls._evidence_get(evidence, "object_target_key"))
    if not cls._return_width_bridge_target_is_specific(object_target_key):
        return None

    slot_stage = cls._evidence_text(evidence, "slot_stage") or cls._evidence_text(
        evidence,
        "proof_stage",
    )
    slot_info = cls._RETURN_WIDTH_BRIDGE_ACCEPTED_DISCHARGES.get(slot_stage)
    if slot_info is None:
        return None
    discharge_kind = cls._evidence_text(evidence, "discharge_proof_kind") or cls._evidence_text(
        evidence,
        "proof_kind",
    ) or cls._evidence_text(evidence, "recovery_proof_kind")
    if discharge_kind not in slot_info["accepted_discharge_proof_kinds"]:
        return None

    slot_obligation_id = cls._return_width_bridge_slot_obligation_id(
        slot_stage,
        object_target_key,
    )
    provided_slot_id = cls._normalize_nested_tuple(
        cls._evidence_get(evidence, "slot_obligation_id")
    )
    if provided_slot_id is not None and provided_slot_id != slot_obligation_id:
        return None

    if discharge_kind == "semantic_return_width_narrowing_proof":
        if cls._evidence_text(evidence, "proof_source") != cls._RETURN_WIDTH_BRIDGE_SEMANTIC_NARROWING_SOURCE:
            return None
        discharge_proof_id = cls._return_width_bridge_discharge_proof_id(
            slot_stage=slot_stage,
            discharge_proof_kind=discharge_kind,
            evidence_kind=cls._evidence_text(evidence, "evidence_kind"),
            object_target_key=object_target_key,
        )
        provided_discharge_id = cls._normalize_nested_tuple(
            cls._evidence_get(evidence, "discharge_proof_id")
        )
        if provided_discharge_id != discharge_proof_id:
            return None
        proof_content = cls._evidence_get(evidence, "proof_content")
        if not cls._return_width_bridge_semantic_narrowing_content_is_complete(
            proof_content,
            object_target_key,
        ):
            return None
        return slot_obligation_id
    if discharge_kind == "return_member_narrow_producer_high_bit_proof":
        if cls._evidence_text(evidence, "proof_source") != cls._RETURN_WIDTH_BRIDGE_MEMBER_NARROW_PRODUCER_SOURCE:
            return None
        discharge_proof_id = cls._return_width_bridge_discharge_proof_id(
            slot_stage=slot_stage,
            discharge_proof_kind=discharge_kind,
            evidence_kind=cls._evidence_text(evidence, "evidence_kind"),
            object_target_key=object_target_key,
        )
        provided_discharge_id = cls._normalize_nested_tuple(
            cls._evidence_get(evidence, "discharge_proof_id")
        )
        if provided_discharge_id != discharge_proof_id:
            return None
        proof_content = cls._evidence_get(evidence, "proof_content")
        if not cls._return_width_bridge_member_narrow_producer_content_is_complete(
            proof_content,
            object_target_key,
        ):
            return None
        return slot_obligation_id

    proof_id = cls._return_width_bridge_proof_id_from_evidence(evidence)
    if proof_id is None:
        return None
    return slot_obligation_id

def _impl__return_width_bridge_completed_proof_content(
    cls,
    proof_kind: str,
    object_target_key: Tuple[Any, ...],
    *,
    query_stage: str,
    narrow_width: int,
) -> Optional[Dict[str, Any]]:
    if not cls._return_width_bridge_target_is_specific(object_target_key):
        return None
    widths = cls._return_width_bridge_target_widths(object_target_key)
    left = cls._return_width_bridge_find_side(object_target_key, "left")
    right = cls._return_width_bridge_find_side(object_target_key, "right")
    if widths is None or left is None or right is None:
        return None
    wide_width = max(widths)
    value_width_evidence = cls._return_width_bridge_value_width_evidence(object_target_key)
    left_extension_policy = cls._return_width_bridge_extension_policy_for_side(left)
    right_extension_policy = cls._return_width_bridge_extension_policy_for_side(right)
    if proof_kind == "abi_relation_proof":
        return {
            "object_derived": True,
            "status": "proven",
            "object_target_key": object_target_key,
            "calling_convention": {
                "object_derived": True,
                "status": "proven",
                "left_function_ref": cls._return_width_bridge_find_tagged_entry(left, "function_ref"),
                "right_function_ref": cls._return_width_bridge_find_tagged_entry(right, "function_ref"),
                "relation": "same_return_abi_family",
            },
            "return_storage": {
                "object_derived": True,
                "status": "proven",
                "left_return_storage": cls._return_width_bridge_find_tagged_entry(left, "return_storage"),
                "right_return_storage": cls._return_width_bridge_find_tagged_entry(right, "return_storage"),
                "relation": "abi_related_return_storage",
            },
            "narrow_return_width": {
                "object_derived": True,
                "status": "proven",
                "narrow_width": int(narrow_width),
                "proven": True,
            },
        }
    if proof_kind == "high_bit_proof":
        if value_width_evidence is None or left_extension_policy is None or right_extension_policy is None:
            return None
        left_extension_evidence = cls._return_width_bridge_extension_evidence_for_side(left)
        right_extension_evidence = cls._return_width_bridge_extension_evidence_for_side(right)
        if left_extension_evidence is None or right_extension_evidence is None:
            return None
        left_extension_ops, left_summary_extension, left_literal_extension = left_extension_evidence
        right_extension_ops, right_summary_extension, right_literal_extension = right_extension_evidence
        query_stage_text = str(query_stage)
        has_summary_extension = bool(left_summary_extension or right_summary_extension)
        if query_stage_text == "return-width-bridge-high-bit-extension":
            if has_summary_extension:
                return None
            high_bit_proof = "high_bits_do_not_affect_compared_return"
        elif query_stage_text == "summary-parameter-extension-object-evidence":
            if not has_summary_extension:
                return None
            high_bit_proof = "summary_parameter_high_bits_follow_return_abi_extension"
        else:
            return None
        return {
            "object_derived": True,
            "status": "proven",
            "object_target_key": object_target_key,
            "producer_width": {
                "object_derived": True,
                "status": "proven",
                "left_width": widths[0],
                "right_width": widths[1],
                "value_width_evidence": value_width_evidence,
            },
            "extension_semantics": {
                "object_derived": True,
                "status": "proven",
                "left_extension": left_extension_policy,
                "right_extension": right_extension_policy,
                "left_extension_ops": left_extension_ops,
                "right_extension_ops": right_extension_ops,
                "left_summary_parameter_extension": left_summary_extension,
                "right_summary_parameter_extension": right_summary_extension,
                "left_constant_literal_extension": left_literal_extension,
                "right_constant_literal_extension": right_literal_extension,
                "relation": "compatible_under_narrow_width",
            },
            "high_bits_irrelevant_or_equal": {
                "object_derived": True,
                "status": "proven",
                "narrow_width": int(narrow_width),
                "wide_width": wide_width,
                "proof": high_bit_proof,
                "proven": True,
                "query_stage": str(query_stage),
            },
        }
    return None

def _impl__return_width_bridge_abi_relation_proof_content_is_complete(
    cls,
    content: Mapping[str, Any],
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not cls._return_width_bridge_common_proof_content_is_complete(content, object_target_key):
        return False
    left = cls._return_width_bridge_find_side(object_target_key, "left")
    right = cls._return_width_bridge_find_side(object_target_key, "right")
    if left is None or right is None:
        return False
    calling_convention = content.get("calling_convention")
    return_storage = content.get("return_storage")
    narrow_return_width = content.get("narrow_return_width")
    if not (
        isinstance(calling_convention, Mapping)
        and calling_convention.get("object_derived") is True
        and calling_convention.get("status") == "proven"
        and cls._normalize_nested_tuple(calling_convention.get("left_function_ref"))
        == cls._return_width_bridge_find_tagged_entry(left, "function_ref")
        and cls._normalize_nested_tuple(calling_convention.get("right_function_ref"))
        == cls._return_width_bridge_find_tagged_entry(right, "function_ref")
        and calling_convention.get("relation") == "same_return_abi_family"
    ):
        return False
    if not (
        isinstance(return_storage, Mapping)
        and return_storage.get("object_derived") is True
        and return_storage.get("status") == "proven"
        and cls._normalize_nested_tuple(return_storage.get("left_return_storage"))
        == cls._return_width_bridge_find_tagged_entry(left, "return_storage")
        and cls._normalize_nested_tuple(return_storage.get("right_return_storage"))
        == cls._return_width_bridge_find_tagged_entry(right, "return_storage")
        and return_storage.get("relation") == "abi_related_return_storage"
    ):
        return False
    narrow_width = cls._return_width_bridge_target_narrow_width(object_target_key)
    return (
        isinstance(narrow_return_width, Mapping)
        and narrow_return_width.get("object_derived") is True
        and narrow_return_width.get("status") == "proven"
        and narrow_return_width.get("proven") is True
        and narrow_return_width.get("narrow_width") == narrow_width
    )

def _impl__return_width_bridge_high_bit_proof_content_is_complete(
    cls,
    content: Mapping[str, Any],
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not cls._return_width_bridge_common_proof_content_is_complete(content, object_target_key):
        return False
    widths = cls._return_width_bridge_target_widths(object_target_key)
    if widths is None:
        return False
    narrow_width = min(widths)
    wide_width = max(widths)
    producer_width = content.get("producer_width")
    extension_semantics = content.get("extension_semantics")
    high_bits = content.get("high_bits_irrelevant_or_equal")
    value_width_evidence = cls._return_width_bridge_value_width_evidence(object_target_key)
    if value_width_evidence is None:
        return False
    left_policy = cls._return_width_bridge_extension_policy_for_side(
        cls._return_width_bridge_find_side(object_target_key, "left")
    )
    right_policy = cls._return_width_bridge_extension_policy_for_side(
        cls._return_width_bridge_find_side(object_target_key, "right")
    )
    if left_policy is None or right_policy is None:
        return False
    left = cls._return_width_bridge_find_side(object_target_key, "left")
    right = cls._return_width_bridge_find_side(object_target_key, "right")
    if left is None or right is None:
        return False
    left_extension_evidence = cls._return_width_bridge_extension_evidence_for_side(left)
    right_extension_evidence = cls._return_width_bridge_extension_evidence_for_side(right)
    if left_extension_evidence is None or right_extension_evidence is None:
        return False
    left_extension_ops, left_summary_extension, left_literal_extension = left_extension_evidence
    right_extension_ops, right_summary_extension, right_literal_extension = right_extension_evidence
    if not (
        isinstance(producer_width, Mapping)
        and producer_width.get("object_derived") is True
        and producer_width.get("status") == "proven"
        and producer_width.get("left_width") == widths[0]
        and producer_width.get("right_width") == widths[1]
        and cls._normalize_nested_tuple(producer_width.get("value_width_evidence"))
        == value_width_evidence
    ):
        return False
    if not (
        isinstance(extension_semantics, Mapping)
        and extension_semantics.get("object_derived") is True
        and extension_semantics.get("status") == "proven"
        and extension_semantics.get("left_extension") == left_policy
        and extension_semantics.get("right_extension") == right_policy
        and cls._normalize_nested_tuple(extension_semantics.get("left_extension_ops"))
        == left_extension_ops
        and cls._normalize_nested_tuple(extension_semantics.get("right_extension_ops"))
        == right_extension_ops
        and cls._return_width_bridge_normalize_optional_tuple(
            extension_semantics.get("left_summary_parameter_extension")
        )
        == left_summary_extension
        and cls._return_width_bridge_normalize_optional_tuple(
            extension_semantics.get("right_summary_parameter_extension")
        )
        == right_summary_extension
        and cls._return_width_bridge_normalize_optional_tuple(
            extension_semantics.get("left_constant_literal_extension")
        )
        == left_literal_extension
        and cls._return_width_bridge_normalize_optional_tuple(
            extension_semantics.get("right_constant_literal_extension")
        )
        == right_literal_extension
        and extension_semantics.get("relation") == "compatible_under_narrow_width"
    ):
        return False
    high_bit_complete = (
        isinstance(high_bits, Mapping)
        and high_bits.get("object_derived") is True
        and high_bits.get("status") == "proven"
        and high_bits.get("proven") is True
        and high_bits.get("narrow_width") == narrow_width
        and high_bits.get("wide_width") == wide_width
    )
    if not high_bit_complete:
        return False
    proof = high_bits.get("proof")
    query_stage = high_bits.get("query_stage")
    if proof == "high_bits_do_not_affect_compared_return":
        return (
            query_stage == "return-width-bridge-high-bit-extension"
            and not bool(left_summary_extension or right_summary_extension)
        )
    if proof == "summary_parameter_high_bits_follow_return_abi_extension":
        if query_stage != "summary-parameter-extension-object-evidence":
            return False
        return bool(left_summary_extension or right_summary_extension)
    return False

def _impl__return_width_bridge_high_bit_proof_source_matches_content(
    cls,
    proof_source: str,
    content: Mapping[str, Any],
    object_target_key: Tuple[Any, ...],
) -> bool:
    high_bits = content.get("high_bits_irrelevant_or_equal")
    if not isinstance(high_bits, Mapping):
        return False
    proof = high_bits.get("proof")
    query_stage = high_bits.get("query_stage")
    left = cls._return_width_bridge_find_side(object_target_key, "left")
    right = cls._return_width_bridge_find_side(object_target_key, "right")
    has_summary_extension = any(
        cls._return_width_bridge_summary_parameter_extension_for_side(side) is not None
        for side in (left, right)
        if side is not None
    )
    if proof_source == "return_width_bridge_narrow_and_high_bit_queries_unsat":
        return (
            proof == "high_bits_do_not_affect_compared_return"
            and query_stage == "return-width-bridge-high-bit-extension"
            and not has_summary_extension
        )
    if proof_source == "return_width_bridge_narrow_query_unsat_and_summary_parameter_extension":
        return (
            proof == "summary_parameter_high_bits_follow_return_abi_extension"
            and query_stage == "summary-parameter-extension-object-evidence"
            and has_summary_extension
        )
    return False

def _impl__return_width_bridge_slot_evidence_matches_current_analyses(
    self,
    evidence: Mapping[str, Any],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    base_ctx: Optional[Mapping[str, Any]] = None,
    wide_param_replace_fn=None,
) -> bool:
    discharge_kind = self._evidence_text(evidence, "discharge_proof_kind") or self._evidence_text(
        evidence,
        "proof_kind",
    )
    if discharge_kind not in {
        "semantic_return_width_narrowing_proof",
        "return_member_narrow_producer_high_bit_proof",
    }:
        return True
    object_target_key = self._normalize_nested_tuple(self._evidence_get(evidence, "object_target_key"))
    narrow_width = self._return_width_bridge_target_narrow_width(object_target_key)
    if narrow_width is None:
        return False
    provided_content = self._evidence_get(evidence, "proof_content")
    if not isinstance(provided_content, Mapping):
        return False
    if discharge_kind == "return_member_narrow_producer_high_bit_proof":
        current_content = self._return_width_bridge_member_narrow_producer_proof_content(
            object_target_key,
            analysis1,
            analysis2,
            narrow_width=int(narrow_width),
        )
        return (
            current_content is not None
            and self._return_width_bridge_member_narrow_producer_content_fingerprint(
                provided_content
            )
            == self._return_width_bridge_member_narrow_producer_content_fingerprint(
                current_content
            )
        )
    current_content = self._return_width_bridge_semantic_narrowing_proof_content(
        object_target_key,
        analysis1,
        analysis2,
        narrow_width=int(narrow_width),
        base_ctx=base_ctx,
        wide_param_replace_fn=wide_param_replace_fn,
    )
    if current_content is None and base_ctx is None and wide_param_replace_fn is None:
        provided_profile = provided_content.get("wide_surface_profile")
        if (
            isinstance(provided_profile, Mapping)
            and provided_profile.get("coverage_status") == "total_under_comparison_precondition"
            and provided_profile.get("coverage_identity_digest") is not None
        ):
            current_content = self._return_width_bridge_semantic_narrowing_proof_content(
                object_target_key,
                analysis1,
                analysis2,
                narrow_width=int(narrow_width),
                assume_total_coverage=True,
            )
    if current_content is None:
        return False
    return (
        self._normalize_nested_tuple(provided_content.get("wide_surface_profile"))
        == self._normalize_nested_tuple(current_content.get("wide_surface_profile"))
    )

def _impl__return_width_bridge_semantic_narrowing_proof_content(
    self,
    object_target_key: Tuple[Any, ...],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    narrow_width: int,
    base_ctx: Optional[Mapping[str, Any]] = None,
    wide_param_replace_fn=None,
    assume_total_coverage: bool = False,
) -> Optional[Dict[str, Any]]:
    target = self._normalize_nested_tuple(object_target_key)
    widths = self._return_width_bridge_target_widths(target)
    if widths is None or widths[0] == widths[1]:
        return None
    if widths[0] > widths[1]:
        wide_side_label = "left"
        wide_analysis = analysis1
        counterpart_analysis = analysis2
        wide_return_bits = widths[0]
    else:
        wide_side_label = "right"
        wide_analysis = analysis2
        counterpart_analysis = analysis1
        wide_return_bits = widths[1]
    wide_side = self._return_width_bridge_find_side(target, wide_side_label)
    if wide_side is None:
        return None
    if self._return_width_bridge_find_tagged_entry(wide_side, "function_ref") != self._analysis_entry_key(wide_analysis):
        return None
    if self._return_width_bridge_find_tagged_entry(wide_side, "return_storage") != self._return_storage_object_key(wide_analysis):
        return None
    wide_member = self._normalize_nested_tuple(
        self._return_width_bridge_find_tagged_entry(
            wide_side,
            "return_case_partition_member",
        )
    )
    if wide_member is None:
        return None

    profile = self._return_width_bridge_wide_surface_profile(
        wide_analysis,
        counterpart_analysis,
        wide_return_bits=wide_return_bits,
        narrow_width=int(narrow_width),
        base_ctx=base_ctx,
        wide_param_replace_fn=wide_param_replace_fn,
        assume_total_coverage=assume_total_coverage,
    )
    if profile is None:
        return None
    if wide_member not in set(
        self._normalize_nested_tuple(profile.get("required_wide_members") or ())
    ):
        return None
    return {
        "object_derived": True,
        "status": "proven",
        "object_target_key": target,
        "semantic_return_width": {
            "object_derived": True,
            "status": "proven",
            "narrow_width": int(narrow_width),
            "wide_width": int(wide_return_bits),
            "relation": "wide_storage_semantic_surface_is_narrow",
            "proven": True,
        },
        "wide_surface_profile": profile,
    }

def _impl__return_width_bridge_member_narrow_producer_proof_content(
    self,
    object_target_key: Tuple[Any, ...],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    narrow_width: int,
) -> Optional[Dict[str, Any]]:
    target = self._normalize_nested_tuple(object_target_key)
    widths = self._return_width_bridge_target_widths(target)
    if widths is None or widths[0] == widths[1]:
        return None
    if widths[0] > widths[1]:
        wide_side_label = "left"
        wide_analysis = analysis1
        counterpart_analysis = analysis2
        wide_return_bits = widths[0]
    else:
        wide_side_label = "right"
        wide_analysis = analysis2
        counterpart_analysis = analysis1
        wide_return_bits = widths[1]
    wide_side = self._return_width_bridge_find_side(target, wide_side_label)
    if wide_side is None:
        return None
    if self._return_width_bridge_find_tagged_entry(wide_side, "function_ref") != self._analysis_entry_key(wide_analysis):
        return None
    if self._return_width_bridge_find_tagged_entry(wide_side, "return_storage") != self._return_storage_object_key(wide_analysis):
        return None
    target_member = self._normalize_nested_tuple(
        self._return_width_bridge_find_tagged_entry(
            wide_side,
            "return_case_partition_member",
        )
    )
    if target_member is None:
        return None

    type_provenance = self._return_width_bridge_return_type_provenance(
        wide_analysis,
        counterpart_analysis,
        narrow_width=int(narrow_width),
    )
    if type_provenance is None:
        self._set_return_width_bridge_pending_evidence(
            object_target_key=target,
            subreason="return_type_provenance_unavailable",
            detail="return type provenance unavailable",
            narrow_width=int(narrow_width),
        )
        self._debug_print(
            "  return-width bridge member producer proof rejected: "
            "return type provenance unavailable"
        )
        return None
    global_narrowing_allowed = type_provenance.get("narrowing_allowed") is True

    try:
        from ..pairwise_query_builder import extract_return_cases
    except Exception:
        return None
    try:
        cases = extract_return_cases(wide_analysis, getattr(self, "normalization_settings", None))
    except Exception:
        return None

    matched_case = None
    matched_return_info = None
    for case in cases or ():
        return_info = getattr(case, "return_info", None)
        member = self._normalize_nested_tuple(
            self._return_case_partition_member_object_key(case, return_info)
        )
        if member == target_member:
            matched_case = case
            matched_return_info = return_info
            break
    if matched_case is None:
        self._set_return_width_bridge_pending_evidence(
            object_target_key=target,
            subreason="target_member_profile_unavailable",
            detail="target return partition member was not found in current return cases",
            narrow_width=int(narrow_width),
        )
        self._debug_print(
            "  return-width bridge member producer proof rejected: "
            "subreason=target_member_profile_unavailable target member not found"
        )
        return None

    width_entry = self._normalize_nested_tuple(
        self._return_width_bridge_return_value_width_object_key(
            matched_case,
            matched_return_info,
            int(wide_return_bits),
        )
    )
    producer_width = self._coerce_return_width(
        width_entry[1] if isinstance(width_entry, tuple) and len(width_entry) > 1 else None
    )
    if producer_width is None:
        self._set_return_width_bridge_pending_evidence(
            object_target_key=target,
            subreason="target_member_profile_unavailable",
            detail="target return member producer width unavailable",
            narrow_width=int(narrow_width),
            extra={"required_wide_member": target_member},
        )
        self._debug_print(
            "  return-width bridge member producer proof rejected: "
            "subreason=target_member_profile_unavailable producer width unavailable"
        )
        return None
    expr_profile = self._return_width_bridge_expression_producer_profile(
        getattr(matched_case, "value_expr", None),
        narrow_width=int(narrow_width),
    )
    effective_producer_width = int(producer_width)
    if (
        effective_producer_width > int(narrow_width)
        and expr_profile["wide_producer_is_materially_narrow_constant"]
    ):
        effective_producer_width = int(narrow_width)
    if (
        effective_producer_width > int(narrow_width)
        and expr_profile.get("wide_producer_is_semantically_narrow_runtime_ref") is True
        and expr_profile.get("semantic_narrow_runtime_ref_key") is not None
    ):
        effective_producer_width = int(narrow_width)
    rejection_reasons = list(expr_profile["rejection_reasons"])
    if (
        int(producer_width) > int(narrow_width)
        and not expr_profile["wide_producer_is_materially_narrow_constant"]
        and expr_profile.get("wide_producer_is_semantically_narrow_runtime_ref") is not True
    ):
        rejection_reasons.append("producer_width_exceeds_narrow_width")
    if expr_profile["unsupported_or_unresolved"]:
        rejection_reasons.append("unsupported_or_unresolved_producer")
    if effective_producer_width <= 0 or effective_producer_width > int(narrow_width):
        rejection_reasons.append("effective_producer_width_not_narrow")
    if rejection_reasons:
        subreason = (
            "member_producer_has_unresolved_or_wide_effect"
            if any(
                reason
                in {
                    "unsupported_or_unresolved_producer",
                    "unsupported_expression",
                    "unresolved_producer",
                    "wide_load",
                    "wide_call_result",
                    "wide_arithmetic",
                }
                for reason in rejection_reasons
            )
            else "member_producer_not_narrow"
        )
        self._set_return_width_bridge_pending_evidence(
            object_target_key=target,
            subreason=subreason,
            detail="target return member producer profile did not prove narrow high bits",
            narrow_width=int(narrow_width),
            extra={
                "required_wide_member": target_member,
                "producer_width": int(producer_width),
                "effective_producer_width": int(effective_producer_width),
                "producer_profile_blockers": tuple(sorted(set(rejection_reasons))),
                "load_widths": tuple(sorted(set(expr_profile["load_widths"]))),
                "call_result_widths": tuple(sorted(set(expr_profile["call_result_widths"]))),
                "constant_widths": tuple(sorted(set(expr_profile["constant_widths"]))),
                "unresolved_widths": tuple(sorted(set(expr_profile["unresolved_widths"]))),
            },
        )
        self._debug_print(
            "  return-width bridge member producer proof rejected: "
            f"subreason={subreason} producer profile blockers={tuple(sorted(set(rejection_reasons)))}"
        )
        return None

    member_local_override = {
        "object_derived": True,
        "status": "proven",
        "proof_kind": "case_member_narrow_producer_override",
        "relation": "member_local_high_bits_irrelevant_not_global_return_width_narrowing",
        "scope": "return_partition_member",
        "global_semantic_narrowing_allowed": bool(global_narrowing_allowed),
        "source_return_type_preserved": True,
        "producer_relation": "target_member_value_expression_has_narrow_producer",
        "subreason": (
            "completed"
            if global_narrowing_allowed
            else "return_type_provenance_disallows_narrowing"
        ),
    }

    member_profile = (
        "member_profile",
        ("member_id", target_member),
        ("return_value_width", width_entry),
        ("producer_width", int(producer_width)),
        ("effective_producer_width", int(effective_producer_width)),
        ("expression_bits", expr_profile["expression_bits"]),
        ("pcode_input_bits", self._return_pcode_value_input_width_bits(getattr(matched_return_info, "pcode_op_ref", None))),
        ("max_value_width", expr_profile["max_value_width"]),
        ("load_widths", tuple(sorted(set(expr_profile["load_widths"])))),
        ("call_result_widths", tuple(sorted(set(expr_profile["call_result_widths"])))),
        ("constant_widths", tuple(sorted(set(expr_profile["constant_widths"])))),
        ("unresolved_widths", tuple(sorted(set(expr_profile["unresolved_widths"])))),
        ("unsupported_or_unresolved", bool(expr_profile["unsupported_or_unresolved"])),
        (
            "semantic_narrow_runtime_ref_key",
            self._normalize_nested_tuple(expr_profile.get("semantic_narrow_runtime_ref_key")),
        ),
        ("expression_profile", expr_profile["profile_key"]),
    )
    return {
        "object_derived": True,
        "status": "proven",
        "object_target_key": target,
        "bridge_subreason": "completed_member_narrow_producer_high_bit_proof",
        "member_high_bit_relation": {
            "object_derived": True,
            "status": "proven",
            "relation": "target_return_member_high_bits_irrelevant_by_narrow_producer",
            "narrow_width": int(narrow_width),
            "wide_width": int(wide_return_bits),
            "proven": True,
            "case_member_narrow_producer_override": member_local_override,
        },
        "target_member_profile": {
            "object_derived": True,
            "status": "proven",
            "function_ref": self._analysis_entry_key(wide_analysis),
            "return_storage": self._return_storage_object_key(wide_analysis),
            "return_type_provenance": type_provenance,
            "case_member_narrow_producer_override": member_local_override,
            "required_wide_member": target_member,
            "member_profile": member_profile,
            "max_producer_width": int(effective_producer_width),
            "load_widths": tuple(sorted(set(expr_profile["load_widths"]))),
            "call_result_widths": tuple(sorted(set(expr_profile["call_result_widths"]))),
            "constant_widths": tuple(sorted(set(expr_profile["constant_widths"]))),
            "unresolved_widths": tuple(sorted(set(expr_profile["unresolved_widths"]))),
            "semantic_narrow_runtime_ref_key": self._normalize_nested_tuple(
                expr_profile.get("semantic_narrow_runtime_ref_key")
            ),
            "unsupported_or_unresolved": False,
            "wide_return_bits": int(wide_return_bits),
            "narrow_width": int(narrow_width),
        },
    }

def _impl__return_width_bridge_wide_surface_profile(
    self,
    wide_analysis: FunctionReturnAnalysis,
    counterpart_analysis: FunctionReturnAnalysis,
    *,
    wide_return_bits: int,
    narrow_width: int,
    base_ctx: Optional[Mapping[str, Any]] = None,
    wide_param_replace_fn=None,
    assume_total_coverage: bool = False,
) -> Optional[Dict[str, Any]]:
    try:
        from ..pairwise_query_builder import extract_return_cases
    except Exception:
        return None
    try:
        cases = extract_return_cases(wide_analysis, getattr(self, "normalization_settings", None))
    except Exception:
        return None
    if not cases:
        return None

    coverage_status = "not_checked"
    if base_ctx is not None and wide_param_replace_fn is not None:
        coverage = self._check_return_case_coverage_gap(
            dict(base_ctx),
            cases,
            wide_param_replace_fn,
            "wide-return-surface",
        )
        if coverage.status != "covered":
            self._debug_print(
                "  return-width bridge semantic narrowing rejected: "
                f"wide surface coverage {coverage.status}"
                + (f" ({coverage.detail})" if getattr(coverage, "detail", None) else "")
            )
            return None
        coverage_status = "total_under_comparison_precondition"
    else:
        if assume_total_coverage:
            coverage_status = "total_under_comparison_precondition"
        elif not any(not getattr(case, "conditions", None) for case in cases):
            self._debug_print(
                "  return-width bridge semantic narrowing rejected: "
                "wide surface coverage context unavailable"
            )
            return None
        else:
            coverage_status = "total_under_comparison_precondition"

    type_provenance = self._return_width_bridge_return_type_provenance(
        wide_analysis,
        counterpart_analysis,
        narrow_width=int(narrow_width),
    )
    if type_provenance is None or type_provenance.get("narrowing_allowed") is not True:
        self._debug_print(
            "  return-width bridge semantic narrowing rejected: "
            f"return type provenance disallows narrowing ({type_provenance})"
        )
        return None

    coverage_identity = self._return_width_bridge_wide_surface_coverage_identity(
        wide_analysis,
        cases,
    )
    coverage_identity_digest = hashlib.sha256(
        repr(self._normalize_nested_tuple(coverage_identity)).encode("utf-8")
    ).hexdigest()
    member_profiles: List[Tuple[Any, ...]] = []
    required_wide_members: List[Tuple[Any, ...]] = []
    max_producer_width = 0
    load_widths: List[int] = []
    call_result_widths: List[int] = []
    constant_widths: List[int] = []
    unresolved_widths: List[int] = []
    rejection_reasons: List[str] = []
    for case in cases:
        return_info = getattr(case, "return_info", None)
        member = self._normalize_nested_tuple(
            self._return_case_partition_member_object_key(case, return_info)
        )
        if member is None:
            rejection_reasons.append("missing_return_partition_member")
            continue
        width_entry = self._normalize_nested_tuple(
            self._return_width_bridge_return_value_width_object_key(
                case,
                return_info,
                int(wide_return_bits),
            )
        )
        producer_width = self._coerce_return_width(width_entry[1] if isinstance(width_entry, tuple) and len(width_entry) > 1 else None)
        if producer_width is None:
            rejection_reasons.append("producer_width_unavailable")
            producer_width = 0
        expr_profile = self._return_width_bridge_expression_producer_profile(
            getattr(case, "value_expr", None),
            narrow_width=int(narrow_width),
        )
        effective_producer_width = int(producer_width)
        if (
            effective_producer_width > int(narrow_width)
            and expr_profile["wide_producer_is_materially_narrow_constant"]
        ):
            effective_producer_width = int(narrow_width)
        if (
            effective_producer_width > int(narrow_width)
            and expr_profile.get("wide_producer_is_semantically_narrow_runtime_ref") is True
            and expr_profile.get("semantic_narrow_runtime_ref_key") is not None
        ):
            effective_producer_width = int(narrow_width)
        max_producer_width = max(max_producer_width, effective_producer_width)
        load_widths.extend(expr_profile["load_widths"])
        call_result_widths.extend(expr_profile["call_result_widths"])
        constant_widths.extend(expr_profile["constant_widths"])
        unresolved_widths.extend(expr_profile["unresolved_widths"])
        if (
            int(producer_width) > int(narrow_width)
            and not expr_profile["wide_producer_is_materially_narrow_constant"]
            and expr_profile.get("wide_producer_is_semantically_narrow_runtime_ref") is not True
        ):
            rejection_reasons.append("producer_width_exceeds_narrow_width")
        rejection_reasons.extend(expr_profile["rejection_reasons"])
        required_wide_members.append(member)
        member_profiles.append(
            (
                "member_profile",
                ("member_id", member),
                ("return_value_width", width_entry),
                ("producer_width", int(producer_width)),
                ("effective_producer_width", effective_producer_width),
                ("expression_bits", expr_profile["expression_bits"]),
                ("pcode_input_bits", self._return_pcode_value_input_width_bits(getattr(return_info, "pcode_op_ref", None))),
                ("max_value_width", expr_profile["max_value_width"]),
                ("load_widths", tuple(sorted(set(expr_profile["load_widths"])))),
                ("call_result_widths", tuple(sorted(set(expr_profile["call_result_widths"])))),
                ("constant_widths", tuple(sorted(set(expr_profile["constant_widths"])))),
                ("unresolved_widths", tuple(sorted(set(expr_profile["unresolved_widths"])))),
                ("unsupported_or_unresolved", bool(expr_profile["unsupported_or_unresolved"])),
                (
                    "semantic_narrow_runtime_ref_key",
                    self._normalize_nested_tuple(expr_profile.get("semantic_narrow_runtime_ref_key")),
                ),
                ("expression_profile", expr_profile["profile_key"]),
            )
        )

    if rejection_reasons:
        self._debug_print(
            "  return-width bridge semantic narrowing rejected: "
            f"producer profile blockers={tuple(sorted(set(rejection_reasons)))}"
        )
        return None
    members_tuple = tuple(required_wide_members)
    digest = hashlib.sha256(repr(self._normalize_nested_tuple(members_tuple)).encode("utf-8")).hexdigest()
    return {
        "object_derived": True,
        "status": "proven",
        "function_ref": self._analysis_entry_key(wide_analysis),
        "return_storage": self._return_storage_object_key(wide_analysis),
        "return_type_provenance": type_provenance,
        "coverage_status": coverage_status,
        "coverage_identity": coverage_identity,
        "coverage_identity_digest": coverage_identity_digest,
        "partition_member_digest": digest,
        "required_wide_members": tuple(required_wide_members),
        "member_profiles": tuple(member_profiles),
        "max_producer_width": max_producer_width,
        "load_widths": tuple(sorted(set(load_widths))),
        "call_result_widths": tuple(sorted(set(call_result_widths))),
        "constant_widths": tuple(sorted(set(constant_widths))),
        "unresolved_widths": tuple(sorted(set(unresolved_widths))),
        "unsupported_or_unresolved": False,
        "wide_return_bits": int(wide_return_bits),
        "narrow_width": int(narrow_width),
    }

def _impl__return_width_bridge_semantic_narrowing_content_is_complete(
    cls,
    content: Any,
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not cls._return_width_bridge_common_proof_content_is_complete(content, object_target_key):
        return False
    semantic_width = content.get("semantic_return_width")
    profile = content.get("wide_surface_profile")
    if not isinstance(semantic_width, Mapping) or not isinstance(profile, Mapping):
        return False
    if not (
        semantic_width.get("object_derived") is True
        and semantic_width.get("status") == "proven"
        and semantic_width.get("proven") is True
        and semantic_width.get("relation") == "wide_storage_semantic_surface_is_narrow"
    ):
        return False
    if not (
        profile.get("object_derived") is True
        and profile.get("status") == "proven"
        and profile.get("coverage_status") == "total_under_comparison_precondition"
        and profile.get("unsupported_or_unresolved") is False
    ):
        return False
    if not profile.get("coverage_identity") or not isinstance(profile.get("coverage_identity_digest"), str):
        return False
    try:
        narrow_width = int(profile.get("narrow_width"))
        max_producer_width = int(profile.get("max_producer_width"))
    except (TypeError, ValueError):
        return False
    if narrow_width <= 0 or max_producer_width <= 0 or max_producer_width > narrow_width:
        return False
    if cls._normalize_nested_tuple(profile.get("required_wide_members")) == ():
        return False
    if cls._normalize_nested_tuple(profile.get("member_profiles")) == ():
        return False
    type_provenance = profile.get("return_type_provenance")
    if not isinstance(type_provenance, Mapping) or type_provenance.get("narrowing_allowed") is not True:
        return False
    return True

def _impl__return_width_bridge_member_narrow_producer_content_is_complete(
    cls,
    content: Any,
    object_target_key: Tuple[Any, ...],
) -> bool:
    if not cls._return_width_bridge_common_proof_content_is_complete(content, object_target_key):
        return False
    relation = content.get("member_high_bit_relation")
    profile = content.get("target_member_profile")
    if not isinstance(relation, Mapping) or not isinstance(profile, Mapping):
        return False
    if not (
        relation.get("object_derived") is True
        and relation.get("status") == "proven"
        and relation.get("proven") is True
        and relation.get("relation") == "target_return_member_high_bits_irrelevant_by_narrow_producer"
    ):
        return False
    if not (
        profile.get("object_derived") is True
        and profile.get("status") == "proven"
        and profile.get("unsupported_or_unresolved") is False
    ):
        return False
    try:
        narrow_width = int(profile.get("narrow_width"))
        max_producer_width = int(profile.get("max_producer_width"))
    except (TypeError, ValueError):
        return False
    if narrow_width <= 0 or max_producer_width <= 0 or max_producer_width > narrow_width:
        return False
    if cls._normalize_nested_tuple(profile.get("required_wide_member")) is None:
        return False
    if cls._normalize_nested_tuple(profile.get("member_profile")) == ():
        return False
    if cls._normalize_nested_tuple(profile.get("unresolved_widths")) not in {(), None}:
        return False
    type_provenance = profile.get("return_type_provenance")
    if not isinstance(type_provenance, Mapping):
        return False
    override = profile.get("case_member_narrow_producer_override")
    relation_override = relation.get("case_member_narrow_producer_override")
    if not cls._return_width_bridge_member_local_override_is_complete(
        override,
        type_provenance,
    ):
        return False
    if cls._normalize_nested_tuple(override) != cls._normalize_nested_tuple(relation_override):
        return False
    return True

def _impl__return_width_bridge_member_local_override_is_complete(
    cls,
    override: Any,
    type_provenance: Mapping[str, Any],
) -> bool:
    if not isinstance(override, Mapping):
        return False
    if not (
        override.get("object_derived") is True
        and override.get("status") == "proven"
        and override.get("proof_kind") == "case_member_narrow_producer_override"
        and override.get("relation")
        == "member_local_high_bits_irrelevant_not_global_return_width_narrowing"
        and override.get("scope") == "return_partition_member"
        and override.get("source_return_type_preserved") is True
        and override.get("producer_relation")
        == "target_member_value_expression_has_narrow_producer"
    ):
        return False
    global_allowed = type_provenance.get("narrowing_allowed") is True
    if override.get("global_semantic_narrowing_allowed") is not bool(global_allowed):
        return False
    expected_subreason = (
        "completed"
        if global_allowed
        else "return_type_provenance_disallows_narrowing"
    )
    return override.get("subreason") == expected_subreason

def _impl__return_width_bridge_member_narrow_producer_content_fingerprint(
    cls,
    content: Any,
) -> Optional[Tuple[Any, ...]]:
    if not isinstance(content, Mapping):
        return None
    relation = content.get("member_high_bit_relation")
    profile = content.get("target_member_profile")
    if not isinstance(relation, Mapping) or not isinstance(profile, Mapping):
        return None
    return (
        "return_member_narrow_producer_high_bit_proof",
        ("object_target_key", cls._normalize_nested_tuple(content.get("object_target_key"))),
        (
            "member_high_bit_relation",
            relation.get("relation"),
            relation.get("narrow_width"),
            relation.get("wide_width"),
            cls._normalize_nested_tuple(
                relation.get("case_member_narrow_producer_override")
            ),
        ),
        ("function_ref", cls._normalize_nested_tuple(profile.get("function_ref"))),
        ("return_storage", cls._normalize_nested_tuple(profile.get("return_storage"))),
        ("required_wide_member", cls._normalize_nested_tuple(profile.get("required_wide_member"))),
        ("member_profile", cls._normalize_nested_tuple(profile.get("member_profile"))),
        ("max_producer_width", profile.get("max_producer_width")),
        ("load_widths", cls._normalize_nested_tuple(profile.get("load_widths"))),
        ("call_result_widths", cls._normalize_nested_tuple(profile.get("call_result_widths"))),
        ("constant_widths", cls._normalize_nested_tuple(profile.get("constant_widths"))),
        ("unresolved_widths", cls._normalize_nested_tuple(profile.get("unresolved_widths"))),
        (
            "semantic_narrow_runtime_ref_key",
            cls._normalize_nested_tuple(profile.get("semantic_narrow_runtime_ref_key")),
        ),
        (
            "case_member_narrow_producer_override",
            cls._normalize_nested_tuple(profile.get("case_member_narrow_producer_override")),
        ),
    )

def _impl__return_width_bridge_return_type_provenance(
    cls,
    analysis: FunctionReturnAnalysis,
    counterpart_analysis: FunctionReturnAnalysis,
    *,
    narrow_width: int,
) -> Optional[Dict[str, Any]]:
    try:
        from ....model.signature import get_declared_type_size_bits, get_data_type_display_name
    except Exception:
        return None
    model_provenance = getattr(analysis, "return_type_provenance", None)
    provenance: Dict[str, Any] = dict(model_provenance) if isinstance(model_provenance, Mapping) else {}
    return_type = get_data_type_display_name(
        getattr(analysis, "return_type_obj", None),
        getattr(analysis, "return_type", None),
    ) or getattr(analysis, "return_type", None)
    counterpart_return_type = get_data_type_display_name(
        getattr(counterpart_analysis, "return_type_obj", None),
        getattr(counterpart_analysis, "return_type", None),
    ) or getattr(counterpart_analysis, "return_type", None)
    declared_bits = get_declared_type_size_bits(
        getattr(analysis, "return_type_obj", None),
        return_type,
    )
    source_declared_known = bool(provenance.get("source_declared_return_type_known") is True)
    source_declared_width = provenance.get("source_declared_return_type_width")
    return_type_source = str(provenance.get("return_type_source") or "decompiler_return_type")
    signature_hypothesis_phase = provenance.get("signature_hypothesis_phase")
    resolved_return_override_source = provenance.get("resolved_return_override_source")
    hypotheses = []
    for item in getattr(analysis, "signature_hypotheses", ()) or ():
        if not isinstance(item, Mapping):
            continue
        phase = item.get("phase")
        resolved = item.get("resolved_return_override")
        resolved_source = resolved.get("source") if isinstance(resolved, Mapping) else None
        evidence = item.get("evidence") if isinstance(item.get("evidence"), Mapping) else {}
        hypotheses.append(
            (
                "signature_hypothesis",
                ("phase", phase),
                ("resolved_return_override_source", resolved_source),
                ("reason", item.get("reason")),
                ("evidence", tuple(sorted((str(k), str(v)) for k, v in evidence.items()))),
            )
        )
        if phase in cls._RETURN_WIDTH_BRIDGE_SOURCE_LEVEL_PHASES:
            source_declared_known = True
            declared_name = evidence.get("declared_return_type") or item.get("return_type_override")
            source_declared_width = evidence.get("declared_return_type_width")
            if source_declared_width is None:
                source_declared_width = get_declared_type_size_bits(None, declared_name)
        if item.get("return_type_override") is not None or resolved is not None:
            signature_hypothesis_phase = phase
            if resolved_source:
                resolved_return_override_source = resolved_source
                return_type_source = str(resolved_source)

    normalized_return_type = str(return_type or "").strip().lower()
    if normalized_return_type.startswith("undefined"):
        return_type_source = "undefined_decompiler_type"
    source_level_64 = (
        source_declared_known
        and source_declared_width is not None
        and int(source_declared_width) > int(narrow_width)
    )
    source_level_width_unknown = source_declared_known and source_declared_width is None
    weak_source = return_type_source in cls._RETURN_WIDTH_BRIDGE_WEAK_RETURN_TYPE_SOURCES
    declared_not_wide = declared_bits is not None and int(declared_bits) <= int(narrow_width)
    source_declared_not_wide = (
        source_declared_known
        and source_declared_width is not None
        and int(source_declared_width) <= int(narrow_width)
    )
    narrowing_allowed = bool(
        not source_level_64
        and not source_level_width_unknown
        and (
            weak_source
            or normalized_return_type.startswith("undefined")
            or declared_not_wide
            or source_declared_not_wide
            or resolved_return_override_source in cls._RETURN_WIDTH_BRIDGE_WEAK_RETURN_TYPE_SOURCES
        )
    )
    result = {
        "object_derived": True,
        "return_type": return_type,
        "return_type_source": return_type_source,
        "signature_hypothesis_phase": signature_hypothesis_phase,
        "resolved_return_override_source": resolved_return_override_source,
        "counterpart_return_type": counterpart_return_type,
        "source_declared_return_type_known": bool(source_declared_known),
        "source_declared_return_type_width": source_declared_width,
        "declared_return_type_width": declared_bits,
        "source_level_64_return_type": bool(source_level_64),
        "source_level_return_type_width_unknown": bool(source_level_width_unknown),
        "narrowing_allowed": narrowing_allowed,
        "signature_hypotheses": tuple(hypotheses),
    }
    for key, value in provenance.items():
        if key not in result:
            result[key] = value
    return result

def _impl__return_width_bridge_expression_producer_profile(
    cls,
    expr: Optional[Expression],
    *,
    narrow_width: int,
) -> Dict[str, Any]:
    load_widths: List[int] = []
    call_result_widths: List[int] = []
    constant_widths: List[int] = []
    unresolved_widths: List[int] = []
    rejection_reasons: List[str] = []
    max_value_width = 0
    unsupported_or_unresolved = False
    semantically_narrow_runtime_ref = False
    semantic_narrow_runtime_ref_key = None
    profile_nodes: List[Tuple[Any, ...]] = []
    try:
        expression_bits = int(expression_smt_bit_width(expr) or 0)
    except Exception:
        expression_bits = 0
    wide_producer_is_materially_narrow_constant = False
    if getattr(expr, "expr_type", None) == ExpressionType.CONSTANT:
        try:
            root_value = int(getattr(expr, "value"))
        except (TypeError, ValueError):
            root_value = 0
        if expression_bits > int(narrow_width):
            wide_producer_is_materially_narrow_constant = (
                (root_value >> int(narrow_width)) == 0
            )
    stack = [expr] if expr is not None else []
    seen: Set[int] = set()
    while stack:
        node = stack.pop()
        if node is None:
            continue
        node_id = id(node)
        if node_id in seen:
            continue
        seen.add(node_id)
        expr_type = getattr(node, "expr_type", None)
        try:
            node_bits = int(expression_smt_bit_width(node) or getattr(node, "get_bit_width", lambda: 0)() or 0)
        except Exception:
            node_bits = 0
        max_value_width = max(max_value_width, node_bits)
        operator = getattr(node, "operator", None)
        runtime_ref = getattr(node, "runtime_ref", None)
        runtime_ref_contract_key = None
        if (
            isinstance(runtime_ref, ReadonlyReductionRef)
            and int(narrow_width) > 0
            and int(narrow_width) % 8 == 0
        ):
            try:
                runtime_ref_contract_key = runtime_ref.readonly_term_sequence_contract_key(
                    result_size=int(narrow_width) // 8
                )
            except (AttributeError, TypeError, ValueError):
                runtime_ref_contract_key = None
            if runtime_ref_contract_key is not None:
                semantically_narrow_runtime_ref = True
                semantic_narrow_runtime_ref_key = runtime_ref_contract_key
        profile_nodes.append(
            (
                "node",
                ("type", getattr(expr_type, "name", str(expr_type))),
                ("operator", operator),
                ("bits", node_bits),
                ("provenance", expression_provenance_key(node)),
                ("semantic_narrow_runtime_ref", runtime_ref_contract_key),
            )
        )
        if expr_type == ExpressionType.UNKNOWN:
            unresolved_widths.append(node_bits)
            unsupported_or_unresolved = True
            rejection_reasons.append("unresolved_producer")
            continue
        if expr_type == ExpressionType.MEMORY:
            load_widths.append(node_bits)
            if node_bits > int(narrow_width):
                rejection_reasons.append("wide_load")
        if expr_type == ExpressionType.CALL:
            call_result_widths.append(node_bits)
            if node_bits > int(narrow_width):
                rejection_reasons.append("wide_call_result")
        if expr_type == ExpressionType.CONSTANT:
            constant_widths.append(node_bits)
            try:
                value = int(getattr(node, "value"))
            except (TypeError, ValueError):
                value = 0
            material_high_bits = node_bits > int(narrow_width) and (value >> int(narrow_width)) != 0
            if material_high_bits:
                rejection_reasons.append("wide_constant")
        if expr_type in {ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.INTRINSIC}:
            width_adapter = operator in {"INT_ZEXT", "INT_SEXT", "SUBPIECE", "CAST", "COPY"}
            if (
                node_bits > int(narrow_width)
                and not width_adapter
                and runtime_ref_contract_key is None
            ):
                rejection_reasons.append("wide_arithmetic")
        try:
            if expression_contains_unsupported_smt_ops(node):
                unsupported_or_unresolved = True
                rejection_reasons.append("unsupported_expression")
        except Exception:
            unsupported_or_unresolved = True
            rejection_reasons.append("unsupported_expression")
        for operand in getattr(node, "operands", ()) or ():
            stack.append(operand)
        if expr_type == ExpressionType.PHI:
            for _condition, branch_value in getattr(node, "value", ()) or ():
                stack.append(branch_value)
    return {
        "expression_bits": expression_bits,
        "max_value_width": max_value_width,
        "load_widths": load_widths,
        "call_result_widths": call_result_widths,
        "constant_widths": constant_widths,
        "unresolved_widths": unresolved_widths,
        "wide_producer_is_materially_narrow_constant": wide_producer_is_materially_narrow_constant,
        "wide_producer_is_semantically_narrow_runtime_ref": semantically_narrow_runtime_ref,
        "semantic_narrow_runtime_ref_key": semantic_narrow_runtime_ref_key,
        "unsupported_or_unresolved": unsupported_or_unresolved,
        "rejection_reasons": tuple(sorted(set(rejection_reasons))),
        "profile_key": tuple(profile_nodes),
    }

def _impl__return_width_bridge_wide_surface_coverage_identity(
    self,
    analysis: FunctionReturnAnalysis,
    cases: Sequence[Any],
) -> Tuple[Any, ...]:
    case_entries: List[Tuple[Any, ...]] = []
    for case in cases or ():
        return_info = getattr(case, "return_info", None)
        member = self._return_case_partition_member_object_key(case, return_info)
        conditions = tuple(getattr(case, "conditions", None) or ())
        miss_expr = self._case_miss_expression(list(conditions))
        case_entries.append(
            (
                "wide_surface_coverage_case",
                ("member", self._normalize_nested_tuple(member)),
                (
                    "guards",
                    self._canonicalize_key_sequence(
                        tuple(self._return_condition_object_key(condition) for condition in conditions)
                    ),
                ),
                (
                    "case_miss_formula",
                    self._expression_runtime_object_key(miss_expr) if miss_expr is not None else None,
                ),
            )
        )
    return (
        "wide_surface_coverage_identity",
        ("normalization_schema_version", self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION),
        ("function_ref", self._analysis_entry_key(analysis)),
        ("return_partition_identity", self._return_coverage_partition_identity_key(analysis)),
        ("guard_disjunction_identity", self._return_coverage_guard_disjunction_identity_key(analysis)),
        ("cases", self._canonicalize_key_sequence(case_entries)),
    )

def _impl__return_width_bridge_common_proof_content_is_complete(
    cls,
    content: Mapping[str, Any],
    object_target_key: Tuple[Any, ...],
) -> bool:
    return (
        isinstance(content, Mapping)
        and content.get("object_derived") is True
        and content.get("status") == "proven"
        and cls._normalize_nested_tuple(content.get("object_target_key")) == object_target_key
        and not cls._evidence_has_any_recursive(content, cls._COMPLETED_PROOF_BLOCKER_FIELDS)
    )

def _impl__return_width_bridge_target_is_specific(cls, object_target_key: Any) -> bool:
    target = cls._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) < 5 or target[0] != "return_width_bridge":
        return False
    widths = cls._return_width_bridge_target_widths(target)
    if widths is None or widths[0] == widths[1]:
        return False
    pair = cls._return_width_bridge_find_tagged_entry(target, "pair")
    if not isinstance(pair, tuple) or len(pair) != 2 or not isinstance(pair[1], str) or not pair[1]:
        return False
    left = cls._return_width_bridge_find_side(target, "left")
    right = cls._return_width_bridge_find_side(target, "right")
    if left is None or right is None:
        return False
    return (
        cls._return_width_bridge_side_is_specific(left, widths[0])
        and cls._return_width_bridge_side_is_specific(right, widths[1])
    )

def _impl__return_width_bridge_side_is_specific(cls, side: Tuple[Any, ...], expected_width: int) -> bool:
    if len(side) < 6 or side[0] != "return_width_side":
        return False
    function_ref = cls._return_width_bridge_find_tagged_entry(side, "function_ref")
    return_size = cls._return_width_bridge_find_tagged_entry(side, "return_size")
    return_storage = cls._return_width_bridge_find_tagged_entry(side, "return_storage")
    partition_member = cls._return_width_bridge_find_tagged_entry(
        side,
        "return_case_partition_member",
    )
    if not isinstance(function_ref, tuple) or not function_ref:
        return False
    if not isinstance(return_size, tuple) or len(return_size) != 2 or return_size[1] != expected_width:
        return False
    if not isinstance(return_storage, tuple) or len(return_storage) < 3:
        return False
    if not isinstance(partition_member, tuple) or len(partition_member) < 6:
        return False
    value_entry = cls._return_width_bridge_find_tagged_entry(partition_member, "value")
    value_width = cls._return_width_bridge_find_tagged_entry(side, "return_value_width")
    return (
        isinstance(value_entry, tuple)
        and bool(value_entry)
        and cls._return_width_bridge_return_value_width_entry_is_specific(
            value_width,
            expected_return_width=expected_width,
        )
    )

def _impl__return_width_bridge_return_value_width_entry_is_specific(
    cls,
    entry: Any,
    *,
    expected_return_width: int,
) -> bool:
    width_entry = cls._normalize_nested_tuple(entry)
    if not isinstance(width_entry, tuple) or len(width_entry) < 6:
        return False
    if width_entry[0] != "return_value_width":
        return False
    if not cls._positive_int_like(width_entry[1]):
        return False
    if not cls._positive_int_like(width_entry[2]):
        return False
    if int(width_entry[2]) != int(expected_return_width):
        return False
    if width_entry[3] not in {True, False}:
        return False
    if not isinstance(width_entry[4], tuple) or not width_entry[4]:
        return False
    if width_entry[5] not in {
        "producer_matches_return_width",
        "producer_narrower_than_return_width",
        "producer_wider_than_return_width",
    }:
        return False
    if len(width_entry) >= 7 and width_entry[6] not in {
        "none",
        "sign_extend",
        "zero_extend",
        "truncate",
    }:
        return False
    return True

def _impl__return_width_bridge_value_width_evidence(
    cls,
    object_target_key: Any,
) -> Optional[Tuple[Any, ...]]:
    target = cls._normalize_nested_tuple(object_target_key)
    left = cls._return_width_bridge_find_side(target, "left")
    right = cls._return_width_bridge_find_side(target, "right")
    if left is None or right is None:
        return None
    left_width = cls._return_width_bridge_find_tagged_entry(left, "return_value_width")
    right_width = cls._return_width_bridge_find_tagged_entry(right, "return_value_width")
    left_return_size = cls._return_width_bridge_find_tagged_entry(left, "return_size")
    right_return_size = cls._return_width_bridge_find_tagged_entry(right, "return_size")
    if (
        not isinstance(left_return_size, tuple)
        or len(left_return_size) != 2
        or not isinstance(right_return_size, tuple)
        or len(right_return_size) != 2
    ):
        return None
    if not (
        cls._return_width_bridge_return_value_width_entry_is_specific(
            left_width,
            expected_return_width=left_return_size[1],
        )
        and cls._return_width_bridge_return_value_width_entry_is_specific(
            right_width,
            expected_return_width=right_return_size[1],
        )
    ):
        return None
    return ("return_value_width_evidence", left_width, right_width)

def _impl__return_width_bridge_extension_policy_for_side(cls, side: Any) -> Optional[str]:
    width_entry = cls._return_width_bridge_find_tagged_entry(side, "return_value_width")
    normalized = cls._normalize_nested_tuple(width_entry)
    if not isinstance(normalized, tuple) or len(normalized) < 7:
        return None
    policy = normalized[6]
    return str(policy) if policy in {"none", "sign_extend", "zero_extend", "truncate"} else None

def _impl__return_width_bridge_required_extension_mnemonic_for_side(
    cls,
    side: Any,
) -> Optional[str]:
    width_entry = cls._normalize_nested_tuple(
        cls._return_width_bridge_find_tagged_entry(side, "return_value_width")
    )
    if not isinstance(width_entry, tuple) or len(width_entry) < 7:
        return None
    relation = width_entry[5]
    policy = width_entry[6]
    if relation != "producer_narrower_than_return_width":
        return None
    if policy == "sign_extend":
        return "INT_SEXT"
    if policy == "zero_extend":
        return "INT_ZEXT"
    return None

def _impl__return_width_bridge_extension_ops_for_side(cls, side: Any) -> Tuple[Any, ...]:
    width_entry = cls._normalize_nested_tuple(
        cls._return_width_bridge_find_tagged_entry(side, "return_value_width")
    )
    if not isinstance(width_entry, tuple):
        return ()
    tagged = cls._return_width_bridge_find_tagged_entry(
        width_entry,
        "return_value_extension_ops",
    )
    if not isinstance(tagged, tuple) or len(tagged) != 2:
        return ()
    profiles = cls._normalize_nested_tuple(tagged[1])
    return profiles if isinstance(profiles, tuple) else ()

def _impl__return_width_bridge_matching_extension_ops_for_side(
    cls,
    side: Any,
) -> Optional[Tuple[Any, ...]]:
    mnemonic = cls._return_width_bridge_required_extension_mnemonic_for_side(side)
    if mnemonic is None:
        return ()
    width_entry = cls._normalize_nested_tuple(
        cls._return_width_bridge_find_tagged_entry(side, "return_value_width")
    )
    if not isinstance(width_entry, tuple) or len(width_entry) < 3:
        return None
    producer_bits = width_entry[1]
    return_bits = width_entry[2]
    matches = []
    for profile in cls._return_width_bridge_extension_ops_for_side(side):
        if not cls._return_width_bridge_extension_op_profile_matches(
            profile,
            mnemonic=mnemonic,
            producer_bits=producer_bits,
            return_bits=return_bits,
        ):
            continue
        matches.append(profile)
    if matches:
        return tuple(matches)
    return None

def _impl__return_width_bridge_extension_evidence_for_side(
    cls,
    side: Any,
) -> Optional[Tuple[Tuple[Any, ...], Tuple[Any, ...], Tuple[Any, ...]]]:
    summary_extension = cls._return_width_bridge_summary_parameter_extension_for_side(side)
    if summary_extension is not None:
        return (), (summary_extension,), ()
    extension_ops = cls._return_width_bridge_matching_extension_ops_for_side(side)
    if extension_ops is not None:
        return extension_ops, (), ()
    literal_extension = cls._return_width_bridge_constant_literal_extension_for_side(side)
    if literal_extension is None:
        return None
    return (), (), (literal_extension,)

def _impl__return_width_bridge_has_summary_parameter_extension_evidence(
    cls,
    object_target_key: Any,
) -> bool:
    target = cls._normalize_nested_tuple(object_target_key)
    left = cls._return_width_bridge_find_side(target, "left")
    right = cls._return_width_bridge_find_side(target, "right")
    return any(
        cls._return_width_bridge_summary_parameter_extension_for_side(side) is not None
        for side in (left, right)
        if side is not None
    )

def _impl__return_width_bridge_summary_parameter_extension_for_side(
    cls,
    side: Any,
) -> Optional[Tuple[Any, ...]]:
    width_entry = cls._normalize_nested_tuple(
        cls._return_width_bridge_find_tagged_entry(side, "return_value_width")
    )
    if not isinstance(width_entry, tuple) or len(width_entry) < 9:
        return None
    producer_bits = width_entry[1]
    return_bits = width_entry[2]
    relation = width_entry[5]
    policy = width_entry[6]
    if relation != "producer_narrower_than_return_width":
        return None
    if policy not in {"sign_extend", "zero_extend"}:
        return None
    value_entry = cls._return_width_bridge_find_tagged_entry(width_entry, "value")
    expression_bits = cls._return_width_bridge_find_tagged_entry(width_entry, "expression_bits")
    pcode_input_bits = cls._return_width_bridge_find_tagged_entry(
        width_entry,
        "return_pcode_value_input_bits",
    )
    try:
        producer_bits_int = int(producer_bits)
        return_bits_int = int(return_bits)
        expression_bits_int = int(
            expression_bits[1]
            if isinstance(expression_bits, tuple) and len(expression_bits) == 2
            else expression_bits
        )
        pcode_input_bits_int = int(
            pcode_input_bits[1]
            if isinstance(pcode_input_bits, tuple) and len(pcode_input_bits) == 2
            else pcode_input_bits
        )
    except (TypeError, ValueError):
        return None
    if not (
        producer_bits_int > 0
        and producer_bits_int == expression_bits_int
        and producer_bits_int < return_bits_int
        and pcode_input_bits_int >= return_bits_int
    ):
        return None
    summary_parameter = cls._return_width_bridge_summary_parameter_value_key(value_entry)
    if summary_parameter is None:
        return None
    return (
        "summary_parameter_extension",
        ("parameter", summary_parameter),
        ("producer_bits", producer_bits_int),
        ("return_bits", return_bits_int),
        ("return_pcode_value_input_bits", pcode_input_bits_int),
        ("policy", policy),
        ("parameter_kind", "synthetic_recursive_summary"),
    )

def _impl__return_width_bridge_constant_literal_extension_for_side(
    cls,
    side: Any,
) -> Optional[Tuple[Any, ...]]:
    width_entry = cls._normalize_nested_tuple(
        cls._return_width_bridge_find_tagged_entry(side, "return_value_width")
    )
    if not isinstance(width_entry, tuple) or len(width_entry) < 7:
        return None
    relation = width_entry[5]
    policy = width_entry[6]
    if relation != "producer_narrower_than_return_width":
        return None
    if policy not in {"sign_extend", "zero_extend"}:
        return None
    value_entry = cls._return_width_bridge_find_tagged_entry(width_entry, "value")
    value = cls._normalize_nested_tuple(value_entry)
    if not isinstance(value, tuple) or len(value) != 2 or value[0] != "value":
        return None
    expr = value[1]
    if not (
        isinstance(expr, tuple)
        and len(expr) == 2
        and expr[0] == "expression"
        and isinstance(expr[1], tuple)
        and len(expr[1]) >= 3
        and expr[1][0] == "const"
    ):
        return None
    const_payload = expr[1]
    try:
        const_value = int(const_payload[1][1])
        const_size_bits = int(const_payload[2]) * 8
        producer_bits = int(width_entry[1])
        return_bits = int(width_entry[2])
    except (TypeError, ValueError, IndexError):
        return None
    if not (
        const_size_bits == producer_bits
        and 0 < producer_bits < return_bits
    ):
        return None
    source_mask = (1 << producer_bits) - 1
    low_value = const_value & source_mask
    has_material_high_bits = (const_value >> producer_bits) != 0
    has_signed_negative_low_bits = (
        policy == "sign_extend"
        and bool(low_value & (1 << (producer_bits - 1)))
    )
    if not (has_material_high_bits or has_signed_negative_low_bits):
        return None
    if policy == "zero_extend":
        extended_value = low_value
    else:
        sign_bit = 1 << (producer_bits - 1)
        if low_value & sign_bit:
            extended_value = low_value | (((1 << (return_bits - producer_bits)) - 1) << producer_bits)
        else:
            extended_value = low_value
    wide_mask = (1 << return_bits) - 1
    if (const_value & wide_mask) != extended_value:
        return None
    return (
        "constant_literal_extension",
        ("value", const_value),
        ("producer_bits", producer_bits),
        ("return_bits", return_bits),
        ("policy", policy),
        ("extended_value", extended_value),
    )

def _impl__return_width_bridge_value_is_deterministic_width_expression(cls, value_entry: Any) -> bool:
    value = cls._normalize_nested_tuple(value_entry)
    if not isinstance(value, tuple) or len(value) != 2 or value[0] != "value":
        return False
    return cls._return_width_bridge_expression_key_is_deterministic_width(value[1])

def _impl__return_width_bridge_expression_key_is_deterministic_width(cls, expr: Any) -> bool:
    if not isinstance(expr, tuple) or len(expr) != 2 or expr[0] != "expression":
        return False
    node = expr[1]
    if not isinstance(node, tuple) or not node:
        return False
    kind = node[0]
    if kind in {"const", "parameter", "variable"}:
        return True
    if kind in {"unary", "binary"}:
        operands = node[3:] if kind == "unary" else node[3:]
        return all(
            cls._return_width_bridge_expression_key_is_deterministic_width(
                ("expression", operand)
            )
            for operand in operands
        )
    return False

def _impl__return_width_bridge_summary_parameter_value_key(cls, value_entry: Any) -> Optional[Tuple[Any, ...]]:
    value = cls._normalize_nested_tuple(value_entry)
    if not isinstance(value, tuple) or len(value) != 2 or value[0] != "value":
        return None
    provenance = value[1]
    if (
        not isinstance(provenance, tuple)
        or len(provenance) != 2
        or provenance[0] != "expression"
    ):
        return None
    expression_key = provenance[1]
    if not isinstance(expression_key, tuple) or len(expression_key) != 4:
        return None
    if expression_key[0] != "parameter":
        return None
    name = expression_key[1]
    index = expression_key[2]
    size_bytes = expression_key[3]
    if not isinstance(name, str) or not (
        name.startswith("summary_rec_") or name.startswith("summary_call_")
    ):
        return None
    index_value = index[1] if isinstance(index, tuple) and len(index) == 2 else index
    try:
        index_int = int(index_value)
        size_int = int(size_bytes)
    except (TypeError, ValueError):
        return None
    if index_int < 10000 or size_int <= 0:
        return None
    return (
        "parameter",
        name,
        ("index", index_int),
        ("size_bits", size_int * 8),
    )

def _impl__return_width_bridge_normalize_optional_tuple(cls, value: Any) -> Tuple[Any, ...]:
    normalized = cls._normalize_nested_tuple(value)
    return normalized if isinstance(normalized, tuple) else ()

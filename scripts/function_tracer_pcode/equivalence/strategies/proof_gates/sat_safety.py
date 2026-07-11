"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.equivalence.strategies.base``."""

from __future__ import annotations

from typing import Any
from ._shared import (
    Mapping,
    UnknownReasonId,
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    UnknownRecoveryProofObligation,
    build_proof_obligation_id,
    hashlib,
    json,
    make_unknown_reason,
)

def invoke(_service_name: str, *args: Any, **kwargs: Any) -> Any:
    implementation_function = globals().get(f"_impl_{_service_name}")
    if implementation_function is None:
        raise AttributeError(_service_name)
    return implementation_function(*args, **kwargs)


def implementation(_service_name: str):
    return globals().get(f"_impl_{_service_name}")

def _impl__collect_decisive_sat_unsafety_reasons(
    self,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> List[str]:
    """SAT を最終確定するには危険な解析要因を収集する。"""
    reasons: List[str] = []
    for label, analysis in (("function1", analysis1), ("function2", analysis2)):
        for reason in analysis.get_decisive_sat_unsafety_reasons():
            reasons.append(f"{label}:{reason}")
    return reasons

def _impl__same_function_counterexample_replay_reasons(
    self,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Tuple[str, ...]:
    """Require replay evidence before accepting same-function SAT as NOT_EQ."""
    function1 = str(getattr(analysis1, "function_name", "") or "")
    function2 = str(getattr(analysis2, "function_name", "") or "")
    if not function1 or function1 != function2:
        return ()
    return ("counterexample_replay_missing",)

def _impl__collect_equivalence_blocking_unsafety_reasons(
    self,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> List[str]:
    """UNSAT を final EQUIVALENT と確定するには危険な解析要因を収集する。"""
    reasons: List[str] = []
    for label, analysis in (("function1", analysis1), ("function2", analysis2)):
        getter = getattr(analysis, "get_equivalence_blocking_unsafety_reasons", None)
        if not callable(getter):
            continue
        for reason in getter():
            reasons.append(f"{label}:{reason}")
        effect_summary = getattr(analysis, "effect_summary", None)
        if effect_summary is not None:
            call_argument_evidence = tuple(
                evidence
                for evidence in getattr(effect_summary, "call_argument_evidence", {}).values()
                if evidence is not None
            )
            for index, _evidence in enumerate(call_argument_evidence):
                suffix = f":{index}" if len(call_argument_evidence) > 1 else ""
                reasons.append(f"{label}:effect_call_argument_evidence{suffix}")
            call_target_resolution_evidence = tuple(
                evidence
                for evidence in getattr(effect_summary, "call_target_resolution_evidence", ()) or ()
                if evidence is not None
            )
            for index, _evidence in enumerate(call_target_resolution_evidence):
                suffix = f":{index}" if len(call_target_resolution_evidence) > 1 else ""
                reasons.append(f"{label}:effect_call_target_resolution_evidence{suffix}")
    return reasons

def _impl__unknown_reason_id_for_blocking_unsafety(self, reason: Optional[str]):
    reason_kind = self._blocking_reason_kind(reason)
    if reason_kind == "return_coverage_gap":
        return UnknownReasonId.RETURN_COVERAGE_GAP
    if reason_kind == "return_coverage_inconclusive":
        return UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
    if reason_kind == "outcome_partition_unknown":
        return UnknownReasonId.OUTCOME_PARTITION_UNKNOWN
    summary_return_reason_ids = {
        UnknownReasonId.SUMMARY_RETURN_CANDIDATE_INVALID.value: UnknownReasonId.SUMMARY_RETURN_CANDIDATE_INVALID,
        UnknownReasonId.SUMMARY_RETURN_OVERLAP_UNPROVEN.value: UnknownReasonId.SUMMARY_RETURN_OVERLAP_UNPROVEN,
        UnknownReasonId.SUMMARY_EFFECT_UNMODELED.value: UnknownReasonId.SUMMARY_EFFECT_UNMODELED,
        UnknownReasonId.SUMMARY_PRECONDITION_INCOMPLETE.value: UnknownReasonId.SUMMARY_PRECONDITION_INCOMPLETE,
        UnknownReasonId.SUMMARY_PARTITION_NOT_TOTAL.value: UnknownReasonId.SUMMARY_PARTITION_NOT_TOTAL,
        UnknownReasonId.PHI_CIRCULAR_REPLACEMENT_UNPROVEN.value: UnknownReasonId.PHI_CIRCULAR_REPLACEMENT_UNPROVEN,
    }
    if reason_kind in summary_return_reason_ids:
        return summary_return_reason_ids[reason_kind]
    if reason_kind in {"recoverable_partial", "argument_recovery_recoverable_partial"}:
        return UnknownReasonId.RECOVERABLE_PARTIAL
    return UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY

def _impl__make_blocking_unsafety_unknown_reason(
    self,
    blocking_reason: str,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    stage: str,
):
    typed_reason_id = self._unknown_reason_id_for_blocking_unsafety(blocking_reason)
    if typed_reason_id in {
        UnknownReasonId.RETURN_COVERAGE_GAP,
        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
    }:
        return self._make_return_coverage_unknown_reason(
            typed_reason_id,
            blocking_reason,
            analysis1,
            analysis2,
            stage=stage,
        )
    if typed_reason_id == UnknownReasonId.OUTCOME_PARTITION_UNKNOWN:
        object_target_key = self._outcome_partition_unknown_object_target_key(
            blocking_reason,
            analysis1,
            analysis2,
        )
        object_evidence = self._outcome_partition_unknown_object_evidence(
            blocking_reason,
            analysis1,
            analysis2,
        )
        return make_unknown_reason(
            typed_reason_id,
            stage=stage,
            evidence_refs=(blocking_reason,),
            detail=blocking_reason,
            recovery_proof_kind=UnknownRecoveryProofKind.GUARD_PARTITION_COMPLETION,
            recovery_proof_obligations=(
                UnknownRecoveryProofObligation.create(
                    UnknownRecoveryProofKind.GUARD_PARTITION_COMPLETION,
                    "outcome_partition_resolution",
                    required_evidence=(
                        "unknown_outcome_guard",
                        "unknown_outcome_reason",
                        "must_diverge_or_return_proof",
                    ),
                    description="Resolve UnknownOutcome members into proved return/divergence outcomes.",
                ),
            ),
            proof_stage="outcome_partition_unknown",
            evidence_kind="outcome_partition",
            object_target_key=object_target_key,
            object_evidence=object_evidence,
            recovery_action="outcome_partition_resolution_required",
            action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
        )
    if typed_reason_id != UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY:
        return make_unknown_reason(
            typed_reason_id,
            stage=stage,
            evidence_refs=(blocking_reason,),
            detail=blocking_reason,
        )

    object_target_key = self._call_effect_blocking_object_target_key(
        blocking_reason,
        analysis1,
        analysis2,
    )
    if object_target_key is None:
        return make_unknown_reason(
            typed_reason_id,
            stage=stage,
            evidence_refs=(blocking_reason,),
            detail=blocking_reason,
        )

    return make_unknown_reason(
        typed_reason_id,
        stage=stage,
        evidence_refs=(blocking_reason,),
        detail=blocking_reason,
        recovery_proof_kind=UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
        recovery_proof_obligations=(
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF,
                "object_evidence_collected",
                required_evidence=(
                    "call_effect_summary",
                    "runtime_ref",
                    "callsite_storage",
                ),
                description="Collect object-derived call/effect evidence before using UNSAT as equivalence proof.",
            ),
        ),
        proof_stage="object_evidence_collected",
        evidence_kind="call_effect_summary",
        object_target_key=object_target_key,
        object_evidence=self._call_effect_blocking_object_evidence(
            blocking_reason,
            object_target_key,
            analysis1,
            analysis2,
        ),
        recovery_action="call_effect_summary_proof_required",
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
    )

def _impl__sat_unsafety_resolution_proof_is_complete(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    current_counterexample_raw: Optional[Mapping[str, Any]] = None,
) -> bool:
    if reason_record.reason_id != UnknownReasonId.SAT_UNSAFETY.value:
        return False
    if reason_record.recovery_proof_kind != UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value:
        return False
    proof_obligation_id = self._normalize_nested_tuple(reason_record.proof_obligation_id)
    if proof_obligation_id is None:
        return False
    current_model_sha256 = self._counterexample_model_fingerprint(current_counterexample_raw)
    if current_model_sha256 is None:
        return False
    for evidence in self._completed_recovery_proof_evidence(analysis1, analysis2):
        evidence_proof_id = self._sat_unsafety_resolution_proof_id_from_evidence(evidence)
        if evidence_proof_id != proof_obligation_id:
            continue
        proof_content = self._evidence_get(evidence, "proof_content")
        if not isinstance(proof_content, Mapping):
            continue
        counterexample_replay = proof_content.get("counterexample_replay")
        if not isinstance(counterexample_replay, Mapping):
            continue
        evidence_model_sha256 = self._evidence_text(
            counterexample_replay,
            "counterexample_model_sha256",
        )
        if evidence_model_sha256 != current_model_sha256:
            continue
        return True
    return False

def _impl__record_completed_sat_counterexample_replay_proof(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    counterexample_raw: Optional[Mapping[str, Any]] = None,
    fixed_model_assertion_count: int = 0,
    replay_source: str,
) -> None:
    if not self.enable_completed_recovery_proofs:
        return
    if reason_record.reason_id != UnknownReasonId.SAT_UNSAFETY.value:
        return
    if reason_record.recovery_proof_kind != UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value:
        return
    proof_obligation_id = self._normalize_nested_tuple(reason_record.proof_obligation_id)
    object_target_key = self._normalize_nested_tuple(reason_record.object_target_key)
    if proof_obligation_id is None or not isinstance(object_target_key, tuple):
        return
    if not counterexample_raw:
        return
    if fixed_model_assertion_count <= 0:
        return
    counterexample_model_sha256 = self._counterexample_model_fingerprint(counterexample_raw)
    if counterexample_model_sha256 is None:
        return

    records: List[Dict[str, Any]] = [
        dict(item)
        for item in getattr(analysis1, "completed_recovery_proof_evidence", ()) or ()
        if isinstance(item, Mapping)
    ]
    existing_ids = {
        self._normalize_nested_tuple(item.get("proof_obligation_id"))
        for item in records
    }
    if proof_obligation_id in existing_ids:
        return

    counterexample_keys = tuple(sorted(str(key) for key in (counterexample_raw or {}).keys()))
    records.append(
        {
            "object_derived": True,
            "status": "complete",
            "reason_id": UnknownReasonId.SAT_UNSAFETY.value,
            "recovery_proof_kind": UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value,
            "proof_stage": "sat_counterexample_safety",
            "evidence_kind": "active_unsafety_summary",
            "object_target_key": object_target_key,
            "proof_obligation_id": proof_obligation_id,
            "proof_source": replay_source,
            "proof_content": {
                "object_derived": True,
                "object_target_key": object_target_key,
                "counterexample_replay": {
                    "status": "replayed",
                    "replay_source": replay_source,
                    "fixed_model_assertion_count": fixed_model_assertion_count,
                    "counterexample_symbol_keys": counterexample_keys,
                    "counterexample_model_sha256": counterexample_model_sha256,
                },
                "active_unsafety_discharge": {
                    "status": "discharged",
                    "discharged_reason_refs": tuple(reason_record.evidence_refs),
                },
                "coverage_effect_safety": {
                    "status": "proven",
                    "coverage_status": "covered_by_counterexample_replay",
                    "effect_status": "no_active_effect_unsafety_for_replay_gate",
                },
            },
        }
    )
    analysis1.completed_recovery_proof_evidence = tuple(records)

def _impl__counterexample_model_fingerprint(
    cls,
    counterexample_raw: Optional[Mapping[str, Any]],
) -> Optional[str]:
    if not isinstance(counterexample_raw, Mapping) or not counterexample_raw:
        return None
    normalized = cls._normalize_counterexample_model_value(counterexample_raw)
    try:
        payload = json.dumps(
            normalized,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        )
    except (TypeError, ValueError):
        return None
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()

def _impl__normalize_counterexample_model_value(cls, value: Any) -> Any:
    if isinstance(value, Mapping):
        return {
            str(key): cls._normalize_counterexample_model_value(value[key])
            for key in sorted(value.keys(), key=lambda item: str(item))
        }
    if isinstance(value, (list, tuple)):
        return [cls._normalize_counterexample_model_value(item) for item in value]
    if isinstance(value, bool) or value is None:
        return value
    if isinstance(value, int):
        return str(value)
    if isinstance(value, float):
        return repr(value)
    return str(value)

def _impl__sat_unsafety_resolution_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
    if not cls._evidence_bool(evidence, "object_derived"):
        return None
    if cls._evidence_text(evidence, "status") not in {"complete", "completed", "proven"}:
        return None
    if cls._evidence_text(evidence, "reason_id") != UnknownReasonId.SAT_UNSAFETY.value:
        return None
    proof_kind = cls._evidence_text(evidence, "recovery_proof_kind")
    if proof_kind != UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value:
        return None
    proof_stage = cls._evidence_text(evidence, "proof_stage")
    if proof_stage != "sat_counterexample_safety":
        return None
    evidence_kind = cls._evidence_text(evidence, "evidence_kind")
    if evidence_kind != "active_unsafety_summary":
        return None
    if cls._evidence_has_any(evidence, cls._COMPLETED_PROOF_BLOCKER_FIELDS):
        return None
    object_target_key = cls._normalize_nested_tuple(cls._evidence_get(evidence, "object_target_key"))
    if not isinstance(object_target_key, tuple):
        return None
    proof_id = build_proof_obligation_id(
        UnknownReasonId.SAT_UNSAFETY.value,
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
    if not cls._evidence_bool(proof_content, "object_derived"):
        return None
    if cls._normalize_nested_tuple(proof_content.get("object_target_key")) != object_target_key:
        return None
    if cls._evidence_has_any_recursive(proof_content, cls._COMPLETED_PROOF_BLOCKER_FIELDS):
        return None
    required_sections = (
        "counterexample_replay",
        "active_unsafety_discharge",
        "coverage_effect_safety",
    )
    if any(section not in proof_content for section in required_sections):
        return None
    for section in required_sections:
        if not cls._completed_proof_section_is_clean(proof_content.get(section)):
            return None
    counterexample_replay = proof_content.get("counterexample_replay")
    if not isinstance(counterexample_replay, Mapping):
        return None
    fixed_model_assertion_count = counterexample_replay.get("fixed_model_assertion_count")
    if (
        isinstance(fixed_model_assertion_count, bool)
        or not isinstance(fixed_model_assertion_count, int)
        or fixed_model_assertion_count <= 0
    ):
        return None
    counterexample_symbol_keys = cls._normalize_nested_tuple(
        counterexample_replay.get("counterexample_symbol_keys")
    )
    if not isinstance(counterexample_symbol_keys, tuple) or not counterexample_symbol_keys:
        return None
    counterexample_model_sha256 = cls._evidence_text(
        counterexample_replay,
        "counterexample_model_sha256",
    )
    if (
        len(counterexample_model_sha256) != 64
        or any(char not in "0123456789abcdef" for char in counterexample_model_sha256)
    ):
        return None
    return proof_id

def _impl__make_sat_unsafety_unknown_reason(
    self,
    sat_unsafety_reasons: Sequence[str],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    case1: Any,
    case2: Any,
    pair_id: str,
    stage: str,
) -> UnknownReasonRecord:
    object_target_key = self._sat_unsafety_object_target_key(
        sat_unsafety_reasons,
        analysis1,
        analysis2,
        case1=case1,
        case2=case2,
        pair_id=pair_id,
    )
    return make_unknown_reason(
        UnknownReasonId.SAT_UNSAFETY,
        stage=stage,
        pair_or_case=pair_id,
        evidence_refs=tuple(sat_unsafety_reasons),
        detail=", ".join(str(reason) for reason in sat_unsafety_reasons),
        recovery_proof_kind=UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION,
        recovery_proof_obligations=(
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION,
                "sat_counterexample_safety",
                required_evidence=(
                    "counterexample_replay",
                    "active_unsafety_discharge",
                    "coverage_effect_safety",
                ),
                description=(
                    "Replay the SAT counterexample and discharge all active "
                    "coverage/effect unsafety before accepting disequivalence."
                ),
            ),
        ),
        proof_stage="sat_counterexample_safety",
        evidence_kind="active_unsafety_summary",
        object_target_key=object_target_key,
        object_evidence=self._sat_unsafety_object_evidence(
            sat_unsafety_reasons,
            object_target_key,
            analysis1,
            analysis2,
            case1=case1,
            case2=case2,
        ),
        recovery_action="sat_unsafety_resolution_required",
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
    )

def _impl__make_sat_counterexample_ambiguous_unknown_reason(
    self,
    evidence_refs: Sequence[str],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    case1: Any,
    case2: Any,
    pair_id: str,
    stage: str,
) -> UnknownReasonRecord:
    object_target_key = self._sat_counterexample_ambiguous_object_target_key(
        evidence_refs,
        analysis1,
        analysis2,
        case1=case1,
        case2=case2,
        pair_id=pair_id,
    )
    return make_unknown_reason(
        UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS,
        stage=stage,
        pair_or_case=pair_id,
        evidence_refs=tuple(str(ref) for ref in evidence_refs or ()),
        detail="SAT counterexample is ambiguous under replayed case partition",
        recovery_proof_kind=UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION,
        recovery_proof_obligations=(
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION,
                "sat_counterexample_safety",
                required_evidence=(
                    "counterexample_replay",
                    "case_partition_disambiguation",
                    "coverage_effect_safety",
                ),
                description=(
                    "Replay the SAT counterexample and prove it identifies a unique "
                    "disequivalence witness under the active case partition."
                ),
            ),
        ),
        proof_stage="sat_counterexample_safety",
        evidence_kind="case_partition_replay",
        object_target_key=object_target_key,
        object_evidence={
            "object_derived": True,
            "evidence_version": 1,
            "evidence_kind": "case_partition_replay",
            "object_target_kind": object_target_key[0],
            "object_target_key": object_target_key,
            "left": self._sat_unsafety_side_object_evidence("left", analysis1, case1),
            "right": self._sat_unsafety_side_object_evidence("right", analysis2, case2),
            "ambiguity_evidence_refs": tuple(str(ref) for ref in evidence_refs or ()),
        },
        recovery_action="sat_counterexample_disambiguation_required",
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
    )

def _impl__sat_unsafety_object_evidence(
    self,
    sat_unsafety_reasons: Sequence[str],
    object_target_key: Tuple[Any, ...],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    case1: Any,
    case2: Any,
) -> Dict[str, Any]:
    return {
        "object_derived": True,
        "evidence_version": 1,
        "evidence_kind": "active_unsafety_summary",
        "object_target_kind": object_target_key[0] if object_target_key else None,
        "object_target_key": object_target_key,
        "left": self._sat_unsafety_side_object_evidence("left", analysis1, case1),
        "right": self._sat_unsafety_side_object_evidence("right", analysis2, case2),
        "active_unsafety": tuple(
            self._sat_unsafety_reason_object_evidence(
                reason,
                analysis1,
                analysis2,
            )
            for reason in sat_unsafety_reasons
        ),
    }

def _impl__sat_unsafety_side_object_evidence(
    self,
    side_label: str,
    analysis: FunctionReturnAnalysis,
    case: Any,
) -> Dict[str, Any]:
    return {
        "side": side_label,
        "function": getattr(analysis, "function_name", None),
        "analysis_key": self._analysis_entry_key(analysis),
        "return_storage": self._return_storage_object_key(analysis),
        "return_case": self._return_case_partition_member_object_key(
            case,
            getattr(case, "return_info", None),
        ),
        "unknown_event_count": int(getattr(analysis, "unknown_event_count", 0) or 0),
        "analysis_notes": tuple(getattr(analysis, "analysis_notes", ()) or ()),
    }

def _impl__sat_unsafety_reason_object_evidence(
    self,
    reason: str,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Dict[str, Any]:
    label, _reason_text = self._split_blocking_reason(reason)
    reason_kind = self._blocking_reason_kind(reason)
    analysis = analysis1 if label == "function1" else analysis2 if label == "function2" else None
    canonical_reason = f"{label}:{reason_kind}" if label else reason_kind
    target = self._sat_unsafety_reason_object_target_key(
        reason,
        analysis1,
        analysis2,
    )
    evidence: Dict[str, Any] = {
        "reason": str(reason),
        "side": label,
        "reason_kind": reason_kind,
        "object_target_key": target,
    }
    if analysis is not None and reason_kind in self._CALL_EFFECT_PROOF_RECOVERABLE_UNSAFETY_REASONS:
        call_effect_target = self._call_effect_blocking_object_target_key(
            canonical_reason,
            analysis1,
            analysis2,
        )
        evidence["call_effect"] = self._call_effect_blocking_object_evidence(
            canonical_reason,
            call_effect_target,
            analysis1,
            analysis2,
        )
    elif analysis is not None and reason_kind in {"return_coverage_gap", "return_coverage_inconclusive"}:
        evidence["return_coverage"] = {
            "object_target_key": self._return_coverage_object_target_key(
                canonical_reason,
                analysis1,
                analysis2,
            ),
            "return_partition": self._return_partition_object_key(analysis),
            "guard_disjunction": self._return_guard_disjunction_object_key(analysis),
        }
    elif analysis is not None and reason_kind == "outcome_partition_unknown":
        evidence["outcome_partition"] = self._outcome_partition_unknown_object_evidence(
            canonical_reason,
            analysis1,
            analysis2,
        )
    elif analysis is not None:
        evidence["analysis"] = {
            "analysis_key": self._analysis_entry_key(analysis),
            "return_storage": self._return_storage_object_key(analysis),
            "return_partition": self._return_partition_object_key(analysis),
            "guard_disjunction": self._return_guard_disjunction_object_key(analysis),
        }
    return evidence

def _impl__sat_unsafety_object_target_key(
    self,
    sat_unsafety_reasons: Sequence[str],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    case1: Any,
    case2: Any,
    pair_id: str,
) -> Tuple[Any, ...]:
    return (
        "sat_unsafety",
        ("pair", pair_id),
        self._sat_unsafety_side_object_key("left", analysis1, case1),
        self._sat_unsafety_side_object_key("right", analysis2, case2),
        (
            "active_unsafety",
            tuple(
                self._sat_unsafety_reason_object_target_key(
                    reason,
                    analysis1,
                    analysis2,
                )
                for reason in sat_unsafety_reasons
            ),
        ),
    )

def _impl__sat_counterexample_ambiguous_object_target_key(
    self,
    evidence_refs: Sequence[str],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    case1: Any,
    case2: Any,
    pair_id: str,
) -> Tuple[Any, ...]:
    return (
        "sat_counterexample_ambiguous",
        ("pair", pair_id),
        self._sat_unsafety_side_object_key("left", analysis1, case1),
        self._sat_unsafety_side_object_key("right", analysis2, case2),
        ("ambiguity_evidence_refs", tuple(str(ref) for ref in evidence_refs or ())),
    )

def _impl__sat_unsafety_side_object_key(
    self,
    side_label: str,
    analysis: FunctionReturnAnalysis,
    case: Any,
) -> Tuple[Any, ...]:
    return self._artifact_stable_key_for_analysis((
        "sat_unsafety_side",
        side_label,
        self._analysis_entry_key(analysis),
        self._return_storage_object_key(analysis),
        self._return_case_partition_member_object_key(
            case,
            getattr(case, "return_info", None),
        ),
    ), analysis)

def _impl__sat_unsafety_reason_object_target_key(
    self,
    reason: str,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Tuple[Any, ...]:
    label, _reason_text = self._split_blocking_reason(reason)
    reason_kind = self._blocking_reason_kind(reason)
    analysis = analysis1 if label == "function1" else analysis2 if label == "function2" else None
    if analysis is None:
        return ("global_unsafety", reason_kind)
    canonical_reason = f"{label}:{reason_kind}" if label else reason_kind
    if reason_kind in {"return_coverage_gap", "return_coverage_inconclusive"}:
        target = self._return_coverage_object_target_key(canonical_reason, analysis1, analysis2)
        return (
            "coverage_unsafety",
            label,
            reason_kind,
            self._artifact_stable_key_for_analysis(target, analysis),
        )
    if reason_kind == "outcome_partition_unknown":
        target = self._outcome_partition_unknown_object_target_key(canonical_reason, analysis1, analysis2)
        return (
            "outcome_partition_unsafety",
            label,
            reason_kind,
            self._artifact_stable_key_for_analysis(target, analysis),
        )
    if reason_kind in self._CALL_EFFECT_PROOF_RECOVERABLE_UNSAFETY_REASONS:
        target = self._call_effect_blocking_object_target_key(canonical_reason, analysis1, analysis2)
        return (
            "call_effect_unsafety",
            label,
            reason_kind,
            self._artifact_stable_key_for_analysis(target, analysis),
        )
    deferred_keys: Tuple[Any, ...] = ()
    if reason_kind in {
        "indirect_control_flow_unresolved",
        "effect_call_argument_evidence_incomplete",
        "bounded_call_refinement_deferred_target_unresolved",
    }:
        deferred_keys = tuple(
            self._deferred_call_object_target_key(info, analysis=analysis, side_label=label)
            for info in getattr(analysis, "deferred_calls", {}).values()
            if info is not None
        )
    return self._artifact_stable_key_for_analysis((
        "analysis_unsafety",
        label,
        reason_kind,
        self._analysis_entry_key(analysis),
        self._return_storage_object_key(analysis),
        self._return_partition_object_key(analysis),
        self._return_guard_disjunction_object_key(analysis),
        deferred_keys,
    ), analysis)

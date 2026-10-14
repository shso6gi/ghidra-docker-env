"""Stateless method implementations extracted from ``scripts.function_tracer_pcode.proof.strategies.base``."""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple
import hashlib
import json
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis
from scripts.function_tracer_pcode.proof.strategies.proof_gates._shared import (
    CrossSideIdentification,
    UnknownReasonId,
    UnknownReasonRecord,
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    UnknownRecoveryProofObligation,
    build_proof_obligation_id,
    comparison_evidence,
    make_internal_v2_reason_diagnostic,
    make_unknown_reason,
    store_comparison_evidence,
)
from scripts.function_tracer_pcode.proof.sat_safety_resolution import (
    COUNTEREXAMPLE_REPLAY_MISSING_REF,
    SAT_SAFETY_RECOVERY_REQUIREMENTS,
    SAT_SAFETY_TYPED_REASON_IDS,
    classify_sat_safety_blocker,
    replay_may_resolve_sat_safety_reason,
    sat_safety_reason_id_for_refs,
)
from scripts.function_tracer_pcode.authority.domains.sat_safety_sites import (
    SAT_SAFETY_AMBIGUITY_COMPLETED_SITE,
    SAT_SAFETY_AMBIGUITY_OBSERVED_SITE,
    SAT_SAFETY_BLOCKER_COMPLETED_SITE,
    SAT_SAFETY_BLOCKER_OBSERVED_SITE,
)

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

#: decisive gate が入力対応の不足を示す reason の label と種類（Issue #167）。
INPUT_CORRESPONDENCE_REASON_LABEL = "pair"
INPUT_CORRESPONDENCE_REASON_KIND = "input_correspondence"


def _impl__input_correspondence_unsafety_reasons(
    self,
    query_correspondence: Any,
    *,
    authority_correspondence: Any,
) -> List[str]:
    """最終 InputCorrespondence が EQ / NOT_EQ の確定に足りないときの reason。

    ``authority_correspondence`` は dispatch frame の prepared pair（互換経路では
    raw pair から作った）relation、``query_correspondence`` は query の premise を
    描いた builder が報告した relation。判定は ``InputCorrespondenceSet`` の型付きの
    値だけを見る（診断文字列や ``sat_pair_info`` は読まない）。返す reason は
    EQ 側（equivalence blocking）と NOT_EQ 側（SAT unsafety）の両方へ入れる。

    * どちらかが無い → ``unavailable``（配線漏れ。0 件であるべき）。
    * digest が違う → ``unbound``（query が別の relation で作られた）。
    * set が不十分（R0 / 未 closure の R5 / 隠れた register alias / 構造欠陥）。
    * 両側 0 parameter の EMPTY は十分（不足扱いしない）。
    """

    from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
        InputCorrespondenceSet,
    )

    label = INPUT_CORRESPONDENCE_REASON_LABEL
    kind = INPUT_CORRESPONDENCE_REASON_KIND
    if type(authority_correspondence) is not InputCorrespondenceSet:
        return [f"{label}:{kind}:unavailable:authority"]
    if type(query_correspondence) is not InputCorrespondenceSet:
        return [f"{label}:{kind}:unavailable:query"]
    if query_correspondence.digest != authority_correspondence.digest:
        return [f"{label}:{kind}:unbound:{query_correspondence.digest[:16]}"]
    if authority_correspondence.decisive_sufficient:
        return []
    return [f"{label}:{ref}" for ref in authority_correspondence.insufficiency_evidence()]


def _is_input_correspondence_reason(reason: Any) -> bool:
    return str(reason or "").startswith(
        f"{INPUT_CORRESPONDENCE_REASON_LABEL}:{INPUT_CORRESPONDENCE_REASON_KIND}:"
    )


def _impl__pair_return_width_unsafety_reasons(
    self,
    base_ctx: Mapping[str, Any],
    pair_id: str,
) -> List[str]:
    """SAT-safety blockers from an unproven return-width observation of a pair.

    The canonical return-width observation proves which bits of the compared
    values are semantic (ABI return slot, parameter correspondence across
    different register widths).  Equal raw widths do not establish that: a
    128-bit ``q0`` surface carrying a 64-bit double compares caller-owned
    upper bits.  When the observation for this pair is blocked, a SAT on it
    may only separate non-semantic bits, so it must not be decisive
    (Issue #28, airy/Sign B1_B2).
    """
    prepared = (base_ctx.get("return_width_observations_by_pair") or {}).get(pair_id)
    if prepared is None or getattr(prepared, "proven", False):
        return []
    semantic_blockers = [
        item for item in (getattr(prepared, "blockers", ()) or ())
        if str(getattr(item, "blocker_kind", "")) in SEMANTIC_RETURN_WIDTH_BLOCKER_KINDS
    ]
    if not semantic_blockers:
        # Only artifact/closure plumbing is missing (proof bundle, contract
        # sealing, query lowering); the compared bits themselves are bound.
        return []
    detail = ", ".join(
        f"{item.blocker_kind}:{getattr(item, 'missing_slot', 'unknown')}"
        for item in semantic_blockers
    )
    self._debug_print(
        f"  Pair {pair_id}: return-width observation blocked ({detail}); SAT is not decisive"
    )
    return ["function1:return_width_observation_blocked"]


# Width blockers that mean the *inputs* of the compared queries are not
# semantically bound or the compared widths are incompatible: parameters of
# different register widths bound only on their overlap (airy/Sign: a 64-bit
# double against the whole 128-bit q0), arity/bijection failures, width
# alignment.  Incomplete unary return-width seeds and missing proof plumbing
# (bundle, contract seal, query lowering) already gate EQUIVALENT and the
# width bridge for unequal return widths; they are not in this set so that
# equal-width constant-return witnesses stay decisive.
SEMANTIC_RETURN_WIDTH_BLOCKER_KINDS = frozenset({
    "input_correspondence",
    "top_level_parameters",
    "parameter_arity",
    "parameter_index_bijection",
    "pair_width_compatibility",
    "canonical_width_alignment",
    "call_site_return_width",
    "return_coverage",
})


def _impl__counterexample_replay_reasons(
    self,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
) -> Tuple[str, ...]:
    """Require bound replay evidence before accepting any SAT as NOT_EQ.

    Whether the two functions share a name is unrelated to semantic soundness,
    so the requirement is uniform (Issue #28): every decisive counterexample
    must carry a replay proof bound to its query, model, premise and pair.
    The reason id keeps its historical name until it is renamed separately.
    """
    if analysis1 is None or analysis2 is None:
        return ()
    return (COUNTEREXAMPLE_REPLAY_MISSING_REF,)

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
    if _is_input_correspondence_reason(reason):
        # UNSAT を EQ closure と認めない（入力対応が不十分）。既存の登録済み reason。
        return "comparison_equivalence_closure_unproven"
    if reason_kind == "return_coverage_gap":
        return UnknownReasonId.RETURN_COVERAGE_GAP
    if reason_kind == "return_coverage_inconclusive":
        return UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
    if reason_kind == "outcome_partition_completion_unproven":
        return "outcome_partition_completion_unproven"
    unary_outcome_ids = {
        item.value: item for item in (
            UnknownReasonId.OUTCOME_CFG_REACHABILITY_INCOMPLETE,
            UnknownReasonId.OUTCOME_PATH_REGION_INCOMPLETE,
            UnknownReasonId.OUTCOME_MEMBER_UNCLASSIFIED,
            UnknownReasonId.OUTCOME_RETURN_CONSISTENCY_UNKNOWN,
            UnknownReasonId.OUTCOME_RETURN_VALUE_CONFLICT,
            UnknownReasonId.OUTCOME_CROSS_KIND_OVERLAP,
            UnknownReasonId.OUTCOME_PARTITION_RESIDUAL_SAT,
            UnknownReasonId.OUTCOME_PARTITION_TOTALITY_TIMEOUT,
        )
    }
    if reason_kind in unary_outcome_ids:
        return unary_outcome_ids[reason_kind]
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
    if reason_kind == UnknownReasonId.EXPANSION_CASE_BUDGET_EXCEEDED.value:
        # Issue #131: 切り捨てが起きた関数の blocker は専用 reason のまま扱う
        # （既定の効果不完全性へ丸めない）。
        return UnknownReasonId.EXPANSION_CASE_BUDGET_EXCEEDED
    call_effect_reasons = {
        "unsupported_call_effect_summary": "unsupported_call_effect_semantics",
        "effect_summary_path_coverage_incomplete": "effect_observation_coverage_incomplete",
        "effect_store_location_unmodeled": "effect_observation_coverage_incomplete",
        "effect_global_read_identity_unavailable": "effect_observation_coverage_incomplete",
        "effect_surface_composition_incomplete": "effect_observation_coverage_incomplete",
        # Issue #131: 効果面の切り捨ては既存の効果観測不完全性へ写像する。
        "effect_expansion_case_budget_exceeded": "effect_observation_coverage_incomplete",
        "effect_call_argument_evidence": "call_argument_extraction_incomplete",
        "effect_call_argument_evidence_incomplete": "call_argument_extraction_incomplete",
        "effect_call_target_resolution_evidence": "call_target_resolution_unproven",
        "bounded_call_refinement_argument_alignment_failed": "call_argument_extraction_incomplete",
        "bounded_call_refinement_deferred_target_unresolved": "call_target_resolution_unproven",
        "bounded_call_refinement_return_summary_unusable": "callee_return_summary_incomplete",
    }
    return call_effect_reasons.get(
        reason_kind, "effect_observation_coverage_incomplete"
    )

def _impl__make_blocking_unsafety_unknown_reason(
    self,
    blocking_reason: str,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    stage: str,
):
    typed_reason_id = self._unknown_reason_id_for_blocking_unsafety(blocking_reason)
    if _is_input_correspondence_reason(blocking_reason):
        return make_internal_v2_reason_diagnostic(
            typed_reason_id,
            stage=stage,
            evidence_refs=(blocking_reason,),
            detail=blocking_reason,
        )
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
    unary_outcome_reason_ids = {
        "outcome_partition_completion_unproven",
        UnknownReasonId.OUTCOME_CFG_REACHABILITY_INCOMPLETE,
        UnknownReasonId.OUTCOME_PATH_REGION_INCOMPLETE,
        UnknownReasonId.OUTCOME_MEMBER_UNCLASSIFIED,
        UnknownReasonId.OUTCOME_RETURN_CONSISTENCY_UNKNOWN,
        UnknownReasonId.OUTCOME_RETURN_VALUE_CONFLICT,
        UnknownReasonId.OUTCOME_CROSS_KIND_OVERLAP,
        UnknownReasonId.OUTCOME_PARTITION_RESIDUAL_SAT,
        UnknownReasonId.OUTCOME_PARTITION_TOTALITY_TIMEOUT,
    }
    if typed_reason_id in unary_outcome_reason_ids:
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
        reason_factory = (
            make_internal_v2_reason_diagnostic
            if type(typed_reason_id) is str
            else make_unknown_reason
        )
        return reason_factory(
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
            proof_stage="unary_outcome_partition",
            evidence_kind="outcome_partition",
            object_target_key=object_target_key,
            object_evidence=object_evidence,
            recovery_action="unary_outcome_partition_proof_required",
            action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
        )
    from scripts.function_tracer_pcode.authority.domains.call_effect import CALL_EFFECT_REASON_SPECS

    if typed_reason_id not in CALL_EFFECT_REASON_SPECS:
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
        return make_internal_v2_reason_diagnostic(
            typed_reason_id,
            stage=stage,
            evidence_refs=(blocking_reason,),
            detail=blocking_reason,
        )

    return make_internal_v2_reason_diagnostic(
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
    expected_binding: Any = None,
    expected_execution_receipt_digest: Optional[str] = None,
) -> bool:
    if reason_record.reason_id not in SAT_SAFETY_TYPED_REASON_IDS:
        return False
    if reason_record.recovery_proof_kind != UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value:
        return False
    if not replay_may_resolve_sat_safety_reason(
        reason_record.reason_id, reason_record.evidence_refs or ()
    ):
        # この gate を完了させる証拠は counterexample の replay の証明だけである。
        # replay は model の値が実際の実行で同時に起こり得ることも、解析が捨てた
        # 経路・効果・入力の上位 bit（入力対応）が無いことも示さないので、replay 型
        # でない理由は、記録済みの証拠があっても解消しない（plan v4 I5・Q6）。
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
        if expected_binding is not None and not _replay_evidence_matches_binding(
            self,
            counterexample_replay,
            expected_binding,
            expected_execution_receipt_digest,
        ):
            continue
        return _v2_complete_sat_unsafety_and_true(self, reason_record, proof_content)
    return False


def _replay_binding_fields(
    evidence_binding: Any,
    execution_receipt_digest: Optional[str],
) -> Dict[str, Any]:
    """Proof-content fields that pin a replay to one query/model/premise/pair."""
    if evidence_binding is None:
        return {}
    fields: Dict[str, Any] = {
        "formula_digest": str(evidence_binding.formula_digest),
        "model_digest": str(evidence_binding.model_digest),
        "premise_digest": str(evidence_binding.premise_digest),
        "pair_key": tuple(evidence_binding.pair_key),
    }
    if execution_receipt_digest:
        fields["solver_execution_receipt_digest"] = str(execution_receipt_digest)
    return fields


def _replay_evidence_matches_binding(
    owner: Any,
    counterexample_replay: Mapping[str, Any],
    expected_binding: Any,
    expected_execution_receipt_digest: Optional[str],
) -> bool:
    """A replay proof may only discharge the witness it was recorded for."""
    for field_name in ("formula_digest", "model_digest", "premise_digest"):
        if owner._evidence_text(counterexample_replay, field_name) != str(
            getattr(expected_binding, field_name)
        ):
            return False
    recorded_pair = owner._normalize_nested_tuple(counterexample_replay.get("pair_key"))
    if recorded_pair != owner._normalize_nested_tuple(tuple(expected_binding.pair_key)):
        return False
    if expected_execution_receipt_digest and owner._evidence_text(
        counterexample_replay, "solver_execution_receipt_digest"
    ) != str(expected_execution_receipt_digest):
        return False
    return True


def _impl__record_pairwise_counterexample_replay_proof(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    base_ctx: Mapping[str, Any],
    counterexample_raw: Optional[Mapping[str, Any]],
    binding: Any,
    execution_receipt_digest: Optional[str],
    pair_id: str,
) -> bool:
    """Record the pairwise case-partition replay as a bound replay proof.

    Only a SAT with a concrete model, at least one fixed-model assertion, a
    validated solver execution receipt and an evidence binding qualifies; the
    replay itself (feasibility, per-side consistency, no equal cross-case
    pair) has already succeeded when this is called.
    """
    from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
        count_counterexample_model_assertions,
    )

    if not counterexample_raw or binding is None or not execution_receipt_digest:
        self._debug_print(
            f"  Pair {pair_id}: replay proof not recorded (model, binding or receipt missing)"
        )
        return False
    fixed_count = count_counterexample_model_assertions(base_ctx, counterexample_raw)
    if fixed_count <= 0:
        self._debug_print(
            f"  Pair {pair_id}: replay proof not recorded (model fixes no declared symbol)"
        )
        return False
    self._record_completed_sat_counterexample_replay_proof(
        reason_record,
        analysis1,
        analysis2,
        counterexample_raw=counterexample_raw,
        fixed_model_assertion_count=fixed_count,
        replay_source="pairwise_case_split_counterexample_validation",
        evidence_binding=binding,
        execution_receipt_digest=execution_receipt_digest,
    )
    return True

def _impl__record_completed_sat_counterexample_replay_proof(
    self,
    reason_record: UnknownReasonRecord,
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    counterexample_raw: Optional[Mapping[str, Any]] = None,
    fixed_model_assertion_count: int = 0,
    replay_source: str,
    evidence_binding: Any = None,
    execution_receipt_digest: Optional[str] = None,
) -> None:
    if not self.enable_completed_recovery_proofs:
        return
    if reason_record.reason_id not in SAT_SAFETY_TYPED_REASON_IDS:
        return
    if reason_record.recovery_proof_kind != UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value:
        return
    if not replay_may_resolve_sat_safety_reason(
        reason_record.reason_id, reason_record.evidence_refs or ()
    ):
        # replay が解消してよいのは replay 型の理由だけ（解析の不安全・入力対応は
        # pending のまま）。証拠を残すと、後で別の gate が同じ obligation を読む。
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
        for item in comparison_evidence(records)
    }
    if proof_obligation_id in existing_ids:
        return

    counterexample_keys = tuple(sorted(str(key) for key in (counterexample_raw or {}).keys()))
    records.append(
        {
            "object_derived": True,
            "status": "complete",
            "reason_id": reason_record.reason_id,
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
                    **_replay_binding_fields(evidence_binding, execution_receipt_digest),
                },
                "active_unsafety_discharge": {
                    "status": "discharged",
                    "discharged_reason_refs": tuple(reason_record.evidence_refs),
                },
                # replay 型の obligation には解析の不安全の ref が無い（記録の前に
                # 確かめた）。replay が被覆や効果を証明したとは主張しない。
                "coverage_effect_safety": {
                    "status": "proven",
                    "coverage_status": "no_active_coverage_unsafety_in_replay_obligation",
                    "effect_status": "no_active_effect_unsafety_in_replay_obligation",
                },
            },
        }
    )
    store_comparison_evidence(analysis1, records, identification=CrossSideIdentification.CORRESPONDENCE)

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
    evidence_reason_id = cls._evidence_text(evidence, "reason_id")
    if evidence_reason_id not in SAT_SAFETY_TYPED_REASON_IDS:
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
        evidence_reason_id,
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
    # この証拠は counterexample の replay の証明である。replay 型でない理由を
    # 解消したと主張する証拠（以前の版が記録した、または手で組んだもの）は
    # 証明として数えない（plan v4 I5）。
    active_unsafety_discharge = proof_content.get("active_unsafety_discharge")
    if not isinstance(active_unsafety_discharge, Mapping):
        return None
    discharged_reason_refs = cls._normalize_nested_tuple(
        active_unsafety_discharge.get("discharged_reason_refs")
    )
    if not isinstance(discharged_reason_refs, tuple) or not replay_may_resolve_sat_safety_reason(
        evidence_reason_id, discharged_reason_refs
    ):
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
    counterexample_binding: Any = None,
) -> UnknownReasonRecord:
    object_target_key = self._sat_unsafety_object_target_key(
        sat_unsafety_reasons,
        analysis1,
        analysis2,
        case1=case1,
        case2=case2,
        pair_id=pair_id,
    )
    if counterexample_binding is not None:
        object_target_key = (
            *object_target_key,
            (
                "counterexample_evidence_binding",
                counterexample_binding.formula_digest,
                counterexample_binding.model_digest,
                counterexample_binding.premise_digest,
                counterexample_binding.pair_key,
            ),
        )
    compatibility_reason_id = sat_safety_reason_id_for_refs(
        str(item) for item in sat_unsafety_reasons
    )
    # 回復の要求は blocker の型で決まる（解析の不安全は replay では解消しない）。
    required_evidence, description = SAT_SAFETY_RECOVERY_REQUIREMENTS[
        classify_sat_safety_blocker(
            compatibility_reason_id, tuple(str(item) for item in sat_unsafety_reasons)
        ).resolution
    ]
    return _v2_observe_sat_unsafety_reason(make_internal_v2_reason_diagnostic(
        compatibility_reason_id,
        stage=stage,
        pair_or_case=pair_id,
        evidence_refs=tuple(sat_unsafety_reasons),
        detail=", ".join(str(reason) for reason in sat_unsafety_reasons),
        recovery_proof_kind=UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION,
        recovery_proof_obligations=(
            UnknownRecoveryProofObligation.create(
                UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION,
                "sat_counterexample_safety",
                required_evidence=required_evidence,
                description=description,
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
    ),
        counterexample_binding=counterexample_binding,
        defer_until_terminal=(stage == "S_PAIRWISE"),
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
    return _v2_observe_sat_ambiguity_reason(make_unknown_reason(
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
    ))


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
    elif analysis is not None and reason_kind == "outcome_partition_completion_unproven":
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
        "counterexample_safety_gate",
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
    if _is_input_correspondence_reason(reason):
        return ("input_correspondence_unsafety", str(reason))
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
    if reason_kind == "outcome_partition_completion_unproven":
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


def _v2_observe_sat_unsafety_reason(
    reason_record: UnknownReasonRecord,
    *,
    counterexample_binding: Any = None,
    defer_until_terminal: bool = False,
) -> UnknownReasonRecord:
    _emit_v2_sat_safety_blockers_observed(
        tuple(str(ref) for ref in reason_record.evidence_refs),
        reason_record.object_target_key,
        counterexample_binding=counterexample_binding,
        defer_until_terminal=defer_until_terminal,
    )
    return reason_record


def _v2_observe_sat_ambiguity_reason(reason_record: UnknownReasonRecord) -> UnknownReasonRecord:
    _emit_v2_sat_safety_ambiguity_observed(
        tuple(str(ref) for ref in reason_record.evidence_refs),
        reason_record.object_target_key,
    )
    return reason_record


def _v2_complete_sat_unsafety_and_true(
    owner: Any,
    reason_record: UnknownReasonRecord,
    proof_content: Mapping[str, Any],
) -> bool:
    _emit_v2_sat_safety_blockers_completed_if_observed(
        tuple(str(ref) for ref in reason_record.evidence_refs),
        owner._normalize_nested_tuple(reason_record.object_target_key),
        proof_artifact_digest=_v2_sat_safety_proof_digest(proof_content),
    )
    return True


def _impl__supersede_rejected_witness_blocker(
    self,
    kind: str,
    evidence_refs: Sequence[str],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    case1: Any,
    case2: Any,
    pair_id: str,
    reason_record: UnknownReasonRecord,
    decisive_binding: Any,
) -> bool:
    """Retire a witness-scoped blocker once another witness is validated.

    A rejected candidate counterexample (ambiguous partition replay, or a SAT
    whose replay proof could not be recorded) only says that *that* model is
    not a witness; it is not an analysis-level unsafety.  A validated,
    bound counterexample on another case pair therefore supersedes it.  The
    completion artifact names the superseding witness so the audit trail
    shows why the blocker no longer applies (Issue #28).

    Returns whether the blocker was retired.  An analysis-level unsafety is not
    witness-scoped and is never retired here (plan v4 I5).
    """
    proof_content = {
        "object_target_key": self._normalize_nested_tuple(reason_record.object_target_key),
        "superseded_by_validated_witness": {
            "formula_digest": str(decisive_binding.formula_digest),
            "model_digest": str(decisive_binding.model_digest),
            "premise_digest": str(decisive_binding.premise_digest),
            "pair_key": tuple(decisive_binding.pair_key),
        },
    }
    proof_digest = _v2_sat_safety_proof_digest(proof_content)
    refs = tuple(str(ref) for ref in evidence_refs or ())
    if kind == "ambiguity":
        target_key = self._sat_counterexample_ambiguous_object_target_key(
            evidence_refs,
            analysis1,
            analysis2,
            case1=case1,
            case2=case2,
            pair_id=pair_id,
        )
        _emit_v2_sat_safety_ambiguity_if_observed(
            refs, target_key, proof_artifact_digest=proof_digest,
        )
        return True
    if not replay_may_resolve_sat_safety_reason(reason_record.reason_id, refs):
        # 別の witness の検証が退けてよいのは、その witness に固有の replay 型の
        # blocker だけ。解析の不安全は witness に固有でないので完了させない。
        return False
    _emit_v2_sat_safety_blockers_completed_if_observed(
        refs,
        self._normalize_nested_tuple(reason_record.object_target_key),
        proof_artifact_digest=proof_digest,
    )
    return True


def _impl__complete_v2_sat_counterexample_ambiguity_if_observed(
    self,
    evidence_refs: Sequence[str],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    case1: Any,
    case2: Any,
    pair_id: str,
    counterexample_raw: Mapping[str, Any],
) -> None:
    object_target_key = self._sat_counterexample_ambiguous_object_target_key(
        evidence_refs,
        analysis1,
        analysis2,
        case1=case1,
        case2=case2,
        pair_id=pair_id,
    )
    _emit_v2_sat_safety_ambiguity_if_observed(
        tuple(str(ref) for ref in evidence_refs or ()),
        object_target_key,
        proof_artifact_digest=_v2_sat_safety_proof_digest({
            "object_target_key": object_target_key,
            "counterexample_raw": counterexample_raw,
            "partition_disambiguation": "validated",
        }),
    )


def _impl__observe_v2_sat_counterexample_ambiguity(
    self,
    evidence_refs: Sequence[str],
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    case1: Any,
    case2: Any,
    pair_id: str,
) -> None:
    object_target_key = self._sat_counterexample_ambiguous_object_target_key(
        evidence_refs,
        analysis1,
        analysis2,
        case1=case1,
        case2=case2,
        pair_id=pair_id,
    )
    _emit_v2_sat_safety_ambiguity_observed(
        tuple(str(ref) for ref in evidence_refs or ()),
        object_target_key,
    )


def _v2_sat_safety_reason_for_ref(reason_ref: str) -> str:
    return sat_safety_reason_id_for_refs((str(reason_ref),))


def _emit_v2_sat_safety_blockers_observed(
    reason_refs: Sequence[str],
    object_target_key: Any,
    *,
    counterexample_binding: Any = None,
    defer_until_terminal: bool = False,
) -> None:
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        SatSafetyBlockerProductionSignal,
        emit_sat_safety_signal,
    )

    for reason_ref in tuple(dict.fromkeys(str(item) for item in reason_refs)):
        emit_sat_safety_signal(SatSafetyBlockerProductionSignal(
            action="OBSERVED",
            reason_id=_v2_sat_safety_reason_for_ref(reason_ref),
            canonical_target_key=(object_target_key, ("safety_gate_ref", reason_ref)),
            missing_semantic_fact=("counterexample_safety_gate_unproven", reason_ref),
            evidence_refs=(reason_ref,),
            producer_id=SAT_SAFETY_BLOCKER_OBSERVED_SITE.producer_id,
            counterexample_binding=counterexample_binding,
            defer_until_terminal=defer_until_terminal,
        ), producer_site_manifest_id="sat-safety-blocker-observed")


def _emit_v2_sat_safety_blockers_completed_if_observed(
    reason_refs: Sequence[str],
    object_target_key: Any,
    *,
    proof_artifact_digest: str,
) -> None:
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        SatSafetyBlockerProductionSignal,
        emit_sat_safety_completion_if_observed,
    )

    for reason_ref in tuple(dict.fromkeys(str(item) for item in reason_refs)):
        emit_sat_safety_completion_if_observed(SatSafetyBlockerProductionSignal(
            action="COMPLETED",
            reason_id=_v2_sat_safety_reason_for_ref(reason_ref),
            canonical_target_key=(object_target_key, ("safety_gate_ref", reason_ref)),
            missing_semantic_fact=("counterexample_safety_gate_unproven", reason_ref),
            evidence_refs=(reason_ref,),
            producer_id=SAT_SAFETY_BLOCKER_COMPLETED_SITE.producer_id,
            proof_artifact_digest=proof_artifact_digest,
        ), producer_site_manifest_id="sat-safety-blocker-completed")


def _emit_v2_sat_safety_ambiguity_observed(
    evidence_refs: Sequence[str],
    object_target_key: Any,
) -> None:
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        SatSafetyBlockerProductionSignal,
        emit_sat_safety_signal,
    )

    emit_sat_safety_signal(SatSafetyBlockerProductionSignal(
        action="OBSERVED",
        reason_id="counterexample_partition_replay_ambiguous",
        canonical_target_key=object_target_key,
        missing_semantic_fact=("unique_counterexample_partition_witness", False),
        evidence_refs=tuple(evidence_refs) or ("partition_replay_ambiguous",),
        producer_id=SAT_SAFETY_AMBIGUITY_OBSERVED_SITE.producer_id,
    ), producer_site_manifest_id="sat-safety-ambiguity-observed")


def _emit_v2_sat_safety_ambiguity_if_observed(
    evidence_refs: Sequence[str],
    object_target_key: Any,
    *,
    proof_artifact_digest: str,
) -> None:
    from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
        SatSafetyBlockerProductionSignal,
        emit_sat_safety_completion_if_observed,
    )

    emit_sat_safety_completion_if_observed(SatSafetyBlockerProductionSignal(
        action="COMPLETED",
        reason_id="counterexample_partition_replay_ambiguous",
        canonical_target_key=object_target_key,
        missing_semantic_fact=("unique_counterexample_partition_witness", False),
        evidence_refs=tuple(evidence_refs) or ("partition_replay_ambiguous",),
        producer_id=SAT_SAFETY_AMBIGUITY_COMPLETED_SITE.producer_id,
        proof_artifact_digest=proof_artifact_digest,
    ), producer_site_manifest_id="sat-safety-ambiguity-completed")


def _v2_sat_safety_proof_digest(proof_content: Mapping[str, Any]) -> str:
    from scripts.function_tracer_pcode.authority.contracts import authority_digest

    return authority_digest({"sat_safety_proof_content": proof_content})

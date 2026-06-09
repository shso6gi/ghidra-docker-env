# -*- coding: utf-8 -*-
"""戦略基底クラス"""

from abc import ABC, abstractmethod
import hashlib
from typing import Optional, Dict, Any, List, Mapping, Sequence, Tuple
from dataclasses import dataclass, field

from ...analysis.condition.smt_oracle import ConditionSMTOracle
from ...model import Condition, Expression, FunctionReturnAnalysis, expression_provenance_key
from ...model import ExpressionType
from ...model.render_smt import expression_contains_unsupported_smt_ops
from ...smt import ParallelResult
from ..unknown_reason import (
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    UnknownRecoveryProofObligation,
    UnknownReasonId,
    UnknownReasonRecord,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
    coerce_unknown_reason_records,
    make_unknown_reason,
)


@dataclass
class StrategyResult:
    """戦略実行結果"""
    is_equivalent: Optional[bool]
    solver_results: ParallelResult
    smt_formula: Optional[str] = None
    counterexample_raw: Optional[Dict] = None
    return_var1: Optional[str] = None
    return_var2: Optional[str] = None
    constrained_fragments: List[str] = field(default_factory=list)
    
    # Pairwise 専用フィールド
    total_pairs: int = 0
    unsat_pairs: int = 0
    sat_pairs: int = 0
    unknown_pairs: int = 0
    error_pairs: int = 0
    sat_pair_info: Optional[Dict[str, Any]] = None  # (i, j, conditions, values)
    normalization_rules: List[Any] = field(default_factory=list)  # List[NormalizationRuleApplication]
    pairwise_debug_stats: Optional[Dict[str, int]] = None
    unknown_reasons: List[UnknownReasonRecord] = field(default_factory=list)

    def __post_init__(self) -> None:
        self.unknown_reasons = list(coerce_unknown_reason_records(self.unknown_reasons))


class CheckStrategy(ABC):
    """等価性判定戦略の基底クラス"""

    _CALL_EFFECT_PROOF_RECOVERABLE_UNSAFETY_REASONS = {
        "unsupported_call_effect_summary",
        "effect_summary_path_coverage_incomplete",
        "effect_call_argument_evidence_incomplete",
        "bounded_call_refinement_argument_alignment_failed",
        "bounded_call_refinement_deferred_target_unresolved",
        "bounded_call_refinement_return_summary_unusable",
    }
    _COMPLETED_PROOF_BLOCKER_FIELDS = (
        "sat_unsafety_reasons",
        "coverage_gap_reasons",
        "unsupported_effect_reasons",
        "active_unsafety_reasons",
        "active_coverage_gaps",
        "active_coverage_gap_reasons",
        "active_unsupported_effects",
        "unsupported_call_effect_reasons",
        "unsupported_memory_effect_reasons",
    )
    
    def __init__(
        self,
        formula_builder,
        solver_runner,
        debug: bool = False,
        enable_completed_recovery_proofs: bool = True,
    ):
        """
        Args:
            formula_builder: FormulaBuilder インスタンス
            solver_runner: ParallelSolverRunner インスタンス
            debug: デバッグモード
        """
        self.formula_builder = formula_builder
        self.solver_runner = solver_runner
        self.debug = debug
        self.enable_completed_recovery_proofs = enable_completed_recovery_proofs
    
    @abstractmethod
    def check(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        save_formula: bool = False
    ) -> StrategyResult:
        """
        等価性をチェック
        
        Args:
            analysis1: 関数1の解析結果
            analysis2: 関数2の解析結果
            save_formula: SMT式を保存するか
        
        Returns:
            StrategyResult
        """
        pass
    
    def _debug_print(self, msg: str):
        """デバッグ出力"""
        if self.debug:
            print(f"[{self.__class__.__name__}] {msg}")

    def _collect_decisive_sat_unsafety_reasons(
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

    def _collect_equivalence_blocking_unsafety_reasons(
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
        return reasons

    def _collect_return_coverage_unsafety_reasons(
        self,
        base_ctx: Dict[str, Any],
        cases1: Sequence[Any],
        cases2: Sequence[Any],
        param_replace_fn1,
        param_replace_fn2,
        analysis1: Optional[FunctionReturnAnalysis] = None,
        analysis2: Optional[FunctionReturnAnalysis] = None,
    ) -> List[str]:
        reasons: List[str] = []
        for label, cases, replace_fn, analysis in (
            ("function1", cases1, param_replace_fn1, analysis1),
            ("function2", cases2, param_replace_fn2, analysis2),
        ):
            status, detail = self._check_return_case_coverage_gap(
                base_ctx,
                cases,
                replace_fn,
                label,
            )
            if status == "gap":
                reasons.append(f"{label}:return_coverage_gap")
            elif status == "inconclusive":
                reasons.append(f"{label}:return_coverage_inconclusive")
            elif (
                status == "covered"
                and analysis1 is not None
                and analysis2 is not None
                and analysis is not None
            ):
                if self.enable_completed_recovery_proofs:
                    self._record_completed_return_coverage_proof(
                        label,
                        analysis,
                        analysis1,
                        analysis2,
                    )
                elif self._analysis_requires_completed_return_coverage_proof(analysis):
                    reasons.append(f"{label}:return_coverage_gap")
            if detail:
                self._debug_print(detail)
        return reasons

    def _record_completed_return_coverage_proof(
        self,
        label: str,
        analysis: FunctionReturnAnalysis,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> None:
        if not self.enable_completed_recovery_proofs:
            return
        if self._analysis_has_active_return_coverage_blockers(analysis):
            return
        object_target_key = self._return_coverage_object_target_key(
            f"{label}:return_coverage_gap",
            analysis1,
            analysis2,
        )
        if object_target_key is None:
            return
        proof_kind = UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION.value
        stages = (
            ("return_partition_extraction", "missing_return_guard"),
            ("return_guard_coverage", "case_guard_disjunction"),
        )
        existing_ids = {
            self._normalize_nested_tuple(item.get("proof_obligation_id"))
            for item in getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
            if isinstance(item, Mapping)
        }
        records: List[Dict[str, Any]] = [
            dict(item)
            for item in getattr(analysis, "completed_recovery_proof_evidence", ()) or ()
            if isinstance(item, Mapping)
        ]
        for proof_stage, evidence_kind in stages:
            proof_id = build_proof_obligation_id(
                UnknownReasonId.RETURN_COVERAGE_GAP.value,
                proof_stage,
                proof_kind,
                evidence_kind,
                object_target_key,
            )
            if proof_id in existing_ids:
                continue
            records.append(
                {
                    "object_derived": True,
                    "status": "complete",
                    "reason_id": UnknownReasonId.RETURN_COVERAGE_GAP.value,
                    "recovery_proof_kind": proof_kind,
                    "proof_stage": proof_stage,
                    "evidence_kind": evidence_kind,
                    "object_target_key": object_target_key,
                    "proof_obligation_id": proof_id,
                    "proof_source": "return_case_coverage_check",
                    "coverage_status": "covered",
                }
            )
            existing_ids.add(proof_id)
        analysis.completed_recovery_proof_evidence = tuple(records)

    def _record_completed_call_effect_summary_proof_if_safe(
        self,
        reason_record: UnknownReasonRecord,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> None:
        if not self.enable_completed_recovery_proofs:
            return
        if reason_record.reason_id != UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value:
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
        proof_content = self._self_recursive_no_store_call_effect_proof_content(
            object_target_key,
            analysis,
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

        records.append(
            {
                "object_derived": True,
                "status": "complete",
                "reason_id": UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
                "recovery_proof_kind": UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value,
                "proof_stage": "object_evidence_collected",
                "evidence_kind": "call_effect_summary",
                "object_target_key": object_target_key,
                "proof_obligation_id": proof_obligation_id,
                "proof_source": "self_recursive_no_store_call_effect_summary",
                "proof_content": proof_content,
            }
        )
        analysis.completed_recovery_proof_evidence = tuple(records)

    @staticmethod
    def _analysis_for_call_effect_object_target(
        object_target_key: Tuple[Any, ...],
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> Optional[FunctionReturnAnalysis]:
        if len(object_target_key) < 2 or object_target_key[0] != "unsupported_call_effect":
            return None
        side_label = object_target_key[1]
        if side_label == "function1":
            return analysis1
        if side_label == "function2":
            return analysis2
        return None

    def _self_recursive_no_store_call_effect_proof_content(
        self,
        object_target_key: Tuple[Any, ...],
        analysis: FunctionReturnAnalysis,
    ) -> Optional[Dict[str, Any]]:
        if len(object_target_key) < 7 or object_target_key[0] != "unsupported_call_effect":
            return None
        if object_target_key[-1] != "callee_effect_summary_missing":
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
            "caller_function": self._analysis_entry_key(analysis),
            "recursive_callee": target_key,
            "callsite_pcode_op_ref": pcode_op_ref,
            "unsupported_call_site": object_target_key,
            "local_store_effect_count": 0,
            "unsupported_call_site_count": 1,
            "recursive_call_effect": "no_memory_effects_by_induction",
        }

    @classmethod
    def _call_target_is_analysis_entry(
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

    def _analysis_has_active_return_coverage_blockers(
        self,
        analysis: FunctionReturnAnalysis,
    ) -> bool:
        return any(
            str(note)
            in {
                "return_case_coverage_gap",
                "return_case_coverage_inconclusive",
            }
            for note in getattr(analysis, "analysis_notes", ()) or ()
        )

    def _analysis_requires_completed_return_coverage_proof(
        self,
        analysis: FunctionReturnAnalysis,
    ) -> bool:
        if self._analysis_has_active_return_coverage_blockers(analysis):
            return True
        proof_dependent_notes = {
            "call_wrapper_return_recovery",
            "counted_scalar_loop_summary",
            "pre_return_counted_loop_summary",
            "state_transition_loop_summary",
        }
        return any(
            str(note) in proof_dependent_notes
            for note in getattr(analysis, "analysis_notes", ()) or ()
        )

    def _unknown_reason_id_for_blocking_unsafety(self, reason: Optional[str]):
        reason_kind = self._blocking_reason_kind(reason)
        if reason_kind == "return_coverage_gap":
            return UnknownReasonId.RETURN_COVERAGE_GAP
        if reason_kind == "return_coverage_inconclusive":
            return UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
        if reason_kind in {"recoverable_partial", "argument_recovery_recoverable_partial"}:
            return UnknownReasonId.RECOVERABLE_PARTIAL
        return UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY

    def _make_blocking_unsafety_unknown_reason(
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
            recovery_action="call_effect_summary_proof_required",
            action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
        )

    def _make_return_coverage_unknown_reason(
        self,
        typed_reason_id: UnknownReasonId,
        blocking_reason: str,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        *,
        stage: str,
    ) -> UnknownReasonRecord:
        object_target_key = self._return_coverage_object_target_key(
            blocking_reason,
            analysis1,
            analysis2,
        )
        kwargs: Dict[str, Any] = {}
        if object_target_key is not None:
            kwargs.update(
                {
                    "object_target_key": object_target_key,
                    "recovery_action": "return_coverage_proof_required",
                    "action_status": UnknownRecoveryActionStatus.PENDING_PROOF,
                }
            )
        return make_unknown_reason(
            typed_reason_id,
            stage=stage,
            evidence_refs=(blocking_reason,),
            detail=blocking_reason,
            **kwargs,
        )

    def _unresolved_equivalence_blocking_unknown_reasons(
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

    def _unresolved_return_coverage_unknown_reasons(
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

    def _recovery_proof_is_complete(
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
        )

    def _call_effect_summary_proof_is_complete(
        self,
        reason_record: UnknownReasonRecord,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> bool:
        if reason_record.reason_id != UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value:
            return False
        if reason_record.recovery_proof_kind != UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value:
            return False
        proof_obligation_id = self._normalize_nested_tuple(reason_record.proof_obligation_id)
        if proof_obligation_id is None:
            return False
        return proof_obligation_id in self._completed_recovery_proof_ids(analysis1, analysis2)

    def _return_coverage_proof_is_complete(
        self,
        reason_record: UnknownReasonRecord,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> bool:
        if reason_record.reason_id != UnknownReasonId.RETURN_COVERAGE_GAP.value:
            return False
        completed = set(self._completed_recovery_proof_ids(analysis1, analysis2))
        required_ids = tuple(
            self._normalize_nested_tuple(action.proof_obligation_id)
            for action in build_unknown_recovery_actions([reason_record])
        )
        if not required_ids or any(proof_id is None for proof_id in required_ids):
            return False
        return all(proof_id in completed for proof_id in required_ids)

    def _sat_unsafety_resolution_proof_is_complete(
        self,
        reason_record: UnknownReasonRecord,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> bool:
        if reason_record.reason_id != UnknownReasonId.SAT_UNSAFETY.value:
            return False
        if reason_record.recovery_proof_kind != UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value:
            return False
        proof_obligation_id = self._normalize_nested_tuple(reason_record.proof_obligation_id)
        if proof_obligation_id is None:
            return False
        return proof_obligation_id in self._completed_recovery_proof_ids(analysis1, analysis2)

    @classmethod
    def _completed_recovery_proof_ids(
        cls,
        *analyses: FunctionReturnAnalysis,
    ) -> Tuple[Tuple[Any, ...], ...]:
        proof_ids: List[Tuple[Any, ...]] = []
        for analysis in analyses:
            proof_ids.extend(cls._produced_recovery_proof_ids(analysis))
        return tuple(proof_ids)

    @classmethod
    def _produced_recovery_proof_ids(
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
        return tuple(proof_ids)

    @classmethod
    def _call_effect_summary_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
        if not cls._evidence_bool(evidence, "object_derived"):
            return None
        if cls._evidence_text(evidence, "status") not in {"complete", "completed", "proven"}:
            return None
        if cls._evidence_text(evidence, "reason_id") != UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value:
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
            UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
            proof_stage,
            proof_kind,
            evidence_kind,
            object_target_key,
        )
        provided_id = cls._normalize_nested_tuple(cls._evidence_get(evidence, "proof_obligation_id"))
        if provided_id is None or provided_id != proof_id:
            return None
        return proof_id

    @classmethod
    def _sat_unsafety_resolution_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
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
        return proof_id

    @classmethod
    def _completed_proof_section_is_clean(cls, section: Any) -> bool:
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

    @classmethod
    def _return_coverage_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
        if not cls._evidence_bool(evidence, "object_derived"):
            return None
        if cls._evidence_text(evidence, "status") not in {"complete", "completed", "proven"}:
            return None
        if cls._evidence_text(evidence, "reason_id") != UnknownReasonId.RETURN_COVERAGE_GAP.value:
            return None
        proof_kind = cls._evidence_text(evidence, "recovery_proof_kind")
        if proof_kind != UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION.value:
            return None
        proof_stage = cls._evidence_text(evidence, "proof_stage")
        if proof_stage not in {"return_partition_extraction", "return_guard_coverage"}:
            return None
        evidence_kind = cls._evidence_text(evidence, "evidence_kind")
        if not evidence_kind:
            return None
        if cls._evidence_has_any(evidence, cls._COMPLETED_PROOF_BLOCKER_FIELDS):
            return None
        object_target_key = cls._normalize_nested_tuple(cls._evidence_get(evidence, "object_target_key"))
        if not isinstance(object_target_key, tuple):
            return None
        proof_id = build_proof_obligation_id(
            UnknownReasonId.RETURN_COVERAGE_GAP.value,
            proof_stage,
            proof_kind,
            evidence_kind,
            object_target_key,
        )
        provided_id = cls._normalize_nested_tuple(cls._evidence_get(evidence, "proof_obligation_id"))
        if provided_id is None or provided_id != proof_id:
            return None
        return proof_id

    @classmethod
    def _analysis_has_active_call_effect_proof_blockers(
        cls,
        analysis: FunctionReturnAnalysis,
    ) -> bool:
        decisive_reasons = getattr(analysis, "get_decisive_sat_unsafety_reasons", lambda: ())()
        for reason in decisive_reasons:
            if str(reason) not in cls._CALL_EFFECT_PROOF_RECOVERABLE_UNSAFETY_REASONS:
                return True
        for note in getattr(analysis, "analysis_notes", ()) or ():
            if str(note) in {
                "return_case_coverage_gap",
                "return_case_coverage_inconclusive",
            }:
                return True
        return False

    @staticmethod
    def _evidence_get(evidence: Any, key: str) -> Any:
        if isinstance(evidence, Mapping):
            return evidence.get(key)
        return getattr(evidence, key, None)

    @classmethod
    def _evidence_text(cls, evidence: Any, key: str) -> str:
        value = cls._evidence_get(evidence, key)
        return "" if value is None else str(value)

    @classmethod
    def _evidence_bool(cls, evidence: Any, key: str) -> bool:
        return bool(cls._evidence_get(evidence, key))

    @classmethod
    def _evidence_has_any(cls, evidence: Any, keys: Sequence[str]) -> bool:
        for key in keys:
            value = cls._evidence_get(evidence, key)
            if value:
                return True
        return False

    @classmethod
    def _evidence_has_any_recursive(cls, evidence: Any, keys: Sequence[str]) -> bool:
        if isinstance(evidence, Mapping):
            if cls._evidence_has_any(evidence, keys):
                return True
            return any(cls._evidence_has_any_recursive(value, keys) for value in evidence.values())
        if isinstance(evidence, Sequence) and not isinstance(evidence, (str, bytes, bytearray)):
            return any(cls._evidence_has_any_recursive(item, keys) for item in evidence)
        return False

    @classmethod
    def _normalize_nested_tuple(cls, value: Any):
        if value is None:
            return None
        if isinstance(value, (tuple, list)):
            return tuple(cls._normalize_nested_tuple(item) for item in value)
        return value

    def _call_effect_blocking_object_target_key(
        self,
        blocking_reason: str,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> Optional[Tuple[Any, ...]]:
        label, reason_text = self._split_blocking_reason(blocking_reason)
        reason_kind = self._blocking_reason_kind(blocking_reason)
        if reason_kind not in {
            "unsupported_call_effect_summary",
            "effect_summary_path_coverage_incomplete",
            "effect_call_argument_evidence_incomplete",
            "bounded_call_refinement_argument_alignment_failed",
            "bounded_call_refinement_deferred_target_unresolved",
            "bounded_call_refinement_return_summary_unusable",
        }:
            return None
        analysis = analysis1 if label == "function1" else analysis2 if label == "function2" else None
        if analysis is None:
            return None
        deferred_call_keys = tuple(
            self._deferred_call_object_target_key(info, analysis=analysis, side_label=label)
            for info in getattr(analysis, "deferred_calls", {}).values()
            if self._deferred_call_is_blocking(info)
        )
        effect_summary = getattr(analysis, "effect_summary", None)
        evidence_keys = ()
        unsupported_call_site_keys = ()
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
        selected_deferred_keys: Tuple[Any, ...] = ()
        selected_evidence_keys: Tuple[Any, ...] = ()
        selected_unsupported_keys: Tuple[Any, ...] = ()

        if reason_kind == "unsupported_call_effect_summary":
            selected_unsupported_keys = unsupported_call_site_keys
            if len(selected_unsupported_keys) == 1:
                return selected_unsupported_keys[0]
        elif reason_kind == "effect_call_argument_evidence_incomplete":
            selected_evidence_keys = evidence_keys
            if not selected_evidence_keys:
                selected_deferred_keys = deferred_call_keys
                if len(selected_deferred_keys) == 1:
                    return selected_deferred_keys[0]
        elif reason_kind in {
            "bounded_call_refinement_argument_alignment_failed",
            "bounded_call_refinement_deferred_target_unresolved",
            "bounded_call_refinement_return_summary_unusable",
        }:
            selected_deferred_keys = deferred_call_keys
            if len(selected_deferred_keys) == 1:
                return selected_deferred_keys[0]
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
        )

    def _return_coverage_object_target_key(
        self,
        blocking_reason: str,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> Optional[Tuple[Any, ...]]:
        label, _reason_text = self._split_blocking_reason(blocking_reason)
        reason_kind = self._blocking_reason_kind(blocking_reason)
        if reason_kind not in {"return_coverage_gap", "return_coverage_inconclusive"}:
            return None
        analysis = analysis1 if label == "function1" else analysis2 if label == "function2" else None
        if analysis is None:
            return None
        return (
            "return_coverage",
            label,
            self._analysis_entry_key(analysis),
            reason_kind,
            self._return_storage_object_key(analysis),
            self._return_partition_object_key(analysis),
            self._return_guard_disjunction_object_key(analysis),
        )

    def _make_sat_unsafety_unknown_reason(
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
            recovery_action="sat_unsafety_resolution_required",
            action_status=UnknownRecoveryActionStatus.PENDING_PROOF,
        )

    def _sat_unsafety_object_target_key(
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

    def _sat_unsafety_side_object_key(
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

    def _sat_unsafety_reason_object_target_key(
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

    def _return_width_bridge_object_target_key(
        self,
        *,
        analysis1: Optional[FunctionReturnAnalysis] = None,
        analysis2: Optional[FunctionReturnAnalysis] = None,
        base_ctx: Optional[Dict[str, Any]] = None,
        case1: Any = None,
        case2: Any = None,
        pair_id: Optional[str] = None,
        mismatch: Any = None,
    ) -> Tuple[Any, ...]:
        """Object-derived target key for return-width bridge proof backlog."""

        if base_ctx is not None:
            analysis1 = analysis1 or base_ctx.get("analysis1")
            analysis2 = analysis2 or base_ctx.get("analysis2")
        return_size1 = self._coerce_return_width(
            getattr(mismatch, "return_size1", None)
            if mismatch is not None
            else None,
            (base_ctx or {}).get("return_size1") if base_ctx is not None else None,
        )
        return_size2 = self._coerce_return_width(
            getattr(mismatch, "return_size2", None)
            if mismatch is not None
            else None,
            (base_ctx or {}).get("return_size2") if base_ctx is not None else None,
        )
        return (
            "return_width_bridge",
            ("pair", pair_id),
            ("return_widths", return_size1, return_size2),
            self._return_width_bridge_side_object_key(
                "left",
                analysis1,
                case1,
                return_size1,
            ),
            self._return_width_bridge_side_object_key(
                "right",
                analysis2,
                case2,
                return_size2,
            ),
        )

    @staticmethod
    def _coerce_return_width(*values: Any) -> Optional[int]:
        for value in values:
            if value is None:
                continue
            try:
                bits = int(value)
            except (TypeError, ValueError):
                continue
            if bits > 0:
                return bits
        return None

    def _return_width_bridge_side_object_key(
        self,
        side_label: str,
        analysis: Optional[FunctionReturnAnalysis],
        case: Any,
        return_size: Optional[int],
    ) -> Tuple[Any, ...]:
        return_info = getattr(case, "return_info", None)
        return (
            "return_width_side",
            side_label,
            self._analysis_entry_key(analysis) if analysis is not None else None,
            ("return_size", return_size),
            self._return_storage_object_key(analysis) if analysis is not None else None,
            self._return_case_partition_member_object_key(case, return_info),
        )

    def _solver_timeout_object_target_key(
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

    def _solver_timeout_options_object_key(
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

    @staticmethod
    def _solver_names_from_parallel_result(parallel_result: Optional[ParallelResult]) -> Tuple[str, ...]:
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

    @staticmethod
    def _coerce_timeout_seconds(value: Any) -> Optional[int]:
        try:
            seconds = int(value)
        except (TypeError, ValueError):
            return None
        return seconds if seconds >= 0 else None

    def _solver_timeout_side_object_key(
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

    @classmethod
    def _binary_pair_id_from_analyses(
        cls,
        analysis1: Optional[FunctionReturnAnalysis],
        analysis2: Optional[FunctionReturnAnalysis],
    ) -> Optional[str]:
        left = cls._analysis_binary_id(analysis1)
        right = cls._analysis_binary_id(analysis2)
        if not left or not right:
            return None
        return "_".join(sorted((left, right)))

    @staticmethod
    def _analysis_binary_id(analysis: Optional[FunctionReturnAnalysis]) -> Optional[str]:
        if analysis is None:
            return None
        binary_id = getattr(analysis, "binary_id", None)
        if isinstance(binary_id, str) and binary_id.strip():
            return binary_id.strip()
        return None

    def _return_case_partition_member_object_key(
        self,
        case: Any,
        return_info: Any,
    ) -> Tuple[Any, ...]:
        case_index = getattr(case, "index", None)
        try:
            normalized_case_index = int(case_index)
        except (TypeError, ValueError):
            normalized_case_index = None
        source_indices = []
        for source_index in getattr(case, "source_indices", ()) or ():
            try:
                source_indices.append(int(source_index))
            except (TypeError, ValueError):
                continue
        return (
            "return_case_partition_member",
            normalized_case_index,
            tuple(source_indices),
            self._return_case_object_key(
                normalized_case_index if normalized_case_index is not None else -1,
                return_info,
            )
            if return_info is not None
            else None,
            (
                "comparison_surface",
                getattr(getattr(case, "comparison_surface", None), "kind", None),
                getattr(getattr(case, "comparison_surface", None), "explicit_bit_width", None),
                getattr(getattr(case, "comparison_surface", None), "use_sign_extension", None),
            ),
            ("value", self._expression_runtime_object_key(getattr(case, "value_expr", None))),
        )

    def _return_storage_object_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
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

    def _return_partition_object_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
        return (
            "return_partition",
            tuple(
                self._return_case_object_key(index, return_info)
                for index, return_info in enumerate(getattr(analysis, "returns", ()) or ())
            ),
        )

    def _return_case_object_key(self, index: int, return_info: Any) -> Tuple[Any, ...]:
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

    def _return_guard_disjunction_object_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
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

    def _return_condition_object_key(self, condition: Any) -> Tuple[Any, ...]:
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

    @staticmethod
    def _split_blocking_reason(blocking_reason: str) -> Tuple[str, str]:
        text = str(blocking_reason or "")
        if ":" not in text:
            return "", text
        label, reason = text.split(":", 1)
        return label, reason

    @classmethod
    def _blocking_reason_kind(cls, blocking_reason: Optional[str]) -> str:
        _label, reason = cls._split_blocking_reason(str(blocking_reason or ""))
        return reason.split(":", 1)[0]

    @staticmethod
    def _deferred_call_is_blocking(info: Any) -> bool:
        status = getattr(info, "call_argument_recovery_status", None)
        return status != "complete"

    def _deferred_call_object_target_key(
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

    def _deferred_call_site_object_key(
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

    def _call_argument_evidence_object_key(
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

    def _unsupported_call_effect_object_key(
        self,
        site: Any,
        *,
        analysis: Optional[FunctionReturnAnalysis] = None,
        side_label: Optional[str] = None,
    ) -> Tuple[Any, ...]:
        pcode_key = self._stable_key_or_none(getattr(site, "pcode_op_ref", None))
        target_key = self._call_target_key_for_analysis(getattr(site, "target_ref", None), analysis)
        target_expr_key = self._typed_target_expression_key(getattr(site, "target_expr", None))
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
            ),
            (
                "callsite_storage",
                ("pcode_op_ref", pcode_key),
                ("callee_identity", callee_identity_key),
                ("target_expression", target_expr_key),
            ),
            ("effect_ordinal", effect_ordinal),
            getattr(site, "reason", None),
        )
        if analysis is not None:
            return self._artifact_stable_key_for_analysis(target, analysis)
        return target

    @staticmethod
    def _call_effect_callee_identity_key(
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

    @classmethod
    def _artifact_stable_key_for_analysis(
        cls,
        value: Any,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> Any:
        binary_id = getattr(analysis, "binary_id", None) if analysis is not None else None
        if binary_id is None:
            return value
        return cls._rewrite_program_identity_keys(value, str(binary_id))

    @classmethod
    def _rewrite_program_identity_keys(cls, value: Any, binary_id: str) -> Any:
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

    @classmethod
    def _rewrite_atom_encoded_program_identity_key(
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

    @staticmethod
    def _program_id_like(value: Any) -> bool:
        return isinstance(value, int) and not isinstance(value, bool)

    @classmethod
    def _atom_program_id_like(cls, value: Any) -> bool:
        return (
            isinstance(value, tuple)
            and len(value) == 2
            and value[0] == "int"
            and cls._program_id_like(value[1])
        )

    @staticmethod
    def _atom_str_is(value: Any, expected: Optional[str]) -> bool:
        return (
            isinstance(value, tuple)
            and len(value) == 2
            and value[0] == "str"
            and (expected is None or value[1] == expected)
        )

    @classmethod
    def _typed_target_expression_key(cls, expr: Any) -> Optional[Tuple[Any, ...]]:
        if expr is None:
            return None
        return ("typed_target_expression", cls._expression_runtime_object_key(expr))

    @staticmethod
    def _analysis_entry_key(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
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

    @classmethod
    def _call_target_key_for_analysis(
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

    @staticmethod
    def _stable_key_or_none(value: Any):
        stable_key = getattr(value, "stable_key", None)
        if callable(stable_key):
            try:
                return stable_key()
            except (AttributeError, TypeError, ValueError, RecursionError):
                return None
        return None

    @classmethod
    def _expression_runtime_object_key(cls, expr: Any) -> Tuple[Any, ...]:
        return expression_provenance_key(expr)

    def _check_return_case_coverage_gap(
        self,
        base_ctx: Dict[str, Any],
        cases: Sequence[Any],
        param_replace_fn,
        label: str,
    ) -> tuple[str, Optional[str]]:
        if not cases:
            return "gap", f"{label} has no return cases after extraction"
        if any(not getattr(case, "conditions", None) for case in cases):
            return "covered", None
        object_centric_status = self._return_cases_have_object_centric_total_coverage(
            cases
        )
        if object_centric_status is True:
            return "covered", None
        if object_centric_status is False:
            return (
                "gap",
                f"{label} object-centric return-case coverage check found uncovered region",
            )
        if object_centric_status is None:
            case_conditions = [
                cond
                for case in (cases or ())
                for cond in (getattr(case, "conditions", None) or ())
            ]
            if not ConditionSMTOracle.has_object_identity_support(case_conditions):
                return (
                    "inconclusive",
                    f"{label} return-case object-centric coverage check was inconclusive",
                )
        if not base_ctx.get("header_lines"):
            return "inconclusive", f"{label} return-case coverage query skipped: base context has no declarations"
        if any(self._case_conditions_contain_unresolved_expression(case) for case in cases):
            return "inconclusive", f"{label} return-case coverage query skipped: unresolved condition expression"

        query = self._build_return_case_coverage_query(
            base_ctx,
            cases,
            param_replace_fn,
            label,
        )
        if query is None:
            return "inconclusive", f"{label} return-case coverage query could not be built"

        result = self.solver_runner.run_sequential(query)
        if result.is_equivalent is False:
            model = result.get_counterexample()
            detail = f"{label} has uncovered return-condition region"
            if model:
                detail += f" under model {model}"
            return "gap", detail
        if result.is_equivalent is None:
            return "inconclusive", f"{label} return-case coverage query was inconclusive"
        return "covered", None

    def _return_cases_have_object_centric_total_coverage(
        self,
        cases: Sequence[Any],
    ) -> Optional[bool]:
        if not cases:
            return False
        if any(not getattr(case, "conditions", None) for case in cases):
            return True
        case_conditions = [
            condition
            for case in cases
            for condition in (getattr(case, "conditions", None) or ())
        ]
        if not ConditionSMTOracle.has_object_identity_support(case_conditions):
            return None
        smt_result = self._return_cases_have_smt_total_coverage(cases)
        if smt_result is not None:
            return smt_result
        return None

    def _return_cases_have_smt_total_coverage(
        self,
        cases: Sequence[Any],
    ) -> Optional[bool]:
        """Prove coverage from Condition objects without rendered-query plumbing.

        A coverage gap exists iff every return case can be missed at once.
        For a case with conditions c1..cn, the case is missed by
        (not c1) or ... or (not cn).  If the conjunction of all case-miss
        formulas is UNSAT, the return partition is total.
        """

        miss_conditions: List[Condition] = []
        for case in cases or ():
            conditions = list(getattr(case, "conditions", None) or [])
            if not conditions:
                return True
            miss_expr = self._case_miss_expression(conditions)
            if miss_expr is None:
                return None
            miss_conditions.append(Condition(miss_expr, False))
        if not miss_conditions:
            return False
        return ConditionSMTOracle.conjunction_is_unsat(miss_conditions)

    def _case_miss_expression(
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

    def _negated_condition_expression(
        self,
        condition: Condition,
    ) -> Optional[Expression]:
        expr = getattr(condition, "expression", None)
        if expr is None:
            return None
        if bool(getattr(condition, "negated", False)):
            return expr
        return Expression.unary_op("BOOL_NEGATE", expr)

    def _build_return_case_coverage_query(
        self,
        base_ctx: Dict[str, Any],
        cases: Sequence[Any],
        param_replace_fn,
        label: str,
    ) -> Optional[str]:
        disjuncts: List[str] = []
        for case in cases:
            conditions = list(getattr(case, "get_conditions_smt")(param_replace_fn))
            if not conditions:
                return None
            if len(conditions) == 1:
                disjuncts.append(conditions[0])
            else:
                disjuncts.append(f"(and {' '.join(conditions)})")

        if not disjuncts:
            return None

        lines = [
            f"; Return coverage gap query: {label}",
            *base_ctx.get("header_lines", []),
            f"(assert (not (or {' '.join(disjuncts)})))",
            "(check-sat)",
            "(get-model)",
        ]
        return "\n".join(lines)

    def _case_conditions_contain_unresolved_expression(self, case: Any) -> bool:
        return any(
            self._expression_contains_unresolved(getattr(cond, "expression", None))
            for cond in getattr(case, "conditions", []) or []
        )

    def _expression_contains_unresolved(self, expr: Any) -> bool:
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

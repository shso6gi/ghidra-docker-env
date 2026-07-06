# -*- coding: utf-8 -*-
"""戦略基底クラス"""

from abc import ABC, abstractmethod
import hashlib
import json
import re
from types import SimpleNamespace
from typing import Optional, Dict, Any, List, Mapping, Sequence, Set, Tuple
from dataclasses import dataclass, field

from ...analysis.condition.smt_oracle import ConditionSMTOracle
from ...model import (
    Condition,
    Expression,
    FunctionReturnAnalysis,
    ReadonlyReductionRef,
    expression_provenance_key,
)
from ...model import ExpressionType
from ...model.render_smt import expression_contains_unsupported_smt_ops, expression_smt_bit_width
from ...smt import ParallelResult
from ..formula.returns import coerce_value_to_bitvec_width
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


@dataclass(frozen=True)
class ReturnCoverageCheckResult:
    status: str
    reason_id: Optional[UnknownReasonId] = None
    detail: Optional[str] = None
    can_record_completion_proof: bool = False
    inconclusive_cause: Optional[str] = None
    coverage_proof_method: Optional[str] = None
    solver_status: Optional[str] = None


class CheckStrategy(ABC):
    """等価性判定戦略の基底クラス"""

    _RETURN_COVERAGE_TARGET_SCHEMA_VERSION = 3
    _RETURN_COVERAGE_PROOF_SCHEMA_VERSION = 2
    _RETURN_COVERAGE_NORMALIZATION_AWARE_PROOF_SCHEMA_VERSION = 3
    _RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION = 1
    _RETURN_COVERAGE_NORMALIZATION_POLICY_ID = "return-coverage-proof-scoped-normalization"
    _RETURN_COVERAGE_NORMALIZATION_RULESET_VERSION = 1
    _RETURN_COVERAGE_NORMALIZATION_CANONICAL_ENCODING_VERSION = 1
    _RETURN_COVERAGE_DISCHARGEABLE_INCONCLUSIVE_CAUSES = {
        "solver_timeout",
        "smt_disambiguation_inconclusive",
    }

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
    _CALL_EFFECT_PROOF_CONTENT_REQUIRED_OBJECT_KINDS = {
        "call_argument_evidence",
        "call_target_resolution_evidence",
        "deferred_call",
        "unsupported_call_effect",
        "call_effect_blocker",
    }
    _UNSUPPORTED_CALL_EFFECT_REASON_COMPATIBILITY_GROUPS = (
        frozenset(
            {
                "target_identity_unavailable",
                "callee_unsupported_call_may_expose_parameter_memory",
            }
        ),
    )
    _UNSUPPORTED_CALL_EFFECT_COMPATIBILITY_REQUIRED_FLAGS = (
        "reason_signature_match",
        "target_expression_match",
        "argument_keys_match",
        "callee_identity_category_match",
        "callee_identity_reachable",
        "unsupported_fact_evidence_complete",
    )
    _RETURN_WIDTH_BRIDGE_ACTION_REQUIREMENTS = {
        ("abi_relation_proof", "abi_relation"): (
            "calling_convention",
            ("calling_convention", "return_storage", "narrow_return_width"),
        ),
        ("high_bit_proof", "high_bit_relation"): (
            "producer_width",
            ("producer_width", "extension_semantics", "high_bits_irrelevant_or_equal"),
        ),
    }
    _RETURN_WIDTH_BRIDGE_ACCEPTED_DISCHARGES = {
        "abi_relation": {
            "canonical_action": "abi_relation_proof",
            "evidence_slot_kind": "calling_convention",
            "accepted_discharge_proof_kinds": frozenset({"abi_relation_proof"}),
        },
        "high_bit_relation": {
            "canonical_action": "high_bit_proof",
            "evidence_slot_kind": "producer_width",
            "accepted_discharge_proof_kinds": frozenset(
                {
                    "high_bit_proof",
                    "semantic_return_width_narrowing_proof",
                    "return_member_narrow_producer_high_bit_proof",
                }
            ),
        },
    }
    _RETURN_WIDTH_BRIDGE_SEMANTIC_NARROWING_SOURCE = (
        "return_width_bridge_narrow_query_unsat_and_semantic_return_width_narrowing"
    )
    _RETURN_WIDTH_BRIDGE_MEMBER_NARROW_PRODUCER_SOURCE = (
        "return_width_bridge_narrow_query_unsat_and_return_member_narrow_producer"
    )
    _RETURN_WIDTH_BRIDGE_SOURCE_LEVEL_PHASES = frozenset({"P0_SOURCE_DECLARATION"})
    _RETURN_WIDTH_BRIDGE_WEAK_RETURN_TYPE_SOURCES = frozenset(
        {
            "undefined_decompiler_type",
            "default_integral_replacement",
            "counterpart_value_width",
            "counterpart_declared_type",
            "counterpart_void_return_surface",
        }
    )
    _READONLY_IDENTITY_ACTION_REQUIREMENT = (
        "object_storage_identity",
        ("object_storage_identity", "count_identity", "guard_implication", "finite_witness"),
    )
    _METHOD_B_ACTION_REQUIREMENTS = {
        ("proof_backed_covering_case", "method_b_covering_case"): (
            "seed_compensation",
            ("seed_compensation", "term_sequence", "pure_side_effect_profile"),
        ),
        ("guard_partition_completion", "method_b_guard_partition"): (
            "guard_partition",
            ("guard_partition", "partition_coverage_proof"),
        ),
    }
    _RETURN_COVERAGE_COMPLETION_REQUIREMENTS = {
        UnknownReasonId.RETURN_COVERAGE_GAP: (
            ("return_partition_extraction", "missing_return_guard"),
            ("return_guard_coverage", "case_guard_disjunction"),
        ),
        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE: (
            ("return_coverage_smt_disambiguation", "case_guard_disjunction"),
        ),
    }
    
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

    def _same_function_counterexample_replay_reasons(
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
        outcome_covered_labels = self._outcome_partition_covered_labels(
            base_ctx,
            analysis1,
            analysis2,
            param_replace_fn1,
            param_replace_fn2,
        )
        outcome_inconclusive_labels = self._outcome_partition_inconclusive_labels(
            base_ctx,
            analysis1,
            analysis2,
            param_replace_fn1,
            param_replace_fn2,
        )
        for label, cases, replace_fn, analysis in (
            ("function1", cases1, param_replace_fn1, analysis1),
            ("function2", cases2, param_replace_fn2, analysis2),
        ):
            if label in outcome_covered_labels:
                coverage_result = ReturnCoverageCheckResult(
                    status="covered",
                    coverage_proof_method="outcome_partition_equivalence",
                    solver_status="unsat",
                )
            elif label in outcome_inconclusive_labels:
                coverage_result = ReturnCoverageCheckResult(
                    status="inconclusive",
                    reason_id=UnknownReasonId.OUTCOME_PARTITION_UNKNOWN,
                    detail=f"Outcome partition unknown for {label}: UnknownOutcome covers missing control region",
                    inconclusive_cause="unknown_outcome_partition",
                    solver_status="unknown",
                )
            else:
                coverage_result = self._check_return_case_coverage_gap(
                    base_ctx,
                    cases,
                    replace_fn,
                    label,
                )
            if coverage_result.status == "gap":
                if coverage_result.detail:
                    self._debug_print(coverage_result.detail)
                reasons.append(f"{label}:return_coverage_gap")
                reasons.extend(
                    f"{label}:{reason_id}"
                    for reason_id in self._summary_return_candidate_blocker_reason_ids(analysis)
                )
            elif coverage_result.status == "inconclusive":
                if coverage_result.detail:
                    self._debug_print(coverage_result.detail)
                blocker_reason = coverage_result.reason_id or UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
                reasons.append(f"{label}:{blocker_reason.value}")
                if (
                    coverage_result.reason_id == UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
                    and self.enable_completed_recovery_proofs
                    and analysis is not None
                    and coverage_result.can_record_completion_proof
                    and coverage_result.inconclusive_cause in self._RETURN_COVERAGE_DISCHARGEABLE_INCONCLUSIVE_CAUSES
                    and self._return_coverage_proof_content_can_discharge_inconclusive(
                        self._return_coverage_inconclusive_proof_content(
                            base_ctx=base_ctx,
                            label=label,
                            cases=cases,
                            replace_fn=replace_fn,
                            inconclusive_cause=coverage_result.inconclusive_cause,
                        )
                    )
                ):
                    self._record_completed_return_coverage_proof(
                        label,
                        blocker_reason,
                        analysis,
                        analysis1,
                        analysis2,
                        proof_content=self._return_coverage_inconclusive_proof_content(
                            base_ctx=base_ctx,
                            label=label,
                            cases=cases,
                            replace_fn=replace_fn,
                            inconclusive_cause=coverage_result.inconclusive_cause,
                        ),
                    )
            elif (
                coverage_result.status == "covered"
                and analysis1 is not None
                and analysis2 is not None
                and analysis is not None
            ):
                blocker_reason = self._analysis_requires_completed_return_coverage_proof(
                    analysis,
                    ignored_reason_ids=(coverage_result.reason_id,),
                )
                required_blocker_reason = blocker_reason
                proof_record_reason = blocker_reason
                if proof_record_reason is None and self.enable_completed_recovery_proofs:
                    proof_record_reason = UnknownReasonId.RETURN_COVERAGE_GAP
                if proof_record_reason is not None and self.enable_completed_recovery_proofs:
                    proof_content = self._return_coverage_covered_proof_content(
                        base_ctx=base_ctx,
                        label=label,
                        cases=cases,
                        replace_fn=replace_fn,
                        coverage_proof_method=coverage_result.coverage_proof_method,
                        solver_status=coverage_result.solver_status,
                    )
                    self._record_completed_return_coverage_proof(
                        label,
                        proof_record_reason,
                        analysis,
                        analysis1,
                        analysis2,
                        proof_content=proof_content,
                    )
                    if required_blocker_reason in {
                        UnknownReasonId.RETURN_COVERAGE_GAP,
                        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
                    }:
                        reason_record = self._make_blocking_unsafety_unknown_reason(
                            f"{label}:{required_blocker_reason.value}",
                            analysis1,
                            analysis2,
                            stage="S_RETURN_COVERAGE_CHECK",
                        )
                        if not self._return_coverage_proof_is_complete(
                            reason_record,
                            analysis1,
                            analysis2,
                        ):
                            reasons.append(f"{label}:{required_blocker_reason.value}")
                elif blocker_reason is not None:
                    reasons.append(f"{label}:{blocker_reason.value}")
                if coverage_result.detail:
                    self._debug_print(coverage_result.detail)
        return reasons

    @classmethod
    def _summary_return_candidate_blocker_reason_ids(
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

    @staticmethod
    def _summary_return_blocker_reason_id(blocker: str) -> str:
        text = str(blocker or "")
        if text == "return_coverage_gap:summary_partition_not_total":
            return UnknownReasonId.SUMMARY_PARTITION_NOT_TOTAL.value
        if text.startswith("return_coverage_gap:summary_partition_not_total:"):
            return UnknownReasonId.SUMMARY_PARTITION_NOT_TOTAL.value
        return text.split(":", 1)[0]

    def _record_completed_return_coverage_proof(
        self,
        label: str,
        reason_id: UnknownReasonId,
        analysis: FunctionReturnAnalysis,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        proof_content: Optional[Mapping[str, Any]] = None,
    ) -> None:
        if not self.enable_completed_recovery_proofs:
            return
        if self._analysis_has_active_return_coverage_blockers(
            analysis,
            ignored_reason_ids=(reason_id,),
        ):
            return
        requirements = self._RETURN_COVERAGE_COMPLETION_REQUIREMENTS.get(reason_id)
        if not requirements:
            return
        object_target_key = self._return_coverage_object_target_key(
            f"{label}:{reason_id.value}",
            analysis1,
            analysis2,
        )
        if object_target_key is None:
            return
        proof_kind = UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION.value
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
        proof_content_map = dict(proof_content) if isinstance(proof_content, Mapping) else {}
        proof_content_map["proof_target_identity"] = object_target_key
        prototype = {
            "status": "complete",
            "reason_id": reason_id.value,
            "target_schema_version": self._RETURN_COVERAGE_TARGET_SCHEMA_VERSION,
            "proof_schema_version": self._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
            "object_target_key": object_target_key,
            "proof_content": proof_content_map,
        }
        if not self._return_coverage_proof_content_is_complete(
            prototype,
            reason_id=reason_id,
        ):
            return
        for proof_stage, evidence_kind in requirements:
            proof_id = build_proof_obligation_id(
                reason_id.value,
                proof_stage,
                proof_kind,
                evidence_kind,
                object_target_key,
            )
            if proof_id in existing_ids:
                continue
            candidate = {
                "object_derived": True,
                "status": "complete",
                "reason_id": reason_id.value,
                "recovery_proof_kind": proof_kind,
                "target_schema_version": self._RETURN_COVERAGE_TARGET_SCHEMA_VERSION,
                "proof_schema_version": self._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
                "proof_stage": proof_stage,
                "evidence_kind": evidence_kind,
                "object_target_key": object_target_key,
                "proof_obligation_id": proof_id,
                "proof_source": "return_case_coverage_check",
                "coverage_status": "covered",
                "required_evidence": (evidence_kind,),
                "proof_content": proof_content_map,
            }
            if self._return_coverage_proof_id_from_evidence(candidate) is None:
                continue
            records.append(candidate)
            existing_ids.add(proof_id)
        analysis.completed_recovery_proof_evidence = tuple(records)

    @staticmethod
    def _return_case_smt_disjunctions(
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


    def _return_coverage_covered_proof_content(
        self,
        base_ctx: Dict[str, Any],
        label: str,
        cases: Sequence[Any],
        replace_fn,
        *,
        coverage_proof_method: Optional[str] = None,
        solver_status: Optional[str] = None,
    ) -> Dict[str, Any]:
        disjuncts = self._return_case_smt_disjunctions(cases, replace_fn)
        query = self._build_return_case_coverage_query(
            base_ctx,
            cases,
            replace_fn,
            label,
        )
        normalized_query = self._normalize_query(query) if query is not None else None
        if normalized_query is None and disjuncts:
            normalized_query = "(or " + " ".join(disjuncts) + ")"
        normalized_query_status = (
            "complete" if normalized_query is not None else "missing"
        )
        structural_evidence = self._return_coverage_structural_proof_content(
            cases,
            solver_status=solver_status,
            coverage_proof_method=coverage_proof_method,
        )
        coverage_method = coverage_proof_method or "return_case_coverage_check"
        return {
            "proof_schema_version": self._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
            "normalization_schema_version": self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION,
            **structural_evidence,
            "case_guard_disjunction": {
                "status": "complete",
                "query_cases": tuple(disjuncts or ()),
                "case_count": len(tuple(disjuncts or ())),
                "status_scope": "function-local",
            },
            "normalized_guard_formula": {
                "status": normalized_query_status,
                "query": normalized_query if normalized_query is not None else query,
            },
            "coverage_guard_evidence": {
                "status": normalized_query_status,
                "guard_source": "return_partition_guard_set",
                "coverage_status": "covered",
                "coverage_proof_method": coverage_method,
                "case_count": len(tuple(disjuncts or ())),
                "normalized_guard_formula_sha256": (
                    hashlib.sha256(normalized_query.encode("utf-8")).hexdigest()
                    if isinstance(normalized_query, str) and normalized_query
                    else None
                ),
            },
            "coverage_status": {
                "status": "complete",
                "result": "covered",
                "proof_source": "return_case_coverage_check",
            },
        }

    def _return_coverage_inconclusive_proof_content(
        self,
        base_ctx: Dict[str, Any],
        label: str,
        cases: Sequence[Any],
        replace_fn,
        inconclusive_cause: Optional[str] = None,
    ) -> Dict[str, Any]:
        disjuncts = self._return_case_smt_disjunctions(cases, replace_fn)
        query = self._build_return_case_coverage_query(
            base_ctx,
            cases,
            replace_fn,
            label,
        )
        normalized_query = self._normalize_query(query) if query is not None else None
        if normalized_query is None and disjuncts:
            normalized_query = "(or " + " ".join(disjuncts) + ")"
        normalized_query_status = (
            "complete" if normalized_query is not None else "missing"
        )
        structural_evidence = self._return_coverage_structural_proof_content(
            cases,
            solver_status="unknown",
        )
        return {
            "proof_schema_version": self._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
            "normalization_schema_version": self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION,
            "inconclusive_cause": inconclusive_cause,
            **structural_evidence,
            "case_guard_disjunction": {
                "status": "complete",
                "query_cases": tuple(disjuncts or ()),
                "case_count": len(tuple(disjuncts or ())),
                "status_scope": "function-local",
            },
            "normalized_guard_formula": {
                "status": normalized_query_status,
                "query": normalized_query if normalized_query is not None else query,
            },
            "coverage_guard_evidence": {
                "status": normalized_query_status,
                "guard_source": "case_guard_disjunction",
                "case_count": len(tuple(disjuncts or ())),
                "normalized_guard_formula_sha256": (
                    hashlib.sha256(normalized_query.encode("utf-8")).hexdigest()
                    if isinstance(normalized_query, str) and normalized_query
                    else None
                ),
            },
            "solver_model_or_timeout": {
                "status": "unknown",
                "detail": "coverage query returned UNKNOWN/timeout",
            },
        }

    def _return_coverage_structural_proof_content(
        self,
        cases: Sequence[Any],
        *,
        solver_status: Optional[str],
        coverage_proof_method: Optional[str] = None,
    ) -> Dict[str, Any]:
        case_entries: List[Tuple[Any, ...]] = []
        miss_entries: List[Tuple[Any, ...]] = []
        bit_widths: Set[int] = set()
        signedness: Set[str] = set()
        for case_index, case in enumerate(cases or ()):
            return_info = getattr(case, "return_info", None)
            structural_conditions = (
                getattr(return_info, "conditions", None)
                if return_info is not None
                else getattr(case, "conditions", None)
            ) or ()
            structural_value = (
                getattr(return_info, "value", None)
                if return_info is not None
                else getattr(case, "value_expr", None)
            )
            guard_keys = tuple(
                self._return_condition_object_key(condition)
                for condition in structural_conditions
            )
            value_key = self._expression_runtime_object_key(structural_value)
            miss_expr = self._case_miss_expression(
                list(structural_conditions)
            )
            miss_key = self._expression_runtime_object_key(miss_expr) if miss_expr is not None else None
            case_entries.append(
                (
                    "return_case_guard_set",
                    int(case_index),
                    ("guard_structural_keys", guard_keys),
                    ("return_value_structural_key", value_key),
                )
            )
            miss_entries.append(
                (
                    "case_miss_formula",
                    int(case_index),
                    miss_key,
                )
            )
            for condition in structural_conditions:
                self._collect_condition_width_sign_metadata(condition, bit_widths, signedness)
        case_entries = list(self._canonicalize_key_sequence(case_entries))
        miss_entries = list(self._canonicalize_key_sequence(miss_entries))
        return {
            "structural_guard_keys": {
                "status": "complete",
                "case_count": len(case_entries),
                "keys": tuple(case_entries),
            },
            "structural_miss_formula_keys": {
                "status": "complete",
                "case_count": len(miss_entries),
                "keys": tuple(miss_entries),
            },
            "coverage_solver_evidence": {
                "status": str(solver_status) if solver_status is not None else "not_applicable",
                "proof_method": coverage_proof_method or "unknown",
            },
            "bit_width_signedness_metadata": {
                "status": "complete",
                "bit_widths": tuple(sorted(bit_widths)),
                "signedness": tuple(sorted(signedness)),
            },
        }

    @staticmethod
    def _normalize_query(query: Optional[str]) -> Optional[str]:
        if not query or not isinstance(query, str):
            return None
        lines = [line.strip() for line in query.splitlines() if line.strip()]
        normalized = [line for line in lines if not line.startswith("; Return coverage")]
        return "\n".join(normalized)

    @staticmethod
    def _canonicalize_key_sequence(values: Sequence[Any]) -> Tuple[Any, ...]:
        return tuple(sorted(tuple(values or ()), key=repr))

    @classmethod
    def _return_coverage_normalization_policy(cls, *, rules: Sequence[Any] = ()) -> Dict[str, Any]:
        return {
            "normalization_policy_id": cls._RETURN_COVERAGE_NORMALIZATION_POLICY_ID,
            "normalization_schema_version": cls._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION,
            "rule_set_version": cls._RETURN_COVERAGE_NORMALIZATION_RULESET_VERSION,
            "canonical_encoding_version": cls._RETURN_COVERAGE_NORMALIZATION_CANONICAL_ENCODING_VERSION,
            "rules": tuple(sorted(tuple(rules or ()), key=repr)),
        }

    @classmethod
    def _canonical_jsonable_for_digest(cls, value: Any) -> Optional[Any]:
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

    @classmethod
    def _canonical_json_digest(cls, value: Any) -> Optional[str]:
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

    @classmethod
    def _return_coverage_normalization_policy_digest(cls, policy: Mapping[str, Any]) -> Optional[str]:
        if not isinstance(policy, Mapping):
            return None
        required = {
            "normalization_policy_id",
            "normalization_schema_version",
            "rule_set_version",
            "canonical_encoding_version",
            "rules",
        }
        if not required.issubset(set(policy.keys())):
            return None
        if policy.get("normalization_policy_id") != cls._RETURN_COVERAGE_NORMALIZATION_POLICY_ID:
            return None
        if policy.get("normalization_schema_version") != cls._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION:
            return None
        if policy.get("rule_set_version") != cls._RETURN_COVERAGE_NORMALIZATION_RULESET_VERSION:
            return None
        if policy.get("canonical_encoding_version") != cls._RETURN_COVERAGE_NORMALIZATION_CANONICAL_ENCODING_VERSION:
            return None
        rules = policy.get("rules")
        if not isinstance(rules, (tuple, list)):
            return None
        normalized_rules = []
        for rule in rules:
            if not isinstance(rule, Mapping) or not isinstance(rule.get("rule_id"), str):
                return None
            normalized_rules.append({key: rule[key] for key in sorted(rule.keys())})
        normalized_rules.sort(key=lambda item: str(item.get("rule_id")))
        return cls._canonical_json_digest(
            {
                "canonical_encoding_version": policy.get("canonical_encoding_version"),
                "normalization_policy_id": policy.get("normalization_policy_id"),
                "normalization_schema_version": policy.get("normalization_schema_version"),
                "rule_set_version": policy.get("rule_set_version"),
                "rules": tuple(normalized_rules),
            }
        )

    @classmethod
    def _collect_condition_width_sign_metadata(
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

    @classmethod
    def _iter_expression_nodes_for_metadata(cls, expr: Any):
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
                "reason_id": UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
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

    @classmethod
    def _iter_call_effect_blocker_candidates(
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


    @classmethod
    def _select_call_effect_blocker_candidate(
        cls,
        object_target_key: Tuple[Any, ...],
    ) -> Optional[Tuple[Any, ...]]:
        candidates = cls._iter_call_effect_blocker_candidates(object_target_key)
        if not candidates:
            return None
        return max(candidates, key=cls._call_effect_blocker_candidate_score)

    def _call_effect_blocker_proof_content(
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

    @classmethod
    def _call_effect_blocker_candidate_score(cls, candidate: Any) -> Tuple[Any, ...]:
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

    @classmethod
    def _call_effect_blocker_semantic_tie_break(cls, candidate: Tuple[Any, ...]) -> Tuple[Any, ...]:
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

    @classmethod
    def _call_effect_blocker_sort_token(cls, value: Any) -> Tuple[Any, ...]:
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

    @classmethod
    def _call_effect_blocker_candidate_priority(cls, candidate_kind: Any) -> int:
        if candidate_kind == "call_argument_evidence":
            return 3
        if candidate_kind == "unsupported_call_effect":
            return 2
        if candidate_kind == "deferred_call":
            return 1
        return 0

    @staticmethod
    def _analysis_for_call_effect_object_target(
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

    def _call_argument_evidence_phase15_proof_content(
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

    def _bounded_call_refinement_evidence_for_call_argument_target(
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

    def _bounded_call_refinement_content_is_complete(
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

    @classmethod
    def _expression_bit_width_from_object_key(cls, object_key: Any) -> Optional[int]:
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
            "object_target_key": object_target_key,
            "caller_function": self._analysis_entry_key(analysis),
            "recursive_callee": target_key,
            "callsite_pcode_op_ref": pcode_op_ref,
            "unsupported_call_site": object_target_key,
            "local_store_effect_count": 0,
            "unsupported_call_site_count": 1,
            "recursive_call_effect": "no_memory_effects_by_induction",
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

    def _matched_unknown_indirect_call_effect_proof_content(
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

    def _matched_unsupported_call_effect_no_store_parameter_exposure_proof_content(
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

    def _matched_deferred_call_argument_proof_content(
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

    def _unsupported_call_effects_semantically_match(
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

    @classmethod
    def _unsupported_call_effect_requires_exact_target_expression_match(
        cls,
        object_target_key: Any,
        peer_object_target_key: Any,
    ) -> bool:
        return True

    @classmethod
    def _unsupported_call_effect_callee_identity_key(cls, object_target_key: Any) -> Any:
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

    @classmethod
    def _unsupported_call_effect_callee_identity_category(cls, object_target_key: Any) -> Optional[str]:
        identity = cls._unsupported_call_effect_callee_identity_key(object_target_key)
        if isinstance(identity, tuple) and identity:
            return str(identity[0])
        if identity is None:
            return None
        return str(identity)

    @classmethod
    def _unsupported_call_effect_callee_identity_is_reachable(cls, object_target_key: Any) -> bool:
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

    @classmethod
    def _unsupported_call_effect_compatibility_policy_evidence(
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
            **flags,
        }

    @classmethod
    def _unsupported_call_effect_compatibility_policy_is_complete(
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

    @classmethod
    def _unsupported_call_effect_callee_identity_is_unknown(cls, object_target_key: Any) -> bool:
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

    def _deferred_calls_semantically_match(
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

    @classmethod
    def _unsupported_call_effect_target_expression_key(cls, object_target_key: Any) -> Any:
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

    @classmethod
    def _call_effect_target_expression_key_is_present(cls, value: Any) -> bool:
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

    @classmethod
    def _unsupported_call_effect_argument_keys(cls, object_target_key: Any) -> Tuple[Any, ...]:
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

    @classmethod
    def _unsupported_call_effect_argument_evidence_is_complete(cls, value: Any) -> bool:
        normalized = cls._normalize_nested_tuple(value)
        if not isinstance(normalized, tuple):
            return False
        if not normalized:
            return True
        return cls._call_effect_argument_keys_are_present(normalized)

    @classmethod
    def _call_effect_argument_keys_are_present(cls, value: Any) -> bool:
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

    @classmethod
    def _deferred_call_target_expression_key(cls, object_target_key: Any) -> Any:
        target = cls._normalize_nested_tuple(object_target_key)
        if not isinstance(target, tuple) or len(target) < 7:
            return None
        return target[6]

    @classmethod
    def _deferred_call_argument_keys(cls, object_target_key: Any) -> Tuple[Any, ...]:
        target = cls._normalize_nested_tuple(object_target_key)
        if not isinstance(target, tuple) or len(target) < 8:
            return ()
        value = cls._normalize_nested_tuple(target[7])
        return value if isinstance(value, tuple) else ()

    @classmethod
    def _cross_binary_call_effect_component_key(cls, value: Any) -> Any:
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
        *,
        ignored_reason_ids: Sequence[Optional[UnknownReasonId]],
    ) -> bool:
        return (
            self._analysis_requires_completed_return_coverage_proof(
                analysis,
                ignored_reason_ids=ignored_reason_ids,
            )
            is not None
        )

    def _analysis_requires_completed_return_coverage_proof(
        self,
        analysis: FunctionReturnAnalysis,
        *,
        ignored_reason_ids: Sequence[Optional[UnknownReasonId]],
    ) -> Optional[UnknownReasonId]:
        ignored_reason_kinds = {
            self._blocking_reason_kind(reason.value)
            for reason in ignored_reason_ids
            if reason is not None
        }
        for reason in (
            getattr(analysis, "get_decisive_sat_unsafety_reasons", lambda: ())()
        ):
            reason_text = str(reason)
            reason_kind = self._blocking_reason_kind(reason_text)
            if reason_kind in {
                "return_case_coverage_gap",
                "return_case_coverage_inconclusive",
            }:
                continue
            if reason_kind in ignored_reason_kinds:
                continue
            if reason_kind == "return_coverage_gap":
                return UnknownReasonId.RETURN_COVERAGE_GAP
            if reason_kind == "return_coverage_inconclusive":
                return UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
            return self._unknown_reason_id_for_blocking_unsafety(reason_text)
        return None

    @classmethod
    def _unsupported_call_effect_reason_compatibility_group(cls, reason: Any) -> Tuple[str, ...]:
        reason_text = str(reason)
        for group in cls._UNSUPPORTED_CALL_EFFECT_REASON_COMPATIBILITY_GROUPS:
            if reason_text in group:
                return tuple(sorted(group))
        return (reason_text,)

    @classmethod
    def _unsupported_call_effect_reason_signature(cls, reason: Any) -> str:
        return "|".join(cls._unsupported_call_effect_reason_compatibility_group(reason))

    @classmethod
    def _unsupported_call_effect_reason_is_compatible(
        cls,
        left_reason: Any,
        right_reason: Any,
    ) -> bool:
        return cls._unsupported_call_effect_reason_signature(left_reason) == cls._unsupported_call_effect_reason_signature(
            right_reason
        )

    def _unknown_reason_id_for_blocking_unsafety(self, reason: Optional[str]):
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

    def _call_effect_blocking_object_evidence(
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
        return proof_obligation_id in self._completed_call_effect_summary_proof_ids(
            analysis1,
            analysis2,
        )

    def _return_coverage_proof_is_complete(
        self,
        reason_record: UnknownReasonRecord,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> bool:
        if reason_record.reason_id not in (
            UnknownReasonId.RETURN_COVERAGE_GAP.value,
            UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE.value,
        ):
            return False
        completed = set(self._completed_recovery_proof_ids(analysis1, analysis2))
        required_ids = tuple(
            self._normalize_nested_tuple(action.proof_obligation_id)
            for action in build_unknown_recovery_actions([reason_record])
        )
        if not required_ids or any(proof_id is None for proof_id in required_ids):
            return False
        return all(proof_id in completed for proof_id in required_ids)

    @classmethod
    def _completed_recovery_proof_evidence(
        cls,
        *analyses: FunctionReturnAnalysis,
    ) -> Tuple[Mapping[str, Any], ...]:
        evidence_records: List[Mapping[str, Any]] = []
        for analysis in analyses:
            for evidence in getattr(analysis, "completed_recovery_proof_evidence", ()) or ():
                if isinstance(evidence, Mapping):
                    evidence_records.append(evidence)
        return tuple(evidence_records)

    def _sat_unsafety_resolution_proof_is_complete(
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

    def _return_width_bridge_proof_is_complete(
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

    @classmethod
    def _return_width_bridge_slot_obligation_id(
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

    @classmethod
    def _return_width_bridge_discharge_proof_id(
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

    @classmethod
    def _completed_return_width_bridge_slots(
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

    def _readonly_identity_proof_is_complete(
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

    def _method_b_closure_proof_is_complete(
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

    def _all_recovery_actions_have_completed_proofs(
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

    def _record_completed_return_width_bridge_proofs(
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

    def _record_completed_return_width_bridge_semantic_narrowing_proofs(
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

    def _record_completed_return_width_bridge_member_narrow_producer_proofs(
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

    def _record_completed_sat_counterexample_replay_proof(
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

    @classmethod
    def _counterexample_model_fingerprint(
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

    @classmethod
    def _normalize_counterexample_model_value(cls, value: Any) -> Any:
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

    @classmethod
    def _completed_call_effect_summary_proof_ids(
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
        if cls._call_effect_summary_proof_content_is_required(object_target_key):
            proof_content = cls._evidence_get(evidence, "proof_content")
            if not cls._call_effect_summary_proof_content_is_complete(
                proof_content,
                object_target_key,
            ):
                return None
        return proof_id

    @classmethod
    def _call_effect_summary_proof_content_is_required(
        cls,
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        if not object_target_key:
            return False
        return str(object_target_key[0]) in cls._CALL_EFFECT_PROOF_CONTENT_REQUIRED_OBJECT_KINDS

    @classmethod
    def _call_effect_summary_proof_content_is_complete(
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

    @classmethod
    def _call_argument_evidence_phase15_proof_content_is_complete(
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

    @classmethod
    def _call_argument_phase15_sections_are_consistent(
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

    @classmethod
    def _call_argument_callee_summary_section_is_complete(
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

    @classmethod
    def _call_argument_precondition_section_is_complete(
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

    @classmethod
    def _call_argument_value_provenance_section_is_complete(
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

    @classmethod
    def _call_argument_dependency_graph_section_is_complete(
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

    @classmethod
    def _call_argument_bounded_refinement_section_is_complete(
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

    @classmethod
    def _validated_call_effect_blocker_selected_candidate(
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

    @classmethod
    def _call_effect_summary_section_matches(
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

    @classmethod
    def _expected_call_effect_proof_content_refs(
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

    @classmethod
    def _expected_deferred_call_proof_content_refs(
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

    @classmethod
    def _unsupported_call_effect_proof_content_is_complete(
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

    @classmethod
    def _deferred_call_proof_content_is_complete(
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

    @classmethod
    def _proof_section_payload_matches(
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

    @classmethod
    def _return_width_bridge_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
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

    @classmethod
    def _return_width_bridge_slot_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
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

    @classmethod
    def _readonly_identity_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
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

    @classmethod
    def _method_b_closure_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
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

    @classmethod
    def _evidence_required_evidence_matches(cls, evidence: Any, expected_required: Sequence[str]) -> bool:
        required_evidence = tuple(
            str(item)
            for item in (cls._evidence_get(evidence, "required_evidence") or ())
        )
        return required_evidence == tuple(expected_required)

    @classmethod
    def _readonly_identity_target_is_specific(cls, object_target_key: Any) -> bool:
        target = cls._normalize_nested_tuple(object_target_key)
        if not isinstance(target, tuple) or len(target) != 5 or target[0] != "readonly_identity":
            return False
        return (
            cls._proof_target_pair_is_specific(target[1])
            and cls._readonly_identity_side_is_specific(target[2], "left")
            and cls._readonly_identity_side_is_specific(target[3], "right")
            and cls._readonly_identity_relation_is_specific(target[4])
        )

    @classmethod
    def _method_b_closure_target_is_specific(cls, object_target_key: Any) -> bool:
        target = cls._normalize_nested_tuple(object_target_key)
        if not isinstance(target, tuple) or len(target) != 5 or target[0] != "method_b_closure":
            return False
        return (
            cls._proof_target_pair_is_specific(target[1])
            and cls._method_b_closure_side_is_specific(target[2], "left")
            and cls._method_b_closure_side_is_specific(target[3], "right")
            and cls._method_b_closure_relation_is_specific(target[4])
        )

    @classmethod
    def _proof_target_pair_is_specific(cls, value: Any) -> bool:
        pair = cls._normalize_nested_tuple(value)
        return (
            isinstance(pair, tuple)
            and len(pair) == 2
            and pair[0] == "pair"
            and cls._proof_text_is_specific(pair[1])
        )

    @classmethod
    def _readonly_identity_side_is_specific(cls, value: Any, expected_side: str) -> bool:
        side = cls._normalize_nested_tuple(value)
        return (
            isinstance(side, tuple)
            and len(side) == 7
            and side[0] == "readonly_identity_side"
            and side[1] == expected_side
            and not cls._proof_target_contains_diagnostic_value(side)
        )

    @classmethod
    def _method_b_closure_side_is_specific(cls, value: Any, expected_side: str) -> bool:
        side = cls._normalize_nested_tuple(value)
        return (
            isinstance(side, tuple)
            and len(side) == 6
            and side[0] == "method_b_closure_side"
            and side[1] == expected_side
            and not cls._proof_target_contains_diagnostic_value(side)
        )

    @classmethod
    def _readonly_identity_relation_is_specific(cls, value: Any) -> bool:
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

    @classmethod
    def _readonly_storage_relation_is_specific(cls, value: Any) -> bool:
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

    @classmethod
    def _tag_payload_is_specific(cls, value: Any, tag: str) -> bool:
        item = cls._normalize_nested_tuple(value)
        return (
            isinstance(item, tuple)
            and len(item) == 2
            and item[0] == tag
            and cls._object_leaf_is_specific(item[1])
        )

    @classmethod
    def _object_leaf_is_specific(cls, value: Any) -> bool:
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

    @classmethod
    def _readonly_bit_span_is_specific(cls, value: Any, tag: str) -> bool:
        span = cls._normalize_nested_tuple(value)
        return (
            isinstance(span, tuple)
            and len(span) == 3
            and span[0] == tag
            and cls._proof_nonnegative_int_like(span[1])
            and cls._proof_positive_int_like(span[2])
        )

    @classmethod
    def _readonly_component_key_is_specific(cls, value: Any) -> bool:
        normalized = cls._normalize_nested_tuple(value)
        if not isinstance(normalized, tuple) or not normalized or not cls._proof_text_is_specific(normalized[0]):
            return False
        if cls._proof_target_contains_missing_or_diagnostic(normalized):
            return False
        root = normalized[0]
        if root in {"parameter", "loop_limit_parameter"}:
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

    @classmethod
    def _method_b_closure_relation_is_specific(cls, value: Any) -> bool:
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

    @classmethod
    def _method_b_summary_profile_is_specific(cls, value: Any) -> bool:
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

    @classmethod
    def _method_b_runtime_ref_key_is_specific(cls, value: Any) -> bool:
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

    @classmethod
    def _method_b_loop_summary_key_is_specific(cls, value: Any) -> bool:
        normalized = cls._normalize_nested_tuple(value)
        return (
            isinstance(normalized, tuple)
            and len(normalized) >= 2
            and normalized[0] in {"loop_summary", "loop_summary_method_b", "counted_loop_summary_loop_profile"}
            and not cls._proof_target_contains_missing_or_diagnostic(normalized)
        )

    @classmethod
    def _readonly_term_contract_is_specific(cls, value: Any) -> bool:
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

    @classmethod
    def _readonly_projection_key_is_specific(cls, value: Any) -> bool:
        projection = cls._normalize_nested_tuple(value)
        return (
            isinstance(projection, tuple)
            and len(projection) == 2
            and all(cls._proof_int_like(item) for item in projection)
        )

    @classmethod
    def _readonly_side_effect_profile_is_specific(cls, value: Any) -> bool:
        profile = cls._normalize_nested_tuple(value)
        return (
            isinstance(profile, tuple)
            and len(profile) >= 2
            and profile[0] == "loop_side_effect_profile"
            and cls._proof_text_is_specific(profile[1])
            and not cls._proof_target_contains_missing_or_diagnostic(profile)
        )

    @classmethod
    def _method_b_count_identities_are_specific(cls, value: Any) -> bool:
        normalized = cls._normalize_nested_tuple(value)
        return (
            isinstance(normalized, tuple)
            and bool(normalized)
            and all(isinstance(item, tuple) and bool(item) for item in normalized)
            and not cls._proof_target_contains_missing_or_diagnostic(normalized)
        )

    @classmethod
    def _method_b_closure_relation_fields(cls, value: Any) -> Optional[Dict[str, Tuple[Any, ...]]]:
        relation = cls._normalize_nested_tuple(value)
        if not isinstance(relation, tuple) or len(relation) < 2 or relation[0] != "method_b_closure_relation":
            return None
        return {
            item[0]: item[1:]
            for item in relation[1:]
            if isinstance(item, tuple) and len(item) >= 2 and isinstance(item[0], str)
        }

    @classmethod
    def _method_b_one_sided_relation_payload(
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

    @classmethod
    def _method_b_exact_terms_are_specific(cls, value: Any) -> bool:
        terms = cls._normalize_nested_tuple(value)
        return (
            isinstance(terms, tuple)
            and bool(terms)
            and all(cls._method_b_readonly_term_is_specific(term) for term in terms)
        )

    @classmethod
    def _method_b_readonly_term_is_specific(cls, value: Any) -> bool:
        term = cls._normalize_nested_tuple(value)
        return (
            isinstance(term, tuple)
            and len(term) == 3
            and term[0] == "readonly_reduction_term"
            and cls._proof_nonnegative_int_like(term[1])
            and cls._proof_positive_int_like(term[2])
        )

    @classmethod
    def _proof_target_contains_weak_value(cls, value: Any) -> bool:
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

    @classmethod
    def _proof_target_contains_diagnostic_value(cls, value: Any) -> bool:
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

    @classmethod
    def _proof_target_contains_missing_or_diagnostic(cls, value: Any) -> bool:
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

    @classmethod
    def _proof_text_is_specific(cls, value: Any) -> bool:
        return isinstance(value, str) and bool(value.strip()) and not cls._proof_target_contains_weak_value(value)

    @classmethod
    def _proof_int_like(cls, value: Any) -> bool:
        if isinstance(value, bool):
            return False
        try:
            int(value)
        except (TypeError, ValueError):
            return False
        return True

    @classmethod
    def _proof_nonnegative_int_like(cls, value: Any) -> bool:
        return cls._proof_int_like(value) and int(value) >= 0

    @classmethod
    def _proof_positive_int_like(cls, value: Any) -> bool:
        return cls._proof_int_like(value) and int(value) > 0

    @classmethod
    def _readonly_identity_proof_content_is_complete(
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

    @classmethod
    def _readonly_identity_storage_relation_from_target(cls, object_target_key: Any) -> Optional[Tuple[Any, ...]]:
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

    @classmethod
    def _readonly_projection_extension_proof_content_is_complete(
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

    @classmethod
    def _method_b_closure_proof_content_is_complete(
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

    @classmethod
    def _method_b_proof_sides_match_relation(
        cls,
        proof_content: Mapping[str, Any],
        relation_payload: Mapping[str, Any],
    ) -> bool:
        return (
            cls._evidence_text(proof_content, "exact_side") == relation_payload.get("exact_side")
            and cls._evidence_text(proof_content, "summary_side") == relation_payload.get("summary_side")
        )

    @classmethod
    def _method_b_covering_proof_content_matches_relation(
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

    @classmethod
    def _method_b_guard_proof_content_matches_relation(
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

    @classmethod
    def _method_b_guard_count_values(cls, proof_content: Mapping[str, Any]) -> Tuple[int, ...]:
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

    @classmethod
    def _method_b_dual_summary_relation_payload(
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

    @classmethod
    def _method_b_dual_summary_proof_content_matches_relation(
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

    @classmethod
    def _proof_status_value_is_complete(cls, value: Any) -> bool:
        return str(value or "") in {"complete", "completed", "covered", "matched", "proven", "checked", "vacuous"}

    @classmethod
    def _return_width_bridge_completed_proof_content(
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

    @classmethod
    def _return_width_bridge_abi_relation_proof_content_is_complete(
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

    @classmethod
    def _return_width_bridge_high_bit_proof_content_is_complete(
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

    @classmethod
    def _return_width_bridge_high_bit_proof_source_matches_content(
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

    def _return_width_bridge_slot_evidence_matches_current_analyses(
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
                and self._normalize_nested_tuple(provided_content)
                == self._normalize_nested_tuple(current_content)
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

    def _return_width_bridge_semantic_narrowing_proof_content(
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

    def _return_width_bridge_member_narrow_producer_proof_content(
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
        if type_provenance is None or type_provenance.get("narrowing_allowed") is not True:
            self._debug_print(
                "  return-width bridge member producer proof rejected: "
                f"return type provenance disallows narrowing ({type_provenance})"
            )
            return None

        try:
            from .pairwise_query_builder import extract_return_cases
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
            self._debug_print("  return-width bridge member producer proof rejected: target member not found")
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
            self._debug_print("  return-width bridge member producer proof rejected: producer width unavailable")
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
            self._debug_print(
                "  return-width bridge member producer proof rejected: "
                f"producer profile blockers={tuple(sorted(set(rejection_reasons)))}"
            )
            return None

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
            "member_high_bit_relation": {
                "object_derived": True,
                "status": "proven",
                "relation": "target_return_member_high_bits_irrelevant_by_narrow_producer",
                "narrow_width": int(narrow_width),
                "wide_width": int(wide_return_bits),
                "proven": True,
            },
            "target_member_profile": {
                "object_derived": True,
                "status": "proven",
                "function_ref": self._analysis_entry_key(wide_analysis),
                "return_storage": self._return_storage_object_key(wide_analysis),
                "return_type_provenance": type_provenance,
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

    def _return_width_bridge_wide_surface_profile(
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
            from .pairwise_query_builder import extract_return_cases
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

    @classmethod
    def _return_width_bridge_semantic_narrowing_content_is_complete(
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

    @classmethod
    def _return_width_bridge_member_narrow_producer_content_is_complete(
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
        if not isinstance(type_provenance, Mapping) or type_provenance.get("narrowing_allowed") is not True:
            return False
        return True

    @classmethod
    def _return_width_bridge_return_type_provenance(
        cls,
        analysis: FunctionReturnAnalysis,
        counterpart_analysis: FunctionReturnAnalysis,
        *,
        narrow_width: int,
    ) -> Optional[Dict[str, Any]]:
        try:
            from ...model.signature import get_declared_type_size_bits, get_data_type_display_name
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

    @classmethod
    def _return_width_bridge_expression_producer_profile(
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

    def _return_width_bridge_wide_surface_coverage_identity(
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

    @classmethod
    def _return_width_bridge_common_proof_content_is_complete(
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

    @classmethod
    def _return_width_bridge_target_is_specific(cls, object_target_key: Any) -> bool:
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

    @classmethod
    def _return_width_bridge_side_is_specific(cls, side: Tuple[Any, ...], expected_width: int) -> bool:
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

    @classmethod
    def _return_width_bridge_return_value_width_entry_is_specific(
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

    @staticmethod
    def _positive_int_like(value: Any) -> bool:
        if isinstance(value, bool):
            return False
        try:
            return int(value) > 0
        except (TypeError, ValueError):
            return False

    @classmethod
    def _return_width_bridge_value_width_evidence(
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

    @classmethod
    def _return_width_bridge_extension_policy_for_side(cls, side: Any) -> Optional[str]:
        width_entry = cls._return_width_bridge_find_tagged_entry(side, "return_value_width")
        normalized = cls._normalize_nested_tuple(width_entry)
        if not isinstance(normalized, tuple) or len(normalized) < 7:
            return None
        policy = normalized[6]
        return str(policy) if policy in {"none", "sign_extend", "zero_extend", "truncate"} else None

    @classmethod
    def _return_width_bridge_required_extension_mnemonic_for_side(
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

    @classmethod
    def _return_width_bridge_extension_ops_for_side(cls, side: Any) -> Tuple[Any, ...]:
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

    @classmethod
    def _return_width_bridge_matching_extension_ops_for_side(
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

    @classmethod
    def _return_width_bridge_extension_evidence_for_side(
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

    @classmethod
    def _return_width_bridge_has_summary_parameter_extension_evidence(
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

    @classmethod
    def _return_width_bridge_summary_parameter_extension_for_side(
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

    @classmethod
    def _return_width_bridge_constant_literal_extension_for_side(
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

    @classmethod
    def _return_width_bridge_value_is_deterministic_width_expression(cls, value_entry: Any) -> bool:
        value = cls._normalize_nested_tuple(value_entry)
        if not isinstance(value, tuple) or len(value) != 2 or value[0] != "value":
            return False
        return cls._return_width_bridge_expression_key_is_deterministic_width(value[1])

    @classmethod
    def _return_width_bridge_expression_key_is_deterministic_width(cls, expr: Any) -> bool:
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

    @classmethod
    def _return_width_bridge_summary_parameter_value_key(cls, value_entry: Any) -> Optional[Tuple[Any, ...]]:
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

    @classmethod
    def _return_width_bridge_normalize_optional_tuple(cls, value: Any) -> Tuple[Any, ...]:
        normalized = cls._normalize_nested_tuple(value)
        return normalized if isinstance(normalized, tuple) else ()

    @classmethod
    def _return_width_bridge_extension_op_profile_matches(
        cls,
        profile: Any,
        *,
        mnemonic: str,
        producer_bits: Any,
        return_bits: Any,
    ) -> bool:
        normalized = cls._normalize_nested_tuple(profile)
        if not isinstance(normalized, tuple) or len(normalized) < 6:
            return False
        if normalized[0] != "extension_op" or normalized[1] != mnemonic:
            return False
        op_ref = cls._return_width_bridge_find_tagged_entry(normalized, "op_ref")
        input_bits = cls._return_width_bridge_find_tagged_entry(normalized, "input_bits")
        output_bits = cls._return_width_bridge_find_tagged_entry(normalized, "output_bits")
        policy = cls._return_width_bridge_find_tagged_entry(normalized, "policy")
        expected_policy = "sign_extend" if mnemonic == "INT_SEXT" else "zero_extend"
        try:
            input_bits_int = int(input_bits[1] if isinstance(input_bits, tuple) and len(input_bits) == 2 else input_bits)
            output_bits_int = int(output_bits[1] if isinstance(output_bits, tuple) and len(output_bits) == 2 else output_bits)
            producer_bits_int = int(producer_bits)
            return_bits_int = int(return_bits)
        except (TypeError, ValueError):
            return False
        return (
            isinstance(op_ref, tuple)
            and len(op_ref) == 2
            and op_ref[1] is not None
            and input_bits_int == producer_bits_int
            and output_bits_int >= return_bits_int
            and isinstance(policy, tuple)
            and len(policy) == 2
            and policy[1] == expected_policy
        )

    @classmethod
    def _return_width_bridge_target_widths(cls, object_target_key: Any) -> Optional[Tuple[int, int]]:
        target = cls._normalize_nested_tuple(object_target_key)
        widths = cls._return_width_bridge_find_tagged_entry(target, "return_widths")
        if not isinstance(widths, tuple) or len(widths) != 3:
            return None
        try:
            left_width = int(widths[1])
            right_width = int(widths[2])
        except (TypeError, ValueError):
            return None
        if left_width <= 0 or right_width <= 0:
            return None
        return left_width, right_width

    @classmethod
    def _return_width_bridge_target_narrow_width(cls, object_target_key: Any) -> Optional[int]:
        widths = cls._return_width_bridge_target_widths(object_target_key)
        if widths is None:
            return None
        return min(widths)

    @classmethod
    def _return_width_bridge_find_side(
        cls,
        object_target_key: Any,
        side_label: str,
    ) -> Optional[Tuple[Any, ...]]:
        target = cls._normalize_nested_tuple(object_target_key)
        if not isinstance(target, tuple):
            return None
        for item in target:
            if (
                isinstance(item, tuple)
                and len(item) >= 2
                and item[0] == "return_width_side"
                and item[1] == side_label
            ):
                return item
        return None

    @classmethod
    def _return_width_bridge_find_tagged_entry(cls, value: Any, tag: str) -> Any:
        normalized = cls._normalize_nested_tuple(value)
        if not isinstance(normalized, tuple):
            return None
        for item in normalized:
            if isinstance(item, tuple) and item and item[0] == tag:
                return item
        return None

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
    def _query_cases_are_nonempty(cls, value: Any) -> bool:
        return (
            isinstance(value, tuple)
            and len(value) > 0
            and all(isinstance(item, str) for item in value)
        )


    @classmethod
    def _return_coverage_proof_content_can_discharge_inconclusive(
        cls,
        proof_content: Any,
    ) -> bool:
        if not isinstance(proof_content, Mapping):
            return False
        solver_evidence = proof_content.get("solver_model_or_timeout")
        if solver_evidence is None:
            return False
        if not isinstance(solver_evidence, Mapping):
            return False
        status = cls._evidence_text(solver_evidence, "status")
        return status in {"complete", "completed", "proven", "unsat", "discharged"}

    @classmethod
    def _return_coverage_guard_evidence_is_complete(
        cls,
        proof_content: Mapping[str, Any],
        normalized_query: str,
    ) -> bool:
        guard_evidence = proof_content.get("coverage_guard_evidence")
        if not isinstance(guard_evidence, Mapping):
            return False
        if cls._evidence_text(guard_evidence, "status") not in {"complete", "completed", "proven"}:
            return False
        guard_source = cls._evidence_text(guard_evidence, "guard_source")
        if guard_source not in {
            "case_guard_disjunction",
            "normalized_guard_formula",
            "return_partition_guard_set",
        }:
            return False
        if guard_source != "case_guard_disjunction" and cls._evidence_text(
            guard_evidence,
            "coverage_status",
        ) != "covered":
            return False
        case_count = guard_evidence.get("case_count")
        if not isinstance(case_count, int) or case_count < 0:
            return False
        expected_hash = hashlib.sha256(normalized_query.encode("utf-8")).hexdigest()
        return guard_evidence.get("normalized_guard_formula_sha256") == expected_hash

    @classmethod
    def _return_coverage_proof_content_is_complete(
        cls,
        evidence: Mapping[str, Any],
        reason_id: Optional[UnknownReasonId] = None,
    ) -> bool:
        if cls._evidence_get(evidence, "target_schema_version") != cls._RETURN_COVERAGE_TARGET_SCHEMA_VERSION:
            return False
        evidence_schema = cls._evidence_get(evidence, "proof_schema_version")
        if evidence_schema not in {
            cls._RETURN_COVERAGE_PROOF_SCHEMA_VERSION,
            cls._RETURN_COVERAGE_NORMALIZATION_AWARE_PROOF_SCHEMA_VERSION,
        }:
            return False
        if reason_id is not None:
            evidence_reason_id = cls._evidence_text(evidence, "reason_id")
            if evidence_reason_id != reason_id.value:
                return False
        proof_content = cls._evidence_get(evidence, "proof_content")
        if not isinstance(proof_content, Mapping):
            return False
        if reason_id is not None:
            applicable_reason_ids = cls._normalize_nested_tuple(
                cls._evidence_get(evidence, "applicable_reason_ids")
            )
            if applicable_reason_ids is None:
                applicable_reason_ids = cls._normalize_nested_tuple(
                    proof_content.get("applicable_reason_ids")
                )
            if applicable_reason_ids is not None and reason_id.value not in set(applicable_reason_ids):
                return False
        evidence_target = cls._normalize_nested_tuple(cls._evidence_get(evidence, "object_target_key"))
        proof_target = cls._normalize_nested_tuple(proof_content.get("proof_target_identity"))
        if proof_target != evidence_target:
            return False
        content_schema = proof_content.get("proof_schema_version")
        if content_schema != evidence_schema:
            return False
        if proof_content.get("normalization_schema_version") != cls._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION:
            return False
        normalization_required = cls._return_coverage_normalization_required(
            evidence,
            proof_content,
            evidence_target,
        )
        if normalization_required and evidence_schema != cls._RETURN_COVERAGE_NORMALIZATION_AWARE_PROOF_SCHEMA_VERSION:
            return False
        if evidence_schema == cls._RETURN_COVERAGE_NORMALIZATION_AWARE_PROOF_SCHEMA_VERSION:
            if not cls._return_coverage_normalization_proof_content_is_complete(
                proof_content,
                evidence_target,
                required=normalization_required,
            ):
                return False
        if not cls._return_coverage_structural_proof_content_is_complete(proof_content):
            return False
        if not cls._return_coverage_structural_proof_content_matches_target(
            proof_content,
            evidence_target,
        ):
            return False
        case_guard_disjunction = proof_content.get("case_guard_disjunction")
        if not isinstance(case_guard_disjunction, Mapping):
            return False
        status = cls._evidence_text(case_guard_disjunction, "status")
        if status not in {"complete", "completed", "proven"}:
            return False
        normalized_guard_formula = proof_content.get("normalized_guard_formula")
        if not isinstance(normalized_guard_formula, Mapping):
            return False
        normalized_status = cls._evidence_text(normalized_guard_formula, "status")
        if normalized_status not in {"complete", "completed", "proven"}:
            return False
        normalized_query = normalized_guard_formula.get("query")
        if not isinstance(normalized_query, str) or not normalized_query:
            return False
        if not cls._return_coverage_guard_evidence_is_complete(proof_content, normalized_query):
            return False
        if reason_id == UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE:
            if not cls._return_coverage_proof_content_can_discharge_inconclusive(proof_content):
                return False
        else:
            solver_evidence = proof_content.get("solver_model_or_timeout")
            if isinstance(solver_evidence, Mapping):
                solver_status = cls._evidence_text(solver_evidence, "status")
                if solver_status in {"unknown", "timeout", "error", "inconclusive"}:
                    return False
        return True

    @classmethod
    def _return_coverage_normalization_required(
        cls,
        evidence: Mapping[str, Any],
        proof_content: Mapping[str, Any],
        object_target_key: Any,
    ) -> bool:
        if cls._evidence_bool(evidence, "normalization_required") or bool(
            proof_content.get("normalization_required")
        ):
            return True
        if cls._nested_contains_tag(object_target_key, "normalization_policy_digest"):
            return True
        for key in (
            "normalized_guard_payload",
            "normalized_value_payload",
            "normalized_address_payload",
            "raw_normalized_correspondence",
        ):
            if key in proof_content:
                return True
        return False

    @classmethod
    def _nested_contains_tag(cls, value: Any, tag: str) -> bool:
        if isinstance(value, Mapping):
            return any(cls._nested_contains_tag(item, tag) for item in value.values())
        if isinstance(value, tuple):
            if value and value[0] == tag:
                return True
            return any(cls._nested_contains_tag(item, tag) for item in value)
        if isinstance(value, list):
            return any(cls._nested_contains_tag(item, tag) for item in value)
        return False

    @classmethod
    def _return_coverage_normalization_proof_content_is_complete(
        cls,
        proof_content: Mapping[str, Any],
        object_target_key: Any,
        *,
        required: bool,
    ) -> bool:
        policy = proof_content.get("normalization_policy")
        policy_digest = proof_content.get("normalization_policy_digest")
        if not isinstance(policy, Mapping) or not isinstance(policy_digest, str) or not policy_digest:
            return not required
        if cls._return_coverage_normalization_policy_digest(policy) != policy_digest:
            return False
        target_digest = cls._normalization_policy_digest_from_target(object_target_key)
        if target_digest is not None and target_digest != policy_digest:
            return False
        correspondence = proof_content.get("raw_normalized_correspondence")
        if not isinstance(correspondence, Mapping):
            return not required
        if cls._evidence_text(correspondence, "status") not in {"complete", "completed", "proven"}:
            return False
        if correspondence.get("normalization_policy_digest") != policy_digest:
            return False
        raw_identity = cls._normalize_nested_tuple(correspondence.get("raw_guard_identity"))
        normalized_identity = cls._normalize_nested_tuple(correspondence.get("normalized_guard_identity"))
        before_key = cls._normalize_nested_tuple(correspondence.get("before_structural_key"))
        after_key = cls._normalize_nested_tuple(correspondence.get("after_structural_key"))
        if raw_identity is None or normalized_identity is None or before_key is None or after_key is None:
            return False
        if not correspondence.get("rule_id"):
            return False
        equivalence_proof = correspondence.get("equivalence_proof")
        if not isinstance(equivalence_proof, Mapping):
            return False
        if cls._evidence_text(equivalence_proof, "status") not in {"complete", "completed", "proven", "unsat"}:
            return False
        normalized_guard_formula = proof_content.get("normalized_guard_formula")
        if not isinstance(normalized_guard_formula, Mapping):
            return False
        query = normalized_guard_formula.get("query")
        if not isinstance(query, str) or not query:
            return False
        expected_query_hash = hashlib.sha256(query.encode("utf-8")).hexdigest()
        payloads: List[Tuple[str, Mapping[str, Any]]] = []
        for kind, key in (
            ("guard", "normalized_guard_payload"),
            ("value", "normalized_value_payload"),
            ("address", "normalized_address_payload"),
        ):
            payload = proof_content.get(key)
            if payload is None:
                continue
            if not isinstance(payload, Mapping):
                return False
            payloads.append((kind, payload))
        if not payloads:
            return not required
        for kind, payload in payloads:
            if not cls._return_coverage_normalized_payload_is_complete(
                kind,
                payload,
                policy_digest=policy_digest,
                expected_query_hash=expected_query_hash,
                correspondence=correspondence,
                default_raw_identity=raw_identity,
                default_normalized_identity=normalized_identity,
            ):
                return False
        return True

    @classmethod
    def _return_coverage_normalized_payload_is_complete(
        cls,
        kind: str,
        payload: Mapping[str, Any],
        *,
        policy_digest: str,
        expected_query_hash: str,
        correspondence: Mapping[str, Any],
        default_raw_identity: Any,
        default_normalized_identity: Any,
    ) -> bool:
        if payload.get("normalization_policy_digest") != policy_digest:
            return False
        payload_raw = cls._normalize_nested_tuple(payload.get("raw_identity"))
        payload_normalized = cls._normalize_nested_tuple(payload.get("normalized_identity"))
        if payload_raw is None or payload_normalized is None:
            return False
        expected_raw = cls._normalize_nested_tuple(correspondence.get(f"raw_{kind}_identity"))
        expected_normalized = cls._normalize_nested_tuple(
            correspondence.get(f"normalized_{kind}_identity")
        )
        if kind == "guard":
            expected_raw = expected_raw if expected_raw is not None else default_raw_identity
            expected_normalized = (
                expected_normalized
                if expected_normalized is not None
                else default_normalized_identity
            )
        elif expected_raw is None or expected_normalized is None:
            return False
        if expected_raw is not None and payload_raw != expected_raw:
            return False
        if expected_normalized is not None and payload_normalized != expected_normalized:
            return False
        final_hash = payload.get("final_query_sha256")
        if not isinstance(final_hash, str) or not final_hash:
            return False
        return final_hash == expected_query_hash

    @classmethod
    def _normalization_policy_digest_from_target(cls, object_target_key: Any) -> Optional[str]:
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

    @classmethod
    def _return_coverage_structural_proof_content_is_complete(
        cls,
        proof_content: Mapping[str, Any],
    ) -> bool:
        guard_keys = proof_content.get("structural_guard_keys")
        miss_keys = proof_content.get("structural_miss_formula_keys")
        solver_evidence = proof_content.get("coverage_solver_evidence")
        bit_width_metadata = proof_content.get("bit_width_signedness_metadata")
        if not isinstance(guard_keys, Mapping) or cls._evidence_text(guard_keys, "status") != "complete":
            return False
        if not isinstance(miss_keys, Mapping) or cls._evidence_text(miss_keys, "status") != "complete":
            return False
        if not isinstance(solver_evidence, Mapping):
            return False
        solver_status = cls._evidence_text(solver_evidence, "status")
        proof_method = cls._evidence_text(solver_evidence, "proof_method")
        if solver_status != "unsat" and not (
            solver_status == "not_applicable"
            and proof_method in {"unconditional_return_case", "object_centric_total_coverage"}
        ):
            return False
        if not isinstance(bit_width_metadata, Mapping):
            return False
        if cls._evidence_text(bit_width_metadata, "status") != "complete":
            return False
        guard_key_values = cls._normalize_nested_tuple(guard_keys.get("keys"))
        miss_key_values = cls._normalize_nested_tuple(miss_keys.get("keys"))
        if not isinstance(guard_key_values, tuple) or not guard_key_values:
            return False
        if not isinstance(miss_key_values, tuple) or not miss_key_values:
            return False
        if cls._evidence_has_any_recursive(
            {
                "structural_guard_keys": guard_key_values,
                "structural_miss_formula_keys": miss_key_values,
            },
            cls._COMPLETED_PROOF_BLOCKER_FIELDS,
        ):
            return False
        return True

    @classmethod
    def _return_coverage_structural_proof_content_matches_target(
        cls,
        proof_content: Mapping[str, Any],
        object_target_key: Any,
    ) -> bool:
        if not cls._return_coverage_object_target_key_is_valid(object_target_key):
            return False
        target_partition_cases = cls._return_coverage_target_partition_cases(object_target_key)
        if target_partition_cases is None:
            return False
        expected_guard_entries: List[Tuple[Any, ...]] = []
        expected_miss_entries: List[Tuple[Any, ...]] = []
        for case in target_partition_cases:
            fields = {
                field[0]: field[1]
                for field in case[1:]
                if isinstance(field, tuple) and len(field) == 2 and isinstance(field[0], str)
            }
            if "guards" not in fields or "return_value" not in fields or "case_miss_formula" not in fields:
                return False
            expected_guard_entries.append(
                (
                    "return_case_guard_set",
                    ("guard_structural_keys", cls._normalize_nested_tuple(fields["guards"])),
                    ("return_value_structural_key", cls._normalize_nested_tuple(fields["return_value"])),
                )
            )
            expected_miss_entries.append(
                (
                    "case_miss_formula",
                    cls._normalize_nested_tuple(fields["case_miss_formula"]),
                )
            )

        guard_keys = proof_content.get("structural_guard_keys")
        miss_keys = proof_content.get("structural_miss_formula_keys")
        if not isinstance(guard_keys, Mapping) or not isinstance(miss_keys, Mapping):
            return False
        actual_guard_entries = []
        for entry in cls._normalize_nested_tuple(guard_keys.get("keys")) or ():
            if not isinstance(entry, tuple) or len(entry) < 4 or entry[0] != "return_case_guard_set":
                return False
            fields = {
                field[0]: field[1]
                for field in entry[2:]
                if isinstance(field, tuple) and len(field) == 2 and isinstance(field[0], str)
            }
            if "guard_structural_keys" not in fields or "return_value_structural_key" not in fields:
                return False
            actual_guard_entries.append(
                (
                    "return_case_guard_set",
                    ("guard_structural_keys", cls._normalize_nested_tuple(fields["guard_structural_keys"])),
                    ("return_value_structural_key", cls._normalize_nested_tuple(fields["return_value_structural_key"])),
                )
            )
        actual_miss_entries = []
        for entry in cls._normalize_nested_tuple(miss_keys.get("keys")) or ():
            if not isinstance(entry, tuple) or len(entry) < 3 or entry[0] != "case_miss_formula":
                return False
            actual_miss_entries.append(
                (
                    "case_miss_formula",
                    cls._normalize_nested_tuple(entry[2]),
                )
            )
        return (
            cls._canonicalize_key_sequence(expected_guard_entries)
            == cls._canonicalize_key_sequence(actual_guard_entries)
            and cls._canonicalize_key_sequence(expected_miss_entries)
            == cls._canonicalize_key_sequence(actual_miss_entries)
        )

    @staticmethod
    def _return_coverage_target_partition_cases(object_target_key: Any) -> Optional[Tuple[Any, ...]]:
        if not isinstance(object_target_key, tuple) or len(object_target_key) < 7:
            return None
        partition = object_target_key[6]
        if not isinstance(partition, tuple) or len(partition) < 3:
            return None
        if partition[0] != "return_partition_identity":
            return None
        cases = partition[2]
        if not isinstance(cases, tuple):
            return None
        for case in cases:
            if not isinstance(case, tuple) or not case or case[0] != "return_case_identity":
                return None
        return cases

    @classmethod
    def _return_coverage_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
        if not cls._evidence_bool(evidence, "object_derived"):
            return None
        if cls._evidence_text(evidence, "status") not in {"complete", "completed", "proven"}:
            return None
        reason_id = cls._evidence_text(evidence, "reason_id")
        if reason_id not in {
            UnknownReasonId.RETURN_COVERAGE_GAP.value,
            UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE.value,
        }:
            return None
        canonical_reason_id = None
        try:
            canonical_reason_id = UnknownReasonId(reason_id)
        except ValueError:
            canonical_reason_id = None
        proof_kind = cls._evidence_text(evidence, "recovery_proof_kind")
        if proof_kind != UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION.value:
            return None
        proof_stage = cls._evidence_text(evidence, "proof_stage")
        requirements = (
            cls._RETURN_COVERAGE_COMPLETION_REQUIREMENTS.get(canonical_reason_id)
            if canonical_reason_id is not None
            else None
        )
        if not requirements:
            return None
        allowed_stages = {proof_stage_ for proof_stage_, _ in requirements}
        if proof_stage not in allowed_stages:
            return None
        evidence_kind = cls._evidence_text(evidence, "evidence_kind")
        if not evidence_kind:
            return None
        if cls._evidence_has_any(evidence, cls._COMPLETED_PROOF_BLOCKER_FIELDS):
            return None
        object_target_key = cls._normalize_nested_tuple(cls._evidence_get(evidence, "object_target_key"))
        if not isinstance(object_target_key, tuple):
            return None
        if not cls._return_coverage_object_target_key_is_valid(object_target_key):
            return None
        proof_id = build_proof_obligation_id(
            reason_id,
            proof_stage,
            proof_kind,
            evidence_kind,
            object_target_key,
        )
        provided_id = cls._normalize_nested_tuple(cls._evidence_get(evidence, "proof_obligation_id"))
        if provided_id is None or provided_id != proof_id:
            return None
        if not cls._return_coverage_proof_content_is_complete(evidence, canonical_reason_id):
            return None
        return proof_id

    @classmethod
    def _return_coverage_object_target_key_is_valid(cls, object_target_key: Tuple[Any, ...]) -> bool:
        if not isinstance(object_target_key, tuple) or len(object_target_key) < 8:
            return False
        if object_target_key[0] != "return_coverage":
            return False
        schema = object_target_key[1]
        if not (
            isinstance(schema, tuple)
            and len(schema) == 2
            and schema[0] == "target_schema_version"
            and schema[1] == cls._RETURN_COVERAGE_TARGET_SCHEMA_VERSION
        ):
            return False
        if object_target_key[2] not in {"function1", "function2"}:
            return False
        if not isinstance(object_target_key[3], tuple) or object_target_key[3][0] != "function_identity":
            return False
        if object_target_key[4] not in {"return_coverage_gap", "return_coverage_inconclusive"}:
            return False
        if not isinstance(object_target_key[6], tuple) or object_target_key[6][0] != "return_partition_identity":
            return False
        if not isinstance(object_target_key[7], tuple) or object_target_key[7][0] != "guard_disjunction_identity":
            return False
        return not cls._return_coverage_identity_contains_forbidden_atoms(object_target_key)

    @classmethod
    def _return_coverage_identity_contains_forbidden_atoms(cls, value: Any) -> bool:
        if isinstance(value, Mapping):
            return True
        if isinstance(value, (list, set, frozenset)):
            return True
        if isinstance(value, tuple):
            if value and value[0] in {"object_id", "program_uid", "opaque"}:
                return True
            if len(value) == 2 and value[0] == "int" and isinstance(value[1], int) and value[1] < 0:
                return False
            return any(cls._return_coverage_identity_contains_forbidden_atoms(item) for item in value)
        if value is None or isinstance(value, str) or isinstance(value, bool):
            return False
        if isinstance(value, int) and not isinstance(value, bool):
            return False
        return True

    @classmethod
    def _analysis_has_active_call_effect_proof_blockers(
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
        target = (
            "return_coverage",
            ("target_schema_version", self._RETURN_COVERAGE_TARGET_SCHEMA_VERSION),
            label,
            self._deterministic_function_identity(analysis),
            reason_kind,
            self._return_storage_object_key(analysis),
            self._return_coverage_partition_identity_key(analysis),
            self._return_coverage_guard_disjunction_identity_key(analysis),
        )
        return self._identity_freeze(
            self._artifact_stable_key_for_analysis(
                self._identity_freeze(target),
                analysis,
            )
        )

    def _outcome_partition_unknown_object_target_key(
        self,
        blocking_reason: str,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> Optional[Tuple[Any, ...]]:
        label, _reason_text = self._split_blocking_reason(blocking_reason)
        reason_kind = self._blocking_reason_kind(blocking_reason)
        if reason_kind != "outcome_partition_unknown":
            return None
        analysis = analysis1 if label == "function1" else analysis2 if label == "function2" else None
        if analysis is None:
            return None
        target = (
            "outcome_partition_unknown",
            ("target_schema_version", 1),
            label,
            self._deterministic_function_identity(analysis),
            self._return_storage_object_key(analysis),
            self._outcome_partition_identity_key(analysis),
            self._unknown_outcome_identity_key(analysis),
        )
        return self._identity_freeze(
            self._artifact_stable_key_for_analysis(
                self._identity_freeze(target),
                analysis,
            )
        )

    def _outcome_partition_unknown_object_evidence(
        self,
        blocking_reason: str,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> Optional[Dict[str, Any]]:
        label, _reason_text = self._split_blocking_reason(blocking_reason)
        analysis = analysis1 if label == "function1" else analysis2 if label == "function2" else None
        if analysis is None:
            return None
        return {
            "object_derived": True,
            "evidence_version": 1,
            "evidence_kind": "outcome_partition",
            "blocker_reason": blocking_reason,
            "side": label,
            "analysis_key": self._analysis_entry_key(analysis),
            "return_storage": self._return_storage_object_key(analysis),
            "outcome_partition": self._outcome_partition_identity_key(analysis),
            "unknown_outcomes": self._unknown_outcome_identity_key(analysis),
        }

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

    def _make_sat_counterexample_ambiguous_unknown_reason(
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

    def _sat_unsafety_object_evidence(
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

    def _sat_unsafety_side_object_evidence(
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

    def _sat_unsafety_reason_object_evidence(
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

    def _sat_counterexample_ambiguous_object_target_key(
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
            self._return_width_bridge_return_value_width_object_key(
                case,
                return_info,
                return_size,
            ),
        )

    def _return_width_bridge_return_value_width_object_key(
        self,
        case: Any,
        return_info: Any,
        return_size: Optional[int],
    ) -> Tuple[Any, ...]:
        value_expr = getattr(case, "value_expr", None)
        expression_bits = self._expression_smt_bit_width_for_object_key(value_expr)
        pcode_op_ref = getattr(return_info, "pcode_op_ref", None)
        pcode_input_bits = self._return_pcode_value_input_width_bits(pcode_op_ref)
        producer_bits = self._coerce_return_width(expression_bits, pcode_input_bits)
        return_bits = self._coerce_return_width(return_size)
        use_sign_extension = bool(
            getattr(case, "should_sign_extend_value", lambda: False)()
        )
        relation = "producer_matches_return_width"
        policy = "none"
        if producer_bits is not None and return_bits is not None:
            if producer_bits < return_bits:
                relation = "producer_narrower_than_return_width"
                policy = "sign_extend" if use_sign_extension else "zero_extend"
            elif producer_bits > return_bits:
                relation = "producer_wider_than_return_width"
                policy = "truncate"
        return (
            "return_value_width",
            producer_bits,
            return_bits,
            use_sign_extension,
            ("value", self._expression_runtime_object_key(value_expr)),
            relation,
            policy,
            ("expression_bits", expression_bits),
            ("return_pcode_value_input_bits", pcode_input_bits),
            self._return_value_extension_ops_object_key(return_info),
        )

    def _return_value_extension_ops_object_key(self, return_info: Any) -> Tuple[Any, ...]:
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

    @staticmethod
    def _expression_smt_bit_width_for_object_key(expr: Any) -> Optional[int]:
        if expr is None:
            return None
        try:
            bits = int(expression_smt_bit_width(expr) or 0)
        except (AttributeError, TypeError, ValueError, RecursionError):
            bits = 0
        if bits <= 0:
            try:
                bits = int(getattr(expr, "get_bit_width", lambda: 0)() or 0)
            except (AttributeError, TypeError, ValueError, RecursionError):
                bits = 0
        return bits if bits > 0 else None

    @staticmethod
    def _return_pcode_value_input_width_bits(pcode_op_ref: Any) -> Optional[int]:
        input_sizes = getattr(pcode_op_ref, "input_sizes", None) or ()
        if not input_sizes:
            return None
        candidates = []
        for size in input_sizes:
            try:
                int_size = int(size)
            except (TypeError, ValueError):
                continue
            if int_size > 0:
                candidates.append(int_size)
        if not candidates:
            return None
        return max(1, candidates[-1]) * 8

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

    def _return_coverage_partition_identity_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
        cases = tuple(
            self._return_coverage_case_identity_key(return_info)
            for return_info in (getattr(analysis, "returns", ()) or ())
        )
        return (
            "return_partition_identity",
            ("normalization_schema_version", self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION),
            self._canonicalize_key_sequence(cases),
        )

    def _return_coverage_case_identity_key(self, return_info: Any) -> Tuple[Any, ...]:
        pcode_op_ref = getattr(return_info, "pcode_op_ref", None)
        value = getattr(return_info, "value", None)
        conditions = tuple(getattr(return_info, "conditions", None) or ())
        miss_expr = self._case_miss_expression(list(conditions))
        return (
            "return_case_identity",
            ("site", self._identity_freeze(getattr(return_info, "address", None))),
            ("pcode_sequence", self._identity_freeze(self._stable_key_or_none(pcode_op_ref))),
            ("pcode_identity", self._identity_freeze(getattr(return_info, "pcode_identity", None))),
            ("pcode_order", self._identity_freeze(getattr(return_info, "pcode_order", None))),
            ("pcode_time", self._identity_freeze(getattr(return_info, "pcode_time", None))),
            ("return_value", self._expression_runtime_object_key(value)),
            (
                "case_miss_formula",
                self._expression_runtime_object_key(miss_expr) if miss_expr is not None else None,
            ),
            (
                "guards",
                self._canonicalize_key_sequence(
                    tuple(
                        self._return_condition_object_key(condition)
                        for condition in conditions
                    )
                ),
            ),
            ("bit_width", self._expression_smt_bit_width_for_object_key(value)),
        )

    def _return_coverage_guard_disjunction_identity_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
        guard_sets = tuple(
            (
                "return_case_guard_identity",
                self._canonicalize_key_sequence(
                    tuple(
                        self._return_condition_object_key(condition)
                        for condition in (getattr(return_info, "conditions", None) or ())
                    )
                ),
            )
            for return_info in (getattr(analysis, "returns", ()) or ())
        )
        return (
            "guard_disjunction_identity",
            ("normalization_schema_version", self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION),
            self._canonicalize_key_sequence(guard_sets),
        )

    def _outcome_partition_identity_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
        return_outcomes = tuple(getattr(analysis, "return_outcomes", ()) or ())
        divergence_outcomes = tuple(getattr(analysis, "divergence_outcomes", ()) or ())
        unknown_outcomes = tuple(getattr(analysis, "unknown_outcomes", ()) or ())
        return_keys = tuple(
            (
                "return",
                index,
                self._canonicalize_key_sequence(
                    tuple(self._return_condition_object_key(condition) for condition in (getattr(outcome, "guard", ()) or ()))
                ),
                self._expression_runtime_object_key(getattr(outcome, "value", None)),
                self._identity_freeze(getattr(outcome, "provenance", None)),
            )
            for index, outcome in enumerate(return_outcomes)
        )
        divergence_keys = tuple(
            (
                "divergence",
                index,
                self._canonicalize_key_sequence(
                    tuple(self._return_condition_object_key(condition) for condition in (getattr(outcome, "guard", ()) or ()))
                ),
                self._identity_freeze(getattr(outcome, "proof", None)),
            )
            for index, outcome in enumerate(divergence_outcomes)
        )
        unknown_keys = tuple(
            self._unknown_outcome_member_identity_key(index, outcome)
            for index, outcome in enumerate(unknown_outcomes)
        )
        return (
            "outcome_partition_identity",
            ("normalization_schema_version", self._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION),
            self._canonicalize_key_sequence(return_keys),
            self._canonicalize_key_sequence(divergence_keys),
            self._canonicalize_key_sequence(unknown_keys),
        )

    def _unknown_outcome_identity_key(self, analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
        return (
            "unknown_outcomes",
            self._canonicalize_key_sequence(
                tuple(
                    self._unknown_outcome_member_identity_key(index, outcome)
                    for index, outcome in enumerate(getattr(analysis, "unknown_outcomes", ()) or ())
                )
            ),
        )

    def _unknown_outcome_member_identity_key(self, index: int, outcome: Any) -> Tuple[Any, ...]:
        return (
            "unknown_outcome",
            int(index),
            ("reason", str(getattr(outcome, "reason", "") or "")),
            (
                "guard",
                self._canonicalize_key_sequence(
                    tuple(self._return_condition_object_key(condition) for condition in (getattr(outcome, "guard", ()) or ()))
                ),
            ),
            ("evidence", self._identity_freeze(getattr(outcome, "evidence", None))),
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

    def _conditions_runtime_object_key(self, conditions: Any) -> Tuple[Any, ...]:
        return (
            "conditions",
            tuple(
                self._return_condition_object_key(condition)
                for condition in (conditions or ())
            ),
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

    @classmethod
    def _blocking_reason_index(cls, reason_text: Optional[str]) -> Optional[int]:
        parts = str(reason_text or "").split(":")
        if len(parts) < 2:
            return None
        try:
            return int(parts[1])
        except (TypeError, ValueError):
            return None

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

    def _call_target_resolution_evidence_object_key(
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
        argument_keys = tuple(
            (
                "argument",
                index,
                self._expression_runtime_object_key(argument),
            )
            for index, argument in enumerate(getattr(site, "arguments", ()) or ())
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
            ),
            (
                "callsite_storage",
                ("pcode_op_ref", pcode_key),
                ("callee_identity", callee_identity_key),
                ("target_expression", target_expr_key),
                ("argument_keys", argument_keys),
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
    def _deterministic_function_identity(
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

    @classmethod
    def _analysis_entry_offset(cls, analysis: FunctionReturnAnalysis) -> Optional[int]:
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

    @classmethod
    def _normalized_function_signature_key(
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

    @staticmethod
    def _return_storage_static_key(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
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

    @classmethod
    def _identity_freeze(cls, value: Any) -> Any:
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

    def _outcome_partition_covered_labels(
        self,
        base_ctx: Mapping[str, Any],
        analysis1: Optional[FunctionReturnAnalysis],
        analysis2: Optional[FunctionReturnAnalysis],
        param_replace_fn1,
        param_replace_fn2,
    ) -> Set[str]:
        if analysis1 is None or analysis2 is None:
            return set()
        if not self._analysis_has_proved_outcome_partition(
            base_ctx,
            analysis1,
            param_replace_fn1,
            "function1",
        ):
            self._debug_print("Outcome partition coverage declined: function1 partition is not proved total")
            return set()
        if not self._analysis_has_proved_outcome_partition(
            base_ctx,
            analysis2,
            param_replace_fn2,
            "function2",
        ):
            self._debug_print("Outcome partition coverage declined: function2 partition is not proved total")
            return set()
        if not self._outcome_partitions_are_equivalent(
            base_ctx,
            analysis1,
            analysis2,
            param_replace_fn1,
            param_replace_fn2,
        ):
            self._debug_print("Outcome partition coverage declined: partitions are not equivalent")
            return set()
        return {"function1", "function2"}

    def _outcome_partition_inconclusive_labels(
        self,
        base_ctx: Mapping[str, Any],
        analysis1: Optional[FunctionReturnAnalysis],
        analysis2: Optional[FunctionReturnAnalysis],
        param_replace_fn1,
        param_replace_fn2,
    ) -> Set[str]:
        labels: Set[str] = set()
        for label, analysis, replace_fn in (
            ("function1", analysis1, param_replace_fn1),
            ("function2", analysis2, param_replace_fn2),
        ):
            if analysis is None:
                continue
            if not getattr(analysis, "unknown_outcomes", ()) or ():
                continue
            if self._analysis_has_total_outcome_partition(
                base_ctx,
                analysis,
                replace_fn,
                label,
            ):
                labels.add(label)
        return labels

    def _analysis_has_total_outcome_partition(
        self,
        base_ctx: Mapping[str, Any],
        analysis: FunctionReturnAnalysis,
        replace_fn,
        label: str,
    ) -> bool:
        return_outcomes = tuple(getattr(analysis, "return_outcomes", ()) or ())
        divergence_outcomes = tuple(getattr(analysis, "divergence_outcomes", ()) or ())
        unknown_outcomes = tuple(getattr(analysis, "unknown_outcomes", ()) or ())
        outcome_guards = [
            tuple(getattr(outcome, "guard", ()) or ())
            for outcome in (*return_outcomes, *divergence_outcomes, *unknown_outcomes)
        ]
        if not outcome_guards:
            return False
        return self._outcome_guard_union_is_total(
            base_ctx,
            outcome_guards,
            replace_fn,
            label,
        )

    def _analysis_has_proved_outcome_partition(
        self,
        base_ctx: Mapping[str, Any],
        analysis: FunctionReturnAnalysis,
        replace_fn,
        label: str,
    ) -> bool:
        if getattr(analysis, "unknown_outcomes", ()) or ():
            return False
        return_outcomes = tuple(getattr(analysis, "return_outcomes", ()) or ())
        divergence_outcomes = tuple(getattr(analysis, "divergence_outcomes", ()) or ())
        if not divergence_outcomes:
            return False
        return self._outcome_guard_union_is_total(
            base_ctx,
            [tuple(getattr(outcome, "guard", ()) or ()) for outcome in (*return_outcomes, *divergence_outcomes)],
            replace_fn,
            label,
        )

    def _outcome_partitions_are_equivalent(
        self,
        base_ctx: Mapping[str, Any],
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        param_replace_fn1,
        param_replace_fn2,
    ) -> bool:
        divergence1 = tuple(getattr(analysis1, "divergence_outcomes", ()) or ())
        divergence2 = tuple(getattr(analysis2, "divergence_outcomes", ()) or ())
        returns1 = tuple(getattr(analysis1, "return_outcomes", ()) or ())
        returns2 = tuple(getattr(analysis2, "return_outcomes", ()) or ())
        if not divergence1 or not divergence2:
            self._debug_print("Outcome partition equivalence declined: missing divergence outcomes")
            return False
        if not self._outcome_guard_unions_equivalent(
            base_ctx,
            [tuple(getattr(outcome, "guard", ()) or ()) for outcome in divergence1],
            [tuple(getattr(outcome, "guard", ()) or ()) for outcome in divergence2],
            param_replace_fn1,
            param_replace_fn2,
        ):
            self._debug_print("Outcome partition equivalence declined: divergence guard unions differ")
            return False
        if not self._outcome_cross_kind_disjoint(
            base_ctx,
            returns1,
            divergence2,
            param_replace_fn1,
            param_replace_fn2,
        ):
            self._debug_print("Outcome partition equivalence declined: function1 returns overlap function2 divergence")
            return False
        if not self._outcome_cross_kind_disjoint(
            base_ctx,
            returns2,
            divergence1,
            param_replace_fn2,
            param_replace_fn1,
        ):
            self._debug_print("Outcome partition equivalence declined: function2 returns overlap function1 divergence")
            return False
        if not self._return_outcome_values_are_equivalent(
            base_ctx,
            returns1,
            returns2,
            param_replace_fn1,
            param_replace_fn2,
        ):
            self._debug_print("Outcome partition equivalence declined: return outcome values differ")
            return False
        return True

    def _return_outcome_values_are_equivalent(
        self,
        base_ctx: Mapping[str, Any],
        returns1: Sequence[Any],
        returns2: Sequence[Any],
        param_replace_fn1,
        param_replace_fn2,
    ) -> bool:
        for left in returns1 or ():
            left_guard = tuple(getattr(left, "guard", ()) or ())
            left_value = getattr(left, "value", None)
            if left_value is None:
                return False
            for right in returns2 or ():
                right_guard = tuple(getattr(right, "guard", ()) or ())
                right_value = getattr(right, "value", None)
                if right_value is None:
                    return False
                if self._outcome_condition_groups_are_unsat(
                    base_ctx,
                    ((left_guard, param_replace_fn1), (right_guard, param_replace_fn2)),
                    title="Outcome return guard overlap",
                ):
                    continue
                if not self._outcome_return_values_equal_under_guards(
                    base_ctx,
                    left_guard,
                    right_guard,
                    left_value,
                    right_value,
                    param_replace_fn1,
                    param_replace_fn2,
                ):
                    return False
        return True

    def _outcome_cross_kind_disjoint(
        self,
        base_ctx: Mapping[str, Any],
        return_outcomes: Sequence[Any],
        divergence_outcomes: Sequence[Any],
        return_replace_fn,
        divergence_replace_fn,
    ) -> bool:
        for ret in return_outcomes or ():
            ret_guard = tuple(getattr(ret, "guard", ()) or ())
            for divergence in divergence_outcomes or ():
                div_guard = tuple(getattr(divergence, "guard", ()) or ())
                if not self._outcome_condition_groups_are_unsat(
                    base_ctx,
                    ((ret_guard, return_replace_fn), (div_guard, divergence_replace_fn)),
                    title="Outcome return/divergence disjointness",
                ):
                    return False
        return True

    def _outcome_guard_unions_equivalent(
        self,
        base_ctx: Mapping[str, Any],
        left_guards: Sequence[Sequence[Condition]],
        right_guards: Sequence[Sequence[Condition]],
        left_replace_fn,
        right_replace_fn,
    ) -> bool:
        left_union = self._outcome_guard_union_smt(left_guards, left_replace_fn)
        right_union = self._outcome_guard_union_smt(right_guards, right_replace_fn)
        if left_union is None or right_union is None:
            return False

        left_implies_right = self._outcome_smt_assertions_are_unsat(
            base_ctx,
            [left_union, f"(not {right_union})"],
            title="Outcome divergence guard implication left-to-right",
        )
        right_implies_left = self._outcome_smt_assertions_are_unsat(
            base_ctx,
            [right_union, f"(not {left_union})"],
            title="Outcome divergence guard implication right-to-left",
        )
        return left_implies_right and right_implies_left

    def _outcome_guard_union_is_total(
        self,
        base_ctx: Mapping[str, Any],
        guard_sets: Sequence[Sequence[Condition]],
        replace_fn,
        label: str,
    ) -> bool:
        union = self._outcome_guard_union_smt(guard_sets, replace_fn)
        if union is None:
            return False
        return self._outcome_smt_assertions_are_unsat(
            base_ctx,
            [f"(not {union})"],
            title=f"Outcome partition total coverage: {label}",
        )

    def _outcome_condition_groups_are_unsat(
        self,
        base_ctx: Mapping[str, Any],
        condition_groups: Sequence[Tuple[Sequence[Condition], Any]],
        *,
        title: str,
    ) -> bool:
        assertions: List[str] = []
        for conditions, replace_fn in condition_groups:
            rendered = self._outcome_conditions_smt(conditions, replace_fn)
            if rendered is None:
                return False
            assertions.extend(rendered)
        return self._outcome_smt_assertions_are_unsat(base_ctx, assertions, title=title)

    def _outcome_return_values_equal_under_guards(
        self,
        base_ctx: Mapping[str, Any],
        left_guard: Sequence[Condition],
        right_guard: Sequence[Condition],
        left_value: Expression,
        right_value: Expression,
        left_replace_fn,
        right_replace_fn,
    ) -> bool:
        left_conditions = self._outcome_conditions_smt(left_guard, left_replace_fn)
        right_conditions = self._outcome_conditions_smt(right_guard, right_replace_fn)
        if left_conditions is None or right_conditions is None:
            return False
        left_smt = self._outcome_expression_smt(left_value, left_replace_fn)
        right_smt = self._outcome_expression_smt(right_value, right_replace_fn)
        if left_smt is None or right_smt is None:
            return False
        left_bits = int(expression_smt_bit_width(left_value) or 0)
        right_bits = int(expression_smt_bit_width(right_value) or 0)
        if left_bits <= 0 or right_bits <= 0:
            return False
        target_bits = max(left_bits, right_bits)
        left_smt = coerce_value_to_bitvec_width(left_value, left_smt, target_bits)
        right_smt = coerce_value_to_bitvec_width(right_value, right_smt, target_bits)
        return self._outcome_smt_assertions_are_unsat(
            base_ctx,
            [*left_conditions, *right_conditions, f"(not (= {left_smt} {right_smt}))"],
            title="Outcome return value equality",
        )

    def _outcome_guard_union_smt(
        self,
        guard_sets: Sequence[Sequence[Condition]],
        replace_fn,
    ) -> Optional[str]:
        disjuncts: List[str] = []
        for guards in guard_sets or ():
            rendered = self._outcome_conditions_smt(guards, replace_fn)
            if rendered is None:
                return None
            if not rendered:
                return "true"
            if len(rendered) == 1:
                disjuncts.append(rendered[0])
            else:
                disjuncts.append(f"(and {' '.join(rendered)})")
        if not disjuncts:
            return None
        if len(disjuncts) == 1:
            return disjuncts[0]
        return f"(or {' '.join(disjuncts)})"

    def _outcome_conditions_smt(
        self,
        conditions: Sequence[Condition],
        replace_fn,
    ) -> Optional[List[str]]:
        rendered: List[str] = []
        for condition in conditions or ():
            smt = self._outcome_condition_smt(condition, replace_fn)
            if smt is None:
                return None
            rendered.append(smt)
        return rendered

    def _outcome_condition_smt(self, condition: Condition, replace_fn) -> Optional[str]:
        try:
            if replace_fn is None:
                return condition.to_smt(float_mode="fp")
            return replace_fn(condition)
        except TypeError:
            try:
                return replace_fn(condition.to_smt(float_mode="fp"))
            except Exception:
                return None
        except Exception:
            return None

    def _outcome_expression_smt(self, expression: Expression, replace_fn) -> Optional[str]:
        try:
            if replace_fn is None:
                return expression.to_smt(float_mode="fp")
            return replace_fn(expression)
        except TypeError:
            try:
                return replace_fn(expression.to_smt(float_mode="fp"))
            except Exception:
                return None
        except Exception:
            return None

    def _outcome_smt_assertions_are_unsat(
        self,
        base_ctx: Mapping[str, Any],
        assertions: Sequence[str],
        *,
        title: str,
    ) -> bool:
        header_lines = list(base_ctx.get("header_lines", []) or []) if isinstance(base_ctx, Mapping) else []
        if not header_lines:
            return False
        if not assertions:
            return False
        normalized_assertions = self._normalize_zero_constant_widths_for_declared_symbols(
            assertions,
            header_lines,
        )
        query = "\n".join(
            [
                f"; {title}",
                *header_lines,
                *(f"(assert {assertion})" for assertion in normalized_assertions),
                "(check-sat)",
                "(get-model)",
            ]
        )
        result = self.solver_runner.run_sequential(query)
        return result.is_equivalent is True

    @classmethod
    def _normalize_zero_constant_widths_for_declared_symbols(
        cls,
        assertions: Sequence[str],
        header_lines: Sequence[str],
    ) -> List[str]:
        widths: Dict[str, int] = {}
        for line in header_lines or ():
            match = re.search(
                r"\(declare-(?:fun|const)\s+([^\s()]+)\s+(?:\(\)\s+)?\(_\s+BitVec\s+(\d+)\)\)",
                str(line),
            )
            if match is None:
                continue
            try:
                widths[match.group(1)] = int(match.group(2))
            except ValueError:
                continue
        if not widths:
            return list(assertions or ())

        normalized = []
        for assertion in assertions or ():
            text = str(assertion)
            for symbol, width in widths.items():
                escaped = re.escape(symbol)
                text = re.sub(
                    rf"(\((?:bvslt|bvult|bvsle|bvule|=|distinct)\s+)\(_ bv0 \d+\)(\s+{escaped}(?=[\s)]))",
                    rf"\1(_ bv0 {width})\2",
                    text,
                )
                text = re.sub(
                    rf"(\((?:bvslt|bvult|bvsle|bvule|=|distinct)\s+{escaped}\s+)\(_ bv0 \d+\)(?=\))",
                    rf"\1(_ bv0 {width})",
                    text,
                )
            normalized.append(text)
        return normalized

    def _guard_union_miss_condition(
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

    def _check_return_case_coverage_gap(
        self,
        base_ctx: Dict[str, Any],
        cases: Sequence[Any],
        param_replace_fn,
        label: str,
    ) -> ReturnCoverageCheckResult:
        if not cases:
            return ReturnCoverageCheckResult(
                status="gap",
                detail=f"{label} has no return cases after extraction",
            )
        if any(not getattr(case, "conditions", None) for case in cases):
            return ReturnCoverageCheckResult(
                status="covered",
                coverage_proof_method="unconditional_return_case",
            )
        object_centric_status = self._return_cases_have_object_centric_total_coverage(
            cases
        )
        if object_centric_status is True:
            return ReturnCoverageCheckResult(
                status="covered",
                coverage_proof_method="object_centric_total_coverage",
            )
        if object_centric_status is False and not self._base_context_has_return_coverage_domain_assumptions(base_ctx):
            return ReturnCoverageCheckResult(
                status="gap",
                detail=f"{label} object-centric return-case coverage check found uncovered region",
            )
        if object_centric_status is None:
            case_conditions = [
                cond
                for case in (cases or ())
                for cond in (getattr(case, "conditions", None) or ())
            ]
            if not ConditionSMTOracle.has_object_identity_support(case_conditions):
                return ReturnCoverageCheckResult(
                    status="inconclusive",
                    reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
                    detail=f"{label} return-case object-centric coverage check was inconclusive",
                    inconclusive_cause="object_identity_unsupported",
                )
        if not base_ctx.get("header_lines"):
            return ReturnCoverageCheckResult(
                status="inconclusive",
                reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
                detail=f"{label} return-case coverage query skipped: base context has no declarations",
                inconclusive_cause="missing_header_context",
            )
        if any(self._case_conditions_contain_unresolved_expression(case) for case in cases):
            return ReturnCoverageCheckResult(
                status="inconclusive",
                reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
                detail=f"{label} return-case coverage query skipped: unresolved condition expression",
                inconclusive_cause="unresolved_expression",
            )

        query = self._build_return_case_coverage_query(
            base_ctx,
            cases,
            param_replace_fn,
            label,
        )
        if query is None:
            return ReturnCoverageCheckResult(
                status="inconclusive",
                reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
                detail=f"{label} return-case coverage query could not be built",
                inconclusive_cause="unsupported_expression",
            )

        result = self.solver_runner.run_sequential(query)
        if result.is_equivalent is False:
            model = result.get_counterexample()
            detail = f"{label} has uncovered return-condition region"
            if model:
                detail += f" under model {model}"
            if getattr(self, "debug", False):
                detail += self._return_coverage_case_debug_suffix(cases)
            return ReturnCoverageCheckResult(status="gap", detail=detail)
        if result.is_equivalent is None:
            return ReturnCoverageCheckResult(
                status="inconclusive",
                reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
                detail=f"{label} return-case coverage query was inconclusive",
                can_record_completion_proof=True,
                inconclusive_cause="smt_disambiguation_inconclusive",
            )
        return ReturnCoverageCheckResult(
            status="covered",
            coverage_proof_method="smt_coverage_query",
            solver_status="unsat",
        )

    def _return_coverage_case_debug_suffix(self, cases: Sequence[Any]) -> str:
        lines: List[str] = []
        for case in cases or ():
            case_index = getattr(case, "index", "?")
            rendered_conditions = []
            for condition in getattr(case, "conditions", []) or []:
                to_string = getattr(condition, "to_string", None)
                if callable(to_string):
                    try:
                        rendered_conditions.append(to_string())
                        continue
                    except Exception:
                        pass
                rendered_conditions.append(repr(condition))
            lines.append(f"case[{case_index}] conditions={rendered_conditions}")
        if not lines:
            return ""
        return "\n  coverage cases:\n  " + "\n  ".join(lines)

    @staticmethod
    def _base_context_has_return_coverage_domain_assumptions(
        base_ctx: Mapping[str, Any],
    ) -> bool:
        assumptions = base_ctx.get("return_coverage_domain_assumptions")
        if not isinstance(assumptions, Mapping):
            return False
        return bool(assumptions.get("fp_non_nan"))

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

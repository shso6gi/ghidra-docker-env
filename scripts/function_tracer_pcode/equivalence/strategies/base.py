# -*- coding: utf-8 -*-
"""Compatibility facade for CheckStrategy."""

from .proof_gates._shared import *

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
        "path_guard_match",
        "callee_identity_category_match",
        "callee_identity_reachable",
        "unsupported_fact_evidence_complete",
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

    def __getattr__(self, name: str):
        from .proof_gates import resolve_method
        implementation = resolve_method(name)
        if implementation is None:
            raise AttributeError(f"{self.__class__.__name__!s} has no attribute {name!r}")
        from types import MethodType
        return MethodType(implementation, self)
    
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
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_debug_print", self, msg)





    @classmethod
    def _summary_return_candidate_blocker_reason_ids(
        cls,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> Tuple[str, ...]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_summary_return_candidate_blocker_reason_ids", cls, analysis)

    @staticmethod
    def _summary_return_blocker_reason_id(blocker: str) -> str:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_summary_return_blocker_reason_id", blocker)


    @staticmethod
    def _return_case_smt_disjunctions(
        cases: Sequence[Any],
        replace_fn,
    ) -> Optional[Tuple[str, ...]]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_return_case_smt_disjunctions", cases, replace_fn)





    @staticmethod
    def _normalize_query(query: Optional[str]) -> Optional[str]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_normalize_query", query)

    @staticmethod
    def _canonicalize_key_sequence(values: Sequence[Any]) -> Tuple[Any, ...]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_canonicalize_key_sequence", values)

    @classmethod
    def _return_coverage_normalization_policy(cls, *, rules: Sequence[Any] = ()) -> Dict[str, Any]:
        from .proof_gates.return_coverage import invoke as _invoke
        return _invoke("_return_coverage_normalization_policy", cls, rules=rules)

    @classmethod
    def _canonical_jsonable_for_digest(cls, value: Any) -> Optional[Any]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_canonical_jsonable_for_digest", cls, value)

    @classmethod
    def _canonical_json_digest(cls, value: Any) -> Optional[str]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_canonical_json_digest", cls, value)

    @classmethod
    def _return_coverage_normalization_policy_digest(cls, policy: Mapping[str, Any]) -> Optional[str]:
        from .proof_gates.return_coverage import invoke as _invoke
        return _invoke("_return_coverage_normalization_policy_digest", cls, policy)

    @classmethod
    def _collect_condition_width_sign_metadata(
        cls,
        condition: Any,
        bit_widths: Set[int],
        signedness: Set[str],
    ) -> None:
        from .proof_gates.return_metadata import invoke as _invoke
        return _invoke("_collect_condition_width_sign_metadata", cls, condition, bit_widths, signedness)

    @classmethod
    def _iter_expression_nodes_for_metadata(cls, expr: Any):
        from .proof_gates.solver_timeout import invoke as _invoke
        yield from _invoke("_iter_expression_nodes_for_metadata", cls, expr)


    @classmethod
    def _iter_call_effect_blocker_candidates(
        cls,
        object_target_key: Tuple[Any, ...],
    ) -> Tuple[Tuple[Any, ...], ...]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_iter_call_effect_blocker_candidates", cls, object_target_key)


    @classmethod
    def _select_call_effect_blocker_candidate(
        cls,
        object_target_key: Tuple[Any, ...],
    ) -> Optional[Tuple[Any, ...]]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_select_call_effect_blocker_candidate", cls, object_target_key)


    @classmethod
    def _call_effect_blocker_candidate_score(cls, candidate: Any) -> Tuple[Any, ...]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_effect_blocker_candidate_score", cls, candidate)

    @classmethod
    def _call_effect_blocker_semantic_tie_break(cls, candidate: Tuple[Any, ...]) -> Tuple[Any, ...]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_effect_blocker_semantic_tie_break", cls, candidate)

    @classmethod
    def _call_effect_blocker_sort_token(cls, value: Any) -> Tuple[Any, ...]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_effect_blocker_sort_token", cls, value)

    @classmethod
    def _call_effect_blocker_candidate_priority(cls, candidate_kind: Any) -> int:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_effect_blocker_candidate_priority", cls, candidate_kind)

    @staticmethod
    def _analysis_for_call_effect_object_target(
        object_target_key: Tuple[Any, ...],
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
    ) -> Optional[FunctionReturnAnalysis]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_analysis_for_call_effect_object_target", object_target_key, analysis1, analysis2)




    @classmethod
    def _expression_bit_width_from_object_key(cls, object_key: Any) -> Optional[int]:
        from .proof_gates.return_metadata import invoke as _invoke
        return _invoke("_expression_bit_width_from_object_key", cls, object_key)







    @classmethod
    def _unsupported_call_effect_has_no_observed_writes(cls, effect_summary: Any) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_has_no_observed_writes", cls, effect_summary)



    @classmethod
    def _unsupported_call_effect_pcode_ref_key(cls, object_target_key: Any) -> Optional[Tuple[Any, ...]]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_pcode_ref_key", cls, object_target_key)

    @classmethod
    def _unsupported_call_effect_path_condition_key(cls, object_target_key: Any) -> Optional[Tuple[Any, ...]]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_path_condition_key", cls, object_target_key)

    @classmethod
    def _expression_contains_runtime_ref(cls, expr: Any, needle: Tuple[Any, ...]) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_expression_contains_runtime_ref", cls, expr, needle)

    @classmethod
    def _unsupported_call_effect_requires_exact_target_expression_match(
        cls,
        object_target_key: Any,
        peer_object_target_key: Any,
    ) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_requires_exact_target_expression_match", cls, object_target_key, peer_object_target_key)

    @classmethod
    def _unsupported_call_effect_callee_identity_key(cls, object_target_key: Any) -> Any:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_callee_identity_key", cls, object_target_key)

    @classmethod
    def _unsupported_call_effect_callee_identity_category(cls, object_target_key: Any) -> Optional[str]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_callee_identity_category", cls, object_target_key)

    @classmethod
    def _unsupported_call_effect_callee_identity_is_reachable(cls, object_target_key: Any) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_callee_identity_is_reachable", cls, object_target_key)

    @classmethod
    def _unsupported_call_effect_compatibility_policy_evidence(
        cls,
        object_target_key: Any,
        peer_object_target_key: Any,
    ) -> Dict[str, Any]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_compatibility_policy_evidence", cls, object_target_key, peer_object_target_key)

    @classmethod
    def _unsupported_call_effect_compatibility_policy_is_complete(
        cls,
        policy: Any,
    ) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_compatibility_policy_is_complete", cls, policy)

    @classmethod
    def _unsupported_call_effect_callee_identity_is_unknown(cls, object_target_key: Any) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_callee_identity_is_unknown", cls, object_target_key)


    @classmethod
    def _unsupported_call_effect_target_expression_key(cls, object_target_key: Any) -> Any:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_target_expression_key", cls, object_target_key)

    @classmethod
    def _call_effect_target_expression_key_is_present(cls, value: Any) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_effect_target_expression_key_is_present", cls, value)

    @classmethod
    def _unsupported_call_effect_argument_keys(cls, object_target_key: Any) -> Tuple[Any, ...]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_argument_keys", cls, object_target_key)

    @classmethod
    def _unsupported_call_effect_argument_evidence_is_complete(cls, value: Any) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_argument_evidence_is_complete", cls, value)

    @classmethod
    def _call_effect_argument_keys_are_present(cls, value: Any) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_effect_argument_keys_are_present", cls, value)

    @classmethod
    def _deferred_call_target_expression_key(cls, object_target_key: Any) -> Any:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_deferred_call_target_expression_key", cls, object_target_key)

    @classmethod
    def _deferred_call_argument_keys(cls, object_target_key: Any) -> Tuple[Any, ...]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_deferred_call_argument_keys", cls, object_target_key)

    @classmethod
    def _cross_binary_call_effect_component_key(cls, value: Any) -> Any:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_cross_binary_call_effect_component_key", cls, value)

    @classmethod
    def _call_target_is_analysis_entry(
        cls,
        target_key: Any,
        analysis: FunctionReturnAnalysis,
    ) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_target_is_analysis_entry", cls, target_key, analysis)



    @classmethod
    def _unsupported_call_effect_reason_compatibility_group(cls, reason: Any) -> Tuple[str, ...]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_reason_compatibility_group", cls, reason)

    @classmethod
    def _unsupported_call_effect_reason_signature(cls, reason: Any) -> str:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_reason_signature", cls, reason)

    @classmethod
    def _unsupported_call_effect_reason_is_compatible(
        cls,
        left_reason: Any,
        right_reason: Any,
    ) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_unsupported_call_effect_reason_is_compatible", cls, left_reason, right_reason)

    def _unknown_reason_id_for_blocking_unsafety(self, reason: Optional[str]):
        from .proof_gates.sat_safety import invoke as _invoke
        return _invoke("_unknown_reason_id_for_blocking_unsafety", self, reason)









    @classmethod
    def _completed_recovery_proof_evidence(
        cls,
        *analyses: FunctionReturnAnalysis,
    ) -> Tuple[Mapping[str, Any], ...]:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_completed_recovery_proof_evidence", cls, *analyses)



    @classmethod
    def _counterexample_model_fingerprint(
        cls,
        counterexample_raw: Optional[Mapping[str, Any]],
    ) -> Optional[str]:
        from .proof_gates.sat_safety import invoke as _invoke
        return _invoke("_counterexample_model_fingerprint", cls, counterexample_raw)

    @classmethod
    def _normalize_counterexample_model_value(cls, value: Any) -> Any:
        from .proof_gates.sat_safety import invoke as _invoke
        return _invoke("_normalize_counterexample_model_value", cls, value)

    @classmethod
    def _completed_recovery_proof_ids(
        cls,
        *analyses: FunctionReturnAnalysis,
    ) -> Tuple[Tuple[Any, ...], ...]:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_completed_recovery_proof_ids", cls, *analyses)

    @classmethod
    def _produced_recovery_proof_ids(
        cls,
        analysis: FunctionReturnAnalysis,
    ) -> Tuple[Tuple[Any, ...], ...]:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_produced_recovery_proof_ids", cls, analysis)

    @classmethod
    def _completed_call_effect_summary_proof_ids(
        cls,
        *analyses: FunctionReturnAnalysis,
    ) -> Tuple[Tuple[Any, ...], ...]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_completed_call_effect_summary_proof_ids", cls, *analyses)

    @classmethod
    def _call_effect_summary_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_effect_summary_proof_id_from_evidence", cls, evidence)

    @classmethod
    def _call_effect_summary_proof_content_is_required(
        cls,
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_effect_summary_proof_content_is_required", cls, object_target_key)

    @classmethod
    def _call_effect_summary_proof_content_is_complete(
        cls,
        proof_content: Any,
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_effect_summary_proof_content_is_complete", cls, proof_content, object_target_key)

    @classmethod
    def _call_argument_evidence_phase15_proof_content_is_complete(
        cls,
        proof_content: Mapping[str, Any],
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_argument_evidence_phase15_proof_content_is_complete", cls, proof_content, object_target_key)

    @classmethod
    def _call_argument_phase15_sections_are_consistent(
        cls,
        callee_summary: Any,
        bounded_refinement: Any,
    ) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_argument_phase15_sections_are_consistent", cls, callee_summary, bounded_refinement)

    @classmethod
    def _call_argument_callee_summary_section_is_complete(
        cls,
        section: Any,
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_argument_callee_summary_section_is_complete", cls, section, object_target_key)

    @classmethod
    def _call_argument_precondition_section_is_complete(
        cls,
        section: Any,
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_argument_precondition_section_is_complete", cls, section, object_target_key)

    @classmethod
    def _call_argument_value_provenance_section_is_complete(
        cls,
        section: Any,
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_argument_value_provenance_section_is_complete", cls, section, object_target_key)

    @classmethod
    def _call_argument_dependency_graph_section_is_complete(
        cls,
        section: Any,
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_argument_dependency_graph_section_is_complete", cls, section, object_target_key)

    @classmethod
    def _call_argument_bounded_refinement_section_is_complete(
        cls,
        section: Any,
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_argument_bounded_refinement_section_is_complete", cls, section, object_target_key)

    @classmethod
    def _validated_call_effect_blocker_selected_candidate(
        cls,
        proof_content: Mapping[str, Any],
        object_target_key: Tuple[Any, ...],
    ) -> Optional[Tuple[Any, ...]]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_validated_call_effect_blocker_selected_candidate", cls, proof_content, object_target_key)

    @classmethod
    def _call_effect_summary_section_matches(
        cls,
        section: Any,
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_call_effect_summary_section_matches", cls, section, object_target_key)

    @classmethod
    def _expected_call_effect_proof_content_refs(
        cls,
        object_target_key: Tuple[Any, ...],
        candidate: Optional[Tuple[Any, ...]] = None,
        default_missing: Optional[Tuple[Any, ...]] = None,
    ) -> Optional[Tuple[Tuple[Any, ...], Tuple[Any, ...]]]:
        # Keep None as the sentinel for "missing references": callers must guard
        # before unpacking to avoid ValueError on empty tuples.
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_expected_call_effect_proof_content_refs", cls, object_target_key, candidate, default_missing)

    @classmethod
    def _expected_deferred_call_proof_content_refs(
        cls,
        object_target_key: Tuple[Any, ...],
    ) -> Optional[Tuple[Tuple[Any, ...], Tuple[Any, ...]]]:
        from .proof_gates.call_effect_1 import invoke as _invoke
        return _invoke("_expected_deferred_call_proof_content_refs", cls, object_target_key)

    @classmethod
    def _unsupported_call_effect_proof_content_is_complete(
        cls,
        proof_content: Mapping[str, Any],
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.call_effect_2 import invoke as _invoke
        return _invoke("_unsupported_call_effect_proof_content_is_complete", cls, proof_content, object_target_key)

    @classmethod
    def _matched_unknown_indirect_call_effect_surface_is_complete(
        cls,
        surface: Any,
        object_target_key: Tuple[Any, ...],
        peer_object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.call_effect_2 import invoke as _invoke
        return _invoke("_matched_unknown_indirect_call_effect_surface_is_complete", cls, surface, object_target_key, peer_object_target_key)

    @classmethod
    def _call_output_use_surface_is_complete(
        cls,
        section: Any,
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.call_effect_2 import invoke as _invoke
        return _invoke("_call_output_use_surface_is_complete", cls, section, object_target_key)

    @classmethod
    def _deferred_call_proof_content_is_complete(
        cls,
        proof_content: Mapping[str, Any],
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.call_effect_2 import invoke as _invoke
        return _invoke("_deferred_call_proof_content_is_complete", cls, proof_content, object_target_key)

    @classmethod
    def _proof_section_payload_matches(
        cls,
        section: Any,
        payload_key: str,
        expected_payload: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_proof_section_payload_matches", cls, section, payload_key, expected_payload)

    @classmethod
    def _sat_unsafety_resolution_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
        from .proof_gates.sat_safety import invoke as _invoke
        return _invoke("_sat_unsafety_resolution_proof_id_from_evidence", cls, evidence)

    @classmethod
    def _readonly_identity_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_readonly_identity_proof_id_from_evidence", cls, evidence)

    @classmethod
    def _method_b_closure_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_method_b_closure_proof_id_from_evidence", cls, evidence)

    @classmethod
    def _evidence_required_evidence_matches(cls, evidence: Any, expected_required: Sequence[str]) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_evidence_required_evidence_matches", cls, evidence, expected_required)

    @classmethod
    def _readonly_identity_target_is_specific(cls, object_target_key: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_readonly_identity_target_is_specific", cls, object_target_key)

    @classmethod
    def _method_b_closure_target_is_specific(cls, object_target_key: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_method_b_closure_target_is_specific", cls, object_target_key)

    @classmethod
    def _proof_target_pair_is_specific(cls, value: Any) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_proof_target_pair_is_specific", cls, value)

    @classmethod
    def _readonly_identity_side_is_specific(cls, value: Any, expected_side: str) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_readonly_identity_side_is_specific", cls, value, expected_side)

    @classmethod
    def _method_b_closure_side_is_specific(cls, value: Any, expected_side: str) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_method_b_closure_side_is_specific", cls, value, expected_side)

    @classmethod
    def _readonly_identity_relation_is_specific(cls, value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_readonly_identity_relation_is_specific", cls, value)

    @classmethod
    def _readonly_storage_relation_is_specific(cls, value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_readonly_storage_relation_is_specific", cls, value)

    @classmethod
    def _tag_payload_is_specific(cls, value: Any, tag: str) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_tag_payload_is_specific", cls, value, tag)

    @classmethod
    def _object_leaf_is_specific(cls, value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_object_leaf_is_specific", cls, value)

    @classmethod
    def _readonly_bit_span_is_specific(cls, value: Any, tag: str) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_readonly_bit_span_is_specific", cls, value, tag)

    @classmethod
    def _readonly_component_key_is_specific(cls, value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_readonly_component_key_is_specific", cls, value)

    @classmethod
    def _method_b_closure_relation_is_specific(cls, value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_method_b_closure_relation_is_specific", cls, value)

    @classmethod
    def _method_b_summary_profile_is_specific(cls, value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_method_b_summary_profile_is_specific", cls, value)

    @classmethod
    def _method_b_runtime_ref_key_is_specific(cls, value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_method_b_runtime_ref_key_is_specific", cls, value)

    @classmethod
    def _method_b_loop_summary_key_is_specific(cls, value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_method_b_loop_summary_key_is_specific", cls, value)

    @classmethod
    def _readonly_term_contract_is_specific(cls, value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_readonly_term_contract_is_specific", cls, value)

    @classmethod
    def _readonly_projection_key_is_specific(cls, value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_readonly_projection_key_is_specific", cls, value)

    @classmethod
    def _readonly_side_effect_profile_is_specific(cls, value: Any) -> bool:
        from .proof_gates.call_effect_2 import invoke as _invoke
        return _invoke("_readonly_side_effect_profile_is_specific", cls, value)

    @classmethod
    def _method_b_count_identities_are_specific(cls, value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_method_b_count_identities_are_specific", cls, value)

    @classmethod
    def _method_b_closure_relation_fields(cls, value: Any) -> Optional[Dict[str, Tuple[Any, ...]]]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_method_b_closure_relation_fields", cls, value)

    @classmethod
    def _method_b_one_sided_relation_payload(
        cls,
        object_target_key: Tuple[Any, ...],
    ) -> Optional[Dict[str, Any]]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_method_b_one_sided_relation_payload", cls, object_target_key)

    @classmethod
    def _method_b_exact_terms_are_specific(cls, value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_method_b_exact_terms_are_specific", cls, value)

    @classmethod
    def _method_b_readonly_term_is_specific(cls, value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_method_b_readonly_term_is_specific", cls, value)

    @classmethod
    def _proof_target_contains_weak_value(cls, value: Any) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_proof_target_contains_weak_value", cls, value)

    @classmethod
    def _proof_target_contains_diagnostic_value(cls, value: Any) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_proof_target_contains_diagnostic_value", cls, value)

    @classmethod
    def _proof_target_contains_missing_or_diagnostic(cls, value: Any) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_proof_target_contains_missing_or_diagnostic", cls, value)

    @classmethod
    def _proof_text_is_specific(cls, value: Any) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_proof_text_is_specific", cls, value)

    @classmethod
    def _proof_int_like(cls, value: Any) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_proof_int_like", cls, value)

    @classmethod
    def _proof_nonnegative_int_like(cls, value: Any) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_proof_nonnegative_int_like", cls, value)

    @classmethod
    def _proof_positive_int_like(cls, value: Any) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_proof_positive_int_like", cls, value)

    @classmethod
    def _readonly_identity_proof_content_is_complete(
        cls,
        proof_content: Any,
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_readonly_identity_proof_content_is_complete", cls, proof_content, object_target_key)

    @classmethod
    def _readonly_identity_storage_relation_from_target(cls, object_target_key: Any) -> Optional[Tuple[Any, ...]]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_readonly_identity_storage_relation_from_target", cls, object_target_key)

    @classmethod
    def _readonly_projection_extension_proof_content_is_complete(
        cls,
        extension: Any,
        storage_relation: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_readonly_projection_extension_proof_content_is_complete", cls, extension, storage_relation)

    @classmethod
    def _method_b_closure_proof_content_is_complete(
        cls,
        proof_content: Any,
        object_target_key: Tuple[Any, ...],
        *,
        proof_stage: str,
    ) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_method_b_closure_proof_content_is_complete", cls, proof_content, object_target_key, proof_stage=proof_stage)

    @classmethod
    def _method_b_proof_sides_match_relation(
        cls,
        proof_content: Mapping[str, Any],
        relation_payload: Mapping[str, Any],
    ) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_method_b_proof_sides_match_relation", cls, proof_content, relation_payload)

    @classmethod
    def _method_b_covering_proof_content_matches_relation(
        cls,
        proof_content: Mapping[str, Any],
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_method_b_covering_proof_content_matches_relation", cls, proof_content, object_target_key)

    @classmethod
    def _method_b_guard_proof_content_matches_relation(
        cls,
        proof_content: Mapping[str, Any],
        object_target_key: Tuple[Any, ...],
    ) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_method_b_guard_proof_content_matches_relation", cls, proof_content, object_target_key)

    @classmethod
    def _method_b_guard_count_values(cls, proof_content: Mapping[str, Any]) -> Tuple[int, ...]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_method_b_guard_count_values", cls, proof_content)

    @classmethod
    def _method_b_dual_summary_relation_payload(
        cls,
        object_target_key: Tuple[Any, ...],
    ) -> Optional[Dict[str, Any]]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_method_b_dual_summary_relation_payload", cls, object_target_key)

    @classmethod
    def _method_b_dual_summary_proof_content_matches_relation(
        cls,
        proof_content: Mapping[str, Any],
        object_target_key: Tuple[Any, ...],
        *,
        proof_stage: str,
    ) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_method_b_dual_summary_proof_content_matches_relation", cls, proof_content, object_target_key, proof_stage=proof_stage)

    @classmethod
    def _proof_status_value_is_complete(cls, value: Any) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_proof_status_value_is_complete", cls, value)

    @staticmethod
    def _positive_int_like(value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_positive_int_like", value)


    @classmethod
    def _completed_proof_section_is_clean(cls, section: Any) -> bool:
        from .proof_gates.recovery import invoke as _invoke
        return _invoke("_completed_proof_section_is_clean", cls, section)

    @classmethod
    def _query_cases_are_nonempty(cls, value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_query_cases_are_nonempty", cls, value)


    @classmethod
    def _return_coverage_proof_content_can_discharge_inconclusive(
        cls,
        proof_content: Any,
    ) -> bool:
        from .proof_gates.return_coverage import invoke as _invoke
        return _invoke("_return_coverage_proof_content_can_discharge_inconclusive", cls, proof_content)

    @classmethod
    def _return_coverage_guard_evidence_is_complete(
        cls,
        proof_content: Mapping[str, Any],
        normalized_query: str,
    ) -> bool:
        from .proof_gates.return_coverage import invoke as _invoke
        return _invoke("_return_coverage_guard_evidence_is_complete", cls, proof_content, normalized_query)

    @classmethod
    def _return_coverage_proof_content_is_complete(
        cls,
        evidence: Mapping[str, Any],
        reason_id: Optional[UnknownReasonId] = None,
    ) -> bool:
        from .proof_gates.return_coverage import invoke as _invoke
        return _invoke("_return_coverage_proof_content_is_complete", cls, evidence, reason_id)

    @classmethod
    def _return_coverage_normalization_required(
        cls,
        evidence: Mapping[str, Any],
        proof_content: Mapping[str, Any],
        object_target_key: Any,
    ) -> bool:
        from .proof_gates.return_coverage import invoke as _invoke
        return _invoke("_return_coverage_normalization_required", cls, evidence, proof_content, object_target_key)

    @classmethod
    def _nested_contains_tag(cls, value: Any, tag: str) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_nested_contains_tag", cls, value, tag)

    @classmethod
    def _return_coverage_normalization_proof_content_is_complete(
        cls,
        proof_content: Mapping[str, Any],
        object_target_key: Any,
        *,
        required: bool,
    ) -> bool:
        from .proof_gates.return_coverage import invoke as _invoke
        return _invoke("_return_coverage_normalization_proof_content_is_complete", cls, proof_content, object_target_key, required=required)

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
        from .proof_gates.return_coverage import invoke as _invoke
        return _invoke("_return_coverage_normalized_payload_is_complete", cls, kind, payload, policy_digest=policy_digest, expected_query_hash=expected_query_hash, correspondence=correspondence, default_raw_identity=default_raw_identity, default_normalized_identity=default_normalized_identity)

    @classmethod
    def _normalization_policy_digest_from_target(cls, object_target_key: Any) -> Optional[str]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_normalization_policy_digest_from_target", cls, object_target_key)

    @classmethod
    def _return_coverage_structural_proof_content_is_complete(
        cls,
        proof_content: Mapping[str, Any],
    ) -> bool:
        from .proof_gates.return_coverage import invoke as _invoke
        return _invoke("_return_coverage_structural_proof_content_is_complete", cls, proof_content)

    @classmethod
    def _return_coverage_structural_proof_content_matches_target(
        cls,
        proof_content: Mapping[str, Any],
        object_target_key: Any,
    ) -> bool:
        from .proof_gates.return_coverage import invoke as _invoke
        return _invoke("_return_coverage_structural_proof_content_matches_target", cls, proof_content, object_target_key)

    @staticmethod
    def _return_coverage_target_partition_cases(object_target_key: Any) -> Optional[Tuple[Any, ...]]:
        from .proof_gates.return_coverage import invoke as _invoke
        return _invoke("_return_coverage_target_partition_cases", object_target_key)

    @classmethod
    def _return_coverage_proof_id_from_evidence(cls, evidence: Any) -> Optional[Tuple[Any, ...]]:
        from .proof_gates.return_coverage import invoke as _invoke
        return _invoke("_return_coverage_proof_id_from_evidence", cls, evidence)

    @classmethod
    def _return_coverage_object_target_key_is_valid(cls, object_target_key: Tuple[Any, ...]) -> bool:
        from .proof_gates.return_coverage import invoke as _invoke
        return _invoke("_return_coverage_object_target_key_is_valid", cls, object_target_key)

    @classmethod
    def _return_coverage_identity_contains_forbidden_atoms(cls, value: Any) -> bool:
        from .proof_gates.return_coverage import invoke as _invoke
        return _invoke("_return_coverage_identity_contains_forbidden_atoms", cls, value)

    @classmethod
    def _analysis_has_active_call_effect_proof_blockers(
        cls,
        analysis: FunctionReturnAnalysis,
    ) -> bool:
        from .proof_gates.call_effect_2 import invoke as _invoke
        return _invoke("_analysis_has_active_call_effect_proof_blockers", cls, analysis)

    @staticmethod
    def _evidence_get(evidence: Any, key: str) -> Any:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_evidence_get", evidence, key)

    @classmethod
    def _evidence_text(cls, evidence: Any, key: str) -> str:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_evidence_text", cls, evidence, key)

    @classmethod
    def _evidence_bool(cls, evidence: Any, key: str) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_evidence_bool", cls, evidence, key)

    @classmethod
    def _evidence_has_any(cls, evidence: Any, keys: Sequence[str]) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_evidence_has_any", cls, evidence, keys)

    @classmethod
    def _evidence_has_any_recursive(cls, evidence: Any, keys: Sequence[str]) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_evidence_has_any_recursive", cls, evidence, keys)

    @classmethod
    def _normalize_nested_tuple(cls, value: Any):
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_normalize_nested_tuple", cls, value)















    @staticmethod
    def _coerce_return_width(*values: Any) -> Optional[int]:
        from .proof_gates.return_metadata import invoke as _invoke
        return _invoke("_coerce_return_width", *values)




    @staticmethod
    def _expression_smt_bit_width_for_object_key(expr: Any) -> Optional[int]:
        from .proof_gates.return_metadata import invoke as _invoke
        return _invoke("_expression_smt_bit_width_for_object_key", expr)

    @staticmethod
    def _return_pcode_value_input_width_bits(pcode_op_ref: Any) -> Optional[int]:
        from .proof_gates.return_metadata import invoke as _invoke
        return _invoke("_return_pcode_value_input_width_bits", pcode_op_ref)



    @staticmethod
    def _solver_names_from_parallel_result(parallel_result: Optional[ParallelResult]) -> Tuple[str, ...]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_solver_names_from_parallel_result", parallel_result)

    @staticmethod
    def _coerce_timeout_seconds(value: Any) -> Optional[int]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_coerce_timeout_seconds", value)


    @classmethod
    def _binary_pair_id_from_analyses(
        cls,
        analysis1: Optional[FunctionReturnAnalysis],
        analysis2: Optional[FunctionReturnAnalysis],
    ) -> Optional[str]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_binary_pair_id_from_analyses", cls, analysis1, analysis2)

    @staticmethod
    def _analysis_binary_id(analysis: Optional[FunctionReturnAnalysis]) -> Optional[str]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_analysis_binary_id", analysis)














    @staticmethod
    def _split_blocking_reason(blocking_reason: str) -> Tuple[str, str]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_split_blocking_reason", blocking_reason)

    @classmethod
    def _blocking_reason_kind(cls, blocking_reason: Optional[str]) -> str:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_blocking_reason_kind", cls, blocking_reason)

    @classmethod
    def _blocking_reason_index(cls, reason_text: Optional[str]) -> Optional[int]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_blocking_reason_index", cls, reason_text)

    @staticmethod
    def _deferred_call_is_blocking(info: Any) -> bool:
        from .proof_gates.call_effect_2 import invoke as _invoke
        return _invoke("_deferred_call_is_blocking", info)






    @staticmethod
    def _call_effect_callee_identity_key(
        target_key: Any,
        target_expr_key: Any,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> Any:
        from .proof_gates.call_effect_2 import invoke as _invoke
        return _invoke("_call_effect_callee_identity_key", target_key, target_expr_key, analysis)

    @classmethod
    def _artifact_stable_key_for_analysis(
        cls,
        value: Any,
        analysis: Optional[FunctionReturnAnalysis],
    ) -> Any:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_artifact_stable_key_for_analysis", cls, value, analysis)

    @classmethod
    def _rewrite_program_identity_keys(cls, value: Any, binary_id: str) -> Any:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_rewrite_program_identity_keys", cls, value, binary_id)

    @classmethod
    def _rewrite_atom_encoded_program_identity_key(
        cls,
        rewritten: Tuple[Any, ...],
        binary_id: str,
    ) -> Optional[Tuple[Any, ...]]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_rewrite_atom_encoded_program_identity_key", cls, rewritten, binary_id)

    @staticmethod
    def _program_id_like(value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_program_id_like", value)

    @classmethod
    def _atom_program_id_like(cls, value: Any) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_atom_program_id_like", cls, value)

    @staticmethod
    def _atom_str_is(value: Any, expected: Optional[str]) -> bool:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_atom_str_is", value, expected)

    @classmethod
    def _typed_target_expression_key(cls, expr: Any) -> Optional[Tuple[Any, ...]]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_typed_target_expression_key", cls, expr)

    @staticmethod
    def _analysis_entry_key(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_analysis_entry_key", analysis)

    @classmethod
    def _deterministic_function_identity(
        cls,
        analysis: FunctionReturnAnalysis,
    ) -> Tuple[Any, ...]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_deterministic_function_identity", cls, analysis)

    @classmethod
    def _analysis_entry_offset(cls, analysis: FunctionReturnAnalysis) -> Optional[int]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_analysis_entry_offset", cls, analysis)

    @classmethod
    def _normalized_function_signature_key(
        cls,
        analysis: FunctionReturnAnalysis,
    ) -> Tuple[Any, ...]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_normalized_function_signature_key", cls, analysis)

    @staticmethod
    def _return_storage_static_key(analysis: FunctionReturnAnalysis) -> Tuple[Any, ...]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_return_storage_static_key", analysis)

    @classmethod
    def _identity_freeze(cls, value: Any) -> Any:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_identity_freeze", cls, value)

    @classmethod
    def _call_target_key_for_analysis(
        cls,
        target_ref: Any,
        analysis: Optional[FunctionReturnAnalysis],
    ):
        from .proof_gates.call_effect_2 import invoke as _invoke
        return _invoke("_call_target_key_for_analysis", cls, target_ref, analysis)

    @staticmethod
    def _stable_key_or_none(value: Any):
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_stable_key_or_none", value)

    @classmethod
    def _expression_runtime_object_key(cls, expr: Any) -> Tuple[Any, ...]:
        from .proof_gates.solver_timeout import invoke as _invoke
        return _invoke("_expression_runtime_object_key", cls, expr)

















    @classmethod
    def _normalize_zero_constant_widths_for_declared_symbols(
        cls,
        assertions: Sequence[str],
        header_lines: Sequence[str],
    ) -> List[str]:
        from .proof_gates.return_metadata import invoke as _invoke
        return _invoke("_normalize_zero_constant_widths_for_declared_symbols", cls, assertions, header_lines)




    @staticmethod
    def _base_context_has_return_coverage_domain_assumptions(
        base_ctx: Mapping[str, Any],
    ) -> bool:
        from .proof_gates.return_coverage import invoke as _invoke
        return _invoke("_base_context_has_return_coverage_domain_assumptions", base_ctx)

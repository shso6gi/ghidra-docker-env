# -*- coding: utf-8 -*-
"""Compatibility facade for PairwiseStrategy."""

from .pairwise_services._shared import *

class PairwiseStrategy(CheckStrategy):
    """
    Pairwise戦略（分岐ペア分割方式・二段階チェック）

    各ペア(i,j)に対して：
    1. Stage 1: 条件のみチェック（C1_i ∧ C2_j）
    2. Stage 2: 値不等式を追加してチェック（C1_i ∧ C2_j ∧ V1_i≠V2_j）
    3. Stage 3: 正規化 fallback
    """

    def __init__(
        self,
        formula_builder,
        solver_runner,
        debug: bool = False,
        normalization_settings: Optional[NormalizationSettings] = None,
        enable_completed_recovery_proofs: bool = True,
    ):
        super().__init__(
            formula_builder,
            solver_runner,
            debug,
            enable_completed_recovery_proofs=enable_completed_recovery_proofs,
        )
        self.per_query_timeout = 5
        self.per_query_timeout_hard = 30
        self.save_unknown_queries = False
        self.unknown_query_dir = "/tmp"
        self.normalization_settings = normalization_settings or NormalizationSettings.safe()
        self.solver_proven_rewrite_settings = self.normalization_settings
        self.enable_solver_proven_rewrite_fallback = True
        self.enable_normalization_fallback = False
        self._active_safety_checker = None
        # Process-local obligation attempt cache.  The cache is intentionally
        # owned by the strategy instance so recursive/derived pairwise branches
        # can reuse identical logical queries without changing public dispatch
        # or persisting mutable FunctionReturnAnalysis objects.
        from ..obligations import AttemptCache
        self._exact_query_attempt_cache = AttemptCache(max_entries=4096)
        self._obligation_scheduler_run_id = 0
        # Sound process-local reuse of already proven UNSAT pair obligations.
        # Keys contain the complete pair semantic surface and ABI context;
        # UNKNOWN/SAT outcomes are never reused across views.
        self._obligation_pair_unsat_cache = {}

    def __getattr__(self, name: str):
        from .pairwise_services import resolve_method
        implementation = resolve_method(name)
        if implementation is None:
            raise AttributeError(f"{self.__class__.__name__!s} has no attribute {name!r}")
        from types import MethodType
        return MethodType(implementation, self)

    def check(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        save_formula: bool = False
    ) -> StrategyResult:
        from .pairwise_services.orchestration_1 import invoke as _invoke
        return _invoke("check", self, analysis1, analysis2, save_formula)

    @staticmethod
    def _merge_completed_recovery_proofs_from_solver_analyses(
        analysis1: FunctionReturnAnalysis,
        solver_analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        solver_analysis2: FunctionReturnAnalysis,
    ) -> None:
        from .pairwise_services.auxiliary_smt import invoke as _invoke
        return _invoke("_merge_completed_recovery_proofs_from_solver_analyses", analysis1, solver_analysis1, analysis2, solver_analysis2)

    @staticmethod
    def _blocking_unknown_reasons_should_replace_pair_unknowns(
        pair_unknown_reasons: Sequence[Any],
        coverage_unknown_reasons: Sequence[Any],
        equivalence_unknown_reasons: Sequence[Any],
    ) -> bool:
        from .pairwise_services.orchestration_1 import invoke as _invoke
        return _invoke("_blocking_unknown_reasons_should_replace_pair_unknowns", pair_unknown_reasons, coverage_unknown_reasons, equivalence_unknown_reasons)

    @classmethod
    def _append_blocking_unknown_reasons(
        cls,
        pair_unknown_reasons: Sequence[Any],
        blocking_unknown_reasons: Sequence[Any],
    ) -> List[Any]:
        from .pairwise_services.orchestration_1 import invoke as _invoke
        return _invoke("_append_blocking_unknown_reasons", cls, pair_unknown_reasons, blocking_unknown_reasons)

    @staticmethod
    def _unknown_reason_dedup_key(reason: Any) -> Tuple[Any, ...]:
        from .pairwise_services.orchestration_1 import invoke as _invoke
        return _invoke("_unknown_reason_dedup_key", reason)











    @staticmethod
    def _fp_denominator_count_identity_matches(
        expr_storage: Optional[tuple],
        expr_index: Optional[tuple],
        proof_storage: Optional[tuple],
        proof_index: Optional[tuple],
    ) -> bool:
        from .pairwise_services.orchestration_1 import invoke as _invoke
        return _invoke("_fp_denominator_count_identity_matches", expr_storage, expr_index, proof_storage, proof_index)










    @staticmethod
    def _method_b_recovery_action(
        actions: Sequence[Any],
        *,
        proof_kind: str,
        proof_stage: str,
    ):
        from .pairwise_services.orchestration_1 import invoke as _invoke
        return _invoke("_method_b_recovery_action", actions, proof_kind=proof_kind, proof_stage=proof_stage)

    @staticmethod
    def _method_b_covering_relation_matches_proof(
        relation: Any,
        *,
        exact_side: str,
        summary_side: str,
        proof: _ExactReadonlyReductionProof,
    ) -> bool:
        from .pairwise_services.orchestration_1 import invoke as _invoke
        return _invoke("_method_b_covering_relation_matches_proof", relation, exact_side=exact_side, summary_side=summary_side, proof=proof)











































    @staticmethod
    def _readonly_projection_span(relation: Tuple[Any, ...], tag: str) -> Optional[Tuple[int, int]]:
        from .pairwise_services.readonly_reduction_1 import invoke as _invoke
        return _invoke("_readonly_projection_span", relation, tag)


    @staticmethod
    def _readonly_declared_parameter_bits(
        analysis: FunctionReturnAnalysis,
        index: int,
    ) -> Optional[int]:
        from .pairwise_services.readonly_reduction_1 import invoke as _invoke
        return _invoke("_readonly_declared_parameter_bits", analysis, index)


    @staticmethod
    def _readonly_parameter_declared_signedness(param: Mapping[str, Any]) -> Optional[str]:
        from .pairwise_services.readonly_reduction_1 import invoke as _invoke
        return _invoke("_readonly_parameter_declared_signedness", param)
































    @classmethod
    def _unresolved_expression_target_uses_generic_pending_census(
        cls,
        object_target_key: Any,
    ) -> bool:
        from .pairwise_services.unresolved_lowering import invoke as _invoke
        return _invoke("_unresolved_expression_target_uses_generic_pending_census", cls, object_target_key)




    @classmethod
    def _opaque_unknown_refs_from_value(cls, value: Any) -> Tuple[Any, ...]:
        from .pairwise_services.orchestration_1 import invoke as _invoke
        return _invoke("_opaque_unknown_refs_from_value", cls, value)



    @classmethod
    def _deferred_call_runtime_refs_from_value(cls, value: Any) -> Tuple[Any, ...]:
        from .pairwise_services.unresolved_lowering import invoke as _invoke
        return _invoke("_deferred_call_runtime_refs_from_value", cls, value)

    @classmethod
    def _deferred_call_semantic_refs(cls, refs: Tuple[Any, ...]) -> Tuple[Any, ...]:
        from .pairwise_services.unresolved_lowering import invoke as _invoke
        return _invoke("_deferred_call_semantic_refs", cls, refs)

    @staticmethod
    def _deferred_call_ref_relation(
        left_refs: Tuple[Any, ...],
        right_refs: Tuple[Any, ...],
    ) -> Tuple[Any, ...]:
        from .pairwise_services.unresolved_lowering import invoke as _invoke
        return _invoke("_deferred_call_ref_relation", left_refs, right_refs)


    @classmethod
    def _semantic_recurrence_query_plan(
        cls,
        *,
        query_id: str,
        query_stage: str,
        assertion_kind: str,
        object_target_key: Tuple[Any, ...],
        object_content: Tuple[Tuple[str, Any], ...],
    ) -> Tuple[Any, ...]:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_semantic_recurrence_query_plan", cls, query_id=query_id, query_stage=query_stage, assertion_kind=assertion_kind, object_target_key=object_target_key, object_content=object_content)

    @staticmethod
    def _stable_semantic_recurrence_hash(value: Any) -> str:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_stable_semantic_recurrence_hash", value)

    @staticmethod
    def _semantic_recurrence_jsonable(value: Any) -> Any:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_semantic_recurrence_jsonable", value)

    @classmethod
    def _phi_circular_origin_shape_relation(
        cls,
        left_unknowns: Tuple[Any, ...],
        right_unknowns: Tuple[Any, ...],
    ) -> Tuple[Any, ...]:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_phi_circular_origin_shape_relation", cls, left_unknowns, right_unknowns)

    @classmethod
    def _phi_circular_unknown_origin_shape_key(cls, unknown: Any) -> Optional[Tuple[Any, ...]]:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_phi_circular_unknown_origin_shape_key", cls, unknown)

    @staticmethod
    def _pcode_origin_cross_binary_shape_key(origin_key: Any) -> Optional[Tuple[Any, ...]]:
        from .pairwise_services.orchestration_1 import invoke as _invoke
        return _invoke("_pcode_origin_cross_binary_shape_key", origin_key)

    @classmethod
    def _find_pair_lowering_diagnostic(cls, value: Any) -> Optional[Tuple[Any, ...]]:
        from .pairwise_services.unresolved_lowering import invoke as _invoke
        return _invoke("_find_pair_lowering_diagnostic", cls, value)

    @classmethod
    def _find_phi_origin_shape_relation(cls, value: Any) -> Optional[Tuple[Any, ...]]:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_find_phi_origin_shape_relation", cls, value)

    @staticmethod
    def _phi_circular_case_value_shape(
        case_shape: Optional[Tuple[Any, ...]],
    ) -> Optional[Any]:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_phi_circular_case_value_shape", case_shape)

    @staticmethod
    def _phi_circular_unknown_count_relation(
        left_count: int,
        right_count: int,
    ) -> Tuple[Any, ...]:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_phi_circular_unknown_count_relation", left_count, right_count)

    @classmethod
    def _phi_circular_value_shape_relation(
        cls,
        left_value: Optional[Any],
        right_value: Optional[Any],
    ) -> Tuple[Any, ...]:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_phi_circular_value_shape_relation", cls, left_value, right_value)

    @staticmethod
    def _phi_circular_shape_kind(value: Optional[Any]) -> str:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_phi_circular_shape_kind", value)

    @staticmethod
    def _phi_circular_summary_parameter_index(value: Optional[Any]) -> Optional[int]:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_phi_circular_summary_parameter_index", value)

    @staticmethod
    def _phi_circular_constant_value(value: Optional[Any]) -> Optional[int]:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_phi_circular_constant_value", value)




    @staticmethod
    def _phi_circular_opposing_condition_literals(
        left_literals: Tuple[Any, ...],
        right_literals: Tuple[Any, ...],
    ) -> Tuple[Any, ...]:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_phi_circular_opposing_condition_literals", left_literals, right_literals)






    @staticmethod
    def _unresolved_expression_location_taxonomy(location_scope: str) -> str:
        from .pairwise_services.unresolved_lowering import invoke as _invoke
        return _invoke("_unresolved_expression_location_taxonomy", location_scope)


    @staticmethod
    def _unresolved_expression_substage(location: str, cause: str) -> str:
        from .pairwise_services.unresolved_lowering import invoke as _invoke
        return _invoke("_unresolved_expression_substage", location, cause)

    @classmethod
    def _value_contains_originated_phi_circular(cls, value: Any) -> bool:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_value_contains_originated_phi_circular", cls, value)

    @classmethod
    def _value_contains_deferred_call_ref(cls, value: Any) -> bool:
        from .pairwise_services.unresolved_lowering import invoke as _invoke
        return _invoke("_value_contains_deferred_call_ref", cls, value)

    @classmethod
    def _value_contains_readonly_ref(cls, value: Any) -> bool:
        from .pairwise_services.readonly_reduction_1 import invoke as _invoke
        return _invoke("_value_contains_readonly_ref", cls, value)

    @staticmethod
    def _unsupported_ops_include_memory_or_effect(unsupported_ops: set[Any]) -> bool:
        from .pairwise_services.orchestration_1 import invoke as _invoke
        return _invoke("_unsupported_ops_include_memory_or_effect", unsupported_ops)

    @staticmethod
    def _expression_uses_float_or_float_op(expr: Any) -> bool:
        from .pairwise_services.auxiliary_smt import invoke as _invoke
        return _invoke("_expression_uses_float_or_float_op", expr)






    @classmethod
    def _unresolved_expression_target_cause(cls, object_target_key: Any) -> Optional[str]:
        from .pairwise_services.unresolved_lowering import invoke as _invoke
        return _invoke("_unresolved_expression_target_cause", cls, object_target_key)


    @classmethod
    def _object_target_contains_void_opaque_unknown(cls, value: Any) -> bool:
        from .pairwise_services.orchestration_1 import invoke as _invoke
        return _invoke("_object_target_contains_void_opaque_unknown", cls, value)

    @classmethod
    def _object_target_contains_deferred_call_unknown(cls, value: Any) -> bool:
        from .pairwise_services.unresolved_lowering import invoke as _invoke
        return _invoke("_object_target_contains_deferred_call_unknown", cls, value)

    @classmethod
    def _object_target_contains_originated_phi_circular(cls, value: Any) -> bool:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_object_target_contains_originated_phi_circular", cls, value)

    @staticmethod
    def _tuple_is_originated_phi_circular_runtime_ref(value: Tuple[Any, ...]) -> bool:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_tuple_is_originated_phi_circular_runtime_ref", value)




    @staticmethod
    def _semantic_key_or_stable_key_or_none(value: Any):
        from .pairwise_services.orchestration_1 import invoke as _invoke
        return _invoke("_semantic_key_or_stable_key_or_none", value)

    @staticmethod
    def _diagnostic_key_or_semantic_key_or_stable_key_or_none(value: Any):
        from .pairwise_services.orchestration_1 import invoke as _invoke
        return _invoke("_diagnostic_key_or_semantic_key_or_stable_key_or_none", value)


















    @staticmethod
    def _counted_residue_term_at_zero_is_zero(
        residue_cases: Tuple[Tuple[int, int, int, int], ...],
    ) -> bool:
        from .pairwise_services.loop_summary_1 import invoke as _invoke
        return _invoke("_counted_residue_term_at_zero_is_zero", residue_cases)

































































































































    def _try_normalization_equivalence(
        self,
        base_ctx: Dict[str, Any],
        case1: ReturnCase,
        case2: ReturnCase,
        param_replace_fn1,
        param_replace_fn2,
        pair_id: str
    ) -> QueryResult:
        from .pairwise_services.orchestration_2 import invoke as _invoke
        return _invoke("_try_normalization_equivalence", self, base_ctx, case1, case2, param_replace_fn1, param_replace_fn2, pair_id)


    def _solve_query_internal(
        self,
        query: str,
        pair_id: str,
        stage: str = "full",
        use_hard_timeout: bool = False
    ) -> QueryResult:
        from .pairwise_services.auxiliary_smt import invoke as _invoke
        return _invoke("_solve_query_internal", self, query, pair_id, stage, use_hard_timeout)













    @classmethod
    def _unknown_expression_is_originated_phi_circular(cls, expr: Any) -> bool:
        from .pairwise_services.loop_summary_2 import invoke as _invoke
        return _invoke("_unknown_expression_is_originated_phi_circular", cls, expr)

















    @staticmethod
    def _pair_id_and_side_from_value_query_label(
        query_label: str,
    ) -> Tuple[Optional[str], Optional[str]]:
        from .pairwise_services.auxiliary_smt import invoke as _invoke
        return _invoke("_pair_id_and_side_from_value_query_label", query_label)

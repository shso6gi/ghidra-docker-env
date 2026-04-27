# -*- coding: utf-8 -*-

from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    post_state_read_expression_for_location,
)
from scripts.function_tracer_pcode.model import (
    COUNTED_LOOP_SUM_OPCODE,
    CallTargetRef,
    Condition,
    DeferredCallInfo,
    CountedLoopSummaryRef,
    Expression,
    FunctionReturnAnalysis,
    LocationBaseRef,
    LoopBodyEffectRef,
    LoopCaseRef,
    LoopSideEffectProfileRef,
    LoopSummaryRef,
    LoopTermDescriptorRef,
    PostStateReadRef,
    PostStateSnapshotRef,
    ReductionAccumulatorProof,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReturnInfo,
    StorageInfo,
    coerce_call_target_ref,
    compare_loop_summaries,
    loop_summary_method_b_key,
)
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_builder import build_pair_query
from scripts.function_tracer_pcode.model.render_smt import _runtime_ref_smt_identity
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


def test_coerce_call_target_ref_rejects_raw_strings():
    assert coerce_call_target_ref("callee") is None


def test_loop_summary_comparator_accepts_pure_object_centric_semantic_key():
    summary = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
    )

    result = compare_loop_summaries(summary, summary)

    assert result.status == "equivalent"
    assert result.is_equivalent() is True


def test_loop_summary_comparator_rejects_different_side_effect_profiles():
    pure = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )
    effectful = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(
            profile="effect_aware",
            memory_writes=True,
            effect_count=1,
            effect_descriptors=(
                LoopBodyEffectRef(
                    kind="memory_write",
                    source="pcode_scan",
                    scope="loop",
                    order_key=1,
                ),
            ),
        ),
    )

    result = compare_loop_summaries(pure, effectful)

    assert result.status == "incompatible"
    assert result.is_equivalent() is None
    assert result.blocks_shortcut() is True


def _pure_counted_loop_summary() -> LoopSummaryRef:
    return LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
    )


def _effect_aware_counted_loop_summary() -> LoopSummaryRef:
    return LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(
            profile="effect_aware",
            memory_writes=True,
            effect_count=1,
            effect_descriptors=(
                LoopBodyEffectRef(
                    kind="memory_write",
                    source="pcode_scan",
                    scope="loop",
                    address_space="ram",
                    location="addr",
                    value_expr="value",
                    order_key=1,
                ),
            ),
        ),
    )


def _path_sensitive_counted_loop_summary() -> LoopSummaryRef:
    return LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        cases=(
            LoopCaseRef(
                path_conditions=("i_is_even",),
                body_effect=LoopBodyEffectRef(kind="accumulator_update", value_expr="acc+i"),
                term_expr="i",
                case_kind="accumulator_delta",
            ),
        ),
    )


def _readonly_loop_summary(
    *,
    start: int,
    seed_terms=(),
    step: int = 1,
) -> LoopSummaryRef:
    return LoopSummaryRef(
        start_expr=Expression.constant(start, size=4),
        limit_expr=Expression.parameter("count", index=1, data_type="int", size=4),
        step_expr=Expression.constant(step, size=4),
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=LocationBaseRef.parameter("base", index=0),
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=4,
        ),
        seed_terms=tuple(seed_terms or ()),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure_memory_read", memory_reads=True),
        loop_var_unit="element_index",
    )


def _readonly_sum_expr(loop_summary: LoopSummaryRef) -> Expression:
    return Expression.intrinsic(
        "READONLY_SUM",
        [
            Expression.parameter("base", index=0, data_type="int *", size=8),
            Expression.parameter("count", index=1, data_type="int", size=4),
        ],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=LocationBaseRef.parameter("base", index=0),
            count_parameter_name="count",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
            loop_summary=loop_summary,
        ),
    )


def test_reduction_accumulator_proof_lowers_to_readonly_reduction_ref_object_centrically():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        index_step=1,
        index_scale=4,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(
            ReadonlyReductionWitness(
                exact_count=4,
                terms=(ReadonlyReductionTermRef(byte_offset=12, access_size=4),),
            ),
        ),
        exact_return_witnesses=(
            ReadonlyReductionWitness(
                exact_count=3,
                terms=(
                    ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=8, access_size=4),
                ),
            ),
        ),
        guard_constraints=(),
        signed_counter=True,
    )

    ref = proof.to_readonly_reduction_ref()

    assert ref is not None
    assert ref.accumulator_proof == proof
    assert ref.loop_summary is not None
    assert proof.full_terms_for_count_value(1) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
    )
    assert proof.full_terms_for_count_value(2) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
    )
    assert proof.full_terms_for_count_value(4) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ReadonlyReductionTermRef(byte_offset=12, access_size=4),
    )
    assert loop_summary_method_b_key(ref.loop_summary) == loop_summary_method_b_key(_readonly_loop_summary(start=0))


def test_reduction_accumulator_proof_with_constant_bias_does_not_lower_to_readonly_sum():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        constant_bias=1,
    )

    assert proof.to_loop_summary_ref() is None
    assert proof.to_readonly_reduction_ref() is None


def test_reduction_accumulator_proof_preserves_independent_start_offset_in_loop_summary():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    base_ref = LocationBaseRef.parameter("base", index=0)
    shifted = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=base_ref,
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=4,
        start_index=0,
        index_step=1,
        index_scale=4,
    ).to_loop_summary_ref()
    unshifted = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=base_ref,
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
    ).to_loop_summary_ref()

    assert shifted is not None
    assert unshifted is not None
    assert shifted.term_descriptor.start_offset == 4
    assert loop_summary_method_b_key(shifted) != loop_summary_method_b_key(unshifted)


def test_reduction_accumulator_proof_materializes_scalar_lane_terms():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=16,
        element_size=8,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=16,
        lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
        loop_body_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
            ),
            ReadonlyReductionWitness(
                exact_count=2,
                terms=(
                    ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ),
            ),
            ReadonlyReductionWitness(
                exact_count=3,
                terms=(
                    ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=8, access_size=4),
                ),
            ),
        ),
    )

    assert proof.loop_var_unit() == "scalar_element_index"
    assert proof.loop_body_terms_for_count_value(2) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
    )
    assert proof.loop_body_terms_for_count_value(5) == (
        ReadonlyReductionTermRef(byte_offset=0, access_size=4),
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ReadonlyReductionTermRef(byte_offset=12, access_size=4),
        ReadonlyReductionTermRef(byte_offset=16, access_size=4),
    )


def test_reduction_accumulator_proof_materializes_shifted_scalar_lane_terms():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=8,
        element_size=8,
        start_offset=4,
        start_index=0,
        index_step=1,
        index_scale=8,
        lane_terms=((4, 4), (8, 4)),
        loop_body_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=4, access_size=4),),
            ),
        ),
    )

    assert proof.lane_terms == ((0, 4), (4, 4))
    assert proof.loop_var_unit() == "scalar_element_index"
    assert proof.loop_body_terms_for_count_value(3) == (
        ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ReadonlyReductionTermRef(byte_offset=12, access_size=4),
    )


def test_reduction_accumulator_proof_infers_shifted_lane_terms_from_witnesses():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    prefix_only = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=8,
        element_size=8,
        start_offset=4,
        start_index=0,
        index_step=1,
        index_scale=8,
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=4, access_size=4),),
            ),
        ),
        exact_return_witnesses=(),
        guard_constraints=(),
        signed_counter=True,
    )
    full_prefix = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=8,
        element_size=8,
        start_offset=4,
        start_index=0,
        index_step=1,
        index_scale=8,
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(
            ReadonlyReductionWitness(
                exact_count=1,
                terms=(ReadonlyReductionTermRef(byte_offset=4, access_size=4),),
            ),
            ReadonlyReductionWitness(
                exact_count=2,
                terms=(
                    ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=8, access_size=4),
                ),
            ),
        ),
        exact_return_witnesses=(),
        guard_constraints=(),
        signed_counter=True,
    )

    assert prefix_only.lane_terms == ()
    assert prefix_only.loop_var_unit() == "element_index"
    assert full_prefix.lane_terms == ((0, 4), (4, 4))
    assert full_prefix.loop_var_unit() == "scalar_element_index"


def test_reduction_accumulator_proof_does_not_materialize_lanes_without_scalar_proof():
    count_expr = Expression.parameter("count", index=1, data_type="int", size=4)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=16,
        element_size=8,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=16,
        lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
    )

    assert proof.loop_var_unit() == "element_index"
    assert proof.loop_body_terms_for_count_value(2) is None


def _counted_loop_expr(loop_summary: LoopSummaryRef) -> Expression:
    return Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [Expression.constant(0), Expression.constant(0), Expression.parameter("n", size=4)],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 1, 0),),
            loop_summary=loop_summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )


def _return_case_for_expr(expr: Expression) -> ReturnCase:
    return ReturnCase(0, [], expr, ReturnInfo(address="0x1000", value=expr, conditions=[]))


def _analysis_with_return(function_name: str, value: Expression, conditions=()) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name=function_name,
        entry_point="0x1000",
        parameters=[
            {"name": "base", "index": 0, "data_type": "int *", "size": 8, "is_signed": False},
            {"name": "count", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        returns=[
            ReturnInfo(
                address="0x1000",
                value=value,
                conditions=list(conditions or ()),
            )
        ],
        return_type="int",
    )


def _pairwise_strategy_for_full_path() -> PairwiseStrategy:
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    strategy.formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    return strategy


def test_loop_summary_method_b_key_normalizes_seed_compensated_suffix():
    full = _readonly_loop_summary(start=0)
    suffix = _readonly_loop_summary(
        start=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )

    assert loop_summary_method_b_key(full) == loop_summary_method_b_key(suffix)
    result = compare_loop_summaries(full, suffix)
    assert result.status == "equivalent"
    assert result.is_equivalent() is True


def test_loop_summary_method_b_key_compensates_vector_lane_scalar_prefix_seed():
    full = _readonly_loop_summary(start=0)
    suffix = LoopSummaryRef(
        start_expr=Expression.constant(2, size=4),
        limit_expr=full.limit_expr,
        step_expr=full.step_expr,
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=LocationBaseRef.parameter("base", index=0),
            start_offset=0,
            stride=16,
            element_size=8,
            result_size=4,
            lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
        ),
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ),
        side_effect_profile=full.side_effect_profile,
        loop_var_unit="scalar_element_index",
    )

    assert loop_summary_method_b_key(full) == loop_summary_method_b_key(suffix)
    assert compare_loop_summaries(full, suffix).status == "equivalent"


def test_loop_summary_method_b_key_requires_seed_to_cover_omitted_prefix():
    full = _readonly_loop_summary(start=0)
    suffix_with_gap = _readonly_loop_summary(
        start=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
        ),
    )

    assert loop_summary_method_b_key(full) != loop_summary_method_b_key(suffix_with_gap)
    result = compare_loop_summaries(full, suffix_with_gap)
    assert result.status == "unknown"
    assert result.is_equivalent() is None


def test_loop_summary_method_b_key_ignores_witness_evidence_identity():
    left = _readonly_loop_summary(start=0)
    right = _readonly_loop_summary(start=0)
    right = LoopSummaryRef(
        start_expr=right.start_expr,
        limit_expr=right.limit_expr,
        step_expr=right.step_expr,
        term_descriptor=right.term_descriptor,
        seed_terms=right.seed_terms,
        witnesses=(object(),),
        side_effect_profile=right.side_effect_profile,
        guard_constraints=right.guard_constraints,
        cases=right.cases,
        loop_var_unit=right.loop_var_unit,
        source=right.source,
    )

    assert right.stable_key() is None
    assert loop_summary_method_b_key(left) == loop_summary_method_b_key(right)
    assert compare_loop_summaries(left, right).status == "equivalent"


def test_loop_summary_method_b_key_treats_guards_as_applicability_conditions():
    full = _readonly_loop_summary(start=0)
    suffix = _readonly_loop_summary(
        start=3,
        seed_terms=(
            ReadonlyReductionTermRef(byte_offset=0, access_size=4),
            ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ReadonlyReductionTermRef(byte_offset=8, access_size=4),
        ),
    )
    full = LoopSummaryRef(
        start_expr=full.start_expr,
        limit_expr=full.limit_expr,
        step_expr=full.step_expr,
        term_descriptor=full.term_descriptor,
        seed_terms=full.seed_terms,
        side_effect_profile=full.side_effect_profile,
        guard_constraints=("0 < count",),
        loop_var_unit=full.loop_var_unit,
    )
    suffix = LoopSummaryRef(
        start_expr=suffix.start_expr,
        limit_expr=suffix.limit_expr,
        step_expr=suffix.step_expr,
        term_descriptor=suffix.term_descriptor,
        seed_terms=suffix.seed_terms,
        side_effect_profile=suffix.side_effect_profile,
        guard_constraints=("3 < count",),
        loop_var_unit=suffix.loop_var_unit,
    )

    assert full.stable_key() != suffix.stable_key()
    assert loop_summary_method_b_key(full) == loop_summary_method_b_key(suffix)
    assert compare_loop_summaries(full, suffix).status == "equivalent"


def test_pairwise_readonly_runtime_values_use_method_b_seed_compensation():
    full = _readonly_sum_expr(_readonly_loop_summary(start=0))
    suffix = _readonly_sum_expr(
        _readonly_loop_summary(
            start=3,
            seed_terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
            ),
        )
    )
    strategy = PairwiseStrategy(None, None)

    assert strategy._intrinsic_runtime_values_equivalent(
        full,
        suffix,
        left_case=_return_case_for_expr(full),
        right_case=_return_case_for_expr(suffix),
    ) is True


def test_pairwise_full_path_prefers_method_b_loop_meaning_signature():
    full = _readonly_sum_expr(_readonly_loop_summary(start=0))
    suffix = _readonly_sum_expr(
        _readonly_loop_summary(
            start=3,
            seed_terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
            ),
        )
    )
    strategy = _pairwise_strategy_for_full_path()

    result = strategy.check(
        _analysis_with_return("full", full),
        _analysis_with_return("suffix", suffix),
    )

    assert result.is_equivalent is True
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_pairwise_full_path_falls_back_unknown_for_unproven_loop_summary():
    full = _readonly_sum_expr(_readonly_loop_summary(start=0))
    suffix_with_gap = _readonly_sum_expr(
        _readonly_loop_summary(
            start=3,
            seed_terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ),
        )
    )
    strategy = _pairwise_strategy_for_full_path()

    result = strategy.check(
        _analysis_with_return("full", full),
        _analysis_with_return("suffix_gap", suffix_with_gap),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 0
    assert result.unknown_pairs == 1
    strategy.solver_runner.run_sequential.assert_not_called()


def test_pairwise_full_path_recursively_falls_back_unknown_for_nested_unproven_loop_summary():
    full = Expression.binary_op(
        "INT_ADD",
        _readonly_sum_expr(_readonly_loop_summary(start=0)),
        Expression.parameter("bias", index=2, data_type="int", size=4),
    )
    suffix_with_gap = Expression.binary_op(
        "INT_ADD",
        _readonly_sum_expr(
            _readonly_loop_summary(
                start=3,
                seed_terms=(
                    ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                    ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ),
            )
        ),
        Expression.parameter("bias", index=2, data_type="int", size=4),
    )
    strategy = _pairwise_strategy_for_full_path()

    result = strategy.check(
        _analysis_with_return("full", full),
        _analysis_with_return("suffix_gap", suffix_with_gap),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 0
    assert result.unknown_pairs == 1
    strategy.solver_runner.run_sequential.assert_not_called()


def test_pairwise_full_path_does_not_bypass_loop_guard_mismatch():
    count = Expression.parameter("count", index=1, data_type="int", size=4)
    full = _readonly_sum_expr(_readonly_loop_summary(start=0))
    suffix = _readonly_sum_expr(
        _readonly_loop_summary(
            start=3,
            seed_terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
            ),
        )
    )
    full_guard = Condition(Expression.binary_op("INT_SLESS", Expression.constant(0, size=4), count))
    suffix_guard = Condition(Expression.binary_op("INT_SLESS", Expression.constant(3, size=4), count))
    strategy = _pairwise_strategy_for_full_path()

    result = strategy.check(
        _analysis_with_return("full", full, conditions=[full_guard]),
        _analysis_with_return("suffix", suffix, conditions=[suffix_guard]),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 0
    assert result.unknown_pairs == 1
    strategy.solver_runner.run_sequential.assert_not_called()


def test_method_b_smt_identity_uses_seed_compensated_loop_summary():
    full = _readonly_sum_expr(_readonly_loop_summary(start=0))
    suffix = _readonly_sum_expr(
        _readonly_loop_summary(
            start=3,
            seed_terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
            ),
        )
    )
    suffix_with_gap = _readonly_sum_expr(
        _readonly_loop_summary(
            start=3,
            seed_terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ),
        )
    )

    assert _runtime_ref_smt_identity(full, full.runtime_ref) == _runtime_ref_smt_identity(
        suffix,
        suffix.runtime_ref,
    )
    assert _runtime_ref_smt_identity(full, full.runtime_ref) != _runtime_ref_smt_identity(
        suffix_with_gap,
        suffix_with_gap.runtime_ref,
    )


def test_loop_side_effect_stable_key_ignores_function_context_descriptors():
    base_profile = LoopSideEffectProfileRef(
        profile="pure",
        context_memory_writes=True,
        context_descriptors=(
            LoopBodyEffectRef(
                kind="memory_write",
                source="function_effect_summary",
                scope="function",
                location="outside_a",
                value_expr=1,
            ),
        ),
    )
    other_context_profile = LoopSideEffectProfileRef(
        profile="pure",
        context_memory_writes=True,
        context_descriptors=(
            LoopBodyEffectRef(
                kind="memory_write",
                source="function_effect_summary",
                scope="function",
                location="outside_b",
                value_expr=2,
            ),
        ),
    )

    assert base_profile.stable_key() == other_context_profile.stable_key()


def test_effect_aware_loop_summary_disables_exact_and_smt_shortcuts():
    summary = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(
            profile="effect_aware",
            memory_writes=True,
            effect_count=1,
            effect_descriptors=(
                LoopBodyEffectRef(
                    kind="memory_write",
                    source="pcode_scan",
                    scope="loop",
                    address_space="ram",
                    location="addr",
                    value_expr="value",
                    order_key=1,
                ),
            ),
        ),
    )
    ref = CountedLoopSummaryRef(
        induction_step=1,
        result_size=4,
        signed_loop=True,
        residue_cases=((1, 0, 1, 0),),
        loop_summary=summary,
    )
    expr = Expression.intrinsic("COUNTED_LOOP_SUM", [Expression.constant(0), Expression.constant(0), Expression.parameter("n")], runtime_ref=ref)

    assert summary.stable_key() is not None
    assert summary.pairwise_exact_key() is None
    assert ref.pairwise_exact_key() is None
    smt_identity = _runtime_ref_smt_identity(expr, ref)
    assert smt_identity[0] == "opaque_loop_summary_identity"
    assert smt_identity[3] == "effect_proof_required"


def test_path_sensitive_loop_summary_disables_exact_and_smt_identity_shortcuts():
    loop_case = LoopCaseRef(
        path_conditions=("i_is_even",),
        body_effect=LoopBodyEffectRef(kind="accumulator_update", value_expr="acc+i"),
        term_expr="i",
        case_kind="accumulator_delta",
    )
    summary = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        cases=(loop_case,),
    )
    ref = CountedLoopSummaryRef(
        induction_step=1,
        result_size=4,
        signed_loop=True,
        residue_cases=((1, 0, 1, 0),),
        loop_summary=summary,
    )
    expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [Expression.constant(0), Expression.constant(0), Expression.parameter("n")],
        runtime_ref=ref,
    )

    assert summary.stable_key() is not None
    assert summary.requires_path_proof() is True
    assert summary.pairwise_exact_key() is None
    assert ref.pairwise_exact_key() is None
    smt_identity = _runtime_ref_smt_identity(expr, ref)
    assert smt_identity[0] == "opaque_loop_summary_identity"
    assert smt_identity[3] == "path_proof_required"


def test_loop_summary_comparator_blocks_different_path_cases():
    base = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        cases=(
            LoopCaseRef(
                path_conditions=("i_is_even",),
                term_expr="i",
                case_kind="accumulator_delta",
            ),
        ),
    )
    changed = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        cases=(
            LoopCaseRef(
                path_conditions=("i_is_odd",),
                term_expr="i",
                case_kind="accumulator_delta",
            ),
        ),
    )

    result = compare_loop_summaries(base, changed)

    assert result.status == "incompatible"
    assert result.blocks_shortcut() is True


def test_pairwise_query_records_loop_summary_cases_as_smt_comments():
    loop_case = LoopCaseRef(
        path_conditions=("i_is_even",),
        body_effect=LoopBodyEffectRef(kind="accumulator_update", value_expr="acc+i"),
        term_expr="i",
        case_kind="accumulator_delta",
    )
    summary = LoopSummaryRef(
        start_expr=0,
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        cases=(loop_case,),
    )
    expr = _counted_loop_expr(summary)
    return_case = _return_case_for_expr(expr)
    render = lambda value: value.to_smt() if hasattr(value, "to_smt") else str(value)

    query = build_pair_query(
        {"header_lines": [], "return_size1": 32, "return_size2": 32},
        return_case,
        return_case,
        render,
        render,
        "loop-case-comments",
    )

    assert "; Case1 loop summary cases: 1" in query
    assert "loop_case[0] kind=accumulator_delta path=[i_is_even] term=i" in query


def test_counted_loop_proof_does_not_bypass_effect_aware_summaries():
    left = _counted_loop_expr(_effect_aware_counted_loop_summary())
    right = _counted_loop_expr(_effect_aware_counted_loop_summary())
    strategy = PairwiseStrategy(None, None)

    assert strategy._counted_loop_values_are_provably_equivalent(
        left,
        right,
        left_case=_return_case_for_expr(left),
        right_case=_return_case_for_expr(right),
    ) is False


def test_counted_loop_proof_does_not_bypass_incompatible_loop_summaries():
    left = _counted_loop_expr(_pure_counted_loop_summary())
    right = _counted_loop_expr(_effect_aware_counted_loop_summary())
    strategy = PairwiseStrategy(None, None)

    assert strategy._counted_loop_values_are_provably_equivalent(
        left,
        right,
        left_case=_return_case_for_expr(left),
        right_case=_return_case_for_expr(right),
    ) is False


def test_intrinsic_runtime_values_equivalent_does_not_bypass_effect_loop_summaries():
    strategy = PairwiseStrategy(None, None)
    effect_left = _counted_loop_expr(_effect_aware_counted_loop_summary())
    effect_right = _counted_loop_expr(_effect_aware_counted_loop_summary())
    incompatible_left = _counted_loop_expr(_pure_counted_loop_summary())
    incompatible_right = _counted_loop_expr(_effect_aware_counted_loop_summary())

    assert strategy._intrinsic_runtime_values_equivalent(
        effect_left,
        effect_right,
        left_case=_return_case_for_expr(effect_left),
        right_case=_return_case_for_expr(effect_right),
    ) is False
    assert strategy._intrinsic_runtime_values_equivalent(
        incompatible_left,
        incompatible_right,
        left_case=_return_case_for_expr(incompatible_left),
        right_case=_return_case_for_expr(incompatible_right),
    ) is False


def test_counted_loop_proof_does_not_bypass_path_sensitive_summaries():
    left = _counted_loop_expr(_path_sensitive_counted_loop_summary())
    right = _counted_loop_expr(_path_sensitive_counted_loop_summary())
    strategy = PairwiseStrategy(None, None)

    assert strategy._counted_loop_values_are_provably_equivalent(
        left,
        right,
        left_case=_return_case_for_expr(left),
        right_case=_return_case_for_expr(right),
    ) is False


def test_intrinsic_runtime_values_equivalent_does_not_bypass_path_sensitive_summaries():
    strategy = PairwiseStrategy(None, None)
    path_left = _counted_loop_expr(_path_sensitive_counted_loop_summary())
    path_right = _counted_loop_expr(_path_sensitive_counted_loop_summary())
    mixed_left = _counted_loop_expr(_pure_counted_loop_summary())
    mixed_right = _counted_loop_expr(_path_sensitive_counted_loop_summary())

    assert strategy._intrinsic_runtime_values_equivalent(
        path_left,
        path_right,
        left_case=_return_case_for_expr(path_left),
        right_case=_return_case_for_expr(path_right),
    ) is False
    assert strategy._intrinsic_runtime_values_equivalent(
        mixed_left,
        mixed_right,
        left_case=_return_case_for_expr(mixed_left),
        right_case=_return_case_for_expr(mixed_right),
    ) is False


def test_counted_loop_method_b_match_does_not_bypass_guard_mismatch():
    strategy = PairwiseStrategy(None, None)
    left = _counted_loop_expr(_pure_counted_loop_summary())
    right = _counted_loop_expr(_pure_counted_loop_summary())
    n = Expression.parameter("n", size=4)
    left_case = ReturnCase(
        0,
        [Condition(Expression.binary_op("INT_SLESS", Expression.constant(0, size=4), n))],
        left,
        ReturnInfo(address="0x1000", value=left, conditions=[]),
    )
    right_case = ReturnCase(
        0,
        [Condition(Expression.binary_op("INT_SLESS", Expression.constant(1, size=4), n))],
        right,
        ReturnInfo(address="0x1004", value=right, conditions=[]),
    )

    assert strategy._intrinsic_runtime_values_equivalent(
        left,
        right,
        left_case=left_case,
        right_case=right_case,
    ) is False
    assert strategy._counted_loop_values_are_provably_equivalent(
        left,
        right,
        left_case=left_case,
        right_case=right_case,
    ) is False


def test_loop_summary_unkeyable_refs_disable_pairwise_exact_shortcut():
    unkeyable_summary = LoopSummaryRef(
        start_expr=object(),
        limit_expr="n",
        step_expr=1,
        term_descriptor=LoopTermDescriptorRef(kind="memory_load", stride=4, element_size=4),
    )
    readonly_ref = ReadonlyReductionRef(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("ptr", index=0),
        count_parameter_name="n",
        count_parameter_index=1,
        stride=4,
        element_size=4,
        result_size=4,
        loop_summary=unkeyable_summary,
    )
    counted_ref = CountedLoopSummaryRef(
        induction_step=1,
        result_size=4,
        signed_loop=True,
        residue_cases=((1, 0, 1, 0),),
        loop_summary=unkeyable_summary,
    )

    assert unkeyable_summary.stable_key() is None
    assert readonly_ref.pairwise_exact_key() is None
    assert counted_ref.pairwise_exact_key() is None


def test_function_analysis_normalizes_deferred_calls_to_deferred_call_refs():
    info = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#2",
        target_ref=CallTargetRef.from_name("callee"),
        sequence=2,
    )
    analysis = create_mock_analysis("wrapper")
    analysis.deferred_calls = {"legacy_placeholder": info}

    analysis.normalize_deferred_calls()

    assert list(analysis.deferred_calls) == [info.deferred_call_ref.stable_key()]


def test_location_base_parameter_identity_uses_index_not_name():
    left = LocationBaseRef.parameter("lhs", index=1)
    right = LocationBaseRef.parameter("rhs", index=1)

    assert left == right
    assert left.stable_key() == right.stable_key()


def test_location_base_parameter_identity_is_scoped_by_function_when_available():
    caller = LocationBaseRef.parameter(
        "param_2",
        index=1,
        owner_program_id=100,
        owner_entry_offset=0x401000,
    )
    callee = LocationBaseRef.parameter(
        "param_2",
        index=1,
        owner_program_id=100,
        owner_entry_offset=0x402000,
    )

    assert caller != callee
    assert caller.stable_key() != callee.stable_key()
    assert caller.semantic_key() == callee.semantic_key()


def test_loop_summary_method_b_key_uses_parameter_semantics_not_owner_identity():
    left_base = LocationBaseRef.parameter(
        "base",
        index=0,
        owner_program_id=100,
        owner_entry_offset=0x401000,
    )
    right_base = LocationBaseRef.parameter(
        "base",
        index=0,
        owner_program_id=200,
        owner_entry_offset=0x501000,
    )
    left = _readonly_loop_summary(start=0)
    right = _readonly_loop_summary(start=0)
    left = LoopSummaryRef(
        start_expr=left.start_expr,
        limit_expr=left.limit_expr,
        step_expr=left.step_expr,
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=left_base,
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=4,
        ),
        side_effect_profile=left.side_effect_profile,
        loop_var_unit=left.loop_var_unit,
    )
    right = LoopSummaryRef(
        start_expr=right.start_expr,
        limit_expr=right.limit_expr,
        step_expr=right.step_expr,
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=right_base,
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=4,
        ),
        side_effect_profile=right.side_effect_profile,
        loop_var_unit=right.loop_var_unit,
    )

    assert left.stable_key() != right.stable_key()
    assert loop_summary_method_b_key(left) == loop_summary_method_b_key(right)
    assert compare_loop_summaries(left, right).status == "equivalent"


def test_method_b_smt_identity_uses_loop_semantics_across_owner_scoped_binaries():
    left_base = LocationBaseRef.parameter(
        "base",
        index=0,
        owner_program_id=100,
        owner_entry_offset=0x401000,
    )
    right_base = LocationBaseRef.parameter(
        "base",
        index=0,
        owner_program_id=200,
        owner_entry_offset=0x501000,
    )
    left_summary = _readonly_loop_summary(start=0)
    right_summary = _readonly_loop_summary(start=0)
    left_summary = LoopSummaryRef(
        start_expr=left_summary.start_expr,
        limit_expr=left_summary.limit_expr,
        step_expr=left_summary.step_expr,
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=left_base,
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=4,
        ),
        side_effect_profile=left_summary.side_effect_profile,
        loop_var_unit=left_summary.loop_var_unit,
    )
    right_summary = LoopSummaryRef(
        start_expr=right_summary.start_expr,
        limit_expr=right_summary.limit_expr,
        step_expr=right_summary.step_expr,
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=right_base,
            start_offset=0,
            stride=4,
            element_size=4,
            result_size=4,
        ),
        side_effect_profile=right_summary.side_effect_profile,
        loop_var_unit=right_summary.loop_var_unit,
    )
    left_expr = Expression.intrinsic(
        "READONLY_SUM",
        [
            Expression.parameter("base", index=0, data_type="int *", size=8),
            Expression.parameter("count", index=1, data_type="int", size=4),
        ],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=left_base,
            count_parameter_name="count",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
            loop_summary=left_summary,
        ),
    )
    right_expr = Expression.intrinsic(
        "READONLY_SUM",
        [
            Expression.parameter("base", index=0, data_type="int *", size=8),
            Expression.parameter("count", index=1, data_type="int", size=4),
        ],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=right_base,
            count_parameter_name="count",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
            loop_summary=right_summary,
        ),
    )

    assert left_expr.runtime_ref.stable_key() != right_expr.runtime_ref.stable_key()
    assert left_expr.runtime_ref.semantic_key() == right_expr.runtime_ref.semantic_key()
    assert _runtime_ref_smt_identity(left_expr, left_expr.runtime_ref) == _runtime_ref_smt_identity(
        right_expr,
        right_expr.runtime_ref,
    )


def test_loop_summary_method_b_key_keeps_vector_width_shape_distinct():
    scalar = _readonly_loop_summary(start=0)
    vector_like = LoopSummaryRef(
        start_expr=scalar.start_expr,
        limit_expr=scalar.limit_expr,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=LocationBaseRef.parameter("base", index=0),
            start_offset=0,
            stride=16,
            element_size=8,
            result_size=4,
        ),
        side_effect_profile=scalar.side_effect_profile,
        loop_var_unit=scalar.loop_var_unit,
    )

    assert loop_summary_method_b_key(scalar) != loop_summary_method_b_key(vector_like)
    assert compare_loop_summaries(scalar, vector_like).status == "unknown"


def test_loop_summary_method_b_key_does_not_scalarize_vector_lanes_without_iteration_proof():
    scalar = _readonly_loop_summary(start=0)
    vector_lanes = LoopSummaryRef(
        start_expr=scalar.start_expr,
        limit_expr=scalar.limit_expr,
        step_expr=scalar.step_expr,
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=LocationBaseRef.parameter("base", index=0),
            start_offset=0,
            stride=16,
            element_size=8,
            result_size=4,
            lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
        ),
        side_effect_profile=scalar.side_effect_profile,
        loop_var_unit=scalar.loop_var_unit,
    )

    assert loop_summary_method_b_key(scalar) != loop_summary_method_b_key(vector_lanes)
    assert compare_loop_summaries(scalar, vector_lanes).status == "unknown"


def test_loop_summary_method_b_key_scalarizes_vector_lanes_only_with_scalar_iteration_proof():
    scalar = _readonly_loop_summary(start=0)
    scalar_proven = LoopSummaryRef(
        start_expr=scalar.start_expr,
        limit_expr=scalar.limit_expr,
        step_expr=scalar.step_expr,
        term_descriptor=scalar.term_descriptor,
        side_effect_profile=scalar.side_effect_profile,
        loop_var_unit="scalar_element_index",
    )
    vector_lanes = LoopSummaryRef(
        start_expr=scalar.start_expr,
        limit_expr=scalar.limit_expr,
        step_expr=scalar.step_expr,
        term_descriptor=LoopTermDescriptorRef(
            kind="memory_load",
            reduction_kind="sum",
            location_base_ref=LocationBaseRef.parameter("base", index=0),
            start_offset=0,
            stride=16,
            element_size=8,
            result_size=4,
            lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
        ),
        side_effect_profile=scalar.side_effect_profile,
        loop_var_unit="scalar_element_index",
    )

    assert loop_summary_method_b_key(scalar_proven) == loop_summary_method_b_key(vector_lanes)


def test_loop_summary_method_b_key_leaves_limit_width_to_smt_parameter_binding():
    int_count = _readonly_loop_summary(start=0)
    long_count = LoopSummaryRef(
        start_expr=Expression.constant(0, size=8),
        limit_expr=Expression.parameter("count64", index=1, data_type="ulong", size=8),
        step_expr=Expression.constant(1, size=8),
        term_descriptor=int_count.term_descriptor,
        side_effect_profile=int_count.side_effect_profile,
        loop_var_unit=int_count.loop_var_unit,
    )

    assert loop_summary_method_b_key(int_count) == loop_summary_method_b_key(long_count)
    assert compare_loop_summaries(int_count, long_count).status == "equivalent"


def test_storage_info_register_identity_uses_numeric_base_metadata():
    left = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=3,
        offset=0x10,
        size=4,
        size_bits=32,
        register_name="w0",
        register_offset=0x10,
        register_size=4,
        register_size_bits=32,
        base_register_name="x0",
        base_register_offset=0x10,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    right = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=3,
        offset=0x10,
        size=4,
        size_bits=32,
        register_name="arg0_low",
        register_offset=0x10,
        register_size=4,
        register_size_bits=32,
        base_register_name="param_alias",
        base_register_offset=0x10,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )

    assert left.shares_base_register_with(right) is True
    assert left.register_identity_key() == right.register_identity_key()


def test_storage_info_matches_base_register_by_name_when_numeric_offsets_differ():
    synthetic = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=0,
        size=8,
        size_bits=64,
        register_name="v0",
        base_register_name="v0",
        base_register_offset=StorageInfo._synthetic_register_offset("v0"),
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )
    concrete = StorageInfo(
        is_register=True,
        space_name="register",
        space_id=548,
        offset=0x10,
        size=8,
        size_bits=64,
        register_name="v0",
        register_offset=0x10,
        register_size=8,
        register_size_bits=64,
        base_register_name="v0",
        base_register_offset=0x10,
        base_register_size=8,
        base_register_size_bits=64,
        bit_offset_in_base=0,
    )

    assert synthetic.base_register_offset != concrete.base_register_offset
    assert synthetic.shares_base_register_with(concrete) is True


def test_post_state_symbolic_locations_bind_parameter_indices():
    parameters = [{"name": "trace", "index": 0, "size": 8}]
    expr = post_state_read_expression_for_location(
        CanonicalLocation("trace", 4, 4),
        parameters,
        symbolic=True,
    )

    runtime_ref = expr.runtime_ref
    assert isinstance(runtime_ref, PostStateReadRef)
    assert runtime_ref.location.base_ref == LocationBaseRef.parameter("trace", index=0)
    assert runtime_ref.snapshot_ref == PostStateSnapshotRef.function_return()

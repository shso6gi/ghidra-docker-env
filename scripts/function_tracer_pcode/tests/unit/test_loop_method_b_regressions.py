# -*- coding: utf-8 -*-
"""Method-B loop-summary regression fixtures.

These tests intentionally use model-level runtime refs.  TaskG is about
pinning the meaning-level contract that real Ghidra extraction must satisfy:
pure loop summaries may use seed compensation, while effect-aware and
path-sensitive summaries remain proof-required and must not silently fall
through legacy shortcuts.
"""

from unittest.mock import Mock

from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.model import (
    COUNTED_LOOP_SUM_OPCODE,
    READONLY_SUM_OPCODE,
    Condition,
    CountedLoopSummaryRef,
    Expression,
    FunctionReturnAnalysis,
    LocationBaseRef,
    LoopBodyEffectRef,
    LoopCaseRef,
    LoopSideEffectProfileRef,
    LoopSummaryRef,
    LoopTermDescriptorRef,
    ReductionAccumulatorProof,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReturnInfo,
    loop_summary_method_b_key,
)


def _base_param() -> Expression:
    return Expression.parameter("base", index=0, data_type="int *", size=8)


def _count_param() -> Expression:
    return Expression.parameter("count", index=1, data_type="int", size=4)


def _const(value: int) -> Expression:
    return Expression.constant(value, size=4)


def _eq_count(value: int) -> Condition:
    return Condition(Expression.binary_op("INT_EQUAL", _count_param(), _const(value)))


def _count_gt(value: int) -> Condition:
    return Condition(Expression.binary_op("INT_SLESS", _const(value), _count_param()))


def _term(byte_offset: int) -> ReadonlyReductionTermRef:
    return ReadonlyReductionTermRef(byte_offset=byte_offset, access_size=4)


def _load_term_expr(index: int) -> Expression:
    return Expression.memory(
        Expression.intrinsic(
            "PTRADD",
            [_base_param(), Expression.constant(index, size=8), Expression.constant(4, size=8)],
            size=8,
        ),
        size=4,
    )


def _sum_expr(*terms: Expression) -> Expression:
    assert terms
    result = terms[0]
    for term in terms[1:]:
        result = Expression.binary_op("INT_ADD", result, term)
    return result


def _readonly_summary(
    *,
    start: int,
    step: int = 1,
    seed_terms=(),
    guard_constraints=(),
) -> LoopSummaryRef:
    return LoopSummaryRef(
        start_expr=Expression.constant(start, size=4),
        limit_expr=_count_param(),
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
        side_effect_profile=LoopSideEffectProfileRef(
            profile="pure_memory_read",
            memory_reads=True,
        ),
        guard_constraints=tuple(guard_constraints or ()),
        loop_var_unit="element_index",
    )


def _readonly_sum(summary: LoopSummaryRef) -> Expression:
    start = int(getattr(summary.start_expr, "value", 0) or 0)
    step = int(getattr(summary.step_expr, "value", 1) or 1)
    return Expression.intrinsic(
        "READONLY_SUM",
        [_base_param(), _count_param()],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=LocationBaseRef.parameter("base", index=0),
            count_parameter_name="count",
            count_parameter_index=1,
            stride=4 * step,
            element_size=4,
            result_size=4,
            start_offset=4 * start,
            signed_counter=True,
            loop_summary=summary,
        ),
        opcode=READONLY_SUM_OPCODE,
    )


def _readonly_sum_from_proof(proof: ReductionAccumulatorProof) -> Expression:
    reduction_ref = proof.to_readonly_reduction_ref()
    assert reduction_ref is not None
    return Expression.intrinsic(
        "READONLY_SUM",
        [_base_param(), _count_param()],
        size=4,
        runtime_ref=reduction_ref,
        opcode=READONLY_SUM_OPCODE,
    )


def _pure_counted_summary() -> LoopSummaryRef:
    return LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=_count_param(),
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        loop_var_unit="element_index",
    )


def _path_sensitive_counted_summary() -> LoopSummaryRef:
    return LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=_count_param(),
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        cases=(
            LoopCaseRef(
                path_conditions=("i_is_even",),
                body_effect=LoopBodyEffectRef(
                    kind="accumulator_update",
                    value_expr="acc + term(i)",
                ),
                term_expr="term(i)",
                case_kind="accumulator_delta",
            ),
        ),
        loop_var_unit="element_index",
    )


def _write_heavy_counted_summary() -> LoopSummaryRef:
    return LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=_count_param(),
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(
            profile="effect_aware",
            memory_writes=True,
            effect_count=3,
            effect_descriptors=(
                LoopBodyEffectRef(
                    kind="memory_write",
                    source="pcode_scan",
                    scope="loop",
                    address_space="ram",
                    location=("base", "i", 0),
                    value_expr=("term", "i"),
                    order_key=1,
                ),
                LoopBodyEffectRef(
                    kind="memory_write",
                    source="pcode_scan",
                    scope="loop",
                    address_space="ram",
                    location=("base", "i", 4),
                    value_expr=("term", "i+1"),
                    order_key=2,
                ),
                LoopBodyEffectRef(
                    kind="memory_write",
                    source="pcode_scan",
                    scope="loop",
                    address_space="ram",
                    location=("base", "i", 8),
                    value_expr=("term", "i+2"),
                    order_key=3,
                ),
            ),
        ),
        loop_var_unit="element_index",
    )


def _counted_loop(summary: LoopSummaryRef) -> Expression:
    return Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [Expression.constant(0, size=4), Expression.constant(0, size=4), _count_param()],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 1, 0),),
            loop_summary=summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )


def _analysis(function_name: str, returns) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name=function_name,
        entry_point="0x1000",
        parameters=[
            {"name": "base", "index": 0, "data_type": "int *", "size": 8, "is_signed": False},
            {"name": "count", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        returns=list(returns),
        return_type="int",
    )


def _branch_returns(value: Expression):
    """Four-way count-domain fixture: n=1, n=2, n=3, and n>=4."""

    return [
        ReturnInfo(address="0x1001", value=value, conditions=[_eq_count(1)], branch_index=1),
        ReturnInfo(address="0x1002", value=value, conditions=[_eq_count(2)], branch_index=2),
        ReturnInfo(address="0x1003", value=value, conditions=[_eq_count(3)], branch_index=3),
        ReturnInfo(address="0x1004", value=value, conditions=[_count_gt(3)], branch_index=4),
    ]


def _pairwise_strategy() -> PairwiseStrategy:
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


def test_ptr_sum_window_branch_fixture_uses_method_b_for_n_1_2_3_and_ge_4():
    full = _readonly_sum(_readonly_summary(start=0, guard_constraints=("0 < count",)))
    tail = _readonly_sum(
        _readonly_summary(
            start=3,
            seed_terms=(_term(0), _term(4), _term(8)),
            guard_constraints=("3 < count",),
        )
    )
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("ptr_sum_window_full", _branch_returns(full)),
        _analysis("ptr_sum_window_tail", _branch_returns(tail)),
    )

    assert result.is_equivalent is True
    assert result.total_pairs == 16
    assert result.unsat_pairs == 16
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_exact_prefix_return_matches_readonly_reduction_accumulator_proof():
    count_expr = _count_param()
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
        seed_terms=(_term(0), _term(4), _term(8)),
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    exact = _sum_expr(_load_term_expr(0), _load_term_expr(1), _load_term_expr(2))
    summarized = _readonly_sum_from_proof(proof)
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("exact_prefix", [ReturnInfo(address="0x1100", value=exact, conditions=[_eq_count(3)])]),
        _analysis("summary_prefix", [ReturnInfo(address="0x1200", value=summarized, conditions=[_count_gt(0)])]),
    )

    assert result.is_equivalent is True
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_exact_prefix_return_matches_seed_term_count_readonly_reduction_proof():
    count_expr = _count_param()
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
        seed_term_count=3,
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    exact = _sum_expr(_load_term_expr(0), _load_term_expr(1), _load_term_expr(2))
    summarized = _readonly_sum_from_proof(proof)
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("exact_prefix_seed_count", [ReturnInfo(address="0x1110", value=exact, conditions=[_eq_count(3)])]),
        _analysis(
            "summary_prefix_seed_count",
            [ReturnInfo(address="0x1210", value=summarized, conditions=[_count_gt(0)])],
        ),
    )

    assert result.is_equivalent is True
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_exact_tail_entry_return_matches_materialized_readonly_reduction_proof():
    count_expr = _count_param()
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
        seed_terms=(_term(0), _term(4), _term(8)),
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    exact = _sum_expr(_load_term_expr(0), _load_term_expr(1), _load_term_expr(2), _load_term_expr(3))
    summarized = _readonly_sum_from_proof(proof)
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("exact_tail_entry", [ReturnInfo(address="0x1250", value=exact, conditions=[_eq_count(4)])]),
        _analysis("summary_tail_entry", [ReturnInfo(address="0x1260", value=summarized, conditions=[_count_gt(0)])]),
    )

    assert result.is_equivalent is True
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_vectorized_readonly_proof_with_prefix_witnesses_matches_scalar_summary():
    count_expr = _count_param()
    vectorized_proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=16,
        element_size=4,
        start_offset=12,
        start_index=0,
        index_step=1,
        index_scale=16,
        lane_terms=((0, 4), (4, 4), (8, 4), (12, 4)),
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(
            ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),
            ReadonlyReductionWitness(exact_count=2, terms=(_term(0), _term(4))),
            ReadonlyReductionWitness(exact_count=3, terms=(_term(0), _term(4), _term(8))),
        ),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    scalar_tail_proof = ReductionAccumulatorProof(
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
        seed_term_count=3,
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis(
            "vectorized_prefix_proof",
            [ReturnInfo(address="0x1300", value=_readonly_sum_from_proof(vectorized_proof), conditions=[_count_gt(0)])],
        ),
        _analysis(
            "scalar_tail_proof",
            [ReturnInfo(address="0x1310", value=_readonly_sum_from_proof(scalar_tail_proof), conditions=[_count_gt(0)])],
        ),
    )

    assert result.is_equivalent is True
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_proof_backed_scalar_and_vectorized_readonly_summaries_compare_equivalent():
    count_expr = _count_param()
    scalar_proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
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
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    vector_proof = ReductionAccumulatorProof(
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
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis(
            "readonly_scalar_proof",
            [ReturnInfo(address="0x1330", value=_readonly_sum_from_proof(scalar_proof), conditions=[_count_gt(0)])],
        ),
        _analysis(
            "readonly_vector_proof",
            [ReturnInfo(address="0x1430", value=_readonly_sum_from_proof(vector_proof), conditions=[_count_gt(0)])],
        ),
    )

    assert result.is_equivalent is True
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_exact_tail_entry_return_requires_condition_to_prove_count():
    count_expr = _count_param()
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
        seed_terms=(_term(0), _term(4), _term(8)),
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    exact_info = ReturnInfo(
        address="0x1270",
        value=_sum_expr(_load_term_expr(0), _load_term_expr(1), _load_term_expr(2), _load_term_expr(3)),
        conditions=[_eq_count(5)],
    )
    summary_info = ReturnInfo(address="0x1280", value=_readonly_sum_from_proof(proof), conditions=[_count_gt(0)])
    exact_case = ReturnCase(
        0,
        list(exact_info.conditions),
        exact_info.value,
        exact_info,
        parameters=_analysis("exact_tail_bad_count", [exact_info]).parameters,
    )
    summary_case = ReturnCase(
        0,
        list(summary_info.conditions),
        summary_info.value,
        summary_info,
        parameters=_analysis("summary_tail_bad_count", [summary_info]).parameters,
    )
    strategy = _pairwise_strategy()

    assert strategy._exact_value_matches_readonly_reduction_proof(exact_case, summary_case) is False


def test_exact_load_sum_proof_requires_readonly_sum_intrinsic():
    count_expr = _count_param()
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
        exact_return_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    reduction_ref = proof.to_readonly_reduction_ref()
    assert reduction_ref is not None
    exact_info = ReturnInfo(address="0x1290", value=_load_term_expr(0), conditions=[_eq_count(1)])
    summary_info = ReturnInfo(
        address="0x12A0",
        value=Expression.intrinsic(
            "COUNTED_LOOP_SUM",
            [_base_param(), _count_param()],
            size=4,
            runtime_ref=reduction_ref,
            opcode=COUNTED_LOOP_SUM_OPCODE,
        ),
        conditions=[_count_gt(0)],
    )
    exact_case = ReturnCase(
        0,
        list(exact_info.conditions),
        exact_info.value,
        exact_info,
        parameters=_analysis("exact_readonly_wrong_opcode", [exact_info]).parameters,
    )
    summary_case = ReturnCase(
        0,
        list(summary_info.conditions),
        summary_info.value,
        summary_info,
        parameters=_analysis("summary_readonly_wrong_opcode", [summary_info]).parameters,
    )
    strategy = _pairwise_strategy()

    assert strategy._exact_value_matches_readonly_reduction_proof(exact_case, summary_case) is False


def test_exact_load_sum_count_proof_distinguishes_same_named_parameter_indices():
    count_expr = _count_param()
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
        exact_return_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    same_name_other_index = Expression.parameter("count", index=2, data_type="int", size=4)
    exact_info = ReturnInfo(
        address="0x12B0",
        value=_load_term_expr(0),
        conditions=[Condition(Expression.binary_op("INT_EQUAL", same_name_other_index, _const(1)))],
    )
    summary_info = ReturnInfo(address="0x12C0", value=_readonly_sum_from_proof(proof), conditions=[_count_gt(0)])
    exact_case = ReturnCase(
        0,
        list(exact_info.conditions),
        exact_info.value,
        exact_info,
        parameters=_analysis("exact_same_named_other_count", [exact_info]).parameters,
    )
    summary_case = ReturnCase(
        0,
        list(summary_info.conditions),
        summary_info.value,
        summary_info,
        parameters=_analysis("summary_real_count", [summary_info]).parameters,
    )
    strategy = _pairwise_strategy()

    assert strategy._exact_value_matches_readonly_reduction_proof(exact_case, summary_case) is False


def test_exact_load_sum_matches_synthesized_readonly_reduction_witness():
    count_expr = _count_param()
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
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
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(
            ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),
            ReadonlyReductionWitness(exact_count=2, terms=(_term(0), _term(4))),
        ),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    exact = _sum_expr(_load_term_expr(0), _load_term_expr(1))
    summarized = _readonly_sum_from_proof(proof)
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("exact_two", [ReturnInfo(address="0x1300", value=exact, conditions=[_eq_count(2)])]),
        _analysis("summary_two", [ReturnInfo(address="0x1400", value=summarized, conditions=[_count_gt(0)])]),
    )

    assert result.is_equivalent is True
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_exact_load_sum_does_not_treat_narrow_count_view_as_full_reduction_count():
    count64 = Expression.parameter("count", index=1, data_type="long", size=8)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count64,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
    ).with_runtime_evidence(
        limit_expr=count64,
        result_size=4,
        loop_body_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
        exact_return_witnesses=(),
        guard_constraints=(
            Condition(
                Expression.binary_op(
                    "INT_SLESS",
                    Expression.constant(0, size=8),
                    count64,
                )
            ),
        ),
        signed_counter=True,
    )
    low_count = Expression.binary_op(
        "SUBPIECE",
        Expression.parameter("count", index=1, data_type="long", size=8),
        Expression.constant(0, size=4),
    )
    low_count.size = 4
    exact_info = ReturnInfo(
        address="0x1308",
        value=_load_term_expr(0),
        conditions=[Condition(Expression.binary_op("INT_EQUAL", low_count, _const(1)))],
    )
    summary_info = ReturnInfo(address="0x1408", value=_readonly_sum_from_proof(proof), conditions=[_count_gt(0)])
    exact_case = ReturnCase(
        0,
        list(exact_info.conditions),
        exact_info.value,
        exact_info,
        parameters=_analysis("exact_narrow_count", [exact_info]).parameters,
    )
    summary_case = ReturnCase(
        0,
        list(summary_info.conditions),
        summary_info.value,
        summary_info,
        parameters=_analysis("summary_wide_count", [summary_info]).parameters,
    )
    strategy = _pairwise_strategy()

    assert strategy._exact_value_matches_readonly_reduction_proof(exact_case, summary_case) is False


def test_exact_load_sum_does_not_treat_narrow_cast_count_view_as_full_reduction_count():
    count64 = Expression.parameter("count", index=1, data_type="long", size=8)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count64,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
    ).with_runtime_evidence(
        limit_expr=count64,
        result_size=4,
        loop_body_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
        exact_return_witnesses=(),
        guard_constraints=(
            Condition(
                Expression.binary_op(
                    "INT_SLESS",
                    Expression.constant(0, size=8),
                    count64,
                )
            ),
        ),
        signed_counter=True,
    )
    narrowed_cast = Expression.unary_op(
        "CAST",
        Expression.parameter("count", index=1, data_type="long", size=8),
    )
    narrowed_cast.size = 4
    exact_info = ReturnInfo(
        address="0x1309",
        value=_load_term_expr(0),
        conditions=[Condition(Expression.binary_op("INT_EQUAL", narrowed_cast, _const(1)))],
    )
    summary_info = ReturnInfo(address="0x1409", value=_readonly_sum_from_proof(proof), conditions=[_count_gt(0)])
    exact_case = ReturnCase(
        0,
        list(exact_info.conditions),
        exact_info.value,
        exact_info,
        parameters=_analysis("exact_narrow_cast_count", [exact_info]).parameters,
    )
    summary_case = ReturnCase(
        0,
        list(summary_info.conditions),
        summary_info.value,
        summary_info,
        parameters=_analysis("summary_wide_cast_count", [summary_info]).parameters,
    )
    strategy = _pairwise_strategy()

    assert strategy._exact_value_matches_readonly_reduction_proof(exact_case, summary_case) is False


def test_exact_load_sum_does_not_treat_narrow_bare_count_parameter_as_full_reduction_count():
    count64 = Expression.parameter("count", index=1, data_type="long", size=8)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count64,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
    ).with_runtime_evidence(
        limit_expr=count64,
        result_size=4,
        loop_body_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
        exact_return_witnesses=(),
        guard_constraints=(
            Condition(
                Expression.binary_op(
                    "INT_SLESS",
                    Expression.constant(0, size=8),
                    count64,
                )
            ),
        ),
        signed_counter=True,
    )
    narrow_count = Expression.parameter("count", index=1, data_type="int", size=4)
    exact_info = ReturnInfo(
        address="0x130a",
        value=_load_term_expr(0),
        conditions=[Condition(Expression.binary_op("INT_EQUAL", narrow_count, _const(1)))],
    )
    summary_info = ReturnInfo(address="0x140a", value=_readonly_sum_from_proof(proof), conditions=[_count_gt(0)])
    exact_case = ReturnCase(
        0,
        list(exact_info.conditions),
        exact_info.value,
        exact_info,
        parameters=_analysis("exact_narrow_bare_count", [exact_info]).parameters,
    )
    summary_case = ReturnCase(
        0,
        list(summary_info.conditions),
        summary_info.value,
        summary_info,
        parameters=_analysis("summary_wide_bare_count", [summary_info]).parameters,
    )
    strategy = _pairwise_strategy()

    assert strategy._exact_value_matches_readonly_reduction_proof(exact_case, summary_case) is False


def test_exact_load_sum_does_not_match_biased_readonly_reduction_without_bias_proof():
    count_expr = _count_param()
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        constant_bias=5,
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
        exact_return_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    exact_info = ReturnInfo(address="0x1500", value=_load_term_expr(0), conditions=[_eq_count(1)])
    summary_info = ReturnInfo(address="0x1600", value=_readonly_sum_from_proof(proof), conditions=[_count_gt(0)])
    exact_case = ReturnCase(
        0,
        list(exact_info.conditions),
        exact_info.value,
        exact_info,
        parameters=_analysis("exact_biased_guard", [exact_info]).parameters,
    )
    summary_case = ReturnCase(
        0,
        list(summary_info.conditions),
        summary_info.value,
        summary_info,
        parameters=_analysis("summary_biased_guard", [summary_info]).parameters,
    )
    strategy = _pairwise_strategy()

    assert strategy._exact_value_matches_readonly_reduction_proof(exact_case, summary_case) is False


def test_biased_exact_load_sum_matches_biased_readonly_reduction_proof():
    count_expr = _count_param()
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        constant_bias=5,
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
        exact_return_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    exact_value = Expression.binary_op("INT_ADD", _load_term_expr(0), _const(5))
    exact_info = ReturnInfo(address="0x1700", value=exact_value, conditions=[_eq_count(1)])
    summary_info = ReturnInfo(address="0x1800", value=_readonly_sum_from_proof(proof), conditions=[_count_gt(0)])
    exact_case = ReturnCase(
        0,
        list(exact_info.conditions),
        exact_info.value,
        exact_info,
        parameters=_analysis("exact_biased", [exact_info]).parameters,
    )
    summary_case = ReturnCase(
        0,
        list(summary_info.conditions),
        summary_info.value,
        summary_info,
        parameters=_analysis("summary_biased", [summary_info]).parameters,
    )
    strategy = _pairwise_strategy()

    assert strategy._exact_value_matches_readonly_reduction_proof(exact_case, summary_case) is True


def test_biased_exact_load_sum_requires_matching_result_width():
    count_expr = _count_param()
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        constant_bias=0,
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
        exact_return_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    wide_bias = Expression.constant(0x100000000, size=8)
    exact_value = Expression.binary_op("INT_ADD", _load_term_expr(0), wide_bias)
    exact_value.size = 8
    exact_info = ReturnInfo(address="0x1710", value=exact_value, conditions=[_eq_count(1)])
    summary_info = ReturnInfo(address="0x1810", value=_readonly_sum_from_proof(proof), conditions=[_count_gt(0)])
    exact_case = ReturnCase(
        0,
        list(exact_info.conditions),
        exact_info.value,
        exact_info,
        parameters=_analysis("exact_wide_bias", [exact_info]).parameters,
    )
    summary_case = ReturnCase(
        0,
        list(summary_info.conditions),
        summary_info.value,
        summary_info,
        parameters=_analysis("summary_narrow_bias", [summary_info]).parameters,
    )
    strategy = _pairwise_strategy()

    assert strategy._exact_value_matches_readonly_reduction_proof(exact_case, summary_case) is False


def test_pairwise_exact_load_matcher_does_not_guess_endianness_for_subpiece():
    strategy = _pairwise_strategy()
    subpiece = Expression.binary_op("SUBPIECE", _load_term_expr(0), Expression.constant(0, size=4))
    subpiece.size = 1

    assert strategy._extract_readonly_reduction_terms_from_expression(
        subpiece,
        [
            {"name": "base", "index": 0, "data_type": "int *", "size": 8, "is_signed": False},
            {"name": "count", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        LocationBaseRef.parameter("base", index=0),
    ) is None


def test_ptr_sum_window_prior_missed_fixture_allows_nonzero_start_with_nonunit_step_seed():
    start_one_step_two = _readonly_summary(start=1, step=2)
    start_three_step_two = _readonly_summary(
        start=3,
        step=2,
        seed_terms=(_term(4),),
    )
    strategy = _pairwise_strategy()

    assert loop_summary_method_b_key(start_one_step_two) == loop_summary_method_b_key(
        start_three_step_two
    )

    result = strategy.check(
        _analysis("ptr_sum_window_step2_full", _branch_returns(_readonly_sum(start_one_step_two))),
        _analysis("ptr_sum_window_step2_tail", _branch_returns(_readonly_sum(start_three_step_two))),
    )

    assert result.is_equivalent is True
    assert result.total_pairs == 16
    assert result.unsat_pairs == 16
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_branch_inside_loop_fixture_stays_unknown_until_path_proof_exists():
    value = _counted_loop(_path_sensitive_counted_summary())
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("branch_inside_loop_a", [ReturnInfo(address="0x2000", value=value)]),
        _analysis("branch_inside_loop_b", [ReturnInfo(address="0x3000", value=value)]),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 0
    assert result.unknown_pairs == 1
    strategy.solver_runner.run_sequential.assert_not_called()


def test_write_heavy_loop_fixture_stays_unknown_until_effect_proof_exists():
    value = _counted_loop(_write_heavy_counted_summary())
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("write_heavy_loop_a", [ReturnInfo(address="0x4000", value=value)]),
        _analysis("write_heavy_loop_b", [ReturnInfo(address="0x5000", value=value)]),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 0
    assert result.unknown_pairs == 1
    strategy.solver_runner.run_sequential.assert_not_called()


def test_pure_and_path_sensitive_loop_shape_mismatch_stays_unknown():
    pure = _counted_loop(_pure_counted_summary())
    path_sensitive = _counted_loop(_path_sensitive_counted_summary())
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("pure_loop", [ReturnInfo(address="0x6000", value=pure)]),
        _analysis("branch_inside_loop", [ReturnInfo(address="0x7000", value=path_sensitive)]),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 0
    assert result.unknown_pairs == 1
    strategy.solver_runner.run_sequential.assert_not_called()

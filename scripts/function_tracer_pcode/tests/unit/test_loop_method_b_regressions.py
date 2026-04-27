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

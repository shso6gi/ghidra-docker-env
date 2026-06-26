# -*- coding: utf-8 -*-
"""Method-B loop-summary regression fixtures.

These tests intentionally use model-level runtime refs.  TaskG is about
pinning the meaning-level contract that real Ghidra extraction must satisfy:
pure loop summaries may use seed compensation, while effect-aware and
path-sensitive summaries remain proof-required and must not silently fall
through legacy shortcuts.
"""

from dataclasses import replace
from unittest.mock import Mock

from scripts.function_tracer_pcode.equivalence.formula.types import ParameterInfo
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_builder import extract_return_cases
from scripts.function_tracer_pcode.analysis.recurrence_summary import StructuralRecurrenceSummarizer
from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownReasonId,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
)
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.model import (
    COUNTED_LOOP_SUM_OPCODE,
    READONLY_SUM_OPCODE,
    Condition,
    ComparisonSurface,
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
    StorageInfo,
    loop_summary_method_b_key,
)
from scripts.function_tracer_pcode.model.runtime_refs import UnknownValueRef


def _base_param() -> Expression:
    return Expression.parameter("base", index=0, data_type="int *", size=8)


def _count_param() -> Expression:
    return Expression.parameter("count", index=1, data_type="int", size=4)


def _const(value: int) -> Expression:
    return Expression.constant(value, size=4)


class _FakePcodeOpRef:
    def __init__(self, *, seq_time: int, target_offset: int = 0x100C, opcode: int = 60):
        self.seq_time = int(seq_time)
        self.target_offset = int(target_offset)
        self.opcode = int(opcode)

    def stable_key(self):
        return (
            "pcode_op",
            "fake",
            ("function_entry", "ram", 0x1000),
            ("seq_target", "ram", self.target_offset),
            self.seq_time,
            0,
            self.opcode,
            0,
        )


def _phi_circular_unknown(*, seq_time: int, target_offset: int = 0x100C, opcode: int = 60) -> Expression:
    expr = Expression.unknown(
        "phi_circular",
        runtime_ref=UnknownValueRef.phi_circular(
            pcode_op_ref=_FakePcodeOpRef(
                seq_time=seq_time,
                target_offset=target_offset,
                opcode=opcode,
            )
        ),
    )
    expr.size = 4
    return expr


def _phi_circular_exit_guard(phi_expr: Expression) -> Condition:
    minus_one = Expression.binary_op("INT_ADD", phi_expr, Expression.constant(0xFFFFFFFF, size=4))
    minus_one.size = 4
    minus_two = Expression.binary_op("INT_ADD", minus_one, Expression.constant(0xFFFFFFFF, size=4))
    minus_two.size = 4
    return Condition(Expression.binary_op("INT_EQUAL", minus_two, _const(0)))


def _eq_count(value: int) -> Condition:
    return Condition(Expression.binary_op("INT_EQUAL", _count_param(), _const(value)))


def _affine_eq_count(value: int) -> Condition:
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op(
            "INT_SUB",
            Expression.unary_op("INT_ZEXT", _count_param()),
            Expression.constant(value - 1, size=4),
        ),
        Expression.constant(0xFFFFFFFF, size=4),
    )
    return Condition(Expression.binary_op("INT_NOTEQUAL", expr, _const(0)), negated=True)


def _ptradd_guard_eq_count(value: int) -> Condition:
    wide_count = Expression.parameter("count", index=1, data_type="long", size=8)
    count_low = Expression.binary_op(
        "SUBPIECE",
        wide_count,
        Expression.constant(0, size=4),
    )
    count_low.size = 4
    count_minus_start = Expression.binary_op(
        "INT_SUB",
        count_low,
        Expression.constant(4, size=4),
    )
    count_minus_start.size = 4
    count_delta = Expression.unary_op("INT_ZEXT", count_minus_start)
    count_delta.size = 8
    rhs_index = Expression.binary_op(
        "INT_ADD",
        Expression.constant(4, size=8),
        count_delta,
    )
    lhs = Expression.intrinsic(
        "PTRADD",
        [
            Expression.intrinsic(
                "PTRADD",
                [_base_param(), Expression.constant(value - 1, size=8), Expression.constant(4, size=8)],
                size=8,
            ),
            Expression.constant(1, size=8),
            Expression.constant(4, size=8),
        ],
        size=8,
    )
    rhs = Expression.intrinsic(
        "PTRADD",
        [_base_param(), rhs_index, Expression.constant(4, size=8)],
        size=8,
    )
    return Condition(Expression.binary_op("INT_EQUAL", lhs, rhs))


def _count_gt(value: int) -> Condition:
    return Condition(Expression.binary_op("INT_SLESS", _const(value), _count_param()))


def _base_eq_zero() -> Condition:
    return Condition(Expression.binary_op("INT_EQUAL", _base_param(), Expression.constant(0, size=8)))


def _base_ne_zero() -> Condition:
    return Condition(Expression.binary_op("INT_NOTEQUAL", _base_param(), Expression.constant(0, size=8)))


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
        size=max(1, int(getattr(reduction_ref, "result_size", 4) or 4)),
        runtime_ref=reduction_ref,
        opcode=READONLY_SUM_OPCODE,
    )


def _readonly_sum_from_ref(reduction_ref: ReadonlyReductionRef) -> Expression:
    return Expression.intrinsic(
        "READONLY_SUM",
        [_base_param(), _count_param()],
        size=max(1, int(getattr(reduction_ref, "result_size", 4) or 4)),
        runtime_ref=reduction_ref,
        opcode=READONLY_SUM_OPCODE,
    )


def test_extract_return_cases_reinjects_readonly_summary_proof_guards():
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=_count_param(),
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        index_step=1,
        index_scale=4,
        seed_terms=(_term(0), _term(8)),
        guard_constraints=(_count_gt(3),),
        side_effect_profile=LoopSideEffectProfileRef(
            profile="pure_memory_read",
            memory_reads=True,
        ),
        return_region_value_proven=True,
    )
    analysis = _analysis(
        "summary_guard_regression",
        [
            ReturnInfo(
                address="0x1000",
                value=_readonly_sum_from_proof(proof),
                conditions=[
                    Condition(
                        Expression.binary_op(
                            "INT_NOTEQUAL",
                            _base_param(),
                            Expression.constant(0, size=8),
                        )
                    )
                ],
            )
        ],
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    assert any(cond.equals(_count_gt(3)) for cond in cases[0].conditions)


def test_extract_return_cases_normalizes_reinjected_summary_guard_widths():
    wide_count_guard = Condition(
        Expression.binary_op(
            "INT_SLESS",
            _count_param(),
            Expression.constant(4, size=8),
        )
    )
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=_count_param(),
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
        guard_constraints=(wide_count_guard,),
        side_effect_profile=LoopSideEffectProfileRef(
            profile="pure_memory_read",
            memory_reads=True,
        ),
        return_region_value_proven=True,
    )
    analysis = _analysis(
        "summary_guard_width_regression",
        [ReturnInfo(address="0x1000", value=_readonly_sum_from_proof(proof), conditions=[])],
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    guard = next(
        cond
        for cond in cases[0].conditions
        if cond.expression.operator == "INT_SLESS"
    )
    assert guard.expression.operands[1].get_bit_width() == 32
    assert "(_ bv4 32)" in guard.to_smt()
    assert "(_ bv4 64)" not in guard.to_smt()


def test_extract_return_cases_normalizes_return_condition_parameter_metadata():
    stale_wide_count = Expression.parameter("count", index=1, data_type="long", size=8)
    stale_wide_condition = Condition(
        Expression.binary_op(
            "INT_SLESS",
            stale_wide_count,
            Expression.constant(4, size=8),
        )
    )
    analysis = _analysis(
        "return_condition_width_regression",
        [
            ReturnInfo(
                address="0x1000",
                value=Expression.constant(1, size=4),
                conditions=[stale_wide_condition],
            )
        ],
    )

    cases = extract_return_cases(analysis)

    assert len(cases) == 1
    condition = cases[0].conditions[0]
    assert condition.expression.operands[0].get_bit_width() == 32
    assert condition.expression.operands[1].get_bit_width() == 32
    assert "(_ bv4 32)" in condition.to_smt()
    assert "(_ bv4 64)" not in condition.to_smt()


def test_pairwise_object_condition_coverage_proves_total_binary_partition_without_base_context():
    non_positive = _count_gt(0).negate()
    positive = _count_gt(0)
    analysis = _analysis(
        "total_partition",
        [
            ReturnInfo(address="0x1000", value=_const(7), conditions=[non_positive]),
            ReturnInfo(address="0x1004", value=_const(7), conditions=[positive]),
        ],
    )
    cases = extract_return_cases(analysis)
    strategy = _pairwise_strategy()

    assert strategy._return_cases_have_object_centric_total_coverage(cases)


def test_pairwise_coverage_uses_parameter_index_before_fragment_runtime_refs():
    class FragmentRuntimeRef:
        def __init__(self, name: str):
            self.name = name

        def stable_key(self):
            return ("fragment", self.name)

    count_from_guard_a = Expression.parameter(
        "count",
        index=1,
        data_type="int",
        size=4,
        runtime_ref=FragmentRuntimeRef("guard_a"),
    )
    count_from_guard_b = Expression.parameter(
        "count",
        index=1,
        data_type="int",
        size=4,
        runtime_ref=FragmentRuntimeRef("guard_b"),
    )
    analysis = _analysis(
        "fragmented_parameter_identity_partition",
        [
            ReturnInfo(
                address="0x1000",
                value=_const(7),
                conditions=[
                    Condition(
                        Expression.binary_op(
                            "INT_SLESS",
                            Expression.constant(0, size=4),
                            count_from_guard_a,
                        )
                    )
                ],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(7),
                conditions=[
                    Condition(
                        Expression.binary_op(
                            "INT_SLESS",
                            count_from_guard_b,
                            Expression.constant(1, size=4),
                        )
                    )
                ],
            ),
        ],
    )
    cases = extract_return_cases(analysis)
    strategy = _pairwise_strategy()

    assert strategy._return_cases_have_object_centric_total_coverage(cases)


def test_object_centric_coverage_falls_back_to_legacy_query_on_solver_inconclusive(monkeypatch):
    p = Expression.parameter(
        "count",
        index=0,
        size=4,
        runtime_ref=LocationBaseRef.parameter("count", index=0),
    )
    analysis = _analysis(
        "object_identity_safe_but_solver_inconclusive",
        [ReturnInfo(address="0x1000", value=_const(7), conditions=[Condition(Expression.binary_op("INT_NOTEQUAL", p, _const(0)) )])],
    )
    cases = extract_return_cases(analysis)
    strategy = _pairwise_strategy()
    strategy._build_return_case_coverage_query = Mock(return_value="(check-sat)")
    strategy.solver_runner = Mock()
    strategy.solver_runner.run_sequential = Mock(
        return_value=Mock(is_equivalent=None, get_counterexample=Mock(return_value=None))
    )
    strategy.formula_builder = Mock()

    monkeypatch.setattr(
        "scripts.function_tracer_pcode.analysis.condition.smt_oracle.ConditionSMTOracle.conjunction_is_unsat",
        lambda conditions, cache_key=None: None,
    )

    result = strategy._check_return_case_coverage_gap(
        {
            "header_lines": ["(set-logic QF_AUFBV)"],
            "params1": [],
            "params2": [],
            "extra_vars1": [],
            "extra_vars2": [],
            "constrained_fragments": [],
        },
        cases,
        lambda expr: expr.to_smt(),
        "function1",
    )

    assert result.status == "inconclusive"
    assert result.detail == "function1 return-case coverage query was inconclusive"
    strategy._build_return_case_coverage_query.assert_called_once()
    strategy.solver_runner.run_sequential.assert_called_once()


def test_object_centric_identity_unsafe_keeps_object_coverage_path_inconclusive():
    p = Expression.parameter("count", size=4)
    analysis = _analysis(
        "object_identity_unsafe",
        [ReturnInfo(address="0x1000", value=_const(7), conditions=[Condition(Expression.binary_op("INT_NOTEQUAL", p, _const(0)) )])],
    )
    cases = extract_return_cases(analysis)
    strategy = _pairwise_strategy()
    strategy._build_return_case_coverage_query = Mock(
        side_effect=AssertionError("legacy coverage query must not be used when object identity is unsafe")
    )

    result = strategy._check_return_case_coverage_gap(
        {
            "header_lines": ["(set-logic QF_AUFBV)"],
            "params1": [],
            "params2": [],
            "extra_vars1": [],
            "extra_vars2": [],
            "constrained_fragments": [],
        },
        cases,
        lambda expr: expr.to_smt(),
        "function1",
    )

    assert result.status == "inconclusive"
    assert result.detail == "function1 return-case object-centric coverage check was inconclusive"
    strategy._build_return_case_coverage_query.assert_not_called()


def test_object_centric_coverage_gap_uses_rendered_query_before_reporting_gap():
    analysis = _analysis(
        "object_centric_gap",
        [
            ReturnInfo(
                address="0x1000",
                value=_const(7),
                conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), _count_param()))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(7),
                conditions=[Condition(Expression.binary_op("INT_SLESS", _count_param(), _const(0)))],
            ),
        ],
    )
    cases = extract_return_cases(analysis)
    strategy = _pairwise_strategy()
    strategy._build_return_case_coverage_query = Mock(return_value="(check-sat)")
    strategy.solver_runner = Mock()
    strategy.solver_runner.run_sequential = Mock(
        return_value=Mock(is_equivalent=False, get_counterexample=Mock(return_value={"count": 0}))
    )
    result = strategy._check_return_case_coverage_gap(
        {
            "header_lines": [
                "(set-logic QF_AUFBV)",
                "; function1:param_1 is assumed non-NaN",
            ],
            "params1": [],
            "params2": [],
            "extra_vars1": [],
            "extra_vars2": [],
            "constrained_fragments": [],
            "return_coverage_domain_assumptions": {"fp_non_nan": True},
        },
        cases,
        lambda expr: expr.to_smt(),
        "function1",
    )

    assert result.status == "gap"
    assert result.detail == "function1 has uncovered return-condition region under model {'count': 0}"
    strategy._build_return_case_coverage_query.assert_called_once()
    strategy.solver_runner.run_sequential.assert_called_once()


def test_object_centric_coverage_gap_without_domain_assumptions_is_used_directly():
    analysis = _analysis(
        "object_centric_gap_without_domain_assumptions",
        [
            ReturnInfo(
                address="0x1000",
                value=_const(7),
                conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), _count_param()))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(7),
                conditions=[Condition(Expression.binary_op("INT_SLESS", _count_param(), _const(0)))],
            ),
        ],
    )
    cases = extract_return_cases(analysis)
    strategy = _pairwise_strategy()
    strategy._build_return_case_coverage_query = Mock(
        side_effect=AssertionError("gap without domain assumptions must not fall through to SMT query")
    )

    result = strategy._check_return_case_coverage_gap(
        {
            "header_lines": ["(set-logic QF_AUFBV)"],
            "params1": [],
            "params2": [],
            "extra_vars1": [],
            "extra_vars2": [],
            "constrained_fragments": [],
        },
        cases,
        lambda expr: expr.to_smt(),
        "function1",
    )

    assert result.status == "gap"
    assert result.detail == "function1 object-centric return-case coverage check found uncovered region"
    strategy._build_return_case_coverage_query.assert_not_called()


def test_object_centric_coverage_gap_comment_only_does_not_enable_domain_fallback():
    analysis = _analysis(
        "object_centric_gap_comment_only",
        [
            ReturnInfo(
                address="0x1000",
                value=_const(7),
                conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), _count_param()))],
            ),
            ReturnInfo(
                address="0x1004",
                value=_const(7),
                conditions=[Condition(Expression.binary_op("INT_SLESS", _count_param(), _const(0)))],
            ),
        ],
    )
    cases = extract_return_cases(analysis)
    strategy = _pairwise_strategy()
    strategy._build_return_case_coverage_query = Mock(
        side_effect=AssertionError("comment-only domain marker must not fall through to SMT query")
    )

    result = strategy._check_return_case_coverage_gap(
        {
            "header_lines": [
                "(set-logic QF_AUFBV)",
                "; function1:param_1 is assumed non-NaN",
            ],
            "params1": [],
            "params2": [],
            "extra_vars1": [],
            "extra_vars2": [],
            "constrained_fragments": [],
        },
        cases,
        lambda expr: expr.to_smt(),
        "function1",
    )

    assert result.status == "gap"
    assert result.detail == "function1 object-centric return-case coverage check found uncovered region"
    strategy._build_return_case_coverage_query.assert_not_called()


def test_object_centric_coverage_gap_can_be_discharged_by_active_smt_assumptions():
    analysis = _analysis(
        "object_centric_gap_discharged",
        [
            ReturnInfo(
                address="0x1000",
                value=_const(7),
                conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0), _count_param()))],
            ),
        ],
    )
    cases = extract_return_cases(analysis)
    strategy = _pairwise_strategy()
    strategy._build_return_case_coverage_query = Mock(
        return_value="\n".join(
            [
                "(set-logic QF_BV)",
                "(declare-const count (_ BitVec 32))",
                "(assert (bvsgt count (_ bv0 32)))",
                "(assert (not (bvsgt count (_ bv0 32))))",
                "(check-sat)",
            ]
        )
    )
    strategy.solver_runner = Mock()
    strategy.solver_runner.run_sequential = Mock(
        return_value=Mock(is_equivalent=True, get_counterexample=Mock(return_value=None))
    )

    result = strategy._check_return_case_coverage_gap(
        {
            "header_lines": [
                "(set-logic QF_BV)",
                "(declare-const count (_ BitVec 32))",
                "; function1:param_1 is assumed non-NaN",
                "(assert (not (fp.isNaN ((_ to_fp 11 53) param_1))))",
                "(assert (bvsgt count (_ bv0 32)))",
            ],
            "params1": [],
            "params2": [],
            "extra_vars1": [],
            "extra_vars2": [],
            "constrained_fragments": [],
            "return_coverage_domain_assumptions": {"fp_non_nan": True},
        },
        cases,
        lambda expr: expr.to_smt(),
        "function1",
    )

    assert result.status == "covered"
    strategy._build_return_case_coverage_query.assert_called_once()
    strategy.solver_runner.run_sequential.assert_called_once()



def _path_sensitive_readonly_ref(proof: ReductionAccumulatorProof) -> ReadonlyReductionRef:
    reduction_ref = proof.to_readonly_reduction_ref()
    assert reduction_ref is not None
    assert reduction_ref.loop_summary is not None
    path_sensitive_summary = replace(
        reduction_ref.loop_summary,
        cases=(
            LoopCaseRef(
                path_conditions=("object_level_path_split",),
                body_effect=LoopBodyEffectRef(
                    kind="accumulator_update",
                    value_expr=("accumulator", "plus", "readonly_term"),
                ),
                term_expr=("readonly_term",),
                case_kind="accumulator_delta",
            ),
        ),
    )
    return replace(reduction_ref, loop_summary=path_sensitive_summary)


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


def _triangular_closed_form(*, inclusive: bool = False) -> Expression:
    n64 = Expression.unary_op("INT_ZEXT", _count_param())
    n64.size = 8
    neighbor = Expression.binary_op(
        "INT_ADD" if inclusive else "INT_SUB",
        n64,
        Expression.constant(1, size=8),
    )
    product = Expression.binary_op("INT_MULT", n64, neighbor)
    half = Expression.binary_op("INT_RIGHT", product, Expression.constant(1, size=8))
    low = Expression.binary_op("SUBPIECE", half, Expression.constant(0, size=4))
    low.size = 4
    return low


def _pure_counted_summary_with_guard() -> LoopSummaryRef:
    return LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=_count_param(),
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(kind="affine_residue"),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(_count_gt(0),),
        loop_var_unit="element_index",
    )


def _analysis(function_name: str, returns, *, comparison_bits: int = 32) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name=function_name,
        entry_point="0x1000",
        parameters=[
            {"name": "base", "index": 0, "data_type": "int *", "size": 8, "is_signed": False},
            {"name": "count", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        returns=list(returns),
        return_type="int",
        comparison_surface=ComparisonSurface(
            kind="return_value",
            explicit_bit_width=int(comparison_bits),
            type_name="int",
        ),
    )


def test_vectorized_affine_counter_descriptor_storage_is_normalized_for_matching():
    summarizer = StructuralRecurrenceSummarizer(Mock())
    storage = {
        "is_register": True,
        "space_name": "register",
        "offset": 16384,
        "size": 4,
        "size_bits": 32,
        "register_name": "w0",
        "base_register_name": "x0",
        "base_register_size": 8,
        "base_register_size_bits": 64,
        "bit_offset_in_base": 0,
    }
    descriptor = {
        "name": "param_1",
        "index": 0,
        "data_type": "int",
        "size": 4,
        "storage_info": storage,
    }
    candidate = summarizer._parameter_expression(descriptor)

    assert isinstance(candidate.storage_info, StorageInfo)
    assert summarizer._counter_parameter_candidate_matches_descriptor(candidate, descriptor)


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


def _stub_pair_solver_unsat(strategy: PairwiseStrategy) -> None:
    result = SolverResult("mock", SolverStatus.UNSAT, elapsed_time=0.0)
    strategy.solver_runner.run_sequential = Mock(return_value=ParallelResult([result]))


def _shared_input_base_context() -> dict:
    return {
        "header_lines": [
            "(set-logic QF_BV)",
            "(declare-const base_1 (_ BitVec 64))",
            "(declare-const count_1 (_ BitVec 32))",
            "(declare-const base_2 (_ BitVec 64))",
            "(declare-const count_2 (_ BitVec 32))",
            "(assert (= base_1 base_2))",
            "(assert (= count_1 count_2))",
        ],
        "params1": [
            ParameterInfo("base", "base_1", 64, 0, is_signed=False),
            ParameterInfo("count", "count_1", 32, 1, is_signed=True),
        ],
        "params2": [
            ParameterInfo("base", "base_2", 64, 0, is_signed=False),
            ParameterInfo("count", "count_2", 32, 1, is_signed=True),
        ],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }


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

    left_analysis = _analysis("ptr_sum_window_full", _branch_returns(full))
    right_analysis = _analysis("ptr_sum_window_tail", _branch_returns(tail))
    result = strategy.check(left_analysis, right_analysis)

    assert result.is_equivalent is None
    assert result.total_pairs == 16
    assert result.unsat_pairs == 16
    assert result.unknown_pairs == 0
    assert "return_case_coverage_gap" in left_analysis.analysis_notes
    assert "return_case_coverage_gap" in right_analysis.analysis_notes
    strategy.solver_runner.run_sequential.assert_not_called()


def test_readonly_runtime_shortcut_requires_case_guard_equivalence():
    summary = _readonly_summary(start=0, guard_constraints=("0 < count",))
    value = _readonly_sum(summary)
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("left", [ReturnInfo(address="0x1000", value=value, conditions=[_count_gt(3)])]),
        _analysis("right", [ReturnInfo(address="0x2000", value=value, conditions=[_count_gt(4)])]),
    )

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    strategy.solver_runner.run_sequential.assert_not_called()


def test_loop_shape_mismatch_unreachable_under_shared_inputs_is_not_unknown():
    summary_value = _readonly_sum(_readonly_summary(start=0))
    constant_value = Expression.constant(0xFFFFFECA, size=4)
    strategy = _pairwise_strategy()
    strategy.formula_builder.build_base_context.return_value = _shared_input_base_context()

    result = strategy.check(
        _analysis(
            "summary_nonzero_base",
            [ReturnInfo(address="0x1100", value=summary_value, conditions=[_base_ne_zero(), _count_gt(0)])],
        ),
        _analysis(
            "constant_zero_base",
            [ReturnInfo(address="0x1200", value=constant_value, conditions=[_base_eq_zero()])],
        ),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    assert all(
        reason.reason_id != UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value
        for reason in result.unknown_reasons
    )
    strategy.solver_runner.run_sequential.assert_not_called()


def test_summary_guard_delta_is_closed_by_exact_return_partition():
    count_expr = _count_param()
    exact_count4 = _sum_expr(
        _load_term_expr(0),
        _load_term_expr(1),
        _load_term_expr(2),
        _load_term_expr(3),
    )
    tail_proof = ReductionAccumulatorProof(
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
        guard_constraints=(_count_gt(4),),
        signed_counter=True,
    )
    full_proof = ReductionAccumulatorProof(
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
        guard_constraints=(_count_gt(3),),
        signed_counter=True,
    )
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis(
            "tail_with_exact_count4",
            [
                ReturnInfo(address="0x1014", value=exact_count4, conditions=[_eq_count(4)]),
                ReturnInfo(address="0x1018", value=_readonly_sum_from_proof(tail_proof), conditions=[_count_gt(4)]),
            ],
        ),
        _analysis(
            "full_summary_from_count4",
            [
                ReturnInfo(address="0x2014", value=_readonly_sum_from_proof(full_proof), conditions=[_count_gt(3)]),
            ],
        ),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 2
    assert result.unsat_pairs == 2
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_summary_guard_delta_uses_proof_backed_term_contract_without_exact_partition():
    count_expr = _count_param()
    tail_proof = ReductionAccumulatorProof(
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
        guard_constraints=(_count_gt(4),),
        signed_counter=True,
    )
    full_proof = ReductionAccumulatorProof(
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
        guard_constraints=(_count_gt(3),),
        signed_counter=True,
    )
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis(
            "tail_without_exact_count4",
            [ReturnInfo(address="0x1028", value=_readonly_sum_from_proof(tail_proof), conditions=[_count_gt(4)])],
        ),
        _analysis(
            "full_summary_without_exact_cover",
            [ReturnInfo(address="0x2028", value=_readonly_sum_from_proof(full_proof), conditions=[_count_gt(3)])],
        ),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
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

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_exact_prefix_return_matches_storage_backed_count_identity():
    count_storage = StorageInfo(
        is_register=True,
        space_name="register",
        register_name="a1",
        base_register_name="a1",
        size=4,
        size_bits=32,
    )
    storage_count = Expression.parameter(
        "renamed_count",
        data_type="int",
        size=4,
        storage_info=count_storage,
    )
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="renamed_count",
        count_parameter_index=None,
        count_parameter_storage_identity_key=count_storage.storage_identity_key(),
        limit_expr=storage_count,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        index_step=1,
        index_scale=4,
        seed_terms=(_term(0), _term(4), _term(8)),
    )
    exact = _sum_expr(_load_term_expr(0), _load_term_expr(1), _load_term_expr(2))
    summarized = Expression.intrinsic(
        "READONLY_SUM",
        [_base_param(), storage_count],
        size=4,
        runtime_ref=proof.to_readonly_reduction_ref(),
        opcode=READONLY_SUM_OPCODE,
    )
    parameters = [
        {"name": "base", "index": 0, "data_type": "int *", "size": 8, "is_signed": False},
        {
            "name": "renamed_count",
            "data_type": "int",
            "size": 4,
            "is_signed": True,
            "storage_info": count_storage,
        },
    ]
    exact_condition = Condition(
        Expression.binary_op("INT_EQUAL", storage_count, Expression.constant(3, size=4))
    )
    summary_condition = Condition(
        Expression.binary_op("INT_SLESS", Expression.constant(0, size=4), storage_count)
    )
    exact_case = ReturnCase(
        0,
        [exact_condition],
        exact,
        ReturnInfo(address="0x1100", value=exact, conditions=[exact_condition]),
        parameters=parameters,
    )
    summary_case = ReturnCase(
        0,
        [summary_condition],
        summarized,
        ReturnInfo(address="0x1200", value=summarized, conditions=[summary_condition]),
        parameters=parameters,
    )

    assert _pairwise_strategy()._exact_value_matches_readonly_reduction_proof(exact_case, summary_case)


def test_exact_prefix_return_matches_loop_summary_without_accumulator_proof():
    exact = _sum_expr(
        _load_term_expr(0),
        _load_term_expr(1),
        _load_term_expr(2),
        _load_term_expr(3),
    )
    summary = _readonly_sum(
        _readonly_summary(
            start=3,
            seed_terms=(_term(0), _term(4), _term(8)),
        )
    )
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("exact_count4", [ReturnInfo(address="0x1300", value=exact, conditions=[_eq_count(4)])]),
        _analysis("summary_count4", [ReturnInfo(address="0x1400", value=summary, conditions=[_eq_count(4)])]),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_exact_prefix_return_does_not_close_path_sensitive_loop_summary_without_proof():
    exact = _sum_expr(
        _load_term_expr(0),
        _load_term_expr(1),
        _load_term_expr(2),
        _load_term_expr(3),
    )
    path_sensitive_summary = replace(
        _readonly_summary(
            start=3,
            seed_terms=(_term(0), _term(4), _term(8)),
        ),
        cases=(
            LoopCaseRef(
                path_conditions=("path_split",),
                body_effect=LoopBodyEffectRef(
                    kind="accumulator_update",
                    value_expr=("accumulator", "plus", "term"),
                ),
                term_expr=("term",),
            ),
        ),
    )
    summary = _readonly_sum(path_sensitive_summary)
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("exact_count4", [ReturnInfo(address="0x1310", value=exact, conditions=[_eq_count(4)])]),
        _analysis("path_sensitive_summary_count4", [ReturnInfo(address="0x1410", value=summary, conditions=[_eq_count(4)])]),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 0
    assert result.unknown_pairs == 1
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.METHOD_B_CLOSURE_BLOCKED.value
    strategy.solver_runner.run_sequential.assert_not_called()


def test_readonly_identity_mismatch_emits_typed_recovery_reason():
    left = _readonly_sum(_readonly_summary(start=0))
    right = _readonly_sum_from_ref(replace(left.runtime_ref, count_parameter_index=2))
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("readonly_left", [ReturnInfo(address="0x1500", value=left, conditions=[])]),
        _analysis("readonly_right", [ReturnInfo(address="0x1600", value=right, conditions=[])]),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unknown_pairs == 1
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.READONLY_IDENTITY_MISSING.value
    assert reason.recovery_proof_obligations
    assert reason.object_target_key[0] == "readonly_identity"
    assert reason.object_target_key[1] == ("pair", "(0,0)")
    assert not any(
        isinstance(item, tuple) and item[:1] == ("reason",)
        for item in reason.object_target_key
    )
    assert reason.object_target_key[2][0] == "readonly_identity_side"
    assert reason.object_target_key[3][0] == "readonly_identity_side"
    assert reason.evidence_kind == "object_storage_identity"
    assert reason.proof_obligation_id == build_proof_obligation_id(
        "readonly_identity_missing",
        "readonly_operand_identity",
        "storage_backed_identity_propagation",
        "object_storage_identity",
        reason.object_target_key,
    )
    actions = build_unknown_recovery_actions(result.unknown_reasons)
    assert len(actions) == 1
    assert actions[0].status == "planned"
    assert actions[0].object_target_key == reason.object_target_key
    assert actions[0].proof_obligation_id == reason.proof_obligation_id
    strategy.solver_runner.run_sequential.assert_not_called()


def test_readonly_identity_proof_target_distinguishes_count_identity():
    left = _readonly_sum(_readonly_summary(start=0))
    right_count2 = _readonly_sum_from_ref(replace(left.runtime_ref, count_parameter_index=2))
    right_count3 = _readonly_sum_from_ref(replace(left.runtime_ref, count_parameter_index=3))
    strategy = _pairwise_strategy()

    result_count2 = strategy.check(
        _analysis("readonly_left", [ReturnInfo(address="0x1500", value=left, conditions=[])]),
        _analysis("readonly_right", [ReturnInfo(address="0x1600", value=right_count2, conditions=[])]),
    )
    result_count3 = strategy.check(
        _analysis("readonly_left", [ReturnInfo(address="0x1500", value=left, conditions=[])]),
        _analysis("readonly_right", [ReturnInfo(address="0x1600", value=right_count3, conditions=[])]),
    )

    reason_count2 = result_count2.unknown_reasons[0]
    reason_count3 = result_count3.unknown_reasons[0]
    assert reason_count2.object_target_key != reason_count3.object_target_key
    assert reason_count2.proof_obligation_id != reason_count3.proof_obligation_id


def test_exact_prefix_return_matches_wide_abi_summary_count_by_active_parameter_width():
    wide_count_expr = Expression.parameter("count", index=1, data_type="long", size=8)
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=wide_count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=0,
        start_index=0,
        index_step=1,
        index_scale=4,
    ).with_runtime_evidence(
        limit_expr=wide_count_expr,
        result_size=4,
        loop_body_witnesses=(
            ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),
            ReadonlyReductionWitness(exact_count=2, terms=(_term(0), _term(4))),
            ReadonlyReductionWitness(exact_count=3, terms=(_term(0), _term(4), _term(8))),
        ),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    exact = _sum_expr(_load_term_expr(0), _load_term_expr(1), _load_term_expr(2))
    summarized = _readonly_sum_from_proof(proof)
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("exact_prefix_32bit_guard", [ReturnInfo(address="0x1100", value=exact, conditions=[_eq_count(3)])]),
        _analysis("summary_prefix_64bit_abi_count", [ReturnInfo(address="0x1200", value=summarized, conditions=[_count_gt(0)])]),
    )

    assert result.is_equivalent is None
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

    assert result.is_equivalent is None
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

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_affine_exact_tail_entry_condition_matches_non_prefix_readonly_reduction_proof():
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
        seed_terms=(_term(0), _term(8)),
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(3),),
        signed_counter=True,
    )
    exact = _sum_expr(_load_term_expr(0), _load_term_expr(2), _load_term_expr(3))
    summarized = _readonly_sum_from_proof(proof)
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis(
            "affine_exact_wrong_tail",
            [ReturnInfo(address="0x1270", value=exact, conditions=[_count_gt(3), _affine_eq_count(4)])],
        ),
        _analysis(
            "summary_wrong_tail",
            [ReturnInfo(address="0x1280", value=summarized, conditions=[_count_gt(3)])],
        ),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_ptradd_guarded_exact_wrong_tail_matches_seeded_readonly_summary():
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
        seed_terms=(_term(0), _term(8)),
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(3),),
        signed_counter=True,
    )
    exact = _sum_expr(_load_term_expr(0), _load_term_expr(2), _load_term_expr(3))
    summarized = _readonly_sum_from_proof(proof)
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis(
            "ptradd_exact_wrong_tail",
            [ReturnInfo(address="0x1270", value=exact, conditions=[_count_gt(3), _ptradd_guard_eq_count(4)])],
        ),
        _analysis(
            "summary_wrong_tail",
            [ReturnInfo(address="0x1280", value=summarized, conditions=[_count_gt(3)])],
        ),
    )

    assert result.is_equivalent is None
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

    assert result.is_equivalent is None
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

    assert result.is_equivalent is None
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


def test_exact_load_sum_proof_uses_readonly_reduction_ref_not_intrinsic_name():
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

    assert strategy._exact_value_matches_readonly_reduction_proof(exact_case, summary_case)


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

    assert result.is_equivalent is None
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


def test_pairwise_exact_load_matcher_uses_known_endianness_for_vector_lanes():
    strategy = _pairwise_strategy()
    base_plus_three = Expression.intrinsic(
        "PTRADD",
        [_base_param(), Expression.constant(3, size=8), Expression.constant(4, size=8)],
        size=8,
    )
    wide_load = Expression.memory(base_plus_three, size=8)
    low_lane = Expression.binary_op("SUBPIECE", wide_load, Expression.constant(0, size=4))
    low_lane.size = 4
    high_lane_shift = Expression.binary_op("INT_RIGHT", wide_load, Expression.constant(32, size=4))
    high_lane_shift.size = 8
    high_lane = Expression.binary_op("SUBPIECE", high_lane_shift, Expression.constant(0, size=4))
    high_lane.size = 4
    summed = Expression.binary_op("INT_ADD", low_lane, high_lane)
    params = [
        {"name": "base", "index": 0, "data_type": "int *", "size": 8, "is_signed": False},
        {"name": "count", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]

    little_terms = strategy._extract_readonly_reduction_terms_from_expression(
        summed,
        params,
        LocationBaseRef.parameter("base", index=0),
        program_is_big_endian=False,
    )
    big_terms = strategy._extract_readonly_reduction_terms_from_expression(
        summed,
        params,
        LocationBaseRef.parameter("base", index=0),
        program_is_big_endian=True,
    )

    assert tuple((term.byte_offset, term.access_size) for term in little_terms) == ((12, 4), (16, 4))
    assert tuple((term.byte_offset, term.access_size) for term in big_terms) == ((12, 4), (16, 4))


def test_summary_guard_equivalence_uses_smt_set_implication_not_condition_shape():
    strategy = _pairwise_strategy()
    left_info = ReturnInfo(
        address="0x1900",
        value=_readonly_sum(_readonly_summary(start=4)),
        conditions=[_count_gt(3)],
    )
    right_guard = Condition(
        Expression.binary_op("INT_SLESS", _count_param(), Expression.constant(4, size=4)),
        negated=True,
    )
    right_info = ReturnInfo(
        address="0x1904",
        value=_readonly_sum(_readonly_summary(start=4)),
        conditions=[right_guard],
    )
    left_case = ReturnCase(
        0,
        list(left_info.conditions),
        left_info.value,
        left_info,
        parameters=_analysis("left_guard", [left_info]).parameters,
    )
    right_case = ReturnCase(
        0,
        list(right_info.conditions),
        right_info.value,
        right_info,
        parameters=_analysis("right_guard", [right_info]).parameters,
    )

    assert strategy._cases_have_equivalent_summary_conditions(left_case, right_case)


def test_exact_load_can_match_any_readonly_reduction_ref_not_only_readonly_sum_name():
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=_count_param(),
        result_size=4,
        stride=4,
        element_size=4,
    ).with_runtime_evidence(
        limit_expr=_count_param(),
        result_size=4,
        loop_body_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
        exact_return_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    runtime_ref = proof.to_readonly_reduction_ref()
    assert runtime_ref is not None
    summary_value = Expression.intrinsic(
        "OBJECT_SUMMARY",
        [_base_param(), _count_param()],
        size=4,
        runtime_ref=runtime_ref,
    )
    exact_info = ReturnInfo(address="0x1910", value=_load_term_expr(0), conditions=[_eq_count(1)])
    summary_info = ReturnInfo(address="0x1914", value=summary_value, conditions=[_count_gt(0)])
    exact_case = ReturnCase(
        0,
        list(exact_info.conditions),
        exact_info.value,
        exact_info,
        parameters=_analysis("exact_runtime_ref", [exact_info]).parameters,
    )
    summary_case = ReturnCase(
        0,
        list(summary_info.conditions),
        summary_info.value,
        summary_info,
        parameters=_analysis("summary_runtime_ref", [summary_info]).parameters,
    )

    assert _pairwise_strategy()._exact_value_matches_readonly_reduction_proof(exact_case, summary_case)


def test_readonly_loop_contract_uses_object_semantics_before_intrinsic_surface():
    proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=_count_param(),
        result_size=4,
        stride=4,
        element_size=4,
    ).with_runtime_evidence(
        limit_expr=_count_param(),
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(0),),
        signed_counter=True,
    )
    proof_ref = proof.to_readonly_reduction_ref()
    summary_ref = _readonly_sum(_readonly_summary(start=0)).runtime_ref
    assert proof_ref is not None
    assert summary_ref is not None
    proof_backed_value = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_count_param(), _base_param()],
        size=4,
        runtime_ref=proof_ref,
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    summary_only_value = Expression.intrinsic(
        "READONLY_SUM_ALIAS",
        [_base_param(), _count_param()],
        size=4,
        runtime_ref=summary_ref,
        opcode=READONLY_SUM_OPCODE,
    )
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis(
            "proof_backed_readonly_contract",
            [ReturnInfo(address="0x1920", value=proof_backed_value, conditions=[_count_gt(0)])],
        ),
        _analysis(
            "summary_only_readonly_contract",
            [ReturnInfo(address="0x1924", value=summary_only_value, conditions=[_count_gt(0)])],
        ),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_readonly_loop_contract_uses_guard_coverage_when_surface_differs():
    left_value = _readonly_sum(_readonly_summary(start=0))
    right_value = Expression.intrinsic(
        "READONLY_SUM_ALIAS",
        [_base_param(), _count_param()],
        size=4,
        runtime_ref=left_value.runtime_ref,
        opcode=READONLY_SUM_OPCODE,
    )
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("left_guard_contract", [ReturnInfo(address="0x1930", value=left_value, conditions=[_count_gt(3)])]),
        _analysis("right_guard_contract", [ReturnInfo(address="0x1934", value=right_value, conditions=[_count_gt(4)])]),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_path_sensitive_readonly_loop_contract_uses_accumulator_proof_terms():
    count_expr = _count_param()
    left_proof = ReductionAccumulatorProof(
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
        seed_terms=(_term(0), _term(8)),
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(3),),
        signed_counter=True,
    )
    right_proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=8,
        start_index=2,
        index_step=1,
        index_scale=4,
        seed_terms=(_term(0),),
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(3),),
        signed_counter=True,
    )
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis(
            "path_sensitive_tail_seed02",
            [
                ReturnInfo(
                    address="0x1940",
                    value=_readonly_sum_from_ref(_path_sensitive_readonly_ref(left_proof)),
                    conditions=[_count_gt(3)],
                )
            ],
        ),
        _analysis(
            "path_sensitive_canonical_seed0_start2",
            [
                ReturnInfo(
                    address="0x1944",
                    value=_readonly_sum_from_ref(_path_sensitive_readonly_ref(right_proof)),
                    conditions=[_count_gt(3)],
                )
            ],
        ),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_path_sensitive_readonly_loop_contract_keeps_seed_mismatch_unknown():
    count_expr = _count_param()
    left_proof = ReductionAccumulatorProof(
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
        seed_terms=(_term(0), _term(8)),
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(3),),
        signed_counter=True,
    )
    right_proof = ReductionAccumulatorProof(
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
        guard_constraints=(_count_gt(3),),
        signed_counter=True,
    )
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis(
            "path_sensitive_wrong_tail",
            [
                ReturnInfo(
                    address="0x1950",
                    value=_readonly_sum_from_ref(_path_sensitive_readonly_ref(left_proof)),
                    conditions=[_count_gt(3)],
                )
            ],
        ),
        _analysis(
            "path_sensitive_full_prefix_tail",
            [
                ReturnInfo(
                    address="0x1954",
                    value=_readonly_sum_from_ref(_path_sensitive_readonly_ref(right_proof)),
                    conditions=[_count_gt(3)],
                )
            ],
        ),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 0
    assert result.unknown_pairs == 1
    strategy.solver_runner.run_sequential.assert_not_called()


def test_readonly_loop_contract_rejects_mismatched_return_width_without_bridge():
    count_expr = _count_param()
    wide_proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=8,
        stride=4,
        element_size=4,
        start_offset=12,
        start_index=3,
        index_step=1,
        index_scale=4,
        seed_terms=(_term(0), _term(8)),
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=8,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(3),),
        signed_counter=True,
    )
    narrow_proof = ReductionAccumulatorProof(
        reduction_kind="memory_sum",
        pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count",
        count_parameter_index=1,
        limit_expr=count_expr,
        result_size=4,
        stride=4,
        element_size=4,
        start_offset=8,
        start_index=2,
        index_step=1,
        index_scale=4,
        seed_terms=(_term(0),),
    ).with_runtime_evidence(
        limit_expr=count_expr,
        result_size=4,
        loop_body_witnesses=(),
        exact_return_witnesses=(),
        guard_constraints=(_count_gt(3),),
        signed_counter=True,
    )
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis(
            "wide_accumulator_wrong_tail",
            [ReturnInfo(address="0x1960", value=_readonly_sum_from_proof(wide_proof), conditions=[_count_gt(3)])],
            comparison_bits=64,
        ),
        _analysis(
            "narrow_accumulator_wrong_tail",
            [ReturnInfo(address="0x1964", value=_readonly_sum_from_proof(narrow_proof), conditions=[_count_gt(3)])],
            comparison_bits=32,
        ),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 0
    assert result.unknown_pairs == 1
    strategy.solver_runner.run_sequential.assert_not_called()


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

    assert result.is_equivalent is None
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


def test_pure_counted_loop_without_runtime_summary_guards_can_be_closed_by_method_b():
    left_value = _counted_loop(_pure_counted_summary())
    right_value = _counted_loop(_pure_counted_summary())
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("pure_counted_no_runtime_guard_left", [ReturnInfo(address="0x7000", value=left_value, conditions=[_count_gt(0)])]),
        _analysis("pure_counted_no_runtime_guard_right", [ReturnInfo(address="0x7004", value=right_value, conditions=[_count_gt(0)])]),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_counted_loop_summary_vs_closed_form_is_discharged_by_smt():
    counted_value = _counted_loop(_pure_counted_summary_with_guard())
    closed_form = _triangular_closed_form()
    non_positive = _count_gt(0).negate()
    strategy = _pairwise_strategy()
    _stub_pair_solver_unsat(strategy)

    result = strategy.check(
        _analysis(
            "barthe_like_counted_summary",
            [
                ReturnInfo(address="0x7300", value=counted_value, conditions=[_count_gt(0)]),
                ReturnInfo(address="0x7308", value=Expression.constant(0, size=4), conditions=[non_positive]),
            ],
        ),
        _analysis(
            "barthe_like_closed_form",
            [
                ReturnInfo(address="0x7304", value=closed_form, conditions=[_count_gt(0)]),
                ReturnInfo(address="0x730c", value=Expression.constant(0, size=4), conditions=[non_positive]),
            ],
        ),
    )

    assert result.is_equivalent is True
    assert result.total_pairs == 4
    assert result.unsat_pairs == 4
    assert result.unknown_pairs == 0


def test_counted_loop_summary_vs_shifted_affine_parameter_closed_form_is_discharged():
    n = Expression.parameter("param_1", index=0, data_type="int", size=4)
    c = Expression.parameter("param_2", index=1, data_type="int", size=4)
    zero = Expression.constant(0, size=4)
    positive = Condition(Expression.binary_op("INT_SLESS", zero, n))
    non_positive = positive.negate()
    summary = LoopSummaryRef(
        start_expr=zero,
        limit_expr=n,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(
            kind="affine_residue",
            residue_cases=((1, 0, 5, 0),),
            residue_bias_terms=((1, 0, c),),
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(positive,),
        loop_var_unit="induction_value",
    )
    counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, zero, n],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 5, 0),),
            residue_bias_terms=((1, 0, c),),
            loop_summary=summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    n_minus_one = Expression.binary_op("INT_SUB", n, Expression.constant(1, size=4))
    n_minus_one.size = 4
    n_minus_two = Expression.binary_op("INT_SUB", n, Expression.constant(2, size=4))
    n_minus_two.size = 4
    wide_n_minus_one = Expression.unary_op("INT_ZEXT", n_minus_one)
    wide_n_minus_one.size = 8
    wide_n_minus_two = Expression.unary_op("INT_ZEXT", n_minus_two)
    wide_n_minus_two.size = 8
    shifted_half = Expression.binary_op(
        "INT_RIGHT",
        Expression.binary_op("INT_MULT", wide_n_minus_one, wide_n_minus_two),
        Expression.constant(1, size=8),
    )
    shifted_low = Expression.binary_op("SUBPIECE", shifted_half, Expression.constant(0, size=4))
    shifted_low.size = 4
    closed = Expression.binary_op(
        "INT_ADD",
        Expression.binary_op(
            "INT_ADD",
            c,
            Expression.binary_op(
                "INT_MULT",
                n_minus_one,
                Expression.binary_op("INT_ADD", c, Expression.constant(5, size=4)),
            ),
        ),
        Expression.binary_op("INT_MULT", shifted_low, Expression.constant(5, size=4)),
    )
    closed.size = 4
    analysis_left = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        returns=[
            ReturnInfo(address="0x1000", value=counted, conditions=[positive]),
            ReturnInfo(address="0x1004", value=Expression.constant(0, size=4), conditions=[non_positive]),
        ],
        return_type="int",
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    analysis_right = replace(
        analysis_left,
        function_name="right",
        returns=[
            ReturnInfo(address="0x2000", value=closed, conditions=[positive]),
            ReturnInfo(address="0x2004", value=Expression.constant(0, size=4), conditions=[non_positive]),
        ],
    )
    strategy = _pairwise_strategy()
    _stub_pair_solver_unsat(strategy)

    result = strategy.check(analysis_left, analysis_right)

    assert result.is_equivalent is True
    assert result.total_pairs == 4
    assert result.unsat_pairs == 4
    assert result.unknown_pairs == 0


def test_counted_loop_summary_vs_nonzero_start_step3_closed_form_is_discharged():
    n = Expression.parameter("param_1", index=0, data_type="int", size=4)
    c = Expression.parameter("param_2", index=1, data_type="uint", size=4)
    zero = Expression.constant(0, size=4)
    three = Expression.constant(3, size=4)
    positive = Condition(Expression.binary_op("INT_SLESS", zero, n))
    non_positive = positive.negate()
    scaled_n = Expression.binary_op("INT_MULT", three, n)
    scaled_n.size = 4
    limit = Expression.binary_op("INT_ADD", c, scaled_n)
    limit.size = 4
    summary = LoopSummaryRef(
        start_expr=c,
        limit_expr=limit,
        step_expr=three,
        term_descriptor=LoopTermDescriptorRef(
            kind="affine_residue",
            residue_cases=((1, 0, 1, 0),),
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(positive,),
        loop_var_unit="induction_value",
    )
    counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, c, limit],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=3,
            result_size=4,
            signed_loop=False,
            residue_cases=((1, 0, 1, 0),),
            loop_summary=summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )

    wide_n = Expression.unary_op("INT_ZEXT", n)
    wide_n.size = 8
    wide_c = Expression.unary_op("INT_ZEXT", c)
    wide_c.size = 8
    count_times_start = Expression.binary_op("INT_MULT", wide_n, wide_c)
    count_times_start.size = 8
    wide_n_minus_one = Expression.binary_op("INT_SUB", wide_n, Expression.constant(1, size=8))
    wide_n_minus_one.size = 8
    triangular_product = Expression.binary_op("INT_MULT", wide_n, wide_n_minus_one)
    triangular_product.size = 8
    triangular = Expression.binary_op(
        "INT_RIGHT",
        triangular_product,
        Expression.constant(1, size=8),
    )
    triangular.size = 8
    step_triangular = Expression.binary_op("INT_MULT", Expression.constant(3, size=8), triangular)
    step_triangular.size = 8
    closed_wide = Expression.binary_op("INT_ADD", count_times_start, step_triangular)
    closed_wide.size = 8
    closed = Expression.binary_op("SUBPIECE", closed_wide, Expression.constant(0, size=4))
    closed.size = 4

    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False},
    ]
    counted_case = ReturnCase(
        0,
        [positive],
        counted,
        ReturnInfo(address="0x7400", value=counted, conditions=[positive]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    closed_case = ReturnCase(
        0,
        [positive],
        closed,
        ReturnInfo(address="0x7408", value=closed, conditions=[positive]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    strategy = _pairwise_strategy()
    _stub_pair_solver_unsat(strategy)
    parameter_specs = strategy._collect_intrinsic_parameter_specs(
        counted_case,
        closed_case,
        counted,
        closed,
        positive.expression,
    )
    assert parameter_specs is not None

    assert strategy._counted_loop_positive_closed_expression(
        counted,
        counted_case=counted_case,
        result_size=4,
        conditions=[positive],
        parameters=parameter_specs,
    ) is None
    assert strategy._counted_loop_affine_closed_expression_candidate(
        counted,
        result_size=4,
        conditions=[positive],
        parameters=parameter_specs,
    ) is not None

    result = strategy.check(
        FunctionReturnAnalysis(
            function_name="nonzero_start_counted",
            entry_point="0x1000",
            parameters=parameters,
            returns=[
                ReturnInfo(address="0x7400", value=counted, conditions=[positive]),
                ReturnInfo(address="0x7404", value=Expression.constant(0, size=4), conditions=[non_positive]),
            ],
            return_type="int",
            comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
        ),
        FunctionReturnAnalysis(
            function_name="nonzero_start_closed",
            entry_point="0x2000",
            parameters=parameters,
            returns=[
                ReturnInfo(address="0x7408", value=closed, conditions=[positive]),
                ReturnInfo(address="0x740c", value=Expression.constant(0, size=4), conditions=[non_positive]),
            ],
            return_type="int",
            comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
        ),
    )

    assert result.is_equivalent is True
    assert result.total_pairs == 4
    assert result.unsat_pairs == 4
    assert result.unknown_pairs == 0


def test_counted_loop_summary_vs_nonzero_start_step2_closed_form_near_miss_is_not_promoted():
    n = Expression.parameter("param_1", index=0, data_type="int", size=4)
    c = Expression.parameter("param_2", index=1, data_type="uint", size=4)
    zero = Expression.constant(0, size=4)
    two = Expression.constant(2, size=4)
    positive = Condition(Expression.binary_op("INT_SLESS", zero, n))
    scaled_n = Expression.binary_op("INT_MULT", two, n)
    scaled_n.size = 4
    limit = Expression.binary_op("INT_ADD", c, scaled_n)
    limit.size = 4
    summary = LoopSummaryRef(
        start_expr=c,
        limit_expr=limit,
        step_expr=two,
        term_descriptor=LoopTermDescriptorRef(
            kind="affine_residue",
            residue_cases=((1, 0, 1, 0),),
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(positive,),
        loop_var_unit="induction_value",
    )
    counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, c, limit],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=2,
            result_size=4,
            signed_loop=False,
            residue_cases=((1, 0, 1, 0),),
            loop_summary=summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    wrong_closed = Expression.binary_op("INT_ADD", n, Expression.constant(1, size=4))
    wrong_closed.size = 4
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "uint", "size": 4, "is_signed": False},
    ]
    strategy = _pairwise_strategy()
    sat = SolverResult("mock", SolverStatus.SAT, elapsed_time=0.0)
    strategy.solver_runner.run_sequential = Mock(return_value=ParallelResult([sat]))
    counted_case = ReturnCase(
        0,
        [positive],
        counted,
        ReturnInfo(address="0x7410", value=counted, conditions=[positive]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    closed_case = ReturnCase(
        0,
        [positive],
        wrong_closed,
        ReturnInfo(address="0x7414", value=wrong_closed, conditions=[positive]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    parameter_specs = strategy._collect_intrinsic_parameter_specs(
        counted_case,
        closed_case,
        counted,
        wrong_closed,
        positive.expression,
    )
    assert parameter_specs is not None

    assert strategy._prove_counted_loop_closed_expression_candidates(
        counted=counted,
        closed=wrong_closed,
        counted_case=counted_case,
        result_size=4,
        conditions=[positive],
        parameters=parameter_specs,
    ) is False


def test_counted_loop_summary_affine_step5_variant_is_discharged_pairwise():
    n = Expression.parameter("param_1", index=0, data_type="int", size=4)
    c = Expression.parameter("param_2", index=1, data_type="int", size=4)
    zero = Expression.constant(0, size=4)
    five = Expression.constant(5, size=4)
    positive = Condition(Expression.binary_op("INT_SLESS", zero, n))
    non_positive = positive.negate()

    left_summary = LoopSummaryRef(
        start_expr=zero,
        limit_expr=n,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(
            kind="affine_residue",
            residue_cases=((1, 0, 5, 0),),
            residue_bias_terms=((1, 0, c),),
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(positive,),
        loop_var_unit="induction_value",
    )
    left_counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, zero, n],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 5, 0),),
            residue_bias_terms=((1, 0, c),),
            loop_summary=left_summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    right_limit = Expression.binary_op("INT_ADD", Expression.binary_op("INT_MULT", five, n), c)
    right_limit.size = 4
    right_summary = LoopSummaryRef(
        start_expr=c,
        limit_expr=right_limit,
        step_expr=five,
        term_descriptor=LoopTermDescriptorRef(
            kind="affine_residue",
            residue_cases=((1, 0, 1, 0),),
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(positive,),
        loop_var_unit="induction_value",
    )
    right_counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, c, right_limit],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=5,
            result_size=4,
            signed_loop=False,
            residue_cases=((1, 0, 1, 0),),
            loop_summary=right_summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    analysis_left = FunctionReturnAnalysis(
        function_name="barthe_step1",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        returns=[
            ReturnInfo(address="0x1000", value=left_counted, conditions=[positive]),
            ReturnInfo(address="0x1004", value=zero, conditions=[non_positive]),
        ],
        return_type="int",
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    analysis_right = replace(
        analysis_left,
        function_name="barthe_step5",
        returns=[
            ReturnInfo(address="0x2000", value=right_counted, conditions=[positive]),
            ReturnInfo(address="0x2004", value=zero, conditions=[non_positive]),
        ],
    )
    strategy = _pairwise_strategy()
    positive_left_case = ReturnCase(
        0,
        [positive],
        left_counted,
        analysis_left.returns[0],
        parameters=analysis_left.parameters,
        comparison_surface=analysis_left.comparison_surface,
    )
    positive_right_case = ReturnCase(
        0,
        [positive],
        right_counted,
        analysis_right.returns[0],
        parameters=analysis_right.parameters,
        comparison_surface=analysis_right.comparison_surface,
    )
    assert strategy._cases_have_equivalent_runtime_reductions(positive_left_case, positive_right_case) is True
    _stub_pair_solver_unsat(strategy)

    result = strategy.check(analysis_left, analysis_right)

    assert result.is_equivalent is True
    assert result.total_pairs == 4
    assert result.unsat_pairs == 4
    assert result.unknown_pairs == 0


def test_loop_summary_solver_comparator_proves_equivalent_seed_expressions():
    n = Expression.parameter("param_1", index=0, data_type="int", size=4)
    c = Expression.parameter("param_2", index=1, data_type="int", size=4)
    zero = Expression.constant(0, size=4)
    positive = Condition(Expression.binary_op("INT_SLESS", zero, n))
    c_plus_zero = Expression.binary_op("INT_ADD", c, zero)
    c_plus_zero.size = 4
    term_descriptor = LoopTermDescriptorRef(
        kind="affine_residue",
        residue_cases=((1, 0, 5, 0),),
    )
    left_summary = LoopSummaryRef(
        start_expr=zero,
        limit_expr=n,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=term_descriptor,
        seed_terms=(c_plus_zero,),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(positive,),
        loop_var_unit="induction_value",
    )
    right_summary = LoopSummaryRef(
        start_expr=zero,
        limit_expr=n,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=term_descriptor,
        seed_terms=(c,),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(positive,),
        loop_var_unit="induction_value",
    )
    left_counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, zero, n],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 5, 0),),
            loop_summary=left_summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    right_counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, zero, n],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 5, 0),),
            loop_summary=right_summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    left_case = ReturnCase(
        0,
        [positive],
        left_counted,
        ReturnInfo(address="0x1000", value=left_counted, conditions=[positive]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    right_case = ReturnCase(
        0,
        [positive],
        right_counted,
        ReturnInfo(address="0x2000", value=right_counted, conditions=[positive]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    strategy = _pairwise_strategy()
    _stub_pair_solver_unsat(strategy)

    assert strategy._case_pair_loop_summaries_solver_equivalent(
        left_counted.runtime_ref,
        right_counted.runtime_ref,
        left_case=left_case,
        right_case=right_case,
    ) is True


def test_loop_summary_solver_comparator_keeps_unproved_seed_expressions_unknown():
    n = Expression.parameter("param_1", index=0, data_type="int", size=4)
    c = Expression.parameter("param_2", index=1, data_type="int", size=4)
    zero = Expression.constant(0, size=4)
    positive = Condition(Expression.binary_op("INT_SLESS", zero, n))
    c_plus_one = Expression.binary_op("INT_ADD", c, Expression.constant(1, size=4))
    c_plus_one.size = 4
    term_descriptor = LoopTermDescriptorRef(
        kind="affine_residue",
        residue_cases=((1, 0, 5, 0),),
    )
    left_summary = LoopSummaryRef(
        start_expr=zero,
        limit_expr=n,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=term_descriptor,
        seed_terms=(c_plus_one,),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(positive,),
        loop_var_unit="induction_value",
    )
    right_summary = replace(left_summary, seed_terms=(c,))
    left_counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, zero, n],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 5, 0),),
            loop_summary=left_summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    right_counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, zero, n],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 5, 0),),
            loop_summary=right_summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    left_case = ReturnCase(
        0,
        [positive],
        left_counted,
        ReturnInfo(address="0x1000", value=left_counted, conditions=[positive]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    right_case = ReturnCase(
        0,
        [positive],
        right_counted,
        ReturnInfo(address="0x2000", value=right_counted, conditions=[positive]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    strategy = _pairwise_strategy()
    sat = SolverResult("mock", SolverStatus.SAT, elapsed_time=0.0, model={"param_2_1": 0})
    strategy.solver_runner.run_sequential = Mock(return_value=ParallelResult([sat]))

    assert strategy._case_pair_loop_summaries_solver_equivalent(
        left_counted.runtime_ref,
        right_counted.runtime_ref,
        left_case=left_case,
        right_case=right_case,
    ) is False


def test_loop_summary_solver_comparator_rejects_constant_bias_mismatch():
    n = Expression.parameter("param_1", index=0, data_type="int", size=4)
    zero = Expression.constant(0, size=4)
    positive = Condition(Expression.binary_op("INT_SLESS", zero, n))
    term_descriptor = LoopTermDescriptorRef(
        kind="affine_residue",
        residue_cases=((1, 0, 5, 0),),
        result_size=4,
    )
    left_summary = LoopSummaryRef(
        start_expr=zero,
        limit_expr=n,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=term_descriptor,
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(positive,),
        loop_var_unit="induction_value",
        constant_bias=1,
    )
    right_summary = replace(left_summary, constant_bias=0)
    left_counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, zero, n],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 5, 0),),
            loop_summary=left_summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    right_counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, zero, n],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 5, 0),),
            loop_summary=right_summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    parameters = [{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}]
    left_case = ReturnCase(
        0,
        [positive],
        left_counted,
        ReturnInfo(address="0x1000", value=left_counted, conditions=[positive]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    right_case = ReturnCase(
        0,
        [positive],
        right_counted,
        ReturnInfo(address="0x2000", value=right_counted, conditions=[positive]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    strategy = _pairwise_strategy()
    _stub_pair_solver_unsat(strategy)

    assert strategy._case_pair_loop_summaries_solver_equivalent(
        left_counted.runtime_ref,
        right_counted.runtime_ref,
        left_case=left_case,
        right_case=right_case,
    ) is False


def test_loop_summary_solver_comparator_rejects_counted_wrapper_semantic_mismatch():
    n = Expression.parameter("param_1", index=0, data_type="int", size=4)
    zero = Expression.constant(0, size=4)
    positive = Condition(Expression.binary_op("INT_SLESS", zero, n))
    summary = LoopSummaryRef(
        start_expr=zero,
        limit_expr=n,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(
            kind="affine_residue",
            residue_cases=((1, 0, 5, 0),),
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(positive,),
        loop_var_unit="induction_value",
    )
    left_counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, zero, n],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 5, 0),),
            loop_summary=summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    right_counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, zero, n],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 6, 0),),
            loop_summary=summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    parameters = [{"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True}]
    left_case = ReturnCase(
        0,
        [positive],
        left_counted,
        ReturnInfo(address="0x1000", value=left_counted, conditions=[positive]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    right_case = ReturnCase(
        0,
        [positive],
        right_counted,
        ReturnInfo(address="0x2000", value=right_counted, conditions=[positive]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    strategy = _pairwise_strategy()
    _stub_pair_solver_unsat(strategy)

    assert strategy._case_pair_loop_summaries_solver_equivalent(
        left_counted.runtime_ref,
        right_counted.runtime_ref,
        left_case=left_case,
        right_case=right_case,
    ) is False


def test_counted_loop_summary_affine_step5_near_miss_is_not_promoted_to_eq():
    n = Expression.parameter("param_1", index=0, data_type="int", size=4)
    c = Expression.parameter("param_2", index=1, data_type="int", size=4)
    zero = Expression.constant(0, size=4)
    five = Expression.constant(5, size=4)
    positive = Condition(Expression.binary_op("INT_SLESS", zero, n))
    left_summary = LoopSummaryRef(
        start_expr=zero,
        limit_expr=n,
        step_expr=Expression.constant(1, size=4),
        term_descriptor=LoopTermDescriptorRef(
            kind="affine_residue",
            residue_cases=((1, 0, 5, 0),),
            residue_bias_terms=((1, 0, c),),
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(positive,),
        loop_var_unit="induction_value",
    )
    left_counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, zero, n],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 5, 0),),
            residue_bias_terms=((1, 0, c),),
            loop_summary=left_summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    right_limit = Expression.binary_op("INT_ADD", Expression.binary_op("INT_MULT", five, n), c)
    right_limit.size = 4
    right_summary = LoopSummaryRef(
        start_expr=c,
        limit_expr=right_limit,
        step_expr=five,
        term_descriptor=LoopTermDescriptorRef(
            kind="affine_residue",
            residue_cases=((1, 0, 1, 1),),
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(positive,),
        loop_var_unit="induction_value",
    )
    right_counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, c, right_limit],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=5,
            result_size=4,
            signed_loop=False,
            residue_cases=((1, 0, 1, 1),),
            loop_summary=right_summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    left_case = ReturnCase(
        0,
        [positive],
        left_counted,
        ReturnInfo(address="0x1000", value=left_counted, conditions=[positive]),
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    right_case = ReturnCase(
        0,
        [positive],
        right_counted,
        ReturnInfo(address="0x2000", value=right_counted, conditions=[positive]),
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    strategy = _pairwise_strategy()

    assert strategy._counted_loop_affine_values_are_provably_equivalent(
        left_counted,
        right_counted,
        left_case=left_case,
        right_case=right_case,
    ) is False


def _mips64_step5_affine_counted_loop_pair():
    n64 = Expression.parameter("param_1", index=0, data_type="long", size=8)
    c = Expression.parameter("param_2", index=1, data_type="int", size=4)
    zero32 = Expression.constant(0, size=4)
    zero64 = Expression.constant(0, size=8)
    one64 = Expression.constant(1, size=8)
    five32 = Expression.constant(5, size=4)
    positive64 = Condition(Expression.binary_op("INT_SLESS", zero64, n64))

    left_summary = LoopSummaryRef(
        start_expr=zero64,
        limit_expr=n64,
        step_expr=one64,
        term_descriptor=LoopTermDescriptorRef(
            kind="affine_residue",
            residue_cases=((1, 0, 5, 0),),
            residue_bias_terms=((1, 0, c),),
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(positive64,),
        loop_var_unit="induction_value",
    )
    left_counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero32, zero64, n64],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 5, 0),),
            residue_bias_terms=((1, 0, c),),
            loop_summary=left_summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )

    n32 = Expression.binary_op("SUBPIECE", n64, Expression.constant(0, size=4))
    n32.size = 4
    right_limit = Expression.binary_op("INT_ADD", Expression.binary_op("INT_MULT", five32, n32), c)
    right_limit.size = 4
    right_summary = LoopSummaryRef(
        start_expr=c,
        limit_expr=right_limit,
        step_expr=five32,
        term_descriptor=LoopTermDescriptorRef(
            kind="affine_residue",
            residue_cases=((1, 0, 1, 0),),
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(positive64,),
        loop_var_unit="induction_value",
    )
    right_counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero32, c, right_limit],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=5,
            result_size=4,
            signed_loop=False,
            residue_cases=((1, 0, 1, 0),),
            loop_summary=right_summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "long", "size": 8, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    left_case = ReturnCase(
        0,
        [positive64],
        left_counted,
        ReturnInfo(address="0x1000", value=left_counted, conditions=[positive64]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    right_case = ReturnCase(
        0,
        [positive64],
        right_counted,
        ReturnInfo(address="0x2000", value=right_counted, conditions=[positive64]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    return left_counted, right_counted, left_case, right_case


def test_counted_loop_summary_affine_step5_mips64_without_semantic_width_is_not_direct_eq():
    left_counted, right_counted, left_case, right_case = _mips64_step5_affine_counted_loop_pair()
    strategy = _pairwise_strategy()

    assert strategy._counted_loop_affine_values_are_provably_equivalent(
        left_counted,
        right_counted,
        left_case=left_case,
        right_case=right_case,
    ) is False


def test_counted_loop_summary_affine_step5_mips64_with_semantic_width_is_direct_eq():
    left_counted, right_counted, left_case, right_case = _mips64_step5_affine_counted_loop_pair()
    strategy = _pairwise_strategy()
    semantic_sources = (
        ParameterInfo(
            original_name="param_1",
            smt_name="param_1_1",
            bit_width=64,
            index=0,
            is_signed=True,
            semantic_narrow_bits=32,
            semantic_signedness="signed",
        ),
        ParameterInfo("param_2", "param_2_1", 32, 1, is_signed=True),
        ParameterInfo(
            original_name="param_1",
            smt_name="param_1_2",
            bit_width=64,
            index=0,
            is_signed=True,
            semantic_narrow_bits=32,
            semantic_signedness="signed",
        ),
        ParameterInfo("param_2", "param_2_2", 32, 1, is_signed=True),
    )

    assert strategy._counted_loop_affine_values_are_provably_equivalent(
        left_counted,
        right_counted,
        left_case=left_case,
        right_case=right_case,
        semantic_parameter_sources=semantic_sources,
    ) is True


def _mips64_counted_loop_vs_low32_closed_form_fixture():
    n = Expression.parameter("param_1", index=0, data_type="long", size=8)
    c = Expression.parameter("param_2", index=1, data_type="int", size=4)
    zero32 = Expression.constant(0, size=4)
    zero64 = Expression.constant(0, size=8)
    positive = Condition(Expression.binary_op("INT_SLESS", zero64, n))
    summary = LoopSummaryRef(
        start_expr=zero64,
        limit_expr=n,
        step_expr=Expression.constant(1, size=8),
        term_descriptor=LoopTermDescriptorRef(
            kind="affine_residue",
            residue_cases=((1, 0, 5, 0),),
            residue_bias_terms=((1, 0, c),),
        ),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure"),
        guard_constraints=(positive,),
        loop_var_unit="induction_value",
    )
    counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero32, zero64, n],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 5, 0),),
            residue_bias_terms=((1, 0, c),),
            loop_summary=summary,
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    n32 = Expression.binary_op("SUBPIECE", n, Expression.constant(0, size=4))
    n32.size = 4
    wide_n = Expression.unary_op("INT_ZEXT", n32)
    wide_n.size = 8
    wide_n_minus_one = Expression.binary_op("INT_SUB", wide_n, Expression.constant(1, size=8))
    wide_n_minus_one.size = 8
    product = Expression.binary_op("INT_MULT", wide_n, wide_n_minus_one)
    half = Expression.binary_op("INT_RIGHT", product, Expression.constant(1, size=8))
    triangular = Expression.binary_op("SUBPIECE", half, Expression.constant(0, size=4))
    triangular.size = 4
    scaled = Expression.binary_op("INT_MULT", triangular, Expression.constant(5, size=4))
    scaled.size = 4
    c_terms = Expression.binary_op("INT_MULT", n32, c)
    c_terms.size = 4
    closed = Expression.binary_op("INT_ADD", scaled, c_terms)
    closed.size = 4
    analysis_left = FunctionReturnAnalysis(
        function_name="mips64_counted",
        entry_point="0x1000",
        parameters=[
            {"name": "param_1", "index": 0, "data_type": "long", "size": 8, "is_signed": True},
            {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
        ],
        returns=[ReturnInfo(address="0x1000", value=counted, conditions=[positive])],
        return_type="int",
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    analysis_right = replace(
        analysis_left,
        function_name="mips64_closed",
        returns=[ReturnInfo(address="0x2000", value=closed, conditions=[positive])],
    )
    return analysis_left, analysis_right


def test_counted_loop_summary_vs_mips64_long_limit_without_semantic_width_stays_proof_missing():
    analysis_left, analysis_right = _mips64_counted_loop_vs_low32_closed_form_fixture()
    strategy = _pairwise_strategy()

    result = strategy.check(analysis_left, analysis_right)

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 0
    assert result.unknown_pairs == 1
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.LOOP_SUMMARY_PROOF_MISSING.value
    assert result.unknown_reasons[0].evidence_refs == ("counted_loop_summary_expression_proof_missing",)
    strategy.solver_runner.run_sequential.assert_not_called()


def test_counted_loop_summary_vs_mips64_long_limit_with_semantic_width_uses_smt():
    analysis_left, analysis_right = _mips64_counted_loop_vs_low32_closed_form_fixture()
    strategy = _pairwise_strategy()
    strategy.formula_builder.build_base_context.return_value["params1"] = [
        ParameterInfo(
            original_name="param_1",
            smt_name="param_1_1",
            bit_width=64,
            index=0,
            is_signed=True,
            semantic_narrow_bits=32,
            semantic_signedness="signed",
        ),
        ParameterInfo("param_2", "param_2_1", 32, 1, is_signed=True),
    ]
    strategy.formula_builder.build_base_context.return_value["params2"] = [
        ParameterInfo("param_1", "param_1_2", 32, 0, is_signed=True),
        ParameterInfo("param_2", "param_2_2", 32, 1, is_signed=True),
    ]

    result = strategy.check(analysis_left, analysis_right)

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_auxiliary_counted_loop_runtime_bias_terms_are_cloned_for_smt():
    n = Expression.parameter("param_1", index=0, data_type="int", size=4)
    c = Expression.parameter("param_2", index=1, data_type="int", size=4)
    zero = Expression.constant(0, size=4)
    positive = Condition(Expression.binary_op("INT_SLESS", zero, n))
    counted = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [zero, zero, n],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((2, 0, 1, 0), (2, 1, 2, 0)),
            residue_bias_terms=((2, 0, c), (2, 1, c)),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    parameters = [
        {"name": "param_1", "index": 0, "data_type": "int", "size": 4, "is_signed": True},
        {"name": "param_2", "index": 1, "data_type": "int", "size": 4, "is_signed": True},
    ]
    left_case = ReturnCase(
        0,
        [positive],
        counted,
        ReturnInfo(address="0x1000", value=counted, conditions=[positive]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    right_value = Expression.constant(0, size=4)
    right_case = ReturnCase(
        0,
        [positive],
        right_value,
        ReturnInfo(address="0x2000", value=right_value, conditions=[positive]),
        parameters=parameters,
        comparison_surface=ComparisonSurface(kind="return_value", explicit_bit_width=32, type_name="int"),
    )
    strategy = _pairwise_strategy()
    conditions = strategy._combined_summary_conditions(left_case, right_case)
    parameter_specs = strategy._collect_intrinsic_parameter_specs(
        left_case,
        right_case,
        counted,
        right_value,
        *(condition.expression for condition in conditions),
    )

    query = strategy._build_intrinsic_equivalence_query(counted, right_value, conditions, parameter_specs)

    assert query is not None
    assert "(declare-const aux_param_1 (_ BitVec 32))" in query
    assert "param_2" not in query
    assert "aux_param_1" in query


def test_counted_loop_summary_vs_closed_form_near_miss_stays_proof_missing():
    counted_value = _counted_loop(_pure_counted_summary_with_guard())
    off_by_n_closed_form = _triangular_closed_form(inclusive=True)
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis(
            "barthe_like_counted_summary",
            [ReturnInfo(address="0x7310", value=counted_value, conditions=[_count_gt(0)])],
        ),
        _analysis(
            "barthe_like_closed_form_near_miss",
            [ReturnInfo(address="0x7314", value=off_by_n_closed_form, conditions=[_count_gt(0)])],
        ),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 1
    assert result.unsat_pairs == 0
    assert result.unknown_pairs == 1
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.LOOP_SUMMARY_PROOF_MISSING.value
    assert result.unknown_reasons[0].evidence_refs == ("counted_loop_summary_expression_proof_missing",)
    strategy.solver_runner.run_sequential.assert_not_called()


def test_counted_loop_summary_vs_closed_form_near_miss_with_total_partition_stays_unknown():
    counted_value = _counted_loop(_pure_counted_summary_with_guard())
    off_by_n_closed_form = _triangular_closed_form(inclusive=True)
    non_positive = _count_gt(0).negate()
    strategy = _pairwise_strategy()
    unsat = SolverResult("mock", SolverStatus.UNSAT, elapsed_time=0.0)
    strategy.solver_runner.run_sequential = Mock(return_value=ParallelResult([unsat]))

    result = strategy.check(
        _analysis(
            "barthe_like_counted_summary_total",
            [
                ReturnInfo(address="0x7310", value=counted_value, conditions=[_count_gt(0)]),
                ReturnInfo(address="0x7314", value=Expression.constant(0, size=4), conditions=[non_positive]),
            ],
        ),
        _analysis(
            "barthe_like_closed_form_near_miss_total",
            [
                ReturnInfo(address="0x7320", value=off_by_n_closed_form, conditions=[_count_gt(0)]),
                ReturnInfo(address="0x7324", value=Expression.constant(0, size=4), conditions=[non_positive]),
            ],
        ),
    )

    assert result.is_equivalent is None
    assert result.total_pairs == 4
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.LOOP_SUMMARY_PROOF_MISSING.value
    assert result.unknown_reasons[0].evidence_refs == ("counted_loop_summary_expression_proof_missing",)


def test_pure_counted_loop_with_total_return_coverage_can_be_closed_by_method_b():
    left_value = _counted_loop(_pure_counted_summary())
    right_value = _counted_loop(_pure_counted_summary())
    non_positive = _count_gt(0).negate()
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis(
            "pure_counted_total_coverage_left",
            [
                ReturnInfo(address="0x7100", value=left_value, conditions=[_count_gt(0)]),
                ReturnInfo(address="0x7104", value=left_value, conditions=[non_positive]),
            ],
        ),
        _analysis(
            "pure_counted_total_coverage_right",
            [
                ReturnInfo(address="0x7200", value=right_value, conditions=[_count_gt(0)]),
                ReturnInfo(address="0x7204", value=right_value, conditions=[non_positive]),
            ],
        ),
    )

    assert result.is_equivalent is True
    assert result.total_pairs == 4
    assert result.unsat_pairs == 4
    assert result.unknown_pairs == 0
    strategy.solver_runner.run_sequential.assert_not_called()


def test_pure_counted_loop_without_runtime_summary_guards_needs_summary_partition():
    value = _counted_loop(_pure_counted_summary())
    strategy = _pairwise_strategy()

    result = strategy.check(
        _analysis("pure_counted_no_runtime_guard_left", [ReturnInfo(address="0x7020", value=value, conditions=[_count_gt(0)])]),
        _analysis("pure_counted_no_runtime_guard_right", [ReturnInfo(address="0x7024", value=value, conditions=[_count_gt(3)]),
]),
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


def test_phi_circular_lowering_rejects_seq_time_only_origin_drift_without_completed_proof():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    value = Expression.binary_op("INT_MULT", _count_param(), _const(2))
    value.size = 4
    left_case = ReturnCase(
        0,
        [_count_gt(0), _phi_circular_exit_guard(_phi_circular_unknown(seq_time=144))],
        value,
        ReturnInfo("left", value),
    )
    right_case = ReturnCase(
        0,
        [_count_gt(0), _phi_circular_exit_guard(_phi_circular_unknown(seq_time=141))],
        value,
        ReturnInfo("right", value),
    )

    lowering = strategy._try_build_unresolved_phi_circular_lowering(
        base_ctx={},
        case1=left_case,
        case2=right_case,
        pair_id="(0,0)",
    )

    assert lowering is None


def test_phi_circular_lowering_rejects_non_seq_time_origin_drift():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    value = Expression.binary_op("INT_MULT", _count_param(), _const(2))
    value.size = 4
    left_case = ReturnCase(
        0,
        [_count_gt(0), _phi_circular_exit_guard(_phi_circular_unknown(seq_time=144))],
        value,
        ReturnInfo("left", value),
    )
    right_case = ReturnCase(
        0,
        [_count_gt(0), _phi_circular_exit_guard(_phi_circular_unknown(seq_time=141, opcode=61))],
        value,
        ReturnInfo("right", value),
    )

    lowering = strategy._try_build_unresolved_phi_circular_lowering(
        base_ctx={},
        case1=left_case,
        case2=right_case,
        pair_id="(0,0)",
    )

    assert lowering is None


def test_phi_circular_lowering_rejects_guard_shape_mismatch():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    value = Expression.binary_op("INT_MULT", _count_param(), _const(2))
    value.size = 4
    left_case = ReturnCase(
        0,
        [_count_gt(0), _phi_circular_exit_guard(_phi_circular_unknown(seq_time=144))],
        value,
        ReturnInfo("left", value),
    )
    right_phi = _phi_circular_unknown(seq_time=141)
    mismatched_guard = Condition(Expression.binary_op("INT_EQUAL", right_phi, _const(0)))
    right_case = ReturnCase(
        0,
        [_count_gt(0), mismatched_guard],
        value,
        ReturnInfo("right", value),
    )

    lowering = strategy._try_build_unresolved_phi_circular_lowering(
        base_ctx={},
        case1=left_case,
        case2=right_case,
        pair_id="(0,0)",
    )

    assert lowering is None


def test_phi_circular_lowering_rejects_unknown_value_shape_mismatch():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_value = _phi_circular_unknown(seq_time=144)
    right_value = Expression.binary_op("INT_ADD", _phi_circular_unknown(seq_time=141), _const(1))
    right_value.size = 4
    left_case = ReturnCase(
        0,
        [_count_gt(0), _phi_circular_exit_guard(_phi_circular_unknown(seq_time=144))],
        left_value,
        ReturnInfo("left", left_value),
    )
    right_case = ReturnCase(
        0,
        [_count_gt(0), _phi_circular_exit_guard(_phi_circular_unknown(seq_time=141))],
        right_value,
        ReturnInfo("right", right_value),
    )

    lowering = strategy._try_build_unresolved_phi_circular_lowering(
        base_ctx={},
        case1=left_case,
        case2=right_case,
        pair_id="(0,0)",
    )

    assert lowering is None


def test_return_coverage_does_not_drop_phi_circular_guard_without_completed_proof():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    value = Expression.binary_op("INT_MULT", _count_param(), _const(2))
    value.size = 4
    positive_case = ReturnCase(
        0,
        [_count_gt(0), _phi_circular_exit_guard(_phi_circular_unknown(seq_time=144))],
        value,
        ReturnInfo("positive", value),
    )
    nonpositive_case = ReturnCase(
        1,
        [_count_gt(0).negate()],
        _const(1),
        ReturnInfo("base", _const(1)),
    )

    assert strategy._return_cases_have_object_centric_total_coverage(
        (positive_case, nonpositive_case)
    ) is not True

    phi_value = _phi_circular_unknown(seq_time=144)
    unresolved_value_case = ReturnCase(
        0,
        [_count_gt(0), _phi_circular_exit_guard(_phi_circular_unknown(seq_time=144))],
        phi_value,
        ReturnInfo("unresolved", phi_value),
    )

    assert strategy._return_cases_have_object_centric_total_coverage(
        (unresolved_value_case, nonpositive_case)
    ) is not True


def test_return_coverage_does_not_treat_single_phi_circular_guard_case_as_total():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    value = _const(1)
    guarded_case = ReturnCase(
        0,
        [_phi_circular_exit_guard(_phi_circular_unknown(seq_time=144))],
        value,
        ReturnInfo("guarded", value),
    )

    assert strategy._return_cases_have_object_centric_total_coverage((guarded_case,)) is not True

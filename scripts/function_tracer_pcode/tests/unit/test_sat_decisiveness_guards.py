# -*- coding: utf-8 -*-

from copy import deepcopy
from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.effect_summary import (
    CanonicalLocation,
    CallArgumentEvidence,
    EffectSummary,
    StoreEffect,
    UnsupportedCallEffectRef,
    post_state_read_expression_for_location,
)
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilderResult
from scripts.function_tracer_pcode.equivalence.formula.types import ParameterInfo
from scripts.function_tracer_pcode.equivalence.strategies.monolithic import MonolithicStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import (
    QueryResult,
    ReturnCase,
)
from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownRecoveryActionStatus,
    UnknownRecoveryProofKind,
    UnknownReasonId,
    build_proof_obligation_id,
    build_unknown_recovery_actions,
)
from scripts.function_tracer_pcode.model import (
    CallTargetRef,
    Condition,
    DeferredCallInfo,
    DeferredCallRef,
    Expression,
    FunctionReturnAnalysis,
    PcodeOpRef,
    ReturnInfo,
    expression_provenance_key,
)
from scripts.function_tracer_pcode.model.runtime_refs import LocationBaseRef
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.validation.phase2_equivalence_blocking_unsafety import (
    _object_target_key_is_specific,
)


def _param(name: str, index: int = 0, size: int = 4, data_type: str = "int"):
    return {
        "name": name,
        "index": index,
        "size": size,
        "data_type": data_type,
        "is_signed": "unsigned" not in data_type,
    }


def _const(value: int, size: int = 4) -> Expression:
    return Expression.constant(value, size)


def _eq(lhs: Expression, rhs: Expression) -> Condition:
    return Condition(Expression.binary_op("INT_EQUAL", lhs, rhs), False)


def _ne(lhs: Expression, rhs: Expression) -> Condition:
    return Condition(Expression.binary_op("INT_NOTEQUAL", lhs, rhs), False)


def _deep_zext_target(name: str, index: int, depth: int = 300) -> Expression:
    expr = Expression.parameter(name, index, size=8)
    for _ in range(depth):
        expr = Expression.unary_op("INT_ZEXT", expr)
    return expr


def _deep_target_with_tail_op(
    name: str,
    index: int,
    tail_operator: str,
    depth: int = 8200,
) -> Expression:
    expr = Expression.parameter(name, index, size=8)
    expr = Expression.unary_op(tail_operator, expr)
    for _ in range(max(0, depth - 1)):
        expr = Expression.unary_op("INT_ZEXT", expr)
    return expr


def _build_symbolic_post_state_analysis(name: str) -> FunctionReturnAnalysis:
    params = [_param("trace", index=0, size=8, data_type="int *")]
    value = post_state_read_expression_for_location(
        CanonicalLocation("trace", 0, 4),
        params,
        symbolic=True,
    )
    return FunctionReturnAnalysis(
        function_name=name,
        entry_point="0x1000",
        parameters=params,
        returns=[ReturnInfo(address="0x1000", value=value, conditions=[])],
        return_type="int",
    )


def _base_context_for_single_int_param():
    return {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }


def _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2):
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == analysis1.function_name else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))


def _return_coverage_gap_analyses():
    x = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x, _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )
    return analysis1, analysis2


def _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2):
    case1 = ReturnCase(
        index=0,
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == analysis1.function_name else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))


def _analysis_with_unsupported_call_effect() -> FunctionReturnAnalysis:
    site = UnsupportedCallEffectRef(
        pcode_op_ref=PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND"),
        target_ref=None,
        target_expr=Expression.parameter("fp", 0, size=8),
        reason="target_identity_unavailable",
        order_key=9,
    )
    return FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )


def _call_effect_summary_proof_evidence(object_target_key=None, **overrides):
    object_target_key = object_target_key or (
        "unsupported_call_effect",
        "function1",
        ("function_ref", ("function", 1, 0x1000)),
        ("pcode_op", 0x3020, 4, 1, "CALLIND"),
        None,
        ("typed_target_expression", ("runtime_ref", ("param", "fp", 0))),
        9,
        "target_identity_unavailable",
    )
    evidence = {
        "object_derived": True,
        "status": "complete",
        "reason_id": UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
        "recovery_proof_kind": UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value,
        "proof_stage": "object_evidence_collected",
        "evidence_kind": "call_effect_summary",
        "object_target_key": object_target_key,
    }
    evidence["proof_obligation_id"] = _expected_call_effect_summary_proof_id(evidence)
    evidence.update(overrides)
    return evidence


def _analysis_with_call_effect_summary_proof_evidence(**evidence_overrides) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        completed_recovery_proof_evidence=(
            _call_effect_summary_proof_evidence(**evidence_overrides),
        ),
    )


def _expected_call_effect_summary_proof_id(evidence):
    return build_proof_obligation_id(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
        evidence["proof_stage"],
        evidence["recovery_proof_kind"],
        evidence["evidence_kind"],
        evidence["object_target_key"],
    )


def _return_coverage_completion_evidence(action, **overrides):
    evidence = {
        "object_derived": True,
        "status": "complete",
        "reason_id": UnknownReasonId.RETURN_COVERAGE_GAP.value,
        "recovery_proof_kind": UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION.value,
        "proof_stage": action.proof_stage,
        "evidence_kind": action.evidence_kind,
        "object_target_key": action.object_target_key,
        "proof_obligation_id": action.proof_obligation_id,
    }
    evidence.update(overrides)
    return evidence


def _return_coverage_completion_evidence_without_proof_id(action):
    evidence = _return_coverage_completion_evidence(action)
    evidence.pop("proof_obligation_id", None)
    return evidence


def _sat_unsafety_resolution_evidence(action, **overrides):
    evidence = {
        "object_derived": True,
        "status": "complete",
        "reason_id": UnknownReasonId.SAT_UNSAFETY.value,
        "recovery_proof_kind": UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value,
        "proof_stage": action.proof_stage,
        "evidence_kind": action.evidence_kind,
        "object_target_key": action.object_target_key,
        "proof_obligation_id": action.proof_obligation_id,
        "proof_content": {
            "object_derived": True,
            "object_target_key": action.object_target_key,
            "counterexample_replay": {
                "status": "replayed",
                "model_ref": ("query_model", "pair", action.pair_or_case),
            },
            "active_unsafety_discharge": {
                "status": "discharged",
                "discharged_reason_refs": tuple(action.evidence_refs),
            },
            "coverage_effect_safety": {
                "status": "proven",
                "coverage_status": "covered",
                "effect_status": "supported",
            },
        },
    }
    evidence.update(overrides)
    return evidence


def _sat_unsafety_resolution_action():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    reason = strategy._make_sat_unsafety_unknown_reason(
        ("function1:unsupported_call_effect_summary",),
        analysis1,
        analysis2,
        case1=case1,
        case2=case2,
        pair_id="(0,0)",
        stage="S_PAIRWISE",
    )
    return build_unknown_recovery_actions([reason])[0]


def _monolithic_return_coverage_gap_setup():
    class _CoverageGapUnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, query: str):
            if "Return coverage gap query: function1" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
                )
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1, analysis2 = _return_coverage_gap_analyses()
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    strategy = MonolithicStrategy(formula_builder, _CoverageGapUnsatSolverRunner(), debug=False)
    return strategy, analysis1, analysis2


def test_function_return_analysis_marks_symbolic_post_state_reads_as_sat_unsafe():
    analysis = _build_symbolic_post_state_analysis("with_locread")

    assert analysis.has_symbolic_post_state_reads() is True
    assert "symbolic_post_state_reads" in analysis.get_decisive_sat_unsafety_reasons()


def test_function_return_analysis_treats_lowerable_post_state_reads_as_sat_safe():
    params = [
        _param("trace", index=0, size=8, data_type="int *"),
        _param("delta", index=1, size=4, data_type="int"),
    ]
    trace = Expression.parameter("trace", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=0,
        size=4,
    )
    analysis = FunctionReturnAnalysis(
        function_name="lowerable",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=post_state_read_expression_for_location(
                    location,
                    params,
                    symbolic=True,
                ),
                conditions=[],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace", "delta"],
            effects=[
                StoreEffect(
                    location=location,
                    value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), delta),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
    )

    assert analysis.has_symbolic_post_state_reads() is False
    assert "symbolic_post_state_reads" not in analysis.get_decisive_sat_unsafety_reasons()


def test_function_return_analysis_marks_effect_sensitive_raw_memory_reads_as_sat_unsafe():
    params = [_param("trace", index=0, size=8, data_type="int *")]
    trace = Expression.parameter("trace", 0, size=8)
    field = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=4,
        size=4,
    )
    analysis = FunctionReturnAnalysis(
        function_name="raw_read_after_effect",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.memory(field, size=4),
                conditions=[],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace"],
            effects=[
                StoreEffect(
                    location=location,
                    value=Expression.constant(1, 4),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
    )

    assert analysis.has_effect_sensitive_raw_memory_reads() is True
    assert "effect_sensitive_raw_memory_reads" in analysis.get_decisive_sat_unsafety_reasons()


def test_function_return_analysis_ignores_effect_sensitive_raw_reads_under_incompatible_guards():
    params = [
        _param("trace", index=0, size=8, data_type="int *"),
        _param("flag", index=1, size=4, data_type="int"),
    ]
    trace = Expression.parameter("trace", 0, size=8)
    flag = Expression.parameter("flag", 1, size=4)
    field = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=4,
        size=4,
    )
    analysis = FunctionReturnAnalysis(
        function_name="guarded_raw_read_after_effect",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.memory(field, size=4),
                conditions=[_eq(flag, _const(0))],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace", "flag"],
            effects=[
                StoreEffect(
                    location=location,
                    value=Expression.constant(1, 4),
                    conditions=[_ne(flag, _const(0))],
                    order_key=1,
                )
            ],
        ),
    )

    assert analysis.has_effect_sensitive_raw_memory_reads() is False
    assert "effect_sensitive_raw_memory_reads" not in analysis.get_decisive_sat_unsafety_reasons()


def test_function_return_analysis_checks_raw_read_alias_under_effect_guard():
    params = [
        _param("p", index=0, size=8, data_type="int *"),
        _param("q", index=1, size=8, data_type="int *"),
    ]
    p = Expression.parameter("p", 0, size=8)
    q = Expression.parameter("q", 1, size=8)
    analysis = FunctionReturnAnalysis(
        function_name="guarded_alias_raw_read_after_effect",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.memory(q, size=4),
                conditions=[],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["p", "q"],
            effects=[
                StoreEffect(
                    location=CanonicalLocation(
                        base_ref=LocationBaseRef.parameter("p", index=0),
                        offset=0,
                        size=4,
                    ),
                    value=Expression.constant(1, 4),
                    conditions=[_eq(p, q)],
                    order_key=1,
                )
            ],
        ),
    )

    assert analysis.has_effect_sensitive_raw_memory_reads() is True
    assert "effect_sensitive_raw_memory_reads" in analysis.get_decisive_sat_unsafety_reasons()


def test_function_return_analysis_scans_raw_sibling_after_lowerable_post_state_read():
    params = [
        _param("trace", index=0, size=8, data_type="int *"),
        _param("flag", index=1, size=4, data_type="int"),
    ]
    trace = Expression.parameter("trace", 0, size=8)
    flag = Expression.parameter("flag", 1, size=4)
    total_location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=0,
        size=4,
    )
    count_location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=4,
        size=4,
    )
    count_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    analysis = FunctionReturnAnalysis(
        function_name="mixed_post_state_and_raw_read",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.binary_op(
                    "INT_ADD",
                    post_state_read_expression_for_location(
                        total_location,
                        params,
                        symbolic=True,
                    ),
                    Expression.memory(count_addr, size=4),
                ),
                conditions=[],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace"],
            effects=[
                StoreEffect(
                    location=total_location,
                    value=Expression.constant(7, 4),
                    conditions=[],
                    order_key=1,
                ),
                StoreEffect(
                    location=count_location,
                    value=Expression.constant(9, 4),
                    conditions=[_ne(flag, _const(0))],
                    order_key=2,
                ),
            ],
        ),
    )

    assert analysis.has_symbolic_post_state_reads() is False
    assert analysis.has_effect_sensitive_raw_memory_reads() is True
    assert "effect_sensitive_raw_memory_reads" in analysis.get_decisive_sat_unsafety_reasons()


def test_function_return_analysis_blocks_equivalence_when_effect_summary_is_unsupported():
    analysis = FunctionReturnAnalysis(
        function_name="unsupported_effect_summary",
        entry_point="0x1000",
        parameters=[],
        returns=[ReturnInfo(address="0x1000", value=_const(0), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=[],
            effects=[],
            has_unsupported_call=True,
        ),
    )

    assert "unsupported_call_effect_summary" in analysis.get_decisive_sat_unsafety_reasons()
    assert "unsupported_call_effect_summary" in analysis.get_equivalence_blocking_unsafety_reasons()


def test_pairwise_strategy_downgrades_sat_when_analysis_retains_symbolic_post_state_reads(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    analysis1 = _build_symbolic_post_state_analysis("f1")
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x2000",
        parameters=[_param("trace", index=0, size=8, data_type="int *")],
        returns=[ReturnInfo(address="0x2000", value=_const(0), conditions=[])],
        return_type="int",
    )

    trace = Expression.parameter("trace", 0, size=8)
    symbolic_case = ReturnCase(
        index=0,
        conditions=[],
        value_expr=post_state_read_expression_for_location(
            CanonicalLocation("trace", 0, 4),
            analysis1.parameters,
            symbolic=True,
        ),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    const_case = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(0),
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [symbolic_case] if analysis.function_name == "f1" else [const_case],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("ambiguous-model validation should not run for SAT-unsafe analyses")
        ),
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"trace_1": 1, "trace_2": 1},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1


def test_monolithic_strategy_downgrades_ambiguous_sat_counterexample_to_unknown():
    class _ValidationSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(
                results=[
                    SolverResult(
                        "fake",
                        SolverStatus.SAT,
                        elapsed_time=0.01,
                        model={"x_1": 5, "x_2": 5},
                    )
                ]
            )

        def run_sequential(self, query: str):
            if "(assert (= (_ bv7 32) (_ bv7 32)))" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 5, "x_2": 5})]
                )
            if "(assert (= x_1 (bvadd x_2 (_ bv1 32))))" in query:
                return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])
            return ParallelResult(
                results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 5, "x_2": 5})]
            )

    x1 = Expression.parameter("x", 0, size=4)
    x2 = Expression.parameter("x", 0, size=4)
    cond1 = _eq(x1, _const(5))
    cond2 = _eq(x2, _const(5))

    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(address="0x1", value=x1, conditions=[]),
            ReturnInfo(address="0x2", value=_const(7), conditions=[cond1]),
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(
                address="0x3",
                value=Expression.binary_op("INT_ADD", x2, _const(1)),
                conditions=[],
            ),
            ReturnInfo(address="0x4", value=_const(7), conditions=[cond2]),
        ],
        return_type="int",
    )

    params1 = [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)]
    params2 = [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)]
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": params1,
        "params2": params2,
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _ValidationSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None


def test_pairwise_strategy_downgrades_sat_when_return_cases_leave_coverage_gap(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    x = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x, _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(2), conditions=[])],
        return_type="int",
    )

    case1 = ReturnCase(
        index=0,
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=_const(1),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(2),
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "func1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("pairwise counterexample validation should not run when coverage is incomplete")
        ),
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 7, "x_2": 7},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    assert "return_case_coverage_gap" in analysis1.analysis_notes
    assert analysis2.analysis_notes == []


def test_pairwise_strategy_does_not_prove_equivalent_with_return_coverage_gap(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    x = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x, _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )

    case1 = ReturnCase(
        index=0,
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=_const(1),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(1),
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "func1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    assert "return_case_coverage_gap" in analysis1.analysis_notes


def test_pairwise_global_blocker_dominates_pair_local_unresolved_expression(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: True)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_pairs == 1
    assert {reason.reason_id for reason in result.unknown_reasons} == {
        UnknownReasonId.RETURN_COVERAGE_GAP.value,
    }
    assert all(
        reason.reason_id != UnknownReasonId.UNRESOLVED_EXPRESSION.value
        for reason in result.unknown_reasons
    )
    assert "return_case_coverage_gap" in analysis1.analysis_notes


def test_pairwise_equivalence_blocker_dominates_pair_local_unresolved_expression(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == analysis1.function_name else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: True)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_pairs == 1
    assert {reason.reason_id for reason in result.unknown_reasons} == {
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
    }
    assert all(
        reason.reason_id != UnknownReasonId.UNRESOLVED_EXPRESSION.value
        for reason in result.unknown_reasons
    )


def test_pairwise_return_coverage_covered_side_emits_completed_proof_evidence(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert analysis1.completed_recovery_proof_evidence == ()
    evidence = analysis2.completed_recovery_proof_evidence
    assert {item["proof_stage"] for item in evidence} == {
        "return_partition_extraction",
        "return_guard_coverage",
    }
    assert all(item["object_derived"] is True for item in evidence)
    assert all(item["coverage_status"] == "covered" for item in evidence)

    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function2:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    expected_actions = build_unknown_recovery_actions([completed_reason])
    assert {
        tuple(item["proof_obligation_id"])
        for item in evidence
    } == {action.proof_obligation_id for action in expected_actions}
    assert PairwiseStrategy._completed_recovery_proof_ids(analysis2) == tuple(
        action.proof_obligation_id for action in expected_actions
    )

    strategy.check(analysis1, analysis2)

    assert len(analysis2.completed_recovery_proof_evidence) == 2


def test_pairwise_completed_recovery_proofs_can_be_disabled(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(
        formula_builder,
        solver_runner,
        debug=False,
        enable_completed_recovery_proofs=False,
    )
    analysis1, analysis2 = _return_coverage_gap_analyses()
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.RETURN_COVERAGE_GAP.value,
    ]
    assert {reason.action_status for reason in result.unknown_reasons} == {
        UnknownRecoveryActionStatus.PENDING_PROOF.value
    }
    assert analysis1.completed_recovery_proof_evidence == ()
    assert analysis2.completed_recovery_proof_evidence == ()


def test_pairwise_disabled_completed_proofs_do_not_create_new_return_gap_without_active_blocker(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(
        formula_builder,
        solver_runner,
        debug=False,
        enable_completed_recovery_proofs=False,
    )
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.analysis_notes = []
    analysis2.analysis_notes = []
    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ("covered", None),
    )

    reasons = strategy._collect_return_coverage_unsafety_reasons(
        _base_context_for_single_int_param(),
        [],
        [],
        lambda value: value,
        lambda value: value,
        analysis1,
        analysis2,
    )

    assert reasons == []
    assert analysis1.completed_recovery_proof_evidence == ()
    assert analysis2.completed_recovery_proof_evidence == ()


def test_pairwise_disabled_completed_proofs_keep_summary_dependent_return_gap(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(
        formula_builder,
        solver_runner,
        debug=False,
        enable_completed_recovery_proofs=False,
    )
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.analysis_notes = []
    analysis2.analysis_notes = ["state_transition_loop_summary"]
    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ("covered", None),
    )

    reasons = strategy._collect_return_coverage_unsafety_reasons(
        _base_context_for_single_int_param(),
        [],
        [],
        lambda value: value,
        lambda value: value,
        analysis1,
        analysis2,
    )

    assert reasons == ["function2:return_coverage_gap"]
    assert analysis1.completed_recovery_proof_evidence == ()
    assert analysis2.completed_recovery_proof_evidence == ()


def test_pairwise_disabled_completed_proofs_do_not_block_switch_or_control_region_recovery(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(
        formula_builder,
        solver_runner,
        debug=False,
        enable_completed_recovery_proofs=False,
    )
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.analysis_notes = []
    analysis2.analysis_notes = [
        "switch_return_recovery",
        "control_region_return_recovery",
    ]
    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ("covered", None),
    )

    reasons = strategy._collect_return_coverage_unsafety_reasons(
        _base_context_for_single_int_param(),
        [],
        [],
        lambda value: value,
        lambda value: value,
        analysis1,
        analysis2,
    )

    assert reasons == []
    assert analysis1.completed_recovery_proof_evidence == ()
    assert analysis2.completed_recovery_proof_evidence == ()


def test_pairwise_return_coverage_gap_requires_all_completed_proof_ids(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([pending_reason])
    analysis1.completed_recovery_proof_evidence = (
        _return_coverage_completion_evidence(actions[0]),
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value


def test_pairwise_return_coverage_gap_completed_proofs_allow_equivalent(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([pending_reason])
    analysis1.completed_recovery_proof_evidence = tuple(
        _return_coverage_completion_evidence(action)
        for action in actions
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0


def test_pairwise_return_coverage_gap_wrong_completed_proof_id_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([pending_reason])
    wrong_id = build_proof_obligation_id(
        UnknownReasonId.RETURN_COVERAGE_GAP,
        actions[0].proof_stage,
        UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
        actions[0].evidence_kind,
        ("return_coverage", "different-target"),
    )
    analysis1.completed_recovery_proof_evidence = (
        _return_coverage_completion_evidence(actions[0], proof_obligation_id=wrong_id),
        _return_coverage_completion_evidence(actions[1]),
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value


def test_pairwise_return_coverage_gap_missing_completed_proof_id_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([pending_reason])
    analysis1.completed_recovery_proof_evidence = tuple(
        _return_coverage_completion_evidence_without_proof_id(action)
        for action in actions
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value


def test_pairwise_strategy_does_not_prove_equivalent_with_incomplete_effect_summary(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            incomplete_reasons=("effect_summary_path_coverage_incomplete",),
        ),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(1),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(1),
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "func1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0


def test_pairwise_strategy_does_not_prove_equivalent_with_unsupported_effect_summary(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            incomplete_reasons=(),
        ),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(1),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(1),
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "func1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0


def test_pairwise_call_effect_summary_proof_pending_blocks_equivalent(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert result.unknown_reasons[0].proof_obligation_id is not None


def test_pairwise_sat_unsafety_emits_object_derived_pending_proof_backlog(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 0, "x_2": 0},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.SAT_UNSAFETY.value
    assert reason.decision_effect == "blocks_disequivalence"
    assert reason.recovery_proof_kind == UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.recovery_action == "sat_unsafety_resolution_required"
    assert reason.object_target_key[0] == "sat_unsafety"
    assert reason.proof_obligation_id == build_proof_obligation_id(
        UnknownReasonId.SAT_UNSAFETY,
        "sat_counterexample_safety",
        UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION,
        "active_unsafety_summary",
        reason.object_target_key,
    )
    actions = build_unknown_recovery_actions([reason])
    assert len(actions) == 1
    assert actions[0].required_evidence == (
        "counterexample_replay",
        "active_unsafety_discharge",
        "coverage_effect_safety",
    )
    assert actions[0].proof_obligation_id == reason.proof_obligation_id


def test_pairwise_sat_unsafety_completed_proof_allows_decisive_sat(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == analysis1.function_name else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: True,
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 0, "x_2": 0},
        )
    )
    reason = strategy._make_sat_unsafety_unknown_reason(
        ("function1:unsupported_call_effect_summary",),
        analysis1,
        analysis2,
        case1=case1,
        case2=case2,
        pair_id="(0,0)",
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    analysis1.completed_recovery_proof_evidence = (
        _sat_unsafety_resolution_evidence(action),
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is False
    assert result.sat_pairs == 1
    assert result.unknown_reasons == []


def test_sat_unsafety_completed_proof_rejects_active_blocker_fields_on_evidence():
    action = _sat_unsafety_resolution_action()
    blocker_fields = (
        "active_coverage_gap_reasons",
        "unsupported_call_effect_reasons",
        "unsupported_memory_effect_reasons",
    )

    for field_name in blocker_fields:
        evidence = _sat_unsafety_resolution_evidence(action, **{field_name: ("still-active",)})

        assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(evidence) is None


def test_sat_unsafety_completed_proof_rejects_active_blocker_fields_inside_proof_content():
    action = _sat_unsafety_resolution_action()
    blocker_fields = (
        "active_coverage_gap_reasons",
        "unsupported_call_effect_reasons",
        "unsupported_memory_effect_reasons",
    )

    for field_name in blocker_fields:
        evidence = deepcopy(_sat_unsafety_resolution_evidence(action))
        evidence["proof_content"]["coverage_effect_safety"][field_name] = ("still-active",)

        assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(evidence) is None


def test_sat_unsafety_completed_proof_requires_object_derived_proof_content():
    action = _sat_unsafety_resolution_action()
    evidence = deepcopy(_sat_unsafety_resolution_evidence(action))
    evidence["proof_content"].pop("object_derived", None)

    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(evidence) is None


def test_sat_unsafety_completed_proof_rejects_nested_blocker_fields_inside_proof_content():
    action = _sat_unsafety_resolution_action()
    evidence = deepcopy(_sat_unsafety_resolution_evidence(action))
    evidence["proof_content"]["coverage_effect_safety"]["details"] = {
        "unsupported_call_effect_reasons": ("still-active",),
    }

    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(evidence) is None


def test_pairwise_sat_unsafety_metadata_only_completed_proof_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 0, "x_2": 0},
        )
    )
    pending_reason = strategy._make_sat_unsafety_unknown_reason(
        ("function1:unsupported_call_effect_summary",),
        analysis1,
        analysis2,
        case1=ReturnCase(
            index=0,
            conditions=[],
            value_expr=analysis1.returns[0].value,
            return_info=analysis1.returns[0],
            return_type=analysis1.return_type or "int",
            parameters=analysis1.parameters,
        ),
        case2=ReturnCase(
            index=0,
            conditions=[],
            value_expr=analysis2.returns[0].value,
            return_info=analysis2.returns[0],
            return_type=analysis2.return_type or "int",
            parameters=analysis2.parameters,
        ),
        pair_id="(0,0)",
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([pending_reason])[0]
    evidence = _sat_unsafety_resolution_evidence(action)
    evidence.pop("proof_content", None)
    analysis1.completed_recovery_proof_evidence = (evidence,)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.SAT_UNSAFETY.value


def test_pairwise_call_effect_summary_proof_wrong_id_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    wrong_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    analysis1.completed_recovery_proof_ids = (
        (
            wrong_reason.reason_id,
            wrong_reason.proof_stage,
            wrong_reason.recovery_proof_kind,
            wrong_reason.evidence_kind,
            ("unsupported_call_effect", "different-callsite"),
        ),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value


def test_pairwise_call_effect_summary_bare_completed_proof_id_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    analysis1.completed_recovery_proof_ids = (completed_reason.proof_obligation_id,)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value


def test_pairwise_call_effect_summary_missing_completed_proof_id_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    evidence = _call_effect_summary_proof_evidence(
        object_target_key=completed_reason.object_target_key,
        proof_obligation_id=completed_reason.proof_obligation_id,
    )
    evidence.pop("proof_obligation_id", None)
    analysis1.completed_recovery_proof_evidence = (evidence,)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value


def test_pairwise_call_effect_summary_producer_connects_completed_target_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    analysis1.completed_recovery_proof_evidence = (
        _call_effect_summary_proof_evidence(
            object_target_key=completed_reason.object_target_key,
            proof_obligation_id=completed_reason.proof_obligation_id,
        ),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0


def test_call_effect_summary_producer_emits_only_object_derived_full_ids():
    evidence = _call_effect_summary_proof_evidence()
    analysis = _analysis_with_call_effect_summary_proof_evidence()

    proof_ids = PairwiseStrategy._completed_recovery_proof_ids(analysis)

    assert proof_ids == (_expected_call_effect_summary_proof_id(evidence),)


def test_call_effect_summary_producer_rejects_missing_full_proof_id():
    evidence = _call_effect_summary_proof_evidence()
    evidence.pop("proof_obligation_id", None)
    analysis = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        completed_recovery_proof_evidence=(evidence,),
    )

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis) == ()


def test_call_effect_summary_producer_rejects_non_object_derived_evidence():
    analysis = _analysis_with_call_effect_summary_proof_evidence(object_derived=False)

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis) == ()


def test_call_effect_summary_producer_rejects_mismatched_full_proof_id():
    evidence = _call_effect_summary_proof_evidence()
    wrong_id = build_proof_obligation_id(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
        evidence["proof_stage"],
        evidence["recovery_proof_kind"],
        evidence["evidence_kind"],
        ("unsupported_call_effect", "different-callsite"),
    )
    analysis = _analysis_with_call_effect_summary_proof_evidence(
        proof_obligation_id=wrong_id,
    )

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis) == ()


def test_call_effect_summary_producer_rejects_active_safety_blockers():
    coverage_blocked = _analysis_with_call_effect_summary_proof_evidence()
    coverage_blocked.analysis_notes.append("return_case_coverage_gap")
    sat_blocked = _analysis_with_call_effect_summary_proof_evidence()
    sat_blocked.analysis_notes.append("indirect_control_flow_unresolved")
    unsupported_blocked = _analysis_with_call_effect_summary_proof_evidence(
        unsupported_effect_reasons=("target_identity_unavailable",),
    )

    assert PairwiseStrategy._completed_recovery_proof_ids(coverage_blocked) == ()
    assert PairwiseStrategy._completed_recovery_proof_ids(sat_blocked) == ()
    assert PairwiseStrategy._completed_recovery_proof_ids(unsupported_blocked) == ()


def test_monolithic_strategy_downgrades_sat_when_return_cases_leave_coverage_gap():
    class _CoverageGapSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(
                results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
            )

        def run_sequential(self, query: str):
            if "Return coverage gap query: function1" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
                )
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    x1 = Expression.parameter("x", 0, size=4)
    x2 = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x1, _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x2, conditions=[])],
        return_type="int",
    )

    params1 = [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)]
    params2 = [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)]
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": params1,
        "params2": params2,
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _CoverageGapSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None


def test_monolithic_strategy_does_not_accept_unsat_with_return_coverage_gap():
    class _CoverageGapUnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, query: str):
            if "Return coverage gap query: function1" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
                )
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    x1 = Expression.parameter("x", 0, size=4)
    x2 = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x1, _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x2, conditions=[])],
        return_type="int",
    )

    params1 = [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)]
    params2 = [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)]
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": params1,
        "params2": params2,
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _CoverageGapUnsatSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None
    assert "return_case_coverage_gap" in analysis1.analysis_notes
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert result.unknown_reasons[0].stage == "S_MONOLITHIC_FALLBACK"
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert result.unknown_reasons[0].recovery_action == "return_coverage_proof_required"
    assert result.unknown_reasons[0].object_target_key[0] == "return_coverage"
    actions = build_unknown_recovery_actions(result.unknown_reasons)
    assert {action.status for action in actions} == {UnknownRecoveryActionStatus.PENDING_PROOF.value}
    assert all(action.proof_obligation_id is not None for action in actions)


def test_monolithic_return_coverage_gap_completed_proofs_allow_equivalent():
    strategy, analysis1, analysis2 = _monolithic_return_coverage_gap_setup()
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_MONOLITHIC_FALLBACK",
    )
    actions = build_unknown_recovery_actions([completed_reason])
    analysis1.completed_recovery_proof_evidence = tuple(
        _return_coverage_completion_evidence(action)
        for action in actions
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert result.counterexample_raw is None


def test_monolithic_return_coverage_gap_missing_completed_proof_id_does_not_recover():
    strategy, analysis1, analysis2 = _monolithic_return_coverage_gap_setup()
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_MONOLITHIC_FALLBACK",
    )
    actions = build_unknown_recovery_actions([completed_reason])
    analysis1.completed_recovery_proof_evidence = tuple(
        _return_coverage_completion_evidence_without_proof_id(action)
        for action in actions
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert result.counterexample_raw is None


def test_monolithic_strategy_does_not_accept_unsat_with_incomplete_effect_summary():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            incomplete_reasons=("effect_summary_path_coverage_incomplete",),
        ),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )

    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None


def test_monolithic_strategy_does_not_accept_unsat_with_unsupported_effect_summary():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            incomplete_reasons=(),
        ),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )

    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None


def test_monolithic_call_effect_summary_proof_complete_allows_recovery():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_MONOLITHIC_FALLBACK",
    )
    analysis1.completed_recovery_proof_evidence = (
        _call_effect_summary_proof_evidence(
            object_target_key=completed_reason.object_target_key,
            proof_obligation_id=completed_reason.proof_obligation_id,
        ),
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert result.counterexample_raw is None


def test_monolithic_call_effect_summary_bare_completed_proof_id_does_not_recover():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_MONOLITHIC_FALLBACK",
    )
    analysis1.completed_recovery_proof_ids = (completed_reason.proof_obligation_id,)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.counterexample_raw is None


def test_monolithic_call_effect_summary_missing_completed_proof_id_does_not_recover():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_MONOLITHIC_FALLBACK",
    )
    evidence = _call_effect_summary_proof_evidence(
        object_target_key=completed_reason.object_target_key,
        proof_obligation_id=completed_reason.proof_obligation_id,
    )
    evidence.pop("proof_obligation_id", None)
    analysis1.completed_recovery_proof_evidence = (evidence,)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.counterexample_raw is None


def test_function_return_analysis_skips_monolithic_fallback_when_coverage_gap_note_is_present():
    analysis = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))])],
        return_type="int",
        analysis_notes=["return_case_coverage_gap"],
    )

    assert analysis.should_skip_monolithic_fallback() is True
    assert "return_case_coverage_gap" in analysis.get_decisive_sat_unsafety_reasons()


def test_pairwise_strategy_downgrades_unsat_when_deferred_call_recovery_is_inconclusive(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    x = Expression.parameter("x", 0, size=4)
    pcode_ref = PcodeOpRef(address_offset=0x3000, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[Expression.parameter("param_1", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee"),
            sequence=0,
        ),
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        call_argument_recovery_reason="argument_recovery_inconclusive",
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=x, conditions=[])],
        return_type="int",
    )
    analysis1.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x, conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=x,
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=x,
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "func1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        strategy,
        "_case_contains_unresolved_expression",
        lambda *_args, **_kwargs: False,
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(is_equivalent=True)
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0


def test_pairwise_strategy_records_call_effect_blocker_as_pending_object_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    x = Expression.parameter("x", 0, size=4)
    pcode_ref = PcodeOpRef(address_offset=0x3000, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
        arguments=[Expression.parameter("param_1", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            caller_program_id=1,
            caller_entry_offset=0x400000,
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
            sequence=0,
        ),
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        call_argument_recovery_reason="argument_recovery_inconclusive",
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=x, conditions=[])],
        return_type="int",
    )
    analysis1.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x, conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=x,
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=x,
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "func1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert len(result.unknown_reasons) == 1
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value
    assert reason.recovery_proof_kind == UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value
    assert reason.proof_stage == "object_evidence_collected"
    assert reason.evidence_kind == "call_effect_summary"
    assert reason.recovery_action == "call_effect_summary_proof_required"
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.object_target_key[0] == "deferred_call"
    assert pcode_ref.stable_key() in reason.object_target_key


def test_pairwise_strategy_uses_unsupported_call_site_object_ref_for_blocking_proof():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    site = UnsupportedCallEffectRef(
        pcode_op_ref=pcode_ref,
        target_ref=None,
        reason="target_identity_unavailable",
        order_key=9,
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )

    assert reason.recovery_proof_kind == UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.object_target_key[0] == "unsupported_call_effect"
    assert pcode_ref.stable_key() in reason.object_target_key


def test_pairwise_unsupported_call_effect_uses_phase2_specific_object_key():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(
        address_offset=0x401020,
        seq_time=31,
        seq_order=7,
        mnemonic="CALLIND",
        binary_id="B10",
        program_uid=12345,
        function_entry_space="ram",
        function_entry_offset=0x401000,
        target_space="ram",
        target_offset=0x401020,
        opcode=8,
        local_op_ordinal=0,
    )
    site = UnsupportedCallEffectRef(
        pcode_op_ref=pcode_ref,
        target_ref=CallTargetRef.from_code_address(0x401234, program_id=12345),
        target_expr=Expression.parameter("fp", 0, size=8),
        reason="target_identity_unavailable",
        order_key=9,
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x401000",
        function_ref=CallTargetRef.from_name("func1", program_id=12345, entry_offset=0x401000),
        binary_id="B10",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x401000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x402000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x402000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )

    assert reason.object_target_key[0] == "unsupported_call_effect"
    assert reason.object_target_key[2] == ("function_ref", ("function", "B10", 0x401000))
    assert reason.object_target_key[3] == pcode_ref.stable_key()
    assert reason.object_target_key[4] == ("code_address", "B10", 0x401234)
    assert _object_target_key_is_specific(reason.object_target_key) is True
    assert reason.proof_obligation_id == build_proof_obligation_id(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
        "object_evidence_collected",
        UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value,
        "call_effect_summary",
        reason.object_target_key,
    )


def test_unsupported_call_site_object_key_keeps_caller_identity_distinct():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    site = UnsupportedCallEffectRef(
        pcode_op_ref=pcode_ref,
        target_ref=None,
        reason="target_identity_unavailable",
        order_key=9,
    )
    left = FunctionReturnAnalysis(
        function_name="func",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    right = FunctionReturnAnalysis(
        function_name="func",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func", program_id=2, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )

    left_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        left,
        right,
        stage="S_PAIRWISE",
    )
    right_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function2:unsupported_call_effect_summary",
        left,
        right,
        stage="S_PAIRWISE",
    )

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id
    assert ("function_ref", ("function", 1, 0x1000)) in left_reason.object_target_key
    assert ("function_ref", ("function", 2, 0x1000)) in right_reason.object_target_key


def test_unsupported_call_effect_blocker_prefers_unsupported_site_over_deferred_call():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    unsupported_pcode = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    deferred_pcode = PcodeOpRef(address_offset=0x4000, seq_time=7, seq_order=2, mnemonic="CALL")
    site = UnsupportedCallEffectRef(
        pcode_op_ref=unsupported_pcode,
        target_ref=None,
        reason="target_identity_unavailable",
        order_key=9,
    )
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
        arguments=[Expression.parameter("x", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            caller_program_id=1,
            caller_entry_offset=0x1000,
            pcode_op_ref=deferred_pcode,
            target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
            sequence=0,
        ),
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
    )
    analysis = FunctionReturnAnalysis(
        function_name="func",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    other = FunctionReturnAnalysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis,
        other,
        stage="S_PAIRWISE",
    )

    assert reason.object_target_key[0] == "unsupported_call_effect"
    assert unsupported_pcode.stable_key() in reason.object_target_key
    assert deferred_pcode.stable_key() not in reason.object_target_key


def test_deferred_call_object_key_distinguishes_unknown_target_expression_provenance():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    deferred_ref = DeferredCallRef(
        caller_program_id=1,
        caller_entry_offset=0x1000,
        pcode_op_ref=pcode_ref,
        target_ref=CallTargetRef.unknown(),
        sequence=0,
    )

    def _analysis_with_target_expr(target_expr: Expression) -> FunctionReturnAnalysis:
        deferred = DeferredCallInfo(
            placeholder_name="indirect",
            target_ref=CallTargetRef.unknown(),
            arguments=[Expression.parameter("x", 0, size=4)],
            call_target_expr=target_expr,
            deferred_call_ref=deferred_ref,
            call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        )
        analysis = FunctionReturnAnalysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
        return analysis

    left = _analysis_with_target_expr(Expression.parameter("fp", 0, size=8))
    right = _analysis_with_target_expr(Expression.parameter("gp", 1, size=8))
    other = FunctionReturnAnalysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    left_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        left,
        other,
        stage="S_PAIRWISE",
    )
    right_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        right,
        other,
        stage="S_PAIRWISE",
    )

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id
    assert ("typed_target_expression", ("expression", ("parameter", "fp", ("int", 0), 8))) in left_reason.object_target_key
    assert ("typed_target_expression", ("expression", ("parameter", "gp", ("int", 1), 8))) in right_reason.object_target_key


def test_deferred_call_object_key_distinguishes_truncated_target_expression_provenance():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    deferred_ref = DeferredCallRef(
        caller_program_id=1,
        caller_entry_offset=0x1000,
        pcode_op_ref=pcode_ref,
        target_ref=CallTargetRef.unknown(),
        sequence=0,
    )

    def _analysis_with_target_expr(target_expr: Expression) -> FunctionReturnAnalysis:
        deferred = DeferredCallInfo(
            placeholder_name="indirect",
            target_ref=CallTargetRef.unknown(),
            arguments=[Expression.parameter("x", 0, size=4)],
            call_target_expr=target_expr,
            deferred_call_ref=deferred_ref,
            call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        )
        analysis = FunctionReturnAnalysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
        return analysis

    left = _analysis_with_target_expr(_deep_zext_target("fp", 0))
    right = _analysis_with_target_expr(_deep_zext_target("gp", 1))
    other = FunctionReturnAnalysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    left_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        left,
        other,
        stage="S_PAIRWISE",
    )
    right_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        right,
        other,
        stage="S_PAIRWISE",
    )

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id


def test_expression_provenance_key_handles_very_deep_target_expression_without_recursion_error():
    left_key = expression_provenance_key(_deep_zext_target("fp", 0, depth=900))
    right_key = expression_provenance_key(_deep_zext_target("gp", 1, depth=900))

    assert left_key != right_key


def test_expression_provenance_key_distinguishes_sources_beyond_digest_node_limit():
    left_key = expression_provenance_key(_deep_zext_target("fp", 0, depth=8200))
    right_key = expression_provenance_key(_deep_zext_target("gp", 1, depth=8200))

    assert left_key != right_key


def test_expression_provenance_key_distinguishes_deep_tail_structure_beyond_digest_node_limit():
    zext_key = expression_provenance_key(
        _deep_target_with_tail_op("fp", 0, "INT_ZEXT", depth=8200)
    )
    sext_key = expression_provenance_key(
        _deep_target_with_tail_op("fp", 0, "INT_SEXT", depth=8200)
    )

    assert zext_key != sext_key


def test_unsupported_call_effect_object_key_distinguishes_target_expression_provenance():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")

    def _analysis_with_site(target_expr: Expression) -> FunctionReturnAnalysis:
        site = UnsupportedCallEffectRef(
            pcode_op_ref=pcode_ref,
            target_ref=None,
            target_expr=target_expr,
            reason="target_identity_unavailable",
            order_key=9,
        )
        return FunctionReturnAnalysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                has_unsupported_call=True,
                unsupported_call_sites=(site,),
            ),
        )

    left = _analysis_with_site(Expression.parameter("fp", 0, size=8))
    right = _analysis_with_site(Expression.parameter("gp", 1, size=8))
    other = FunctionReturnAnalysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    left_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        left,
        other,
        stage="S_PAIRWISE",
    )
    right_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        right,
        other,
        stage="S_PAIRWISE",
    )

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id
    assert ("typed_target_expression", ("expression", ("parameter", "fp", ("int", 0), 8))) in left_reason.object_target_key
    assert ("typed_target_expression", ("expression", ("parameter", "gp", ("int", 1), 8))) in right_reason.object_target_key


def test_unsupported_call_effect_object_key_does_not_embed_process_local_target_expression_id():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3030, seq_time=5, seq_order=1, mnemonic="CALLIND")
    target_expr = _deep_zext_target("fp", 0)

    site = UnsupportedCallEffectRef(
        pcode_op_ref=pcode_ref,
        target_ref=None,
        target_expr=target_expr,
        reason="target_identity_unavailable",
        order_key=10,
    )
    analysis = FunctionReturnAnalysis(
        function_name="func",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    other = FunctionReturnAnalysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis,
        other,
        stage="S_PAIRWISE",
    )

    target_identity = id(target_expr)
    assert not _nested_contains(site.stable_key(), target_identity)
    assert not _nested_contains(reason.object_target_key, target_identity)
    assert not _nested_contains(reason.proof_obligation_id, target_identity)


def test_unsupported_call_effect_object_key_distinguishes_truncated_target_expression_provenance():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3030, seq_time=5, seq_order=1, mnemonic="CALLIND")

    def _reason_for(target_expr: Expression):
        site = UnsupportedCallEffectRef(
            pcode_op_ref=pcode_ref,
            target_ref=None,
            target_expr=target_expr,
            reason="target_identity_unavailable",
            order_key=10,
        )
        analysis = FunctionReturnAnalysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                has_unsupported_call=True,
                unsupported_call_sites=(site,),
            ),
        )
        other = FunctionReturnAnalysis(
            function_name="other",
            entry_point="0x2000",
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        return site, strategy._make_blocking_unsafety_unknown_reason(
            "function1:unsupported_call_effect_summary",
            analysis,
            other,
            stage="S_PAIRWISE",
        )

    left_site, left_reason = _reason_for(_deep_zext_target("fp", 0))
    right_site, right_reason = _reason_for(_deep_zext_target("gp", 1))

    assert left_site.stable_key() != right_site.stable_key()
    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id


def test_unsupported_call_effect_object_key_handles_very_deep_target_expression_without_recursion_error():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3030, seq_time=5, seq_order=1, mnemonic="CALLIND")

    def _reason_for(target_expr: Expression):
        site = UnsupportedCallEffectRef(
            pcode_op_ref=pcode_ref,
            target_ref=None,
            target_expr=target_expr,
            reason="target_identity_unavailable",
            order_key=10,
        )
        analysis = FunctionReturnAnalysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                has_unsupported_call=True,
                unsupported_call_sites=(site,),
            ),
        )
        other = FunctionReturnAnalysis(
            function_name="other",
            entry_point="0x2000",
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        return strategy._make_blocking_unsafety_unknown_reason(
            "function1:unsupported_call_effect_summary",
            analysis,
            other,
            stage="S_PAIRWISE",
        )

    left_reason = _reason_for(_deep_zext_target("fp", 0, depth=900))
    right_reason = _reason_for(_deep_zext_target("gp", 1, depth=900))

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id


def test_unsupported_call_effect_object_key_distinguishes_sources_beyond_digest_node_limit():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3030, seq_time=5, seq_order=1, mnemonic="CALLIND")

    def _reason_for(target_expr: Expression):
        site = UnsupportedCallEffectRef(
            pcode_op_ref=pcode_ref,
            target_ref=None,
            target_expr=target_expr,
            reason="target_identity_unavailable",
            order_key=10,
        )
        analysis = FunctionReturnAnalysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                has_unsupported_call=True,
                unsupported_call_sites=(site,),
            ),
        )
        other = FunctionReturnAnalysis(
            function_name="other",
            entry_point="0x2000",
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        return strategy._make_blocking_unsafety_unknown_reason(
            "function1:unsupported_call_effect_summary",
            analysis,
            other,
            stage="S_PAIRWISE",
        )

    left_reason = _reason_for(_deep_zext_target("fp", 0, depth=8200))
    right_reason = _reason_for(_deep_zext_target("gp", 1, depth=8200))

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id


def test_unsupported_call_effect_object_key_distinguishes_deep_tail_structure_beyond_digest_node_limit():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3030, seq_time=5, seq_order=1, mnemonic="CALLIND")

    def _reason_for(target_expr: Expression):
        site = UnsupportedCallEffectRef(
            pcode_op_ref=pcode_ref,
            target_ref=None,
            target_expr=target_expr,
            reason="target_identity_unavailable",
            order_key=10,
        )
        analysis = FunctionReturnAnalysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                has_unsupported_call=True,
                unsupported_call_sites=(site,),
            ),
        )
        other = FunctionReturnAnalysis(
            function_name="other",
            entry_point="0x2000",
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        return strategy._make_blocking_unsafety_unknown_reason(
            "function1:unsupported_call_effect_summary",
            analysis,
            other,
            stage="S_PAIRWISE",
        )

    zext_reason = _reason_for(_deep_target_with_tail_op("fp", 0, "INT_ZEXT", depth=8200))
    sext_reason = _reason_for(_deep_target_with_tail_op("fp", 0, "INT_SEXT", depth=8200))

    assert zext_reason.object_target_key != sext_reason.object_target_key
    assert zext_reason.proof_obligation_id != sext_reason.proof_obligation_id


def _nested_contains(value, needle) -> bool:
    if value == needle:
        return True
    if isinstance(value, (tuple, list)):
        return any(_nested_contains(item, needle) for item in value)
    if isinstance(value, dict):
        return any(
            _nested_contains(key, needle) or _nested_contains(item, needle)
            for key, item in value.items()
        )
    return False


def test_blocking_unsafety_reason_mapping_accepts_detail_suffix_for_return_coverage():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)

    assert (
        strategy._unknown_reason_id_for_blocking_unsafety("function1:return_coverage_gap:case=3")
        == UnknownReasonId.RETURN_COVERAGE_GAP
    )
    assert (
        strategy._unknown_reason_id_for_blocking_unsafety("function2:return_coverage_inconclusive:branch=exit")
        == UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
    )


def test_return_coverage_gap_emits_object_derived_pending_proof_backlog():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    x = Expression.parameter("x", 0, size=4)
    return_ref = PcodeOpRef(
        address_offset=0x401020,
        seq_time=0x401020,
        seq_order=3,
        block_index=1,
        mnemonic="RETURN",
        input_sizes=(8, 4),
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x401000",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(
                address="0x401020",
                value=_const(1),
                conditions=[_eq(x, _const(0))],
                pcode_op_ref=return_ref,
            )
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x402000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x402020", value=_const(1), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([reason])

    assert reason.reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.recovery_action == "return_coverage_proof_required"
    assert reason.object_target_key[0] == "return_coverage"
    assert return_ref.stable_key() in reason.object_target_key[5][1][0]
    assert ("return_storage", "return_value", 32, None, "int") in reason.object_target_key
    assert [action.proof_stage for action in actions] == [
        "return_partition_extraction",
        "return_guard_coverage",
    ]
    assert {action.status for action in actions} == {
        UnknownRecoveryActionStatus.PENDING_PROOF.value
    }
    assert actions[0].proof_obligation_id == build_proof_obligation_id(
        UnknownReasonId.RETURN_COVERAGE_GAP,
        "return_partition_extraction",
        UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
        "missing_return_guard",
        reason.object_target_key,
    )


def test_return_coverage_object_target_ignores_diagnostic_suffix():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    x = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x401000",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(address="0x401020", value=_const(1), conditions=[_eq(x, _const(0))])
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x402000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x402020", value=_const(1), conditions=[])],
        return_type="int",
    )

    plain_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    suffixed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap:case=3",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )

    assert plain_reason.object_target_key == suffixed_reason.object_target_key
    assert build_unknown_recovery_actions([plain_reason])[0].proof_obligation_id == (
        build_unknown_recovery_actions([suffixed_reason])[0].proof_obligation_id
    )


def test_return_coverage_object_target_distinguishes_guard_partitions():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    x = Expression.parameter("x", 0, size=4)
    left_zero = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x401000",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(address="0x401020", value=_const(1), conditions=[_eq(x, _const(0))])
        ],
        return_type="int",
    )
    left_one = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x401000",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(address="0x401020", value=_const(1), conditions=[_eq(x, _const(1))])
        ],
        return_type="int",
    )
    right = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x402000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x402020", value=_const(1), conditions=[])],
        return_type="int",
    )

    zero_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        left_zero,
        right,
        stage="S_PAIRWISE",
    )
    one_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        left_one,
        right,
        stage="S_PAIRWISE",
    )

    assert zero_reason.object_target_key != one_reason.object_target_key
    assert build_unknown_recovery_actions([zero_reason])[0].proof_obligation_id != (
        build_unknown_recovery_actions([one_reason])[0].proof_obligation_id
    )


def test_monolithic_strategy_does_not_accept_unsat_with_deferred_call_argument_inconclusive():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    x = Expression.parameter("x", 0, size=4)
    pcode_ref = PcodeOpRef(address_offset=0x3010, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[Expression.parameter("param_1", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee"),
            sequence=0,
        ),
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        call_argument_recovery_reason="argument_recovery_inconclusive",
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=x, conditions=[])],
        return_type="int",
    )
    analysis1.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x, conditions=[])],
        return_type="int",
    )

    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None

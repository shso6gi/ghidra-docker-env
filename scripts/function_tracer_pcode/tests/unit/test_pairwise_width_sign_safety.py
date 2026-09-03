# -*- coding: utf-8 -*-

from types import MethodType, SimpleNamespace
from unittest.mock import Mock

from scripts.function_tracer_pcode.semantics.semantic_width import RETURN_EXTENSION_SURFACE_SOURCE
from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.proof.strategies.pairwise_models import QueryResult
from scripts.function_tracer_pcode.proof.obligations import SolverQueryExecutionReceipt
from scripts.function_tracer_pcode.core import (
    ComparisonSurface,
    Expression,
    FunctionReturnAnalysis,
    ReturnInfo,
)


_CROSS_SIDE_EXTENSION_SURFACE_EVIDENCE = {
    "source": RETURN_EXTENSION_SURFACE_SOURCE,
    "extension_surface_bit_width": 32,
    "return_width_sign_artifact": True,
    "extension_surface_coercion": "equal_width_or_object_proven_extract",
    "extension_surface_extension_kind": "INT_ZEXT",
    "extension_surface_source_bit_widths": (32,),
}


def _solver_bound_sat_result() -> QueryResult:
    query = "(check-sat)"
    model = {}
    parallel_result = SimpleNamespace(
        is_equivalent=False,
        results=(),
        get_counterexample=lambda: model,
    )
    result = QueryResult(
        is_equivalent=False,
        counterexample_raw=model,
        solver_results=parallel_result,
    )
    result.last_query = query
    result.solver_query_execution_receipt = (
        SolverQueryExecutionReceipt.from_execution(
            query=query,
            query_label="(0,0)",
            proof_stage="with-ineq",
            parallel_result=parallel_result,
            solver_identity=("unit", "fake", ("fake",)),
            timeout_budget=5.0,
            use_hard_timeout=False,
        )
    )
    return result


def _analysis(
    name: str,
    value: Expression,
    *,
    return_type: str = "long",
    use_sign_extension=None,
    surface_evidence=None,
    surface_bits: int = 64,
) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name=name,
        entry_point="0x1000",
        parameters=[],
        returns=[ReturnInfo(address="0x1000", value=value, conditions=[])],
        return_type=return_type,
        comparison_surface=None
        if use_sign_extension is None
        else ComparisonSurface(
            kind="return_value",
            explicit_bit_width=surface_bits,
            type_name=return_type,
            use_sign_extension=bool(use_sign_extension),
            evidence=dict(surface_evidence or {}),
        ),
    )


def test_pairwise_keeps_constant_return_width_sign_sat_decisive_without_surface_evidence():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    strategy.formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 64,
        "return_size2": 64,
    }

    def _sat_query(_self, *_args, **_kwargs):
        return _solver_bound_sat_result()

    strategy._solve_query_after_guard = MethodType(_sat_query, strategy)

    result = strategy.check(
        _analysis(
            "o0",
            Expression.constant(0x00000000FFFFFED4, size=8),
            return_type="ulong",
            use_sign_extension=False,
        ),
        _analysis(
            "o1",
            Expression.constant(0xFFFFFFFFFFFFFED4, size=8),
            return_type="ulong",
            use_sign_extension=False,
        ),
    )

    assert result.is_equivalent is False
    assert result.sat_pairs == 1
    assert result.unknown_pairs == 0


def test_pairwise_keeps_constant_return_width_sign_sat_artifact_not_equivalent_with_surface_evidence():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    strategy.formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 64,
        "return_size2": 64,
    }

    def _sat_query(_self, *_args, **_kwargs):
        return _solver_bound_sat_result()

    strategy._solve_query_after_guard = MethodType(_sat_query, strategy)

    result = strategy.check(
        _analysis(
            "o0",
            Expression.constant(0x00000000FFFFFED4, size=8),
            return_type="ulong",
            use_sign_extension=False,
            surface_evidence=_CROSS_SIDE_EXTENSION_SURFACE_EVIDENCE,
            surface_bits=32,
        ),
        _analysis(
            "o1",
            Expression.constant(0xFFFFFFFFFFFFFED4, size=8),
            return_type="ulong",
            use_sign_extension=False,
            surface_evidence=_CROSS_SIDE_EXTENSION_SURFACE_EVIDENCE,
            surface_bits=32,
        ),
    )

    assert result.is_equivalent is False
    assert result.sat_pairs == 1
    assert result.unknown_pairs == 0


def test_pairwise_keeps_subsurface_constant_sign_artifact_decisive_for_wider_surface():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    strategy.formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 64,
        "return_size2": 64,
    }

    def _sat_query(_self, *_args, **_kwargs):
        return _solver_bound_sat_result()

    strategy._solve_query_after_guard = MethodType(_sat_query, strategy)

    result = strategy.check(
        _analysis(
            "o0",
            Expression.constant(0x000000000000FED4, size=8),
            return_type="ulong",
            use_sign_extension=False,
            surface_evidence=_CROSS_SIDE_EXTENSION_SURFACE_EVIDENCE,
            surface_bits=32,
        ),
        _analysis(
            "o1",
            Expression.constant(0xFFFFFFFFFFFFFED4, size=8),
            return_type="ulong",
            use_sign_extension=False,
            surface_evidence=_CROSS_SIDE_EXTENSION_SURFACE_EVIDENCE,
            surface_bits=32,
        ),
    )

    assert result.is_equivalent is False
    assert result.sat_pairs == 1
    assert result.unknown_pairs == 0


def test_pairwise_keeps_constant_return_width_sign_sat_decisive_with_one_sided_surface_evidence():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    strategy.formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 64,
        "return_size2": 64,
    }

    def _sat_query(_self, *_args, **_kwargs):
        return _solver_bound_sat_result()

    strategy._solve_query_after_guard = MethodType(_sat_query, strategy)

    result = strategy.check(
        _analysis(
            "o0",
            Expression.constant(0x00000000FFFFFED4, size=8),
            return_type="ulong",
            use_sign_extension=False,
            surface_evidence=_CROSS_SIDE_EXTENSION_SURFACE_EVIDENCE,
            surface_bits=32,
        ),
        _analysis(
            "o1",
            Expression.constant(0xFFFFFFFFFFFFFED4, size=8),
            return_type="ulong",
            use_sign_extension=False,
        ),
    )

    assert result.is_equivalent is False
    assert result.sat_pairs == 1
    assert result.unknown_pairs == 0


def test_pairwise_keeps_constant_return_width_sign_sat_decisive_with_detached_surface_evidence():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    strategy.formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 64,
        "return_size2": 64,
    }

    def _sat_query(_self, *_args, **_kwargs):
        return _solver_bound_sat_result()

    strategy._solve_query_after_guard = MethodType(_sat_query, strategy)

    result = strategy.check(
        _analysis(
            "o0",
            Expression.constant(0x00000000FFFFFED4, size=8),
            return_type="ulong",
            use_sign_extension=False,
            surface_evidence=_CROSS_SIDE_EXTENSION_SURFACE_EVIDENCE,
        ),
        _analysis(
            "o1",
            Expression.constant(0xFFFFFFFFFFFFFED4, size=8),
            return_type="ulong",
            use_sign_extension=False,
            surface_evidence=_CROSS_SIDE_EXTENSION_SURFACE_EVIDENCE,
        ),
    )

    assert result.is_equivalent is False
    assert result.sat_pairs == 1
    assert result.unknown_pairs == 0


def test_pairwise_keeps_true_constant_sat_decisive():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    strategy.formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 64,
        "return_size2": 64,
    }

    def _sat_query(_self, *_args, **_kwargs):
        return _solver_bound_sat_result()

    strategy._solve_query_after_guard = MethodType(_sat_query, strategy)

    result = strategy.check(
        _analysis("a", Expression.constant(1, size=8)),
        _analysis("b", Expression.constant(2, size=8)),
    )

    assert result.is_equivalent is False
    assert result.sat_pairs == 1

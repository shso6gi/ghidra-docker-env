# -*- coding: utf-8 -*-
"""Regression tests for explicit comparison surfaces backed by memory effects."""

from __future__ import annotations

import shutil
import subprocess

import pytest

from conftest import resolve_mock_data_type
from scripts.function_tracer_pcode.analysis.effect_summary import (
    EffectSummary,
    StoreEffect,
    build_void_effect_summary_expr,
)
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.equivalence.formula.symbol_replace import (
    build_symbol_replacer,
)
from scripts.function_tracer_pcode.equivalence.semantic_width import (
    normalize_analysis_semantic_width,
)
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_query_builder import (
    build_pair_query,
    extract_return_cases,
)
from scripts.function_tracer_pcode.model import (
    CanonicalLocation,
    ComparisonSurface,
    Condition,
    Expression,
    FunctionReturnAnalysis,
    ReturnInfo,
)


def _nonnull_condition(ptr: Expression) -> Condition:
    return Condition(
        Expression.binary_op("INT_NOTEQUAL", ptr, Expression.constant(0, 8)),
        False,
    )


def _positive_condition(value: Expression) -> Condition:
    return Condition(
        Expression.binary_op("INT_SLESS", Expression.constant(0, 4), value),
        False,
    )


def _bit_hack_abs_expr(value: Expression) -> Expression:
    sign = Expression.binary_op("INT_SRIGHT", value, Expression.constant(31, 4))
    return Expression.binary_op(
        "INT_XOR",
        Expression.binary_op("INT_ADD", value, sign),
        sign,
    )


def _void_effect_analysis(
    function_name: str,
    effects,
) -> FunctionReturnAnalysis:
    effect_summary = EffectSummary(
        parameter_names=["ptr", "value"],
        effects=list(effects),
    )
    synthetic_expr = build_void_effect_summary_expr(effect_summary.effects)
    assert synthetic_expr is not None
    effect_summary.synthetic_expr = synthetic_expr
    return FunctionReturnAnalysis(
        function_name=function_name,
        entry_point="0x401000",
        parameters=[
            {
                "name": "ptr",
                "index": 0,
                "size": 8,
                "data_type": "int *",
                "is_signed": False,
            },
            {
                "name": "value",
                "index": 1,
                "size": 4,
                "data_type": "int",
                "is_signed": True,
            },
        ],
        returns=[
            ReturnInfo(
                address="0x401000",
                conditions=[],
                value=synthetic_expr,
            )
        ],
        return_type="void",
        return_type_obj=resolve_mock_data_type("void"),
        effect_summary=effect_summary,
        comparison_surface=ComparisonSurface(
            kind="memory_effect",
            explicit_bit_width=synthetic_expr.get_bit_width(),
            use_sign_extension=False,
            evidence={
                "source": "effect_summary.synthetic_expr",
                "effect_count": len(effect_summary.effects),
            },
        ),
    )


def _equivalent_void_effect_analyses() -> tuple[FunctionReturnAnalysis, FunctionReturnAnalysis]:
    ptr = Expression.parameter("ptr", 0, size=8)
    value = Expression.parameter("value", 1, size=4)
    nonnull = _nonnull_condition(ptr)
    positive = _positive_condition(value)
    non_positive = positive.negate()
    location = CanonicalLocation(base_param="ptr", offset=0, size=4)

    branchy = _void_effect_analysis(
        "void_writer_branchy",
        [
            StoreEffect(
                location=location,
                value=value,
                conditions=[nonnull, positive],
                order_key=2,
            ),
            StoreEffect(
                location=location,
                value=Expression.unary_op("INT_2COMP", value),
                conditions=[nonnull, non_positive],
                order_key=1,
            ),
        ],
    )
    bithack = _void_effect_analysis(
        "void_writer_bithack",
        [
            StoreEffect(
                location=location,
                value=_bit_hack_abs_expr(value),
                conditions=[nonnull],
                order_key=1,
            ),
        ],
    )
    return branchy, bithack


def _run_z3(query: str) -> str:
    z3_path = shutil.which("z3")
    if z3_path is None:
        pytest.skip("z3 is not available in PATH")
    sanitized = query.replace("(get-model)", "")
    completed = subprocess.run(
        [z3_path, "-in"],
        input=sanitized,
        text=True,
        capture_output=True,
        check=False,
    )
    assert completed.returncode == 0, completed.stderr
    assert completed.stderr == ""
    return completed.stdout.strip().splitlines()[0]


def test_void_effect_analysis_exposes_memory_effect_comparison_surface():
    analysis1, _ = _equivalent_void_effect_analyses()

    surface = analysis1.get_comparison_surface()

    assert surface.kind == "memory_effect"
    assert analysis1.get_comparison_bit_width() == 40
    assert surface.use_sign_extension is False


def test_memory_effect_keeps_synthetic_effect_width_when_surface_is_rederived():
    analysis1, _ = _equivalent_void_effect_analyses()
    analysis1.comparison_surface = ComparisonSurface(
        kind="memory_effect",
        explicit_bit_width=0,
        use_sign_extension=False,
        evidence={"source": "legacy_surface_without_width"},
    )

    surface = analysis1.get_comparison_surface()

    assert surface.kind == "memory_effect"
    assert surface.explicit_bit_width == 40
    assert analysis1.get_comparison_bit_width() == 40
    assert surface.evidence["source"] == "effect_summary.synthetic_expr"


def test_formula_builder_uses_effect_surface_width_for_void_effect_equivalence():
    analysis1, analysis2 = _equivalent_void_effect_analyses()
    builder = FormulaBuilder(debug=False, exclude_ub=False)

    formula = builder.build_equivalence_formula_extended(analysis1, analysis2).formula

    assert "(_ BitVec 0)" not in formula
    assert "(_ extract -1 0)" not in formula
    assert "(define-fun return_1 () (_ BitVec 40)" in formula
    assert "(define-fun return_2 () (_ BitVec 40)" in formula
    assert _run_z3(formula) == "unsat"


def test_pairwise_query_uses_effect_surface_width_for_void_effects():
    analysis1, analysis2 = _equivalent_void_effect_analyses()
    analysis1 = normalize_analysis_semantic_width(analysis1)
    analysis2 = normalize_analysis_semantic_width(analysis2)
    builder = FormulaBuilder(debug=False, exclude_ub=False)
    base_ctx = builder.build_base_context(analysis1, analysis2)

    cases1 = extract_return_cases(analysis1)
    cases2 = extract_return_cases(analysis2)
    replace1 = build_symbol_replacer(base_ctx["params1"], base_ctx.get("extra_vars1", []))
    replace2 = build_symbol_replacer(base_ctx["params2"], base_ctx.get("extra_vars2", []))
    query = build_pair_query(base_ctx, cases1[0], cases2[0], replace1, replace2, "(0,0)")

    assert base_ctx["return_size1"] == 40
    assert base_ctx["return_size2"] == 40
    assert "(_ BitVec 0)" not in query
    assert "(_ extract -1 0)" not in query
    assert _run_z3(query) == "unsat"


def test_semantic_width_normalization_preserves_memory_effect_surface():
    analysis1, _ = _equivalent_void_effect_analyses()

    normalized = normalize_analysis_semantic_width(analysis1)
    surface = normalized.get_comparison_surface()

    assert surface.kind == "memory_effect"
    assert normalized.get_comparison_bit_width() == 40
    assert surface.use_sign_extension is False

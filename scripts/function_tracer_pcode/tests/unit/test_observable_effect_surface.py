"""Issue #13: non-void functions with caller-observable stores are compared on
stores ⊕ return value, never on the return value alone."""
import shutil
import subprocess
from unittest.mock import Mock

import pytest

from scripts.function_tracer_pcode.analysis.effects.models import EffectSummary, StoreEffect
from scripts.function_tracer_pcode.analysis.effects.summary import build_void_effect_summary_expr
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.analysis.returns.effect_integration import (
    OBSERVABLE_EFFECT_SURFACE_SOURCE,
    observable_store_effects,
)
from scripts.function_tracer_pcode.core import (
    CanonicalLocation,
    Expression,
    FunctionReturnAnalysis,
    LocationBaseRef,
    ReturnInfo,
)
from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.proof.formula.returns import get_return_size
from scripts.function_tracer_pcode.proof.formula.symbol_replace import build_symbol_replacer
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import (
    build_pair_query,
    extract_return_cases,
)
from scripts.function_tracer_pcode.semantics.semantic_width import normalize_analysis_semantic_width
from conftest import resolve_mock_data_type


def _store(location, value, order):
    return StoreEffect(location=location, value=value, conditions=[], order_key=order)


def _sret_constructor(radsqr_value):
    """Sphere SphereConstructor(...): writes fields through the sret pointer and
    returns that pointer; the two versions differ only in the stored radSqr."""
    obj = Expression.parameter("param_1", 0, data_type="undefined8 *", size=8)
    r = Expression.parameter("param_2", 1, data_type="float", size=4)
    effects = [
        _store(CanonicalLocation(base_param="param_1", offset=0, size=4), r, 1),
        _store(CanonicalLocation(base_param="param_1", offset=4, size=4), radsqr_value, 2),
        _store(CanonicalLocation(base_param="stackframe", offset=-8, size=8), obj, 3),  # local spill
    ]
    analysis = FunctionReturnAnalysis(
        function_name="SphereConstructor", entry_point="0x1000",
        parameters=[{"name": "param_1", "index": 0, "size": 8, "data_type": "undefined8 *", "is_signed": False},
                    {"name": "param_2", "index": 1, "size": 4, "data_type": "float", "is_signed": False}],
        returns=[ReturnInfo("0x1010", obj, [])],
        return_type="undefined8 *",
        return_type_obj=resolve_mock_data_type("undefined8 *"),
    )
    analysis.effect_summary = EffectSummary(parameter_names=["param_1", "param_2"], effects=effects)
    # Production summaries carry the effects-only synthetic expression (the
    # void surface); it must not become the width authority of the combined
    # stores ⊕ return surface.
    analysis.effect_summary.synthetic_expr = build_void_effect_summary_expr(effects)
    return analysis


def _run_z3(query: str) -> str:
    z3_path = shutil.which("z3")
    if z3_path is None:
        pytest.skip("z3 is not available in PATH")
    completed = subprocess.run(
        [z3_path, "-in"], input=query.replace("(get-model)", ""),
        text=True, capture_output=True, check=False,
    )
    assert completed.returncode == 0, completed.stderr
    assert completed.stderr == ""
    return completed.stdout.strip().splitlines()[0]


def _old_and_new_constructors():
    # radSqr = r*r (old) vs r*2 (new); integer arithmetic keeps the SMT
    # rendering self-contained.
    r = Expression.parameter("param_2", 1, data_type="int", size=4)
    old = _sret_constructor(Expression.binary_op("INT_MULT", r, r))
    new = _sret_constructor(Expression.binary_op("INT_MULT", r, Expression.constant(2, size=4)))
    analyzer = _analyzer()
    assert analyzer._apply_observable_effect_surface(old, old.return_type_obj, old.return_type) is True
    assert analyzer._apply_observable_effect_surface(new, new.return_type_obj, new.return_type) is True
    return old, new


def _analyzer():
    analyzer = ReturnAnalyzer(Mock(), debug=False)
    analyzer._is_void_type = lambda dtype: str(dtype) == "void"
    return analyzer


def test_observable_effects_exclude_the_stack_frame():
    analysis = _sret_constructor(Expression.constant(2, size=4))
    kinds = [e.location.base_ref.kind for e in observable_store_effects(analysis.effect_summary)]
    assert kinds == ["parameter", "parameter"]


def test_sret_constructor_is_compared_on_stores_and_return_value():
    analyzer = _analyzer()
    analysis = _sret_constructor(Expression.constant(2, size=4))

    assert analyzer._apply_observable_effect_surface(analysis, "undefined8 *", "undefined8 *") is True

    surface = analysis.comparison_surface
    assert surface.kind == "memory_effect"
    assert surface.evidence["source"] == OBSERVABLE_EFFECT_SURFACE_SOURCE
    assert surface.evidence["effect_count"] == 2
    # 2 locations x (8-bit presence flag + 32-bit value) + 64-bit return pointer
    assert surface.explicit_bit_width == 2 * 40 + 64
    assert surface.evidence["effect_bits"] == 80 and surface.evidence["return_bits"] == 64
    assert analysis.returns[0].value.operator == "PIECE"
    assert analysis.returns[0].value.get_bit_width() == 2 * 40 + 64
    assert "observable_effect_surface" in analysis.analysis_notes


def test_functions_that_differ_only_in_a_store_get_different_surfaces():
    analyzer = _analyzer()
    old, new = _old_and_new_constructors()
    # The return values were identical (the pointer); the surfaces now are not.
    assert old.returns[0].value.to_smt() != new.returns[0].value.to_smt()


def test_surface_is_not_built_for_void_or_untrusted_or_storeless_functions():
    analyzer = _analyzer()
    void = _sret_constructor(Expression.constant(2, size=4))
    assert analyzer._apply_observable_effect_surface(void, "void", "void") is False
    assert void.comparison_surface is None

    untrusted = _sret_constructor(Expression.constant(2, size=4))
    untrusted.effect_summary.has_unsupported_call = True
    assert analyzer._apply_observable_effect_surface(untrusted, "undefined8 *", "undefined8 *") is False

    local_only = _sret_constructor(Expression.constant(2, size=4))
    local_only.effect_summary = EffectSummary(
        parameter_names=["param_1"],
        effects=[_store(CanonicalLocation(base_param="stackframe", offset=-8, size=8), Expression.constant(1, size=8), 1)],
    )
    assert analyzer._apply_observable_effect_surface(local_only, "undefined8 *", "undefined8 *") is False
    assert local_only.returns[0].value.operator != "PIECE"


COMBINED_BITS = 2 * 40 + 64


def test_semantic_width_normalization_keeps_the_combined_surface_width():
    old, _ = _old_and_new_constructors()
    # The effects-only synthetic expression (all three stores, stack spill
    # included) is narrower than nothing but different from the surface.
    assert old.effect_summary.synthetic_expr.get_bit_width() == 3 * 8 + 32 + 32 + 64
    assert old.get_memory_effect_bit_width() == COMBINED_BITS

    normalized = normalize_analysis_semantic_width(old)
    surface = normalized.get_comparison_surface()

    assert surface.kind == "memory_effect"
    # Before the fix normalisation reset the width to the effects-only
    # synthetic expression, silently dropping the return value.
    assert surface.explicit_bit_width == COMBINED_BITS
    assert normalized.get_memory_effect_bit_width() == COMBINED_BITS
    assert normalized.returns[0].value.get_bit_width() == COMBINED_BITS
    assert get_return_size(normalized) == COMBINED_BITS


def test_memory_effect_width_follows_the_returns_not_the_synthetic_expr():
    old, _ = _old_and_new_constructors()
    # A surface whose width is missing is re-derived from the comparison
    # values (returns), with the synthetic expression only as a fallback.
    old.comparison_surface = old.comparison_surface.__class__(
        kind="memory_effect", explicit_bit_width=0, use_sign_extension=False, evidence={}
    )
    assert old.get_comparison_surface().explicit_bit_width == COMBINED_BITS
    assert old.memory_effect_surface_bit_width() == COMBINED_BITS


def test_pair_query_on_store_only_difference_is_sat_after_normalization():
    old, new = _old_and_new_constructors()
    old = normalize_analysis_semantic_width(old)
    new = normalize_analysis_semantic_width(new)
    builder = FormulaBuilder(debug=False, exclude_ub=False)
    base_ctx = builder.build_base_context(old, new)
    assert base_ctx["return_size1"] == COMBINED_BITS
    assert base_ctx["return_size2"] == COMBINED_BITS

    cases1 = extract_return_cases(old)
    cases2 = extract_return_cases(new)
    replace1 = build_symbol_replacer(base_ctx["params1"], base_ctx.get("extra_vars1", []))
    replace2 = build_symbol_replacer(base_ctx["params2"], base_ctx.get("extra_vars2", []))
    query = build_pair_query(base_ctx, cases1[0], cases2[0], replace1, replace2, "(0,0)")

    assert "(_ BitVec 0)" not in query
    assert "(_ extract -1 0)" not in query
    # Both sides compare presence flags, stored values and the pointer.
    assert query.count("(concat (_ bv1 8)") == 4
    # r*r vs r*2 differ in the stored radSqr although the returned pointer is
    # the same: the pair must not be provable equal.
    assert _run_z3(query) == "sat"


def test_surface_is_not_built_for_incomplete_effect_summaries():
    analyzer = _analyzer()
    analysis = _sret_constructor(Expression.constant(2, size=4))
    analysis.effect_summary.incomplete_reasons = ("effect_coverage_incomplete",)
    assert analyzer._apply_observable_effect_surface(analysis, analysis.return_type_obj, analysis.return_type) is False
    assert analysis.comparison_surface is None
    assert analysis.returns[0].value.operator != "PIECE"


def test_surface_is_not_built_when_return_cases_disagree_on_width():
    analyzer = _analyzer()
    analysis = _sret_constructor(Expression.constant(2, size=4))
    analysis.returns.append(ReturnInfo("0x1020", Expression.constant(0, size=1), []))
    assert analyzer._apply_observable_effect_surface(analysis, analysis.return_type_obj, analysis.return_type) is False
    assert analysis.comparison_surface is None

"""Issue #13: non-void functions with caller-observable stores are compared on
stores ⊕ return value, never on the return value alone."""
from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.effects.models import EffectSummary, StoreEffect
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
        parameters=[{"name": "param_1", "index": 0, "size": 8, "data_type": "undefined8 *"},
                    {"name": "param_2", "index": 1, "size": 4, "data_type": "float"}],
        returns=[ReturnInfo("0x1010", obj, [])],
        return_type="undefined8 *",
    )
    analysis.effect_summary = EffectSummary(parameter_names=["param_1", "param_2"], effects=effects)
    return analysis


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
    old = _sret_constructor(Expression.binary_op("FLOAT_MULT", Expression.parameter("param_2", 1, size=4), Expression.parameter("param_2", 1, size=4)))
    new = _sret_constructor(Expression.binary_op("FLOAT_MULT", Expression.parameter("param_2", 1, size=4), Expression.constant(2, size=4)))
    analyzer._apply_observable_effect_surface(old, "undefined8 *", "undefined8 *")
    analyzer._apply_observable_effect_surface(new, "undefined8 *", "undefined8 *")
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

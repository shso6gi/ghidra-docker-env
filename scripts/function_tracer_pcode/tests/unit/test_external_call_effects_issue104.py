"""Issue #104 Gap 4: external / thunk callees are never "effect-free by absence".

Unit fixtures are Ghidra-shaped fakes; the opt-in test at the end runs the
real analyser on ``tests/fixtures/issue104_gap4_external_callee.c`` when
PyGhidra and a cross compiler are available (RUN_PYGHIDRA_REGRESSIONS=1).
"""
import os
import shutil
import subprocess
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.analysis.effects.external_call_models import (
    PURE_MATH_EXTERNALS,
    EffectCalleeResolution,
    ExternalCallEffectPolicy,
    normalize_external_name,
    resolve_effect_callee,
)


class _Fn:
    def __init__(self, name, *, external=False, thunk_to=None, body=32):
        self._name, self._external, self._thunk_to, self._body = name, external, thunk_to, body

    def getName(self):
        return self._name

    def isExternal(self):
        return self._external

    def isThunk(self):
        return self._thunk_to is not None

    def getThunkedFunction(self, recursive=False):
        if self._thunk_to is None:
            return None
        if recursive:
            target = self._thunk_to
            while target._thunk_to is not None:
                target = target._thunk_to
            return target
        return self._thunk_to


def _external_thunk(name):
    """A relocatable-object undefined symbol: thunk -> EXTERNAL function."""
    return _Fn(name, thunk_to=_Fn(name, external=True, body=0), body=1)


# --------------------------------------------------------------------------
# classification
# --------------------------------------------------------------------------

def test_internal_function_is_analysed():
    resolution = resolve_effect_callee(_Fn("helper"), ExternalCallEffectPolicy())
    assert resolution.kind == "analyze"
    assert resolution.function.getName() == "helper"


def test_thunk_to_internal_function_is_analysed_at_its_target():
    target = _Fn("real_impl")
    resolution = resolve_effect_callee(_Fn("thunk", thunk_to=target), ExternalCallEffectPolicy())
    assert resolution.kind == "analyze"
    assert resolution.function is target


def test_unmodelled_external_is_not_summarised():
    """The empty HighFunction of ``unknown_external`` is not evidence."""
    resolution = resolve_effect_callee(_external_thunk("unknown_external"), ExternalCallEffectPolicy())
    assert resolution.kind == "unsupported"
    assert resolution.reason == "external_callee_effect_unmodeled"
    assert resolution.external_name == "unknown_external"
    assert resolution.summary is None


def test_direct_external_function_object_is_not_summarised():
    resolution = resolve_effect_callee(_Fn("memcpy", external=True), ExternalCallEffectPolicy())
    assert resolution.kind == "unsupported"


@pytest.mark.parametrize("name", ["printf", "puts", "memcpy", "frexp", "modf", "malloc", "free", "strlen"])
def test_io_memory_and_out_parameter_externals_stay_unsupported(name):
    resolution = resolve_effect_callee(_external_thunk(name), ExternalCallEffectPolicy())
    assert resolution.kind == "unsupported", name


@pytest.mark.parametrize("name", ["sqrt", "sqrtf", "fabs", "sin", "cos", "exp", "log", "pow", "floor", "ceil", "abs"])
def test_pure_math_externals_get_a_complete_effect_free_summary(name):
    resolution = resolve_effect_callee(_external_thunk(name), ExternalCallEffectPolicy())
    assert resolution.kind == "modeled", name
    assert resolution.model is PURE_MATH_EXTERNALS[name]
    summary = resolution.summary
    assert summary.effects == []
    assert summary.has_unsupported_call is False
    assert summary.incomplete_reasons == ()


def test_pure_math_model_respects_the_observation_policy():
    sqrt = _external_thunk("sqrt")
    assert resolve_effect_callee(sqrt, ExternalCallEffectPolicy(observe_errno=True)).reason == "external_callee_errno_observed"
    assert resolve_effect_callee(sqrt, ExternalCallEffectPolicy(observe_fenv=True)).reason == "external_callee_fenv_observed"
    # fabs neither sets errno nor touches the fp environment
    fabs = _external_thunk("fabs")
    assert resolve_effect_callee(fabs, ExternalCallEffectPolicy(observe_errno=True, observe_fenv=True)).kind == "modeled"
    # floor can raise fp exceptions but never sets errno
    floor = _external_thunk("floor")
    assert resolve_effect_callee(floor, ExternalCallEffectPolicy(observe_errno=True)).kind == "modeled"
    assert resolve_effect_callee(floor, ExternalCallEffectPolicy(observe_fenv=True)).kind == "unsupported"


def test_library_symbol_names_are_normalised_like_the_deferred_call_lane():
    assert normalize_external_name("__sqrt_finite") == "sqrt"
    assert normalize_external_name("sqrt@plt") == "sqrt"
    assert normalize_external_name("_fabs") == "fabs"
    assert normalize_external_name("libm.so.6.cos") == "cos"
    assert normalize_external_name(None) == ""
    assert resolve_effect_callee(_external_thunk("__sqrt_finite"), ExternalCallEffectPolicy()).kind == "modeled"


def test_policy_and_resolution_are_exact():
    with pytest.raises(TypeError):
        ExternalCallEffectPolicy(observe_errno=1)
    assert resolve_effect_callee(None, ExternalCallEffectPolicy()).kind == "unsupported"
    assert isinstance(resolve_effect_callee(_Fn("f"), None), EffectCalleeResolution)


def test_no_model_writes_caller_memory():
    assert all(model.writes_caller_memory is False for model in PURE_MATH_EXTERNALS.values())
    assert "frexp" not in PURE_MATH_EXTERNALS and "modf" not in PURE_MATH_EXTERNALS


# --------------------------------------------------------------------------
# opt-in: the real analyser on a compiled fixture
# --------------------------------------------------------------------------

@pytest.mark.skipif(
    os.environ.get("RUN_PYGHIDRA_REGRESSIONS") != "1",
    reason="real PyGhidra analysis is opt-in; set RUN_PYGHIDRA_REGRESSIONS=1",
)
def test_real_analysis_does_not_treat_an_external_thunk_as_effect_free(tmp_path):
    pytest.importorskip("pyghidra")
    compiler = shutil.which("aarch64-linux-gnu-gcc")
    if compiler is None:
        pytest.skip("aarch64-linux-gnu-gcc is not available")
    from scripts.function_tracer_pcode.config.settings import apply_runtime_environment
    from scripts.function_tracer_pcode.ghidra.pyghidra_support import (
        load_pyghidra,
        start_headless_pyghidra,
    )

    source = Path(__file__).resolve().parents[1] / "fixtures" / "issue104_gap4_external_callee.c"
    binary = tmp_path / "gap4-arm64-gcc-O0"
    subprocess.run([compiler, "-O0", "-c", str(source), "-o", str(binary)], check=True)
    pyghidra = load_pyghidra()
    runtime_env = apply_runtime_environment()
    try:
        start_headless_pyghidra(
            pyghidra,
            install_dir=Path(runtime_env.ghidra_install_dir) if runtime_env.ghidra_install_dir else None,
        )
    except Exception as exc:
        pytest.skip(f"PyGhidra startup failed: {exc}")
    from scripts.function_tracer_pcode.analysis import ReturnAnalyzer

    with pyghidra.open_program(str(binary), analyze=True) as flat:
        analyzer = ReturnAnalyzer(flat.getCurrentProgram(), external_call_effect_policy=ExternalCallEffectPolicy())
        try:
            f = analyzer.analyze_function_by_name("f", 60)
            s = analyzer.analyze_function_by_name("s", 60)
            p = analyzer.analyze_function_by_name("p", 60)
        finally:
            analyzer.dispose()
    assert f is not None and f.effect_summary.has_unsupported_call is True
    assert any(site.reason in {"callee_unsupported_call_effects_unresolved", "callee_effect_summary_missing"}
               for site in f.effect_summary.unsupported_call_sites)
    assert s is not None and s.effect_summary.has_unsupported_call is False
    assert p is not None and p.effect_summary.has_unsupported_call is True

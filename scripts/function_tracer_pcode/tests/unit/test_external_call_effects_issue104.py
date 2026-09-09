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
    MAX_THUNK_CHAIN_LENGTH,
    EffectCalleeResolution,
    ExternalCallEffectPolicy,
    resolution_is_confirmed_external,
    resolve_effect_callee,
)
from scripts.function_tracer_pcode.proof.call_effect.obligations import EquivalenceObservationContract


class _Fn:
    def __init__(self, name, *, external=False, thunk_to=None, is_thunk=None):
        self._name, self._external, self._thunk_to = name, external, thunk_to
        # ``is_thunk`` overrides the derived flag so "thunk without target" is expressible.
        self._is_thunk = (thunk_to is not None) if is_thunk is None else is_thunk

    def getName(self):
        return self._name

    def isExternal(self):
        return self._external

    def isThunk(self):
        return self._is_thunk

    def getThunkedFunction(self, recursive=False):
        return self._thunk_to


class _Raising(_Fn):
    def __init__(self, name, *, raise_in):
        super().__init__(name)
        self._raise_in = raise_in

    def __getattribute__(self, item):
        if item == object.__getattribute__(self, "_raise_in"):
            def boom(*_args, **_kwargs):
                raise RuntimeError("ghidra api failure")
            return boom
        return super().__getattribute__(item)


def _external_thunk(name):
    """A relocatable-object undefined symbol: thunk -> EXTERNAL function."""
    return _Fn(name, thunk_to=_Fn(name, external=True))


# --------------------------------------------------------------------------
# classification: only a provably internal body is analysed
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


@pytest.mark.parametrize(
    "name",
    ["printf", "puts", "memcpy", "frexp", "modf", "malloc", "free", "strlen",
     "sqrt", "sqrtf", "__sqrt_finite", "sqrt@plt", "fabs", "sin", "exp", "log", "pow", "floor", "abs"],
)
def test_every_external_is_unsupported_regardless_of_its_name(name):
    """A symbol name is not evidence of standard-library semantics (no name-based model)."""
    resolution = resolve_effect_callee(_external_thunk(name), ExternalCallEffectPolicy())
    assert resolution.kind == "unsupported", name
    assert resolution.reason == "external_callee_effect_unmodeled"
    assert resolution.summary is None


# --------------------------------------------------------------------------
# thunk resolution is tri-state: "not a thunk" != "thunk whose target is unknown"
# --------------------------------------------------------------------------

def test_thunk_without_obtainable_target_is_unsupported_not_analysed():
    stub = _Fn("stub", is_thunk=True)  # isThunk() True, getThunkedFunction() -> None
    resolution = resolve_effect_callee(stub, ExternalCallEffectPolicy())
    assert resolution.kind == "unsupported"
    assert resolution.reason == "thunk_target_unresolved"


def test_thunk_whose_target_getter_raises_is_unsupported():
    stub = _Raising("stub", raise_in="getThunkedFunction")
    stub._is_thunk = True
    resolution = resolve_effect_callee(stub, ExternalCallEffectPolicy())
    assert resolution.kind == "unsupported"
    assert resolution.reason == "thunk_target_unresolved"


def test_thunk_without_target_api_is_unsupported():
    class _NoGetter:
        def getName(self):
            return "stub"

        def isThunk(self):
            return True

        def isExternal(self):
            return False

    resolution = resolve_effect_callee(_NoGetter(), ExternalCallEffectPolicy())
    assert resolution.kind == "unsupported"
    assert resolution.reason == "thunk_target_unresolved"


@pytest.mark.parametrize("api", ["isThunk", "isExternal"])
def test_classification_api_exception_is_unsupported_never_analyse(api):
    resolution = resolve_effect_callee(_Raising("f", raise_in=api), ExternalCallEffectPolicy())
    assert resolution.kind == "unsupported"
    assert resolution.reason in {"thunk_target_unresolved", "callee_classification_unavailable"}


@pytest.mark.parametrize("api", ["isThunk", "isExternal"])
def test_non_bool_classification_answer_is_unsupported(api):
    fn = _Fn("f")
    setattr(fn, api, lambda: None)
    resolution = resolve_effect_callee(fn, ExternalCallEffectPolicy())
    assert resolution.kind == "unsupported"


def test_missing_classification_api_is_unsupported():
    resolution = resolve_effect_callee(object(), ExternalCallEffectPolicy())
    assert resolution.kind == "unsupported"


def test_self_thunk_is_unsupported():
    fn = _Fn("self")
    fn._thunk_to, fn._is_thunk = fn, True
    resolution = resolve_effect_callee(fn, ExternalCallEffectPolicy())
    assert resolution.kind == "unsupported"
    assert resolution.reason == "thunk_chain_cyclic"


def test_cyclic_thunk_chain_is_unsupported():
    a, b = _Fn("a"), _Fn("b")
    a._thunk_to, a._is_thunk = b, True
    b._thunk_to, b._is_thunk = a, True
    resolution = resolve_effect_callee(a, ExternalCallEffectPolicy())
    assert resolution.kind == "unsupported"
    assert resolution.reason == "thunk_chain_cyclic"


def test_thunk_chain_within_bound_reaches_internal_body():
    target = _Fn("body")
    head = target
    for i in range(MAX_THUNK_CHAIN_LENGTH - 1):
        head = _Fn(f"t{i}", thunk_to=head)
    resolution = resolve_effect_callee(head, ExternalCallEffectPolicy())
    assert resolution.kind == "analyze"
    assert resolution.function is target


def test_thunk_chain_exceeding_bound_is_unsupported():
    target = _Fn("body")
    head = target
    for i in range(MAX_THUNK_CHAIN_LENGTH):
        head = _Fn(f"t{i}", thunk_to=head)
    resolution = resolve_effect_callee(head, ExternalCallEffectPolicy())
    assert resolution.kind == "unsupported"
    assert resolution.reason == "thunk_chain_length_exceeded"


def test_thunk_chain_ending_at_external_is_unsupported():
    resolution = resolve_effect_callee(
        _Fn("plt", thunk_to=_Fn("stub", thunk_to=_Fn("sqrt", external=True))), ExternalCallEffectPolicy(),
    )
    assert resolution.kind == "unsupported"
    assert resolution.reason == "external_callee_effect_unmodeled"


def test_only_a_resolved_external_counts_as_confirmed_external():
    """Issue #47 (PR-B): "unsupported" のうち external と確定した 1 件だけを区別する。

    分類できなかった callee（thunk target 不明・循環・API 不通）は "external" では
    ないので、それを external の証拠として扱う読み手が現れないよう固定する。
    """
    policy = ExternalCallEffectPolicy()
    confirmed = resolve_effect_callee(_Fn("plt", thunk_to=_Fn("log", external=True)), policy)
    assert resolution_is_confirmed_external(confirmed) is True
    assert resolution_is_confirmed_external(resolve_effect_callee(_Fn("body"), policy)) is False
    for ambiguous in (
        _Fn("plt", is_thunk=True, thunk_to=None),
        _Fn("self", is_thunk=True),
        _Fn("broken", is_thunk="yes"),
    ):
        assert resolution_is_confirmed_external(resolve_effect_callee(ambiguous, policy)) is False
    assert resolution_is_confirmed_external(None) is False


def test_policy_and_resolution_are_exact():
    with pytest.raises(TypeError):
        ExternalCallEffectPolicy(observe_errno=1)
    with pytest.raises(TypeError):
        resolve_effect_callee(_Fn("f"), object())
    assert resolve_effect_callee(None, ExternalCallEffectPolicy()).kind == "unsupported"
    assert isinstance(resolve_effect_callee(_Fn("f"), None), EffectCalleeResolution)


# --------------------------------------------------------------------------
# the policy is a projection of the authoritative observation contract
# --------------------------------------------------------------------------

def test_policy_is_built_from_the_observation_contract():
    contract = EquivalenceObservationContract(observe_errno=True, observe_fenv=False)
    policy = ExternalCallEffectPolicy.from_observation_contract(contract)
    assert policy == ExternalCallEffectPolicy(observe_errno=True, observe_fenv=False)
    with pytest.raises(TypeError):
        ExternalCallEffectPolicy.from_observation_contract(object())


def test_checker_derives_flags_and_policy_from_an_explicit_contract():
    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker

    contract = EquivalenceObservationContract(observe_errno=True, observe_fenv=True)
    checker = EquivalenceChecker(observation_contract=contract)
    assert checker.observation_contract is contract
    assert checker.observes_errno is True and checker.observes_fenv is True
    assert checker.external_call_effect_policy == ExternalCallEffectPolicy(observe_errno=True, observe_fenv=True)


def test_checker_shorthand_flags_build_the_contract_when_none_is_given():
    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker

    checker = EquivalenceChecker(observes_errno=True)
    assert checker.observation_contract.observe_errno is True
    assert checker.observation_contract.observe_fenv is False
    assert checker.external_call_effect_policy == ExternalCallEffectPolicy(observe_errno=True, observe_fenv=False)
    default = EquivalenceChecker()
    assert default.observation_contract.observe_errno is False and default.observes_errno is False


def test_checker_rejects_flags_that_contradict_an_explicit_contract():
    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker

    contract = EquivalenceObservationContract(observe_errno=True)
    with pytest.raises(ValueError, match="observes_errno"):
        EquivalenceChecker(observes_errno=False, observation_contract=contract)
    # an explicit value that agrees with the contract is fine
    assert EquivalenceChecker(observes_errno=True, observation_contract=contract).observes_errno is True
    with pytest.raises(TypeError):
        EquivalenceChecker(observes_fenv=1)


# --------------------------------------------------------------------------
# opt-in: the real analyser on a compiled fixture
# --------------------------------------------------------------------------

@pytest.mark.skipif(
    os.environ.get("RUN_PYGHIDRA_REGRESSIONS") != "1",
    reason="real PyGhidra analysis is opt-in; set RUN_PYGHIDRA_REGRESSIONS=1",
)
def test_real_analysis_does_not_treat_any_external_thunk_as_effect_free(tmp_path):
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
    # ``sqrt`` has no body in the object either: its name is not evidence of libm semantics.
    assert s is not None and s.effect_summary.has_unsupported_call is True
    assert p is not None and p.effect_summary.has_unsupported_call is True

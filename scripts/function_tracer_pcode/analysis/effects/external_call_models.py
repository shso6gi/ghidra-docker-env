"""Effect-lane treatment of external / thunk callees (Issue #104, Gap 4).

An undefined external symbol in a relocatable object, or a PLT entry in a
linked binary, is represented by Ghidra as a *thunk* function whose thunked
target lives in the EXTERNAL space.  Decompiling the thunk yields an empty
``HighFunction`` (a bare ``RETURN``), which the store-effect summariser would
otherwise read as "this callee has no observable effect".  That is not
evidence: the callee's body is simply not in the binary.

This module decides, once per callee, how the effect lane may treat it:

* an internal function (or a thunk that resolves to an internal function)
  is analysed like any other callee;
* an external whose effect semantics are covered by an explicit model
  (``PURE_MATH_EXTERNALS``: libm / libc arithmetic functions that write no
  caller-visible memory) is given the modelled, complete effect summary;
* every other external / unresolvable thunk is *not* summarised, so the
  caller records ``callee_effect_summary_missing`` and fails closed.

The models here are about the *memory effect* lane only.  The pure-return
contract of the deferred-call lane (``proof/deferred_call_abstraction.py``)
and the printf-family argument recovery keep their own, unchanged rules.
``errno`` / floating-point environment writes are a caller-visible effect
only when the observation policy asks for them; the policy is carried from
the CLI flags (``--observe-errno`` / ``--observe-fenv``).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Optional, Tuple

from scripts.function_tracer_pcode.analysis.effects.models import EffectSummary


@dataclass(frozen=True)
class ExternalCallEffectPolicy:
    """What the comparison observes beyond memory reachable from the caller."""

    observe_errno: bool = False
    observe_fenv: bool = False

    def __post_init__(self) -> None:
        if type(self.observe_errno) is not bool or type(self.observe_fenv) is not bool:
            raise TypeError("external call effect policy flags must be exact bools")


@dataclass(frozen=True)
class ExternalEffectModel:
    """Explicit effect contract of one external function in the memory lane."""

    name: str
    writes_caller_memory: bool = False
    may_set_errno: bool = False
    may_touch_fenv: bool = False


def _pure(name: str, *, errno: bool = True, fenv: bool = True) -> ExternalEffectModel:
    return ExternalEffectModel(name, writes_caller_memory=False, may_set_errno=errno, may_touch_fenv=fenv)


# Arithmetic library functions that read only their arguments and write no
# caller-visible memory.  Functions with out-parameters (``frexp``, ``modf``,
# ``remquo``, ...) are deliberately absent: they write through a pointer and
# stay unsupported until modelled as store effects.
PURE_MATH_EXTERNALS: dict[str, ExternalEffectModel] = {
    model.name: model
    for model in (
        _pure("sqrt"), _pure("sqrtf"), _pure("cbrt"), _pure("cbrtf"),
        _pure("fabs", errno=False, fenv=False), _pure("fabsf", errno=False, fenv=False),
        _pure("abs", errno=False, fenv=False), _pure("labs", errno=False, fenv=False),
        _pure("llabs", errno=False, fenv=False),
        _pure("sin"), _pure("sinf"), _pure("cos"), _pure("cosf"), _pure("tan"), _pure("tanf"),
        _pure("asin"), _pure("acos"), _pure("atan"), _pure("atan2"), _pure("atan2f"),
        _pure("sinh"), _pure("cosh"), _pure("tanh"),
        _pure("exp"), _pure("expf"), _pure("exp2"), _pure("expm1"),
        _pure("log"), _pure("logf"), _pure("log2"), _pure("log10"), _pure("log1p"),
        _pure("pow"), _pure("powf"), _pure("hypot"), _pure("fmod"),
        _pure("floor", errno=False), _pure("floorf", errno=False),
        _pure("ceil", errno=False), _pure("ceilf", errno=False),
        _pure("round", errno=False), _pure("roundf", errno=False),
        _pure("trunc", errno=False), _pure("truncf", errno=False),
        _pure("rint"), _pure("nearbyint", errno=False),
        _pure("fmax", errno=False, fenv=False), _pure("fmin", errno=False, fenv=False),
        _pure("copysign", errno=False, fenv=False),
    )
}


def normalize_external_name(name: Optional[str]) -> str:
    """``__sqrt_finite`` / ``sqrt@plt`` / ``_sqrt`` -> ``sqrt``-style key.

    Mirrors the deferred-call lane's name normalisation so both lanes agree
    on which library symbol a callee is.
    """

    raw = str(name or "").strip()
    if not raw:
        return ""
    raw = raw.split("@", 1)[0]
    raw = raw.rsplit(".", 1)[-1] if "." in raw else raw
    while raw.startswith("_"):
        raw = raw[1:]
    if raw.endswith("_finite"):
        raw = raw[: -len("_finite")]
    return raw.lower()


def _safe_call(obj: Any, method: str, *args: Any) -> Any:
    getter = getattr(obj, method, None)
    if not callable(getter):
        return None
    try:
        return getter(*args)
    except Exception:
        return None


def _is_external_function(function: Any) -> bool:
    return _safe_call(function, "isExternal") is True


def _thunked_function(function: Any) -> Any:
    if _safe_call(function, "isThunk") is not True:
        return None
    for args in ((True,), ()):
        thunked = _safe_call(function, "getThunkedFunction", *args)
        if thunked is not None and thunked is not function:
            return thunked
    return None


@dataclass(frozen=True)
class EffectCalleeResolution:
    """How the effect lane must treat a resolved callee function object.

    ``kind`` is ``"analyze"`` (decompile and summarise ``function``),
    ``"modeled"`` (use ``summary``; ``model`` names the contract) or
    ``"unsupported"`` (no summary; ``reason`` explains why).
    """

    kind: str
    function: Any = None
    summary: Optional[EffectSummary] = None
    model: Optional[ExternalEffectModel] = None
    reason: Optional[str] = None
    external_name: Optional[str] = None


def resolve_effect_callee(
    function: Any,
    policy: Optional[ExternalCallEffectPolicy],
    *,
    parameter_names: Tuple[str, ...] = (),
) -> EffectCalleeResolution:
    """Classify a Ghidra function object for the effect lane (see module doc)."""

    if function is None:
        return EffectCalleeResolution("unsupported", reason="callee_function_unavailable")
    policy = policy or ExternalCallEffectPolicy()

    resolved = function
    thunked = _thunked_function(function)
    if thunked is not None:
        # Follow thunk chains (bounded) to the real body when it is internal.
        depth = 0
        while thunked is not None and depth < 8:
            resolved = thunked
            thunked = _thunked_function(resolved)
            depth += 1
        if not _is_external_function(resolved):
            return EffectCalleeResolution("analyze", function=resolved)
    if not _is_external_function(resolved):
        return EffectCalleeResolution("analyze", function=resolved)

    external_name = normalize_external_name(_safe_call(resolved, "getName"))
    model = PURE_MATH_EXTERNALS.get(external_name)
    if model is None:
        return EffectCalleeResolution(
            "unsupported",
            reason="external_callee_effect_unmodeled",
            external_name=external_name or None,
        )
    if model.writes_caller_memory:
        return EffectCalleeResolution(
            "unsupported", reason="external_callee_writes_caller_memory", external_name=external_name,
        )
    if policy.observe_errno and model.may_set_errno:
        return EffectCalleeResolution(
            "unsupported", reason="external_callee_errno_observed", external_name=external_name,
        )
    if policy.observe_fenv and model.may_touch_fenv:
        return EffectCalleeResolution(
            "unsupported", reason="external_callee_fenv_observed", external_name=external_name,
        )
    summary = EffectSummary(
        parameter_names=list(parameter_names),
        effects=[],
        synthetic_expr=None,
        has_unsupported_call=False,
        incomplete_reasons=(),
    )
    return EffectCalleeResolution(
        "modeled", function=resolved, summary=summary, model=model, external_name=external_name,
    )

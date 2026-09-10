"""Effect-lane treatment of external / thunk callees (Issue #104, Gap 4).

An undefined external symbol in a relocatable object, or a PLT entry in a
linked binary, is represented by Ghidra as a *thunk* function whose thunked
target lives in the EXTERNAL space.  Decompiling the thunk yields an empty
``HighFunction`` (a bare ``RETURN``), which the store-effect summariser would
otherwise read as "this callee has no observable effect".  That is not
evidence: the callee's body is simply not in the binary.

``classify_callee_chain`` は、この分類（exact-bool な ``isExternal`` /
``isThunk`` 判定と thunk chain の fail-closed 解決）を単体で提供する共有 helper で
ある。effect lane の ``resolve_effect_callee`` も、Issue #20 PR-B1 の call-model
candidate 分類も同じ helper を通す。callee を external と認める判定器を各所に
複製しないこと。

This module decides, once per callee, how the effect lane may treat it:

* a function that is provably *not* a thunk and *not* external, or a thunk
  chain that provably ends at such an internal function, is analysed like
  any other callee (``"analyze"``);
* everything else is ``"unsupported"``: an external function (no body in
  the binary), a thunk whose target cannot be obtained, a thunk chain that
  is cyclic or longer than the bound, and any callee whose classification
  API raises or returns a non-boolean.  The caller then records
  ``callee_effect_summary_missing`` and fails closed.

There is deliberately *no* name-based model of library functions here.  A
symbol name is not evidence of standard-library semantics (an unresolved
``sqrt`` may bind to any provider), so treating one as effect-free would
reintroduce the very "effect-free without a body" path this module closes.
Trusted external models, if ever wanted, must be an explicit analysis
assumption bound to the observation contract and to the result receipt.

The pure-return contract of the deferred-call lane
(``proof/deferred_call_abstraction.py``) and the printf-family argument
recovery keep their own, unchanged rules.  ``ExternalCallEffectPolicy`` is
the effect lane's projection of the authoritative
``EquivalenceObservationContract`` (``observe_errno`` / ``observe_fenv``);
it must be built from the finalised contract, never from raw flags.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Optional, Tuple

from scripts.function_tracer_pcode.analysis.effects.models import EffectSummary

#: Longest thunk chain the resolver follows before giving up (fail closed).
MAX_THUNK_CHAIN_LENGTH = 8

#: The one ``unsupported`` reason that means "resolved cleanly, and the callee it
#: resolves to is external".  Every other reason is *unknowable*, not external.
EXTERNAL_CALLEE_EFFECT_UNMODELED = "external_callee_effect_unmodeled"


@dataclass(frozen=True)
class ExternalCallEffectPolicy:
    """What the comparison observes beyond memory reachable from the caller.

    Projection of ``EquivalenceObservationContract.observe_errno`` /
    ``observe_fenv``.  Build it with :meth:`from_observation_contract` so the
    effect lane can never disagree with the authoritative contract.
    """

    observe_errno: bool = False
    observe_fenv: bool = False

    def __post_init__(self) -> None:
        if type(self.observe_errno) is not bool or type(self.observe_fenv) is not bool:
            raise TypeError("external call effect policy flags must be exact bools")

    @classmethod
    def from_observation_contract(cls, contract: Any) -> "ExternalCallEffectPolicy":
        observe_errno = getattr(contract, "observe_errno", None)
        observe_fenv = getattr(contract, "observe_fenv", None)
        if type(observe_errno) is not bool or type(observe_fenv) is not bool:
            raise TypeError("observation contract must expose exact-bool observe_errno / observe_fenv")
        return cls(observe_errno=observe_errno, observe_fenv=observe_fenv)


class _ClassificationUnavailable(Exception):
    """A Ghidra classification API is missing, raised, or returned a non-bool."""


def _exact_bool_call(obj: Any, method: str) -> bool:
    getter = getattr(obj, method, None)
    if not callable(getter):
        raise _ClassificationUnavailable(f"{method} unavailable")
    try:
        value = getter()
    except Exception as exc:  # noqa: BLE001 - any failure is "unknown", never "false"
        raise _ClassificationUnavailable(f"{method} raised {type(exc).__name__}") from exc
    if type(value) is not bool:
        raise _ClassificationUnavailable(f"{method} returned non-bool {type(value).__name__}")
    return value


def _is_external_function(function: Any) -> bool:
    return _exact_bool_call(function, "isExternal")


# Tri-state thunk probe: "not_thunk" / "resolved" (with target) / "unavailable".
_NOT_THUNK = "not_thunk"
_RESOLVED = "resolved"
_UNAVAILABLE = "unavailable"


def _probe_thunk(function: Any) -> Tuple[str, Any]:
    """Classify ``function`` as not-a-thunk, a thunk with a target, or unknowable.

    ``isThunk() is True`` with no obtainable target is *not* the same as
    ``not a thunk``: the callee is known to be a forwarding stub whose body
    must not be read as evidence.
    """

    try:
        if not _exact_bool_call(function, "isThunk"):
            return _NOT_THUNK, None
    except _ClassificationUnavailable:
        return _UNAVAILABLE, None
    getter = getattr(function, "getThunkedFunction", None)
    if not callable(getter):
        return _UNAVAILABLE, None
    try:
        target = getter(False)
    except Exception:  # noqa: BLE001
        return _UNAVAILABLE, None
    if target is None:
        return _UNAVAILABLE, None
    return _RESOLVED, target


#: ``classify_callee_chain`` の判定値。
CALLEE_CHAIN_INTERNAL = "internal"
CALLEE_CHAIN_EXTERNAL = "external"
CALLEE_CHAIN_UNCLASSIFIABLE = "unclassifiable"


@dataclass(frozen=True)
class CalleeChainClassification:
    """thunk chain を辿った先の callee を exact-bool で分類した結果。

    ``kind`` は ``CALLEE_CHAIN_INTERNAL``（binary 内に body を持つ）/
    ``CALLEE_CHAIN_EXTERNAL``（proven external）/ ``CALLEE_CHAIN_UNCLASSIFIABLE``
    （missing API / 例外 / non-bool / thunk target 不明 / 循環 / 上限超過）の 3 値。
    ``function`` は判定対象になった chain の終端で、``reason`` を名乗る対象でもある。

    **この package で callee を external と認めるのはここだけ**である。
    ``isExternal()`` が ``"true"`` のような非 bool を返しても external と見なさない
    こと、循環・上限超過・解決不能な thunk chain を external と見なさないことを、
    この 1 か所で保証する。effect lane も candidate 分類（Issue #20 PR-B1）も
    同じ判定を通し、弱い分類器を各所に持たない。
    """

    kind: str
    function: Any = None
    reason: Optional[str] = None


def classify_callee_chain(function: Any) -> CalleeChainClassification:
    """``function`` の thunk chain を辿り、終端を fail closed に分類する。

    ``resolve_effect_callee`` の分類部分そのもの。effect lane の判定を変えないよう、
    reason 文字列と「どの関数オブジェクトが reason を名乗るか」も従来どおりにする。
    """

    if function is None:
        return CalleeChainClassification(
            CALLEE_CHAIN_UNCLASSIFIABLE, reason="callee_function_unavailable"
        )

    resolved = function
    seen: list = [function]
    state, target = _probe_thunk(resolved)
    while state == _RESOLVED:
        if any(target is prior for prior in seen):
            return CalleeChainClassification(
                CALLEE_CHAIN_UNCLASSIFIABLE, function=function, reason="thunk_chain_cyclic"
            )
        if len(seen) >= MAX_THUNK_CHAIN_LENGTH:
            return CalleeChainClassification(
                CALLEE_CHAIN_UNCLASSIFIABLE,
                function=function,
                reason="thunk_chain_length_exceeded",
            )
        seen.append(target)
        resolved = target
        state, target = _probe_thunk(resolved)
    if state == _UNAVAILABLE:
        return CalleeChainClassification(
            CALLEE_CHAIN_UNCLASSIFIABLE, function=resolved, reason="thunk_target_unresolved"
        )

    try:
        external = _is_external_function(resolved)
    except _ClassificationUnavailable:
        return CalleeChainClassification(
            CALLEE_CHAIN_UNCLASSIFIABLE,
            function=resolved,
            reason="callee_classification_unavailable",
        )
    if external:
        return CalleeChainClassification(CALLEE_CHAIN_EXTERNAL, function=resolved)
    return CalleeChainClassification(CALLEE_CHAIN_INTERNAL, function=resolved)


@dataclass(frozen=True)
class EffectCalleeResolution:
    """How the effect lane must treat a resolved callee function object.

    ``kind`` is ``"analyze"`` (decompile and summarise ``function``) or
    ``"unsupported"`` (no summary; ``reason`` explains why).  ``summary``
    is always ``None`` today: no external is modelled.
    """

    kind: str
    function: Any = None
    summary: Optional[EffectSummary] = None
    reason: Optional[str] = None
    external_name: Optional[str] = None


def _unsupported(reason: str, function: Any = None) -> EffectCalleeResolution:
    name = None
    getter = getattr(function, "getName", None)
    if callable(getter):
        try:
            raw = getter()
            name = str(raw) if raw is not None else None
        except Exception:  # noqa: BLE001
            name = None
    return EffectCalleeResolution("unsupported", reason=reason, external_name=name)


def resolve_effect_callee(
    function: Any,
    policy: Optional[ExternalCallEffectPolicy],
    *,
    parameter_names: Tuple[str, ...] = (),
) -> EffectCalleeResolution:
    """Classify a Ghidra function object for the effect lane (see module doc).

    ``policy`` is accepted so callers thread the observation boundary through
    one place; with no modelled external it does not change the answer.
    """

    del parameter_names  # no modelled summary is produced
    if function is None:
        return _unsupported("callee_function_unavailable")
    if policy is not None and type(policy) is not ExternalCallEffectPolicy:
        raise TypeError("policy must be an ExternalCallEffectPolicy or None")

    classification = classify_callee_chain(function)
    if classification.kind == CALLEE_CHAIN_UNCLASSIFIABLE:
        return _unsupported(classification.reason, classification.function)
    if classification.kind == CALLEE_CHAIN_EXTERNAL:
        return _unsupported(EXTERNAL_CALLEE_EFFECT_UNMODELED, classification.function)
    return EffectCalleeResolution("analyze", function=classification.function)


def resolution_is_confirmed_external(resolution: Optional[EffectCalleeResolution]) -> bool:
    """Is ``resolution`` the *unambiguous* "this callee is external" answer?

    Read-only classification helper (Issue #47 PR-B): it adds no policy of its
    own and changes no effect-lane decision.  ``resolve_effect_callee`` reports
    "unsupported" both for a callee it *knows* is external and for one whose
    classification it could not obtain (a cyclic or over-long thunk chain, an
    unresolvable thunk target, a classification API that raised).  Only the
    first is evidence of anything; the rest must keep their fail-closed
    treatment wherever a caller asks this question.
    """

    return (
        resolution is not None
        and resolution.kind == "unsupported"
        and resolution.reason == EXTERNAL_CALLEE_EFFECT_UNMODELED
    )

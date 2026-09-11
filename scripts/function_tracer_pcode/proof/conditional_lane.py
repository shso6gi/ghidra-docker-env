# -*- coding: utf-8 -*-
"""Conditional (assumption-dependent) proof adapter.

Issue #20 PR-20-B3。B2 が作った ``ConditionalSemanticView`` /
``build_conditional_equivalence_formula`` を solver まで運び、**proof artifact**
を返す。receipt 化・lane の起動・conditional verdict は authority/checker 境界の
責務で、この module は authority を import しない（proof → authority の新規 edge
を作らない）。proof kind は素の文字列で返し、``ConditionalDecisiveProofKind``
への写像は authority 側が行う。

adapter の範囲（正本 v4 §4.4 / B3 §6）:

* 無条件 stage plan を流用しない。conditional formula に対して意味のある
  ものだけを使う ―― 片側ずつの解析事実に基づく既存 safety gate
  (``FunctionReturnAnalysis.get_*_unsafety_reasons``) と、
  ``build_conditional_equivalence_formula`` が組む formula の充足性。
* 無条件 lane の ``FormulaBuilder(allow_call=False)`` は触らない。CALL を
  unsupported として扱う既存 helper を conditional のためにグローバルへ
  緩めることもしない。

soundness の要点:

* **UF を含む式の SAT model だけを根拠に NOT_EQ を出さない。** uninterpreted
  function の解釈は実際の ``log`` / ``sin`` の値を保証しないので、SAT が
  「任意の UF 解釈に依存しない反例」であることを現在の contract で確認できない
  限り non-decisive に留める。現行 contract では counterexample replay 証明
  (``counterexample_replay_missing``) が必須で、その証明は本 adapter の外
  （Issue #18）にあるため、conditional NOT_EQ は実際には発行されない。
  これは gate を緩めないための意図的な fail closed。
* EQ 側は既存の equivalence-blocking safety reason をそのまま適用する。仮定が
  引き受けるのは「modelled した外部 callee の効果」だけなので、
  ``unsupported_call_effect_summary`` は **その unsupported call site が
  すべて modelled 済み callee のとき**に限り discharge する。ほかの理由
  （expansion budget 打ち切り、effect summary の不完全性、argument evidence）は
  discharge しない。
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from typing import Any, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core.render_smt import expression_contains_call
from scripts.function_tracer_pcode.proof.assumptions import (
    AssumptionPremise,
    normalize_assumption_premises,
)
from scripts.function_tracer_pcode.proof.conditional_view import (
    ConditionalSemanticView,
    build_conditional_equivalence_formula,
    create_conditional_view,
)


CONDITIONAL_PROOF_ADAPTER_VERSION = "conditional-external-call-proof-v1"

#: authority 側 ``ConditionalDecisiveProofKind`` と同じ名前（import はしない）。
CONDITIONAL_EQ_CLOSURE = "CONDITIONAL_EQ_CLOSURE"
CONDITIONAL_SAFE_COUNTEREXAMPLE = "CONDITIONAL_SAFE_COUNTEREXAMPLE"

# lane が decisive にならなかった理由（診断。判定 authority ではない）。
LANE_ANALYSIS_UNAVAILABLE = "conditional_lane_analysis_unavailable"
LANE_VIEW_REFUSED = "conditional_lane_view_refused"
LANE_UNMAPPED_CALL_PRESENT = "conditional_lane_unmapped_call_present"
LANE_FORMULA_UNAVAILABLE = "conditional_lane_formula_unavailable"
LANE_SOLVER_UNAVAILABLE = "conditional_lane_solver_unavailable"
LANE_SOLVER_INCONCLUSIVE = "conditional_lane_solver_inconclusive"
LANE_EQ_CLOSURE_BLOCKED = "conditional_lane_eq_closure_blocked"
LANE_COUNTEREXAMPLE_UNSAFE = "conditional_lane_counterexample_unsafe"

#: SAT が「任意の UF 解釈に依存しない反例」だと確認できないこと。
COUNTEREXAMPLE_UF_INTERPRETATION_DEPENDENT = (
    "conditional_counterexample_uf_interpretation_dependent"
)
#: 既存 production contract が decisive counterexample に要求する replay 証明。
COUNTEREXAMPLE_REPLAY_MISSING = "counterexample_replay_missing"

#: 仮定が引き受ける EQ 側 safety reason。ここに無いものは discharge しない。
ASSUMPTION_DISCHARGED_SAFETY_REASONS = frozenset({"unsupported_call_effect_summary"})


def _digest(payload: Any) -> str:
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, default=repr).encode("utf-8")
    ).hexdigest()


@dataclass(frozen=True)
class ConditionalProofArtifact:
    """conditional lane 1 回分の proof 成果物（authority ではない）。

    ``proof_kind`` が ``None`` なら decisive ではない。``assumption_set`` は
    左右 view の和で、**最小化しない**。receipt はこれをそのまま
    ``assumption_dependencies`` に使う。
    """

    proof_kind: Optional[str]
    assumption_set: Tuple[AssumptionPremise, ...]
    artifact_digest: str
    modelled_call_count: int = 0
    all_calls_modelled: bool = False
    unsupported_calls_all_modelled: bool = False
    non_decisive_reasons: Tuple[str, ...] = ()
    diagnostics: Mapping[str, Any] = field(default_factory=dict)

    @property
    def decisive(self) -> bool:
        return self.proof_kind is not None

    def __post_init__(self) -> None:
        if self.proof_kind is not None:
            if self.proof_kind not in (
                CONDITIONAL_EQ_CLOSURE,
                CONDITIONAL_SAFE_COUNTEREXAMPLE,
            ):
                raise ValueError(f"unknown conditional proof kind: {self.proof_kind}")
            if not self.assumption_set:
                raise ValueError("a decisive conditional proof carries its assumption set")
            if not self.all_calls_modelled:
                raise ValueError(
                    "a decisive conditional proof models every deferred call of both sides"
                )


def _non_decisive(
    assumption_set: Sequence[AssumptionPremise],
    reasons: Sequence[str],
    diagnostics: Mapping[str, Any],
    *,
    modelled_call_count: int = 0,
    all_calls_modelled: bool = False,
    unsupported_calls_all_modelled: bool = False,
) -> ConditionalProofArtifact:
    return ConditionalProofArtifact(
        proof_kind=None,
        assumption_set=tuple(assumption_set),
        artifact_digest=_digest(
            {
                "adapter": CONDITIONAL_PROOF_ADAPTER_VERSION,
                "decisive": False,
                "reasons": list(reasons),
            }
        ),
        modelled_call_count=modelled_call_count,
        all_calls_modelled=all_calls_modelled,
        unsupported_calls_all_modelled=unsupported_calls_all_modelled,
        non_decisive_reasons=tuple(reasons),
        diagnostics=dict(diagnostics),
    )


def _modelled_target_keys(analysis: Any, view: ConditionalSemanticView) -> Optional[frozenset]:
    """view が写像した callsite の callee target key 集合。

    1 つでも key が取れなければ ``None``（fail closed）。
    """

    modelled = {model.deferred_call_key for model in view.call_models}
    keys = set()
    for info in (getattr(analysis, "deferred_calls", None) or {}).values():
        deferred_call_ref = getattr(info, "deferred_call_ref", None)
        stable_key = getattr(deferred_call_ref, "stable_key", None)
        deferred_key = stable_key() if callable(stable_key) else None
        if deferred_key not in modelled:
            continue
        target_ref = getattr(info, "target_ref", None)
        target_key = getattr(target_ref, "stable_key", None)
        if not callable(target_key):
            return None
        keys.add(target_key())
    return frozenset(keys)


def view_lowers_uninterpreted_call(view: ConditionalSemanticView) -> bool:
    """view の返り値 / guard が実際に CALL 応用を含むか。

    formula に UF が出るかどうかを、SMT 文字列の一致ではなく、builder が宣言
    収集に使うのと同じ式集合から判定する。
    """

    analysis = getattr(view, "analysis", None)
    for ret in getattr(analysis, "returns", None) or []:
        if expression_contains_call(getattr(ret, "value", None)):
            return True
        for condition in getattr(ret, "conditions", None) or []:
            if expression_contains_call(getattr(condition, "expression", None)):
                return True
    return False


def unsupported_calls_are_modelled(analysis: Any, view: ConditionalSemanticView) -> bool:
    """effect summary の unsupported call がすべて modelled 済み callee か。

    仮定が引き受けるのは modelled した外部 callee の効果だけなので、それ以外の
    unsupported call が 1 つでも残っていれば ``unsupported_call_effect_summary``
    は discharge しない。target_ref が取れない site があるときも False。
    """

    effect_summary = getattr(analysis, "effect_summary", None)
    if effect_summary is None:
        return False
    sites = tuple(getattr(effect_summary, "unsupported_call_sites", ()) or ())
    if not sites:
        # unsupported call が無いなら discharge するものも無い。
        return not bool(getattr(effect_summary, "has_unsupported_call", False))
    modelled_keys = _modelled_target_keys(analysis, view)
    if modelled_keys is None:
        return False
    for site in sites:
        target_ref = getattr(site, "target_ref", None)
        stable_key = getattr(target_ref, "stable_key", None)
        if not callable(stable_key):
            return False
        if stable_key() not in modelled_keys:
            return False
    return True


def conditional_equivalence_blocking_reasons(
    analysis: Any,
    view: ConditionalSemanticView,
) -> Tuple[str, ...]:
    """conditional EQ closure を止める safety reason（仮定が引き受ける分を除く）。"""

    getter = getattr(analysis, "get_equivalence_blocking_unsafety_reasons", None)
    if not callable(getter):
        return ("conditional_equivalence_safety_contract_unavailable",)
    dischargeable = (
        ASSUMPTION_DISCHARGED_SAFETY_REASONS
        if unsupported_calls_are_modelled(analysis, view)
        else frozenset()
    )
    return tuple(
        reason for reason in getter() if reason not in dischargeable
    )


def conditional_counterexample_safety_reasons(
    analysis1: Any,
    analysis2: Any,
    *,
    formula_has_uninterpreted_call: bool,
) -> Tuple[str, ...]:
    """conditional SAT を decisive な反例として扱えない理由。

    空のときだけ ``CONDITIONAL_SAFE_COUNTEREXAMPLE`` を発行してよい。
    """

    reasons = []
    for label, analysis in (("function1", analysis1), ("function2", analysis2)):
        getter = getattr(analysis, "get_decisive_sat_unsafety_reasons", None)
        if not callable(getter):
            reasons.append(f"{label}:conditional_sat_safety_contract_unavailable")
            continue
        for reason in getter():
            reasons.append(f"{label}:{reason}")
    if formula_has_uninterpreted_call:
        # UF の解釈は実際の callee の値を保証しない。任意解釈に依存しない反例だと
        # 現在の contract では示せないので decisive にしない。
        reasons.append(COUNTEREXAMPLE_UF_INTERPRETATION_DEPENDENT)
    # 既存 production と同じ replay 要求。conditional lane はこの証明を作らない。
    reasons.append(COUNTEREXAMPLE_REPLAY_MISSING)
    return tuple(reasons)


def run_conditional_proof(
    analysis1: Any,
    analysis2: Any,
    *,
    observation_policy: Any,
    solver_runner: Any,
    timeout: Optional[float] = None,
    debug: bool = False,
) -> ConditionalProofArtifact:
    """conditional lane の proof 本体。base analysis は変更しない。"""

    diagnostics: dict = {"adapter": CONDITIONAL_PROOF_ADAPTER_VERSION}
    if analysis1 is None or analysis2 is None:
        return _non_decisive((), (LANE_ANALYSIS_UNAVAILABLE,), diagnostics)

    views = []
    for label, analysis in (("function1", analysis1), ("function2", analysis2)):
        result = create_conditional_view(analysis, observation_policy=observation_policy)
        diagnostics[f"{label}_view_refusal"] = result.refusal_reason
        diagnostics[f"{label}_call_diagnostics"] = [
            reason for _key, reason in result.call_diagnostics
        ]
        if not result.constructed:
            return _non_decisive((), (LANE_VIEW_REFUSED,), diagnostics)
        views.append(result.view)
    left_view, right_view = views

    assumption_set = normalize_assumption_premises(
        sorted(
            (*left_view.assumption_set, *right_view.assumption_set),
            key=lambda premise: premise.premise_key(),
        )
    )
    modelled_call_count = len(left_view.call_models) + len(right_view.call_models)
    diagnostics["modelled_call_count"] = modelled_call_count
    diagnostics["assumption_count"] = len(assumption_set)

    # 写像しきれない callsite が残っていると、仮定は解析全体を引き受けられない。
    unmapped = tuple(
        reason
        for view in (left_view, right_view)
        for _key, reason in view.unmapped_calls
    )
    if unmapped:
        diagnostics["unmapped_calls"] = list(unmapped)
        return _non_decisive(
            assumption_set,
            (LANE_UNMAPPED_CALL_PRESENT,),
            diagnostics,
            modelled_call_count=modelled_call_count,
        )

    unsupported_modelled = all(
        unsupported_calls_are_modelled(analysis, view)
        for analysis, view in ((analysis1, left_view), (analysis2, right_view))
    )
    diagnostics["unsupported_calls_all_modelled"] = unsupported_modelled

    try:
        built = build_conditional_equivalence_formula(left_view, right_view, debug=debug)
    except (ValueError, TypeError) as exc:
        diagnostics["formula_error"] = f"{type(exc).__name__}: {exc}"
        return _non_decisive(
            assumption_set,
            (LANE_FORMULA_UNAVAILABLE,),
            diagnostics,
            modelled_call_count=modelled_call_count,
            all_calls_modelled=True,
            unsupported_calls_all_modelled=unsupported_modelled,
        )

    runner = getattr(solver_runner, "run_parallel", None)
    if not callable(runner):
        return _non_decisive(
            assumption_set,
            (LANE_SOLVER_UNAVAILABLE,),
            diagnostics,
            modelled_call_count=modelled_call_count,
            all_calls_modelled=True,
            unsupported_calls_all_modelled=unsupported_modelled,
        )
    try:
        if timeout is None:
            solver_result = runner(built.formula)
        else:
            solver_result = runner(built.formula, timeout=timeout)
    except Exception as exc:  # noqa: BLE001 - solver 側の失敗は fail closed
        diagnostics["solver_error"] = f"{type(exc).__name__}: {exc}"
        return _non_decisive(
            assumption_set,
            (LANE_SOLVER_UNAVAILABLE,),
            diagnostics,
            modelled_call_count=modelled_call_count,
            all_calls_modelled=True,
            unsupported_calls_all_modelled=unsupported_modelled,
        )

    disposition = getattr(solver_result, "is_equivalent", None)
    diagnostics["solver_disposition"] = (
        "unsat" if disposition is True else "sat" if disposition is False else "unknown"
    )
    artifact_digest = _digest(
        {
            "adapter": CONDITIONAL_PROOF_ADAPTER_VERSION,
            "left_view_key": left_view.view_key(),
            "right_view_key": right_view.view_key(),
            "formula_digest": _digest(built.formula),
            "solver_disposition": diagnostics["solver_disposition"],
        }
    )
    common = {
        "modelled_call_count": modelled_call_count,
        "all_calls_modelled": True,
        "unsupported_calls_all_modelled": unsupported_modelled,
    }

    if disposition is True:
        blocking = tuple(
            f"{label}:{reason}"
            for label, analysis, view in (
                ("function1", analysis1, left_view),
                ("function2", analysis2, right_view),
            )
            for reason in conditional_equivalence_blocking_reasons(analysis, view)
        )
        diagnostics["equivalence_blocking_reasons"] = list(blocking)
        if blocking:
            return _non_decisive(
                assumption_set, (LANE_EQ_CLOSURE_BLOCKED, *blocking), diagnostics, **common
            )
        return ConditionalProofArtifact(
            proof_kind=CONDITIONAL_EQ_CLOSURE,
            assumption_set=assumption_set,
            artifact_digest=artifact_digest,
            non_decisive_reasons=(),
            diagnostics=diagnostics,
            **common,
        )

    if disposition is False:
        safety = conditional_counterexample_safety_reasons(
            analysis1,
            analysis2,
            formula_has_uninterpreted_call=any(
                view_lowers_uninterpreted_call(view)
                for view in (left_view, right_view)
            ),
        )
        diagnostics["counterexample_safety_reasons"] = list(safety)
        if safety:
            return _non_decisive(
                assumption_set, (LANE_COUNTEREXAMPLE_UNSAFE, *safety), diagnostics, **common
            )
        return ConditionalProofArtifact(
            proof_kind=CONDITIONAL_SAFE_COUNTEREXAMPLE,
            assumption_set=assumption_set,
            artifact_digest=artifact_digest,
            non_decisive_reasons=(),
            diagnostics=diagnostics,
            **common,
        )

    return _non_decisive(
        assumption_set, (LANE_SOLVER_INCONCLUSIVE,), diagnostics, **common
    )

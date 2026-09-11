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
from typing import Any, List, Mapping, Optional, Sequence, Tuple

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


#: この token を持つ ``_create`` 以外から artifact を作らせない。
_CONDITIONAL_PROOF_ARTIFACT_FACTORY_TOKEN = object()


@dataclass(frozen=True, init=False)
class ConditionalProofArtifact:
    """conditional lane 1 回分の proof 成果物（authority ではない）。

    authority 側の discharge / receipt 発行が読む field は **すべて
    ``artifact_digest`` に bind される**。artifact は :meth:`_create` からしか
    作れず、:meth:`validate` が保存された field から digest を組み直して
    改竄を検出する。``diagnostics`` だけは判定に使わない観測なので digest に
    入れない（``compare=False``）。

    ``proof_kind`` が ``None`` なら decisive ではない。``assumption_set`` は
    左右 view の和で、**最小化しない**。receipt はこれをそのまま
    ``assumption_dependencies`` に使う。
    """

    proof_kind: Optional[str]
    assumption_set: Tuple[AssumptionPremise, ...]
    assumption_set_digest: str
    formula_digest: Optional[str]
    solver_disposition: Optional[str]
    modelled_call_count: int
    #: 写像した callsite の object identity。``(side, pcode_op_stable_key)``。
    #: authority 側が「どの cause occurrence を仮定が引き受けたか」を exact に
    #: 突き合わせるための唯一の根拠で、1 つでも identity が取れなければ
    #: ``modelled_call_sites_complete`` が False になり discharge は行われない。
    modelled_call_sites: Tuple[Tuple[str, Tuple[Any, ...]], ...]
    modelled_call_sites_complete: bool
    all_calls_modelled: bool
    unsupported_calls_all_modelled: bool
    non_decisive_reasons: Tuple[str, ...]
    artifact_digest: str
    diagnostics: Mapping[str, Any] = field(
        default_factory=dict, compare=False, repr=False
    )

    def __init__(
        self,
        *,
        proof_kind: Optional[str],
        assumption_set: Sequence[AssumptionPremise],
        assumption_set_digest: str,
        formula_digest: Optional[str],
        solver_disposition: Optional[str],
        modelled_call_count: int,
        modelled_call_sites: Sequence[Tuple[str, Tuple[Any, ...]]],
        modelled_call_sites_complete: bool,
        all_calls_modelled: bool,
        unsupported_calls_all_modelled: bool,
        non_decisive_reasons: Sequence[str],
        artifact_digest: str,
        diagnostics: Optional[Mapping[str, Any]] = None,
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _CONDITIONAL_PROOF_ARTIFACT_FACTORY_TOKEN:
            raise ValueError(
                "conditional proof artifacts are issued only by run_conditional_proof"
            )
        object.__setattr__(self, "proof_kind", proof_kind)
        object.__setattr__(self, "assumption_set", tuple(assumption_set))
        object.__setattr__(self, "assumption_set_digest", assumption_set_digest)
        object.__setattr__(self, "formula_digest", formula_digest)
        object.__setattr__(self, "solver_disposition", solver_disposition)
        object.__setattr__(self, "modelled_call_count", int(modelled_call_count))
        object.__setattr__(
            self,
            "modelled_call_sites",
            tuple((str(side), tuple(key)) for side, key in modelled_call_sites),
        )
        object.__setattr__(
            self, "modelled_call_sites_complete", bool(modelled_call_sites_complete)
        )
        object.__setattr__(self, "all_calls_modelled", bool(all_calls_modelled))
        object.__setattr__(
            self, "unsupported_calls_all_modelled", bool(unsupported_calls_all_modelled)
        )
        object.__setattr__(self, "non_decisive_reasons", tuple(non_decisive_reasons))
        object.__setattr__(self, "artifact_digest", artifact_digest)
        object.__setattr__(self, "diagnostics", dict(diagnostics or {}))

    @property
    def decisive(self) -> bool:
        return self.proof_kind is not None

    @staticmethod
    def assumption_digest(
        assumption_set: Sequence[AssumptionPremise],
    ) -> str:
        """assumption set の内容そのものを表す digest。

        ``premise_key()`` は schema version / kind / subject / payload を含む
        canonical identity なので、premise を 1 つ差し替えても digest が動く。
        """

        return _digest(tuple(premise.premise_key() for premise in assumption_set))

    def artifact_payload(self) -> Mapping[str, Any]:
        """``artifact_digest`` の preimage（authority が読む field 全部）。"""

        return {
            "adapter": CONDITIONAL_PROOF_ADAPTER_VERSION,
            "proof_kind": self.proof_kind,
            "assumption_set_digest": self.assumption_set_digest,
            "formula_digest": self.formula_digest,
            "solver_disposition": self.solver_disposition,
            "modelled_call_count": self.modelled_call_count,
            "modelled_call_sites": [
                [side, list(key)] for side, key in self.modelled_call_sites
            ],
            "modelled_call_sites_complete": self.modelled_call_sites_complete,
            "all_calls_modelled": self.all_calls_modelled,
            "unsupported_calls_all_modelled": self.unsupported_calls_all_modelled,
            "non_decisive_reasons": list(self.non_decisive_reasons),
        }

    def validate(self) -> None:
        """保存された field から digest を組み直して一致を確かめる。"""

        if self.proof_kind is not None and self.proof_kind not in (
            CONDITIONAL_EQ_CLOSURE,
            CONDITIONAL_SAFE_COUNTEREXAMPLE,
        ):
            raise ValueError(f"unknown conditional proof kind: {self.proof_kind}")
        for premise in self.assumption_set:
            if type(premise) is not AssumptionPremise:
                raise TypeError(
                    "conditional proof artifacts carry AssumptionPremise only: "
                    f"{type(premise).__name__}"
                )
        if self.assumption_digest(self.assumption_set) != self.assumption_set_digest:
            raise ValueError("conditional proof artifact assumption digest mismatch")
        if _digest(self.artifact_payload()) != self.artifact_digest:
            raise ValueError("conditional proof artifact digest mismatch")
        if self.decisive:
            if not self.assumption_set:
                raise ValueError("a decisive conditional proof carries its assumption set")
            if not self.all_calls_modelled:
                raise ValueError(
                    "a decisive conditional proof models every deferred call of both sides"
                )
            if not self.formula_digest or not self.solver_disposition:
                raise ValueError(
                    "a decisive conditional proof binds its formula and solver disposition"
                )
            if self.non_decisive_reasons:
                raise ValueError("a decisive conditional proof carries no refusal reason")

    def validates(self) -> bool:
        try:
            self.validate()
        except (TypeError, ValueError):
            return False
        return True

    @classmethod
    def _create(
        cls,
        *,
        proof_kind: Optional[str],
        assumption_set: Sequence[AssumptionPremise] = (),
        formula_digest: Optional[str] = None,
        solver_disposition: Optional[str] = None,
        modelled_call_count: int = 0,
        modelled_call_sites: Sequence[Tuple[str, Tuple[Any, ...]]] = (),
        modelled_call_sites_complete: bool = False,
        all_calls_modelled: bool = False,
        unsupported_calls_all_modelled: bool = False,
        non_decisive_reasons: Sequence[str] = (),
        diagnostics: Optional[Mapping[str, Any]] = None,
    ) -> "ConditionalProofArtifact":
        """artifact を発行する唯一の入口。digest はここでだけ計算する。"""

        assumption_set = tuple(assumption_set)
        fields = {
            "proof_kind": proof_kind,
            "assumption_set": assumption_set,
            "assumption_set_digest": cls.assumption_digest(assumption_set),
            "formula_digest": formula_digest,
            "solver_disposition": solver_disposition,
            "modelled_call_count": int(modelled_call_count),
            "modelled_call_sites": tuple(
                (str(side), tuple(key)) for side, key in modelled_call_sites
            ),
            "modelled_call_sites_complete": bool(modelled_call_sites_complete),
            "all_calls_modelled": bool(all_calls_modelled),
            "unsupported_calls_all_modelled": bool(unsupported_calls_all_modelled),
            "non_decisive_reasons": tuple(non_decisive_reasons),
        }
        artifact = cls(
            **fields,
            artifact_digest="",
            diagnostics=diagnostics,
            _factory_token=_CONDITIONAL_PROOF_ARTIFACT_FACTORY_TOKEN,
        )
        artifact = cls(
            **fields,
            artifact_digest=_digest(artifact.artifact_payload()),
            diagnostics=diagnostics,
            _factory_token=_CONDITIONAL_PROOF_ARTIFACT_FACTORY_TOKEN,
        )
        artifact.validate()
        return artifact


def _non_decisive(
    assumption_set: Sequence[AssumptionPremise],
    reasons: Sequence[str],
    diagnostics: Mapping[str, Any],
    *,
    modelled_call_count: int = 0,
    all_calls_modelled: bool = False,
    unsupported_calls_all_modelled: bool = False,
    modelled_call_sites: Sequence[Tuple[str, Tuple[Any, ...]]] = (),
    modelled_call_sites_complete: bool = False,
    formula_digest: Optional[str] = None,
    solver_disposition: Optional[str] = None,
) -> ConditionalProofArtifact:
    return ConditionalProofArtifact._create(
        proof_kind=None,
        assumption_set=assumption_set,
        formula_digest=formula_digest,
        solver_disposition=solver_disposition,
        modelled_call_count=modelled_call_count,
        modelled_call_sites=modelled_call_sites,
        modelled_call_sites_complete=modelled_call_sites_complete,
        all_calls_modelled=all_calls_modelled,
        unsupported_calls_all_modelled=unsupported_calls_all_modelled,
        non_decisive_reasons=reasons,
        diagnostics=diagnostics,
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


def modelled_call_site_identities(
    analysis: Any,
    view: ConditionalSemanticView,
) -> Optional[Tuple[Tuple[Any, ...], ...]]:
    """view が写像した callsite の ``PcodeOpRef.stable_key()`` 集合。

    1 つでも identity が取れない、あるいは写像した数と一致しないなら ``None``
    （fail closed）。この key は call-effect 側の ``CallSiteFact.identity``
    (``ArtifactObjectIdentity.pcode_op_key``) と同じ object identity なので、
    別実装の対応付けを作らずに cause occurrence へ突き合わせられる。
    """

    modelled = {model.deferred_call_key for model in view.call_models}
    keys = []
    for info in (getattr(analysis, "deferred_calls", None) or {}).values():
        deferred_call_ref = getattr(info, "deferred_call_ref", None)
        stable_key = getattr(deferred_call_ref, "stable_key", None)
        deferred_key = stable_key() if callable(stable_key) else None
        if deferred_key not in modelled:
            continue
        pcode_op_ref = getattr(deferred_call_ref, "pcode_op_ref", None)
        op_key = getattr(pcode_op_ref, "stable_key", None)
        if not callable(op_key):
            return None
        key = op_key()
        if not key:
            return None
        keys.append(tuple(key))
    if len(keys) != len(modelled):
        return None
    return tuple(keys)


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

    call_sites: List[Tuple[str, Tuple[Any, ...]]] = []
    sites_complete = True
    for label, analysis, view in (
        ("function1", analysis1, left_view),
        ("function2", analysis2, right_view),
    ):
        identities = modelled_call_site_identities(analysis, view)
        if identities is None:
            sites_complete = False
            continue
        call_sites.extend((label, identity) for identity in identities)
    modelled_call_sites = tuple(call_sites)
    diagnostics["modelled_call_sites_complete"] = sites_complete

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
    # formula digest は view identity も一緒に束ねる（同じ SMT 文字列でも、
    # 別の view から来たものは別 artifact）。
    formula_digest = _digest(
        {
            "left_view_key": left_view.view_key(),
            "right_view_key": right_view.view_key(),
            "formula": built.formula,
        }
    )
    common = {
        "modelled_call_count": modelled_call_count,
        "all_calls_modelled": True,
        "unsupported_calls_all_modelled": unsupported_modelled,
        "modelled_call_sites": modelled_call_sites,
        "modelled_call_sites_complete": sites_complete,
        "formula_digest": formula_digest,
        "solver_disposition": diagnostics["solver_disposition"],
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
        return ConditionalProofArtifact._create(
            proof_kind=CONDITIONAL_EQ_CLOSURE,
            assumption_set=assumption_set,
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
        return ConditionalProofArtifact._create(
            proof_kind=CONDITIONAL_SAFE_COUNTEREXAMPLE,
            assumption_set=assumption_set,
            non_decisive_reasons=(),
            diagnostics=diagnostics,
            **common,
        )

    return _non_decisive(
        assumption_set, (LANE_SOLVER_INCONCLUSIVE,), diagnostics, **common
    )

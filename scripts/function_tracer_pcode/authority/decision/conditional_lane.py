# -*- coding: utf-8 -*-
"""Production activation of the conditional (assumption-dependent) lane.

Issue #20 PR-20-B3。proof 層が返した ``ConditionalProofArtifact`` を
PR-20-A の sealed contract へ載せる境界。proof は authority を import せず、
receipt 化はここだけで行う。

起動順序（正本 v4 §4.4）:

    unconditional analysis → stage plan → unconditional DecisionReceipt
    → final_outcome == UNKNOWN のときだけ conditional eligibility
    → conditional lane

``EQUIVALENT`` / ``NOT_EQ`` / ``TIMEOUT`` / ``ERROR`` では絶対に起動しない。
UNKNOWN でも view が立たない・仮定が成立しない・formula が組めないなら decisive
な conditional receipt を作らない。無条件の結果は決して上書きしない。

**discharge 規則**: conditional lane が持ち込む事実は「modelled した外部 callee が
catalog 仕様どおりに振る舞い、observable memory write が無く、normal return する」
という仮定と、その callsite を同名 UF として左右そろって扱う formula だけである。
したがって conditional projection から落としてよい active cause は、その 2 つが
置き換える理由だけに限る。ここに無い理由（outcome partition、ABI 幅、recurrence、
argument extraction など）は残り、``finalize_conditional_decision`` の
``blocks_equivalence`` / ``blocks_decision`` 判定でそのまま効く（= fail closed）。
"""

from __future__ import annotations

from typing import Any, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.authority.contracts import (
    Outcome,
    VerifiedLifecycleProjection,
)
from scripts.function_tracer_pcode.authority.decision.conditional import (
    ConditionalDecisiveProofKind,
    ConditionalDecisiveProofReceipt,
    ConditionalFinalizationAuthority,
    finalize_conditional_decision,
)
from scripts.function_tracer_pcode.authority.decision.decision import DecisionReceipt


#: 外部 callee 仮定 + UF モデルが置き換える active cause の reason id。
#:
#: * ``pure_call_semantics_unproven`` — 「callee が値意味を持つ純関数だ」という、
#:   まさに premise が明示的に引き受ける事実。
#: * ``unsupported_call_effect_semantics`` — premise の
#:   ``no_observable_memory_write`` / ``returns_normally`` が引き受ける。
#: * ``callsite_correspondence_unproven`` — UF モデルでは位置対応は不要で、
#:   同じ canonical symbol の同じ引数式が同じ値になることを formula が使う。
#: * ``external_call_coupling_unproven`` — 左右が同じ catalog symbol を同じ UF へ
#:   写すことが coupling そのもの。
#: * ``call_effect_correspondence_unproven`` /
#:   ``effect_endpoint_correspondence_unproven`` — 観測可能な write が無いという
#:   仮定の下では対応づける効果が存在しない。
#:
#: 引数復元 (``call_argument_extraction_incomplete``)、ABI 引数関係
#: (``abi_argument_relation_unproven``) は **入れない**。前者は PR-20-D の
#: 所有で、view は ``complete`` な callsite しか写像しない。後者は formula が
#: 復元済み引数式から証明するものであって仮定ではない。
ASSUMPTION_DISCHARGED_REASON_IDS = frozenset({
    "pure_call_semantics_unproven",
    "unsupported_call_effect_semantics",
    "callsite_correspondence_unproven",
    "external_call_coupling_unproven",
    "call_effect_correspondence_unproven",
    "effect_endpoint_correspondence_unproven",
})


def conditional_lane_projection(
    projection: VerifiedLifecycleProjection,
    *,
    discharged_reason_ids: Sequence[str],
) -> VerifiedLifecycleProjection:
    """discharge した cause だけを落とした conditional projection を封する。

    落とした cause にぶら下がる open requirement も一緒に落とす（``seal`` は
    「open requirement には対応する active cause が要る」を検査する）。
    blocker eligibility 行はそのまま残す ―― 観測事実は仮定では消えない。
    """

    projection.validate()
    discharged = frozenset(discharged_reason_ids)
    if not discharged:
        return projection
    kept_causes = tuple(
        row for row in projection.c_active_base if row.reason_id not in discharged
    )
    kept_cause_keys = {
        (row.result_occurrence_id, row.occurrence_id, row.cause_id)
        for row in kept_causes
    }
    kept_requirements = tuple(
        row for row in projection.q_open_base
        if (row.result_occurrence_id, row.occurrence_id, row.cause_id) in kept_cause_keys
    )
    return VerifiedLifecycleProjection.seal(
        result_occurrence_id=projection.result_occurrence_id,
        snapshot_digest=projection.snapshot_digest,
        c_active_base=kept_causes,
        q_open_base=kept_requirements,
        blocker_eligibility_base=projection.blocker_eligibility_base,
        satisfaction_projection=projection.satisfaction_projection,
    )


_PROOF_KIND_BY_NAME = {
    "CONDITIONAL_EQ_CLOSURE": ConditionalDecisiveProofKind.CONDITIONAL_EQ_CLOSURE,
    "CONDITIONAL_SAFE_COUNTEREXAMPLE": (
        ConditionalDecisiveProofKind.CONDITIONAL_SAFE_COUNTEREXAMPLE
    ),
}


def conditional_lane_is_eligible(unconditional_decision: Any) -> bool:
    """conditional lane を起動してよいのは無条件 UNKNOWN のときだけ。"""

    if type(unconditional_decision) is not DecisionReceipt:
        return False
    unconditional_decision.validate()
    return unconditional_decision.outcome is Outcome.UNKNOWN


def issue_conditional_decision(
    *,
    unconditional_decision: DecisionReceipt,
    projection: VerifiedLifecycleProjection,
    artifact: Any,
) -> Any:
    """proof artifact を conditional 列の ``ConditionalDecisionReceipt`` にする。

    decisive でない artifact でも receipt は出す（conditional_outcome は
    ``UNKNOWN``）。無条件 receipt / projection / 結果には触れない。
    """

    if not conditional_lane_is_eligible(unconditional_decision):
        raise ValueError("the conditional lane runs only after an unconditional UNKNOWN")
    assumption_set = tuple(getattr(artifact, "assumption_set", ()) or ())
    if not assumption_set:
        raise ValueError("a conditional lane requires a non-empty assumption set")

    proof_kind_name = getattr(artifact, "proof_kind", None)
    receipts: Tuple[ConditionalDecisiveProofReceipt, ...] = ()
    lane_projection = projection
    if proof_kind_name is not None:
        proof_kind = _PROOF_KIND_BY_NAME.get(str(proof_kind_name))
        if proof_kind is None:
            raise ValueError(f"unknown conditional proof kind: {proof_kind_name}")
        lane_projection = conditional_lane_projection(
            projection, discharged_reason_ids=ASSUMPTION_DISCHARGED_REASON_IDS
        )
        receipts = (
            ConditionalDecisiveProofReceipt.create(
                result_occurrence_id=lane_projection.result_occurrence_id,
                lifecycle_projection_digest=lane_projection.lifecycle_projection_digest,
                proof_kind=proof_kind,
                proof_artifact_digest=str(getattr(artifact, "artifact_digest", "")),
                # dependency minimization はしない。view が運んだ集合そのもの。
                assumption_dependencies=assumption_set,
            ),
        )
    authority = ConditionalFinalizationAuthority(
        lane_projection.result_occurrence_id,
        unconditional_decision,
        lane_projection,
        assumption_set,
        conditional_decisive_proof_receipts=receipts,
    )
    return finalize_conditional_decision(authority)


def run_production_conditional_lane(
    result: Any,
    *,
    projection: VerifiedLifecycleProjection,
    analyses: Optional[Tuple[Any, Any]],
    observation_policy: Any,
    solver_runner: Any,
    timeout: Optional[float] = None,
    debug: bool = False,
) -> Optional[Mapping[str, Any]]:
    """production の conditional lane。``result`` の conditional 列だけを触る。

    conditional 列を付けたときはその診断を返し、起動しなかった / 付けなかった
    ときは ``None`` を返す。例外は投げない（無条件の判定を絶対に壊さない）。
    """

    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        attach_conditional_decision,
    )
    from scripts.function_tracer_pcode.proof.conditional_lane import (
        run_conditional_proof,
    )

    decision = getattr(result, "decision_receipt", None)
    if not conditional_lane_is_eligible(decision):
        return None
    if analyses is None:
        return None
    analysis1, analysis2 = analyses

    try:
        artifact = run_conditional_proof(
            analysis1,
            analysis2,
            observation_policy=observation_policy,
            solver_runner=solver_runner,
            timeout=timeout,
            debug=debug,
        )
        if not artifact.assumption_set:
            # view が立たなかった。conditional 列は作らない（fail closed）。
            return {
                "conditional_lane": "not_constructed",
                "non_decisive_reasons": list(artifact.non_decisive_reasons),
                "diagnostics": dict(artifact.diagnostics),
            }
        if not artifact.decisive:
            # 何も証明できていない。conditional 列は「出たときだけ出す」ので、
            # 起動した事実と非決定理由は診断にだけ残す。
            return {
                "conditional_lane": "non_decisive",
                "non_decisive_reasons": list(artifact.non_decisive_reasons),
                "assumption_count": len(artifact.assumption_set),
                "diagnostics": dict(artifact.diagnostics),
            }
        receipt = issue_conditional_decision(
            unconditional_decision=decision,
            projection=projection,
            artifact=artifact,
        )
        attach_conditional_decision(result, receipt)
    except Exception as exc:  # noqa: BLE001
        # conditional 列は付けない。無条件の判定・reason・exit code は不変。
        return {
            "conditional_lane": "failed",
            "error": f"{type(exc).__name__}: {exc}",
        }
    return {
        "conditional_lane": "issued",
        "conditional_outcome": receipt.conditional_outcome.value,
        "proof_kind": artifact.proof_kind,
        "assumption_count": len(artifact.assumption_set),
        "non_decisive_reasons": list(artifact.non_decisive_reasons),
        "diagnostics": dict(artifact.diagnostics),
    }

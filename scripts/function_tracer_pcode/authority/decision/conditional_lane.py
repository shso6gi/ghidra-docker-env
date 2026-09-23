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
したがって conditional projection から落とせる active cause は

1. reason id が :data:`ASSUMPTION_DISCHARGED_REASON_IDS` にあり、**かつ**
2. その cause occurrence が **仮定で写像した callsite そのもの**に bind されている

ものだけに限る。**reason id 単位では落とさない。** 同じ
``callsite_correspondence_unproven`` でも、写像していない internal call 由来の
occurrence は残す ―― external callee の仮定はそれを discharge する根拠にならない。

対応付けは既存の typed identity をそのまま使う（新しい identity を作らない）:

    c_active_base row (occurrence_id, cause_id)
      → 同じ pair の UnknownReasonRecord.typed_cause_key で join
      → record.object_target_key
         = (target_kind, "call_effect_prerequisite", obligation_id,
            observation_contract_id, left_fact_id, right_fact_id,
            structural_certificate_id)                   ← call_effect 域の cause 鍵
      → call-effect shadow manifest の left_facts / right_facts で
         fact_id → CallSiteFact.identity.pcode_op_key    ← 既存の object identity
      → proof artifact が運んだ modelled callsite の PcodeOpRef.stable_key() と一致

いずれかが解決できなければ **その cause は落とさない**（fail closed）。occurrence 数・
並び順・reason 名の一致は対応根拠にしない。ここで落とせなかった理由（outcome
partition、ABI 幅、recurrence、argument extraction など）は残り、
``finalize_conditional_decision`` の ``blocks_equivalence`` / ``blocks_decision``
判定でそのまま効く。
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


#: call-effect 域の prerequisite cause 鍵のタグ（``_prerequisite_authority`` が作る）。
CALL_EFFECT_PREREQUISITE_TARGET_TAG = "call_effect_prerequisite"
_PREREQUISITE_TARGET_KEY_LENGTH = 7
_PREREQUISITE_LEFT_FACT_SLOT = 4
_PREREQUISITE_RIGHT_FACT_SLOT = 5


def _canonical_key(value: Any) -> Any:
    """list / tuple を再帰的に tuple へ揃える（JSON 往復で形だけ変わるため）。"""

    if isinstance(value, (list, tuple)):
        return tuple(_canonical_key(item) for item in value)
    return value


def _cause_target_keys(result: Any) -> Mapping[Tuple[str, str], Any]:
    """``(occurrence_id, cause_id) -> object_target_key``。

    同じ cause に食い違う target key が付いていたら ``None`` を値にして、
    その cause は対応付け不能（= discharge しない）ことを表す。
    """

    keys: dict = {}
    for record in getattr(result, "unknown_reasons", None) or ():
        typed_cause_key = getattr(record, "typed_cause_key", None)
        if not isinstance(typed_cause_key, Mapping):
            continue
        occurrence_id = typed_cause_key.get("occurrence_id")
        cause_id = typed_cause_key.get("cause_id")
        target_key = _canonical_key(getattr(record, "object_target_key", None))
        if not occurrence_id or not cause_id or not target_key:
            continue
        identity = (str(occurrence_id), str(cause_id))
        if identity in keys and keys[identity] != target_key:
            keys[identity] = None
            continue
        keys[identity] = target_key
    return keys


def _fact_pcode_keys(manifest: Any, side: str) -> Mapping[str, Any]:
    """``fact_id -> CallSiteFact.identity.pcode_op_key`` を manifest から読む。"""

    if not isinstance(manifest, Mapping):
        return {}
    rows = manifest.get(side) or ()
    resolved: dict = {}
    for fact in rows:
        if not isinstance(fact, Mapping):
            continue
        fact_id = fact.get("fact_id")
        identity = fact.get("identity")
        if not fact_id or not isinstance(identity, Mapping):
            continue
        pcode_op_key = _canonical_key(identity.get("pcode_op_key"))
        if not pcode_op_key:
            continue
        resolved[str(fact_id)] = pcode_op_key
    return resolved


def validated_conditional_proof_artifact(artifact: Any) -> Any:
    """exact な proof artifact であり、digest が保存 field と一致することを確かめる。

    duck typing では受け付けない。artifact の authority-relevant field
    （proof kind / assumption set / modelled callsite / 各完全性フラグ）は
    ``artifact_digest`` に bind されているので、差し替えはここで落ちる。
    """

    from scripts.function_tracer_pcode.proof.conditional_lane import (
        ConditionalProofArtifact,
    )

    if type(artifact) is not ConditionalProofArtifact:
        raise TypeError(
            "the conditional lane accepts an exact ConditionalProofArtifact only: "
            f"{type(artifact).__name__}"
        )
    artifact.validate()
    return artifact


def conditional_discharged_causes(
    projection: VerifiedLifecycleProjection,
    *,
    result: Any,
    artifact: Any,
) -> frozenset:
    """仮定が実際に引き受けた ``(occurrence_id, cause_id)`` だけを返す。

    対応を既存 authority / evidence から証明できない cause は返さない
    （= conditional projection に残る）。artifact は exact 型 + digest 検証を
    通ったものだけを受け付ける。
    """

    artifact = validated_conditional_proof_artifact(artifact)
    if not bool(getattr(artifact, "modelled_call_sites_complete", False)):
        return frozenset()
    modelled: dict = {"function1": set(), "function2": set()}
    for side, identity in getattr(artifact, "modelled_call_sites", ()) or ():
        if side not in modelled:
            return frozenset()
        modelled[side].add(_canonical_key(identity))
    if not (modelled["function1"] or modelled["function2"]):
        return frozenset()

    manifest = getattr(result, "call_effect_shadow_manifest", None)
    left_facts = _fact_pcode_keys(manifest, "left_facts")
    right_facts = _fact_pcode_keys(manifest, "right_facts")
    if not left_facts and not right_facts:
        return frozenset()
    target_keys = _cause_target_keys(result)

    discharged = set()
    for row in projection.c_active_base:
        if row.reason_id not in ASSUMPTION_DISCHARGED_REASON_IDS:
            continue
        target_key = target_keys.get((row.occurrence_id, row.cause_id))
        if not target_key or len(target_key) != _PREREQUISITE_TARGET_KEY_LENGTH:
            continue
        if target_key[1] != CALL_EFFECT_PREREQUISITE_TARGET_TAG:
            continue
        endpoints = (
            ("function1", left_facts, target_key[_PREREQUISITE_LEFT_FACT_SLOT]),
            ("function2", right_facts, target_key[_PREREQUISITE_RIGHT_FACT_SLOT]),
        )
        if all(fact_id is None for _side, _facts, fact_id in endpoints):
            continue
        bound = True
        for side, facts, fact_id in endpoints:
            if fact_id is None:
                continue
            pcode_op_key = facts.get(str(fact_id))
            if pcode_op_key is None or pcode_op_key not in modelled[side]:
                bound = False
                break
        if bound:
            discharged.add((row.occurrence_id, row.cause_id))
    return frozenset(discharged)


def _as_mapping(value: Any) -> Optional[dict]:
    """Mapping か、``canonical_value`` が作る ``((key, value), ...)`` を dict にする。

    ``VerifiedLifecycleProjection.seal`` は satisfaction projection を
    ``canonical_value`` へ通すので、封じる前（Mapping）と封じた後（pair tuple）で
    形が変わる。どちらでも同じ規則で扱えるようにする。
    """

    if isinstance(value, Mapping):
        return dict(value)
    if isinstance(value, tuple) and value and all(
        isinstance(item, tuple) and len(item) == 2 and isinstance(item[0], str)
        for item in value
    ):
        return dict(value)
    return None


def _satisfaction_row_identity(row: Any) -> Optional[Tuple[str, str]]:
    fields = _as_mapping(row)
    if fields is None:
        return None
    occurrence_id = fields.get("occurrence_id")
    cause_id = fields.get("cause_id")
    if occurrence_id is None or cause_id is None:
        return None
    return (str(occurrence_id), str(cause_id))


def _satisfaction_without(projection: Any, removed: frozenset) -> Any:
    """discharge した occurrence の satisfaction 行を落とす。

    ``seal()`` は satisfaction projection の中身を検査しないので、ここで
    整合させないと「c_active から消えたのに satisfaction では active のまま」
    という派生情報の食い違いが残る。行の形が読めなければ落とさない（fail closed
    ではなく、そのまま持ち越して整合検査で弾く）。
    """

    satisfaction = projection.satisfaction_projection
    fields = _as_mapping(satisfaction)
    if fields is None:
        return satisfaction
    rows = fields.get("occurrences")
    if not isinstance(rows, (list, tuple)):
        return satisfaction
    kept = tuple(
        row for row in rows
        if _satisfaction_row_identity(row) not in removed
    )
    fields["occurrences"] = kept
    return fields


def _assert_conditional_projection_consistent(
    lane_projection: VerifiedLifecycleProjection,
    *,
    removed: frozenset,
) -> None:
    """封じ直した projection の派生情報が整合していることを確かめる。

    ``seal()`` が通ることだけを根拠にしない。落とした occurrence がどこにも
    残っていないこと、open requirement と active cause が対応すること、
    satisfaction の active 行と c_active_base が一致することを直接検査する。
    """

    active = {
        (row.occurrence_id, row.cause_id) for row in lane_projection.c_active_base
    }
    if active & removed:
        raise ValueError("discharged cause is still active in the conditional projection")
    for row in lane_projection.q_open_base:
        if (row.occurrence_id, row.cause_id) in removed:
            raise ValueError("discharged cause still has an open proof requirement")
        if (row.occurrence_id, row.cause_id) not in active:
            raise ValueError("conditional projection open requirement lacks its cause")
    fields = _as_mapping(lane_projection.satisfaction_projection) or {}
    rows = fields.get("occurrences") or ()
    satisfied_active = set()
    for row in rows:
        identity = _satisfaction_row_identity(row)
        if identity is None:
            raise ValueError("conditional projection satisfaction row is unreadable")
        if identity in removed:
            raise ValueError("discharged cause still has a satisfaction row")
        if (_as_mapping(row) or {}).get("active"):
            satisfied_active.add(identity)
    if satisfied_active != active:
        raise ValueError("conditional projection satisfaction rows disagree with c_active_base")


def conditional_lane_projection(
    projection: VerifiedLifecycleProjection,
    *,
    discharged_causes: Sequence[Tuple[str, str]],
) -> VerifiedLifecycleProjection:
    """引き受けた cause occurrence だけを落とした conditional projection を封する。

    落とした cause にぶら下がる open requirement と satisfaction 行も一緒に落とす。
    blocker eligibility 行はそのまま残す ―― 観測事実は仮定では消えない。
    """

    projection.validate()
    removed = frozenset((str(occ), str(cause)) for occ, cause in discharged_causes)
    if not removed:
        return projection
    kept_causes = tuple(
        row for row in projection.c_active_base
        if (row.occurrence_id, row.cause_id) not in removed
    )
    kept_requirements = tuple(
        row for row in projection.q_open_base
        if (row.occurrence_id, row.cause_id) not in removed
    )
    lane_projection = VerifiedLifecycleProjection.seal(
        result_occurrence_id=projection.result_occurrence_id,
        snapshot_digest=projection.snapshot_digest,
        c_active_base=kept_causes,
        q_open_base=kept_requirements,
        blocker_eligibility_base=projection.blocker_eligibility_base,
        satisfaction_projection=_satisfaction_without(projection, removed),
    )
    _assert_conditional_projection_consistent(lane_projection, removed=removed)
    return lane_projection


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
    result: Any = None,
) -> Any:
    """proof artifact を conditional 列の ``ConditionalDecisionReceipt`` にする。

    decisive でない artifact でも receipt は出す（conditional_outcome は
    ``UNKNOWN``）。無条件 receipt / projection / 結果には触れない。
    """

    if not conditional_lane_is_eligible(unconditional_decision):
        raise ValueError("the conditional lane runs only after an unconditional UNKNOWN")
    artifact = validated_conditional_proof_artifact(artifact)
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
        # 仮定が実際に引き受けた cause occurrence だけを落とす。対応を証明
        # できなければ 1 つも落とさず、残った blocker がそのまま効く。
        discharged = conditional_discharged_causes(
            projection, result=result, artifact=artifact
        )
        lane_projection = conditional_lane_projection(
            projection, discharged_causes=discharged
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
    from scripts.function_tracer_pcode.core.errors import (
        LimitationAfterFinalization,
        limitations_after_finalization,
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

    limitations_before = limitations_after_finalization()
    try:
        artifact = run_conditional_proof(
            analysis1,
            analysis2,
            observation_policy=observation_policy,
            solver_runner=solver_runner,
            timeout=timeout,
            debug=debug,
        )
        if limitations_after_finalization() != limitations_before:
            # 計算の途中で限界が上がり、どこかで握り潰された。結果は不完全なので
            # conditional 列を作らない（fail closed。判定は既に確定している）。
            return {"conditional_lane": "stopped_by_limitation", "swallowed": True}
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
            result=result,
        )
        attach_conditional_decision(result, receipt)
    except LimitationAfterFinalization as exc:
        # Issue #22 PR-22-D: lane は authority 確定の **後** に走る非 authoritative
        # な consumer。そこで上がった限界（式サイズ予算など）は判定を変えず、
        # 台帳にも記録されない — lane の結果だけを作らない（fail closed）。
        return {
            "conditional_lane": "stopped_by_limitation",
            "reason_id": exc.limitation.reason_id,
            "site": exc.limitation.site,
        }
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
        "discharged_cause_count": len(
            conditional_discharged_causes(projection, result=result, artifact=artifact)
        ),
        "non_decisive_reasons": list(artifact.non_decisive_reasons),
        "diagnostics": dict(artifact.diagnostics),
    }

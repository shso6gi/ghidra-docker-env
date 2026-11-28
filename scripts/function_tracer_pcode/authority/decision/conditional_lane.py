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

**具体実行の反例（Issue #18 C2）**: ``proof.concrete_counterexample`` が両 binary の
具体実行で戻り値の差を確定したとき、その証拠は記号解析の近似に依存しない（witness は
入力の選び方にすぎず、差を示すのは実行）。したがって落とせるのは **同じ pair の SAT-safety
の cause**（:data:`CONCRETE_DISCHARGED_REASON_IDS`、記号の反例が安全と示せないこと）だけで、
それ以外の ``blocks_disequivalence`` / ``blocks_decision`` は残る。仮定（呼び出し規約・
P-code の意味）は receipt の assumption set に載る。

いずれかが解決できなければ **その cause は落とさない**（fail closed）。occurrence 数・
並び順・reason 名の一致は対応根拠にしない。ここで落とせなかった理由（outcome
partition、ABI 幅、recurrence、argument extraction など）は残り、
``finalize_conditional_decision`` の ``blocks_equivalence`` / ``blocks_decision``
判定でそのまま効く（その判定は主判定と共通の ``obligation_scope`` の規則。Issue #325 E1 では
どの証拠も全事実に依存するので、``decision_effect`` だけで阻む従来の規則と同じ結果になる）。
"""

from __future__ import annotations

from contextlib import contextmanager
from typing import Any, Iterator, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.authority.contracts import (
    Outcome,
    VerifiedLifecycleProjection,
)
from scripts.function_tracer_pcode.authority.decision.conditional import (
    canonical_assumption_dependencies,
    assumption_set_receipt_bound_violation,
    ConditionalDecisiveProofKind,
    ConditionalDecisiveProofReceipt,
    ConditionalFinalizationAuthority,
    finalize_conditional_decision_with_scope,
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


#: 具体実行の反例が引き受ける active cause の reason id: 記号の反例の安全性（SAT-safety）。
#: 語彙の owner は ``proof.sat_safety_resolution``（ここには写さない）。
def _concrete_discharged_reason_ids() -> frozenset:
    from scripts.function_tracer_pcode.proof.sat_safety_resolution import (
        SAT_SAFETY_TYPED_REASON_IDS,
    )

    return frozenset(SAT_SAFETY_TYPED_REASON_IDS)


CONCRETE_DISCHARGED_REASON_IDS = _concrete_discharged_reason_ids()


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


def validated_concrete_proof_artifact(artifact: Any) -> Any:
    """exact な ``ConcreteCounterexampleArtifact`` で、digest が保存 field と一致すること。"""

    from scripts.function_tracer_pcode.proof.concrete_counterexample import (
        ConcreteCounterexampleArtifact,
    )

    if type(artifact) is not ConcreteCounterexampleArtifact:
        raise TypeError(
            "the conditional lane accepts an exact ConcreteCounterexampleArtifact only: "
            f"{type(artifact).__name__}"
        )
    artifact.validate()
    return artifact


def concrete_discharged_causes(
    projection: VerifiedLifecycleProjection, *, artifact: Any
) -> frozenset:
    """具体実行の反例が引き受けた ``(occurrence_id, cause_id)``: 決定的な artifact のとき、
    同じ pair の SAT-safety の active cause だけ。"""

    artifact = validated_concrete_proof_artifact(artifact)
    if not artifact.decisive:
        return frozenset()
    return frozenset(
        (row.occurrence_id, row.cause_id)
        for row in projection.c_active_base
        if row.reason_id in CONCRETE_DISCHARGED_REASON_IDS
    )


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
#: 具体実行の artifact が名乗れる唯一の kind
_CONCRETE_PROOF_KIND_NAME = "CONDITIONAL_CONCRETE_COUNTEREXAMPLE"


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
    concrete_artifact: Any = None,
    concrete_reliance: Any = None,
) -> Any:
    """`issue_conditional_decision_with_scope` の receipt だけ（従来の呼び出し口）。"""

    return issue_conditional_decision_with_scope(
        unconditional_decision=unconditional_decision,
        projection=projection,
        artifact=artifact,
        result=result,
        concrete_artifact=concrete_artifact,
        concrete_reliance=concrete_reliance,
    ).receipt


def issue_conditional_decision_with_scope(
    *,
    unconditional_decision: DecisionReceipt,
    projection: VerifiedLifecycleProjection,
    artifact: Any,
    result: Any = None,
    concrete_artifact: Any = None,
    concrete_reliance: Any = None,
) -> Any:
    """proof artifact を conditional 列の ``ConditionalDecisionReceipt`` にする。

    返り値は receipt と、その導出に使った obligation scope の記録（Issue #325）の組
    （``ConditionalDecisionFinalization``）。``concrete_reliance`` は具体実行の反例が依存した
    事実の閉包（``core.fact_reliance.ReliesOn``。``None`` は全事実）。

    decisive でない artifact でも receipt は出す（conditional_outcome は
    ``UNKNOWN``）。無条件 receipt / projection / 結果には触れない。

    ``artifact`` は外部 callee の仮定の lane（Issue #20、``None`` 可）、
    ``concrete_artifact`` は具体実行の反例（Issue #18、``None`` 可）。決定的な artifact
    ごとに receipt を 1 つ作り、どの receipt も **決定的な artifact の仮定の和**に依存する
    （最小化しない。列の仮定の集合は 1 つ）。決定的なものが無ければ、外部 callee の lane の
    集合で ``UNKNOWN`` の receipt を作る（従来どおり）。
    """

    if not conditional_lane_is_eligible(unconditional_decision):
        raise ValueError("the conditional lane runs only after an unconditional UNKNOWN")
    decisive = []        # (proof kind, artifact digest, assumption set, discharged causes)
    base_set: Tuple[Any, ...] = ()
    if artifact is not None:
        artifact = validated_conditional_proof_artifact(artifact)
        base_set = tuple(getattr(artifact, "assumption_set", ()) or ())
        proof_kind_name = getattr(artifact, "proof_kind", None)
        if proof_kind_name is not None:
            proof_kind = _PROOF_KIND_BY_NAME.get(str(proof_kind_name))
            if proof_kind is None:
                raise ValueError(f"unknown conditional proof kind: {proof_kind_name}")
            if not base_set:
                raise ValueError("a conditional lane requires a non-empty assumption set")
            # 仮定が実際に引き受けた cause occurrence だけを落とす。対応を証明
            # できなければ 1 つも落とさず、残った blocker がそのまま効く。
            decisive.append((
                proof_kind,
                str(getattr(artifact, "artifact_digest", "")),
                base_set,
                conditional_discharged_causes(projection, result=result, artifact=artifact),
            ))
    if concrete_artifact is not None:
        concrete_artifact = validated_concrete_proof_artifact(concrete_artifact)
        if concrete_artifact.decisive:
            if concrete_artifact.proof_kind != _CONCRETE_PROOF_KIND_NAME:
                raise ValueError(f"unknown concrete proof kind: {concrete_artifact.proof_kind}")
            decisive.append((
                ConditionalDecisiveProofKind.CONDITIONAL_CONCRETE_COUNTEREXAMPLE,
                concrete_artifact.artifact_digest,
                tuple(concrete_artifact.assumption_set),
                concrete_discharged_causes(projection, artifact=concrete_artifact),
            ))
    if decisive:
        assumption_set = canonical_assumption_dependencies(
            premise for _kind, _digest, premises, _causes in decisive for premise in premises
        )
    else:
        assumption_set = base_set
    if not assumption_set:
        raise ValueError("a conditional lane requires a non-empty assumption set")

    receipts: Tuple[ConditionalDecisiveProofReceipt, ...] = ()
    lane_projection = projection
    if decisive:
        discharged = frozenset().union(*(causes for _kind, _digest, _premises, causes in decisive))
        lane_projection = conditional_lane_projection(
            projection, discharged_causes=discharged
        )
        receipts = tuple(
            ConditionalDecisiveProofReceipt.create(
                result_occurrence_id=lane_projection.result_occurrence_id,
                lifecycle_projection_digest=lane_projection.lifecycle_projection_digest,
                proof_kind=proof_kind,
                proof_artifact_digest=digest,
                # dependency minimization はしない。列の集合そのもの。
                assumption_dependencies=assumption_set,
            )
            for proof_kind, digest, _premises, _causes in decisive
        )
    authority = ConditionalFinalizationAuthority(
        lane_projection.result_occurrence_id,
        unconditional_decision,
        lane_projection,
        assumption_set,
        conditional_decisive_proof_receipts=receipts,
        concrete_reliance=concrete_reliance,
    )
    return finalize_conditional_decision_with_scope(authority)


class _PostDecisionConsumer:
    """authority 確定後の consumer の台帳 identity（どの pair の台帳とも一致しない）。"""

    __slots__ = ("label",)

    def __init__(self, label: str) -> None:
        self.label = label

    def __repr__(self) -> str:  # pragma: no cover - debug 表示
        return f"PostDecisionConsumer({self.label})"


@contextmanager
def post_decision_failure_scope(label: str = "conditional_lane") -> Iterator[Any]:
    """authority 確定 **後** の計算を、pair の台帳から切り離して走らせる scope。

    Issue #22 PR-22-D: 判定と receipt は既に確定している。その後の計算（conditional
    lane の proof）で上がった限界・内部バグは pair の台帳へ入れてはいけない — 入れて
    も判定は変えられず、「pair を止めた failure が結果に出ていない」状態だけが残る。
    既存の `pair_failure_scope` に **どの pair とも一致しない identity** を渡すと
    新しい台帳が積まれるので、scope の中の `raise_limitation` / `record_internal_bug`
    はその台帳へ記録され、抜けると捨てられる。consumer はその台帳を読んで、自分の
    結果だけを fail closed にする（途中で例外が握り潰されても記録は残る）。

    `PairExecutionControl` には何も足さない（pair lifecycle の owner は PR-106-0 の
    台帳、deadline の finalization は PR-106-A の `Deadline`）。
    """

    from scripts.function_tracer_pcode.core.errors import pair_failure_scope

    with pair_failure_scope(_PostDecisionConsumer(label), None) as ledger:
        yield ledger


def _stopped_lane_diagnostic(exc: BaseException, *, swallowed: bool) -> Mapping[str, Any]:
    """lane を止めた failure の診断（限界なら reason、内部バグなら元の例外型）。"""

    reason_id = getattr(exc, "reason_id", None)
    return {
        "conditional_lane": (
            "stopped_by_limitation" if reason_id is not None else "stopped_by_internal_error"
        ),
        "reason_id": reason_id if reason_id is not None else getattr(
            exc, "exception_type", type(exc).__name__
        ),
        "site": getattr(exc, "site", None),
        "swallowed": swallowed,
    }


def _concrete_lane_budget(budget_seconds: float) -> Optional[float]:
    """具体実行に使ってよい秒数: 設定の予算と pair の解析期限の残りの小さい方。

    解析期限が無い（runner の ``ANALYSIS_TIMEOUT=0``、CLI で ``--analysis-timeout`` を
    渡さない）なら ``None``: 具体実行は期限の中でだけ走る。期限の外で走ると、確定済みの
    判定の後に process の期限（supervisor の TIMEOUT）へ近づく時間を足すことになる。
    """

    from scripts.function_tracer_pcode.core.deadline import active_deadline

    deadline = active_deadline()
    if deadline is None:
        return None
    return min(float(budget_seconds), deadline.remaining_seconds())


def return_width_parity_inputs(projection: Any, result: Any) -> Mapping[str, Any]:
    """The SMT_PARITY inputs of the concrete observation (Issue #327), plain data.

    * ``return_width_domain_active``: whether the final projection has an active
      cause of the return-width / ABI-width domain (its sealed reason registry);
    * ``completed``: per completed unary return-width proof on the result, the
      side (``function1`` / ``function2``; a record naming no side is dropped),
      the entry offset of the function it proved, the return members it covers
      (the source indices of its return-member target), its payload width, and
      whether it is **applicable** to the final analysis (the result's
      completion-applicability contexts validated it against the live snapshot:
      a proof made on an earlier phase's analysis is not applicable).

    The checker's adapter turns them into a per-side evidence level: complete only
    when every return member of the final analysis is covered by an applicable
    proof (``checker.concrete_replay.smt_parity_of_side``).  They are an evidence
    level of an assumed observation element, never verification.
    """

    import json

    from scripts.function_tracer_pcode.authority.domains.abi_width_readonly import (
        ABI_WIDTH_READONLY_REASON_REGISTRY,
    )
    from scripts.function_tracer_pcode.proof.obligations.return_width import (
        UNARY_RETURN_WIDTH_PROOF_KIND,
    )

    def key(requirement: Any) -> str:
        return json.dumps(requirement, sort_keys=True, separators=(",", ":"), default=repr)

    width_reasons = {definition.reason_id for definition in ABI_WIDTH_READONLY_REASON_REGISTRY.snapshot()}
    active = any(row.reason_id in width_reasons for row in getattr(projection, "c_active_base", ()) or ())
    applicable = {
        key(context.get("proof_requirement_id"))
        for context in getattr(result, "reason_completion_applicability_contexts", ()) or ()
        if isinstance(context, Mapping) and context.get("artifact_is_valid") is True
        and isinstance(context.get("proof_requirement_id"), Mapping)
    }
    completed = []
    for item in getattr(result, "completed_recovery_proof_evidence", ()) or ():
        if not isinstance(item, Mapping) or item.get("side") not in ("function1", "function2"):
            continue
        evidence = item.get("evidence")
        if not isinstance(evidence, Mapping):
            continue
        requirement = evidence.get("proof_requirement_id")
        if not isinstance(requirement, Mapping) or requirement.get("proof_kind") != UNARY_RETURN_WIDTH_PROOF_KIND:
            continue
        entry, members = _return_width_target(requirement.get("proof_target_key"))
        facts = evidence.get("width_facts")
        payload = facts.get("semantic_payload_width") if isinstance(facts, Mapping) else None
        completed.append({
            "side": item["side"],
            "entry": entry,
            "members": members,
            "payload_bits": payload if type(payload) is int else None,
            "applicable": key(requirement) in applicable,
        })
    return {"return_width_domain_active": active, "completed": tuple(completed)}


def _return_width_target(target: Any) -> Tuple[Optional[int], Tuple[int, ...]]:
    """``(entry offset, return-member source indices)`` of a unary return-width
    proof target (``proof.return_width.surface.build_function_return_width_target``
    as serialized); ``(None, ())`` when its shape is not the known one."""
    try:
        if target[0] != "function_return_width_target":
            return None, ()
        function = target[2]
        entry = function[2][2] if function[0] == "function_identity_v1" else None
        member = target[3]
        indices = ()
        if member[0] == "return_member_v1":
            for part in member[1:]:
                if isinstance(part, (list, tuple)) and len(part) == 2 and part[0] == "source_indices":
                    indices = tuple(i for i in part[1] if type(i) is int)
        return (entry if type(entry) is int else None), indices
    except (IndexError, KeyError, TypeError):
        return None, ()


def _run_concrete_proof(
    result: Any, analyses: Tuple[Any, Any], concrete_subjects: Any, options: Any, projection: Any = None,
) -> Any:
    """solver の witness を両 binary で再生した proof artifact（Issue #18 C2）と、その artifact が
    依存した事実の閉包（Issue #325。subject の fact handle の閉包）の組。"""

    from scripts.function_tracer_pcode.proof.concrete_counterexample import (
        CONCRETE_BUDGET_EXHAUSTED,
        CONCRETE_NO_DEADLINE,
        ConcreteCounterexampleArtifact,
        run_concrete_counterexample_proof,
        solver_witnesses,
        subject_reliance,
    )

    witnesses = solver_witnesses(result)
    budget = _concrete_lane_budget(getattr(options, "budget_seconds", 0.0))
    if witnesses and budget is None:
        return ConcreteCounterexampleArtifact._create(
            witness_count=len(witnesses), non_decisive_reasons=(CONCRETE_NO_DEADLINE,)
        ), subject_reliance(None)
    if witnesses and budget <= 0:
        return ConcreteCounterexampleArtifact._create(
            witness_count=len(witnesses), non_decisive_reasons=(CONCRETE_BUDGET_EXHAUSTED,)
        ), subject_reliance(None)
    subjects = (
        concrete_subjects(*analyses, observation_inputs=return_width_parity_inputs(projection, result))
        if witnesses else None
    )
    # Issue #325: the proof reads the analyses only through the subjects' fact
    # handles; what it relied on is their closure.
    return run_concrete_counterexample_proof(
        witnesses, subjects,
        budget_seconds=budget, step_limit=int(getattr(options, "step_limit", 0)),
    ), subject_reliance(subjects)


def _concrete_diagnostic(artifact: Any) -> Mapping[str, Any]:
    """結果に残す具体実行の記録（receipt が digest を bind する artifact の内容そのもの）。"""

    record = dict(artifact.to_json())
    record["diagnostics"] = dict(artifact.diagnostics)
    return record


def run_production_conditional_lane(
    result: Any,
    *,
    projection: VerifiedLifecycleProjection,
    analyses: Optional[Tuple[Any, Any]],
    observation_policy: Any,
    solver_runner: Any,
    timeout: Optional[float] = None,
    debug: bool = False,
    input_correspondence_factory: Optional[Any] = None,
    concrete_subjects: Optional[Any] = None,
    concrete_options: Any = None,
) -> Optional[Mapping[str, Any]]:
    """production の conditional lane。``result`` の conditional 列だけを触る。

    conditional 列を付けたときはその診断を返し、起動しなかった / 付けなかった
    ときは ``None`` を返す。例外は投げない（無条件の判定を絶対に壊さない）。

    ``concrete_subjects(analysis1, analysis2)`` と ``concrete_options`` があれば（CLI が
    具体実行を有効にした checker）、solver の witness の具体実行（Issue #18 C2）も行い、
    その記録を診断の ``concrete_replay`` に残す。差を確定したら conditional 列の
    ``CONDITIONAL_CONCRETE_COUNTEREXAMPLE`` になる。
    """

    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        attach_conditional_decision,
    )
    from scripts.function_tracer_pcode.core.errors import AnalysisLimitation
    from scripts.function_tracer_pcode.proof.conditional_lane import (
        run_conditional_proof,
    )

    decision = getattr(result, "decision_receipt", None)
    if not conditional_lane_is_eligible(decision):
        return None
    if analyses is None or input_correspondence_factory is None:
        # base pair か、その最終 relation（Issue #167）が結び付いていない（fail closed）。
        return None
    analysis1, analysis2 = analyses
    concrete_enabled = concrete_subjects is not None and concrete_options is not None

    try:
        with post_decision_failure_scope() as lane_ledger:
            artifact = run_conditional_proof(
                analysis1,
                analysis2,
                input_correspondence=input_correspondence_factory(),
                observation_policy=observation_policy,
                solver_runner=solver_runner,
                timeout=timeout,
                debug=debug,
            )
            concrete, concrete_reliance = (
                _run_concrete_proof(result, (analysis1, analysis2), concrete_subjects, concrete_options, projection)
                if concrete_enabled else (None, None)
            )
            stopped = lane_ledger.pending_failure()
        if stopped is not None:
            # 計算の途中で限界 / 内部バグが記録され、どこかで握り潰された。結果は
            # 不完全なので conditional 列を作らない（fail closed。判定は確定済み）。
            return _stopped_lane_diagnostic(stopped.exception, swallowed=True)
        extra = {} if concrete is None else {"concrete_replay": _concrete_diagnostic(concrete)}
        if concrete is not None and concrete.decisive:
            extra["concrete_proof_kind"] = concrete.proof_kind
        concrete_decisive = concrete is not None and concrete.decisive
        if concrete_decisive and assumption_set_receipt_bound_violation(tuple(concrete.assumption_set)):
            concrete_decisive = False
        external_decisive = bool(artifact.assumption_set) and artifact.decisive
        if not artifact.assumption_set and not concrete_decisive:
            # view が立たなかった。conditional 列は作らない（fail closed）。
            return {
                "conditional_lane": "not_constructed",
                "non_decisive_reasons": list(artifact.non_decisive_reasons),
                "diagnostics": dict(artifact.diagnostics),
                **extra,
            }
        if not external_decisive and not concrete_decisive:
            # 何も証明できていない。conditional 列は「出たときだけ出す」ので、
            # 起動した事実と非決定理由は診断にだけ残す。
            return {
                "conditional_lane": "non_decisive",
                "non_decisive_reasons": list(artifact.non_decisive_reasons),
                "assumption_count": len(artifact.assumption_set),
                "diagnostics": dict(artifact.diagnostics),
                **extra,
            }
        over_bound = (
            assumption_set_receipt_bound_violation(tuple(artifact.assumption_set))
            if external_decisive else None
        )
        if over_bound is not None and not concrete_decisive:
            # receipt の契約（仮定の数と大きさ）に収まらない: receipt を作らない（fail closed。
            # 確定済みの判定・exit code は不変。出力の契約違反の ERROR にしない）
            return {
                "conditional_lane": "over_receipt_bound",
                "detail": over_bound,
                "assumption_count": len(artifact.assumption_set),
                "non_decisive_reasons": list(artifact.non_decisive_reasons),
                "diagnostics": dict(artifact.diagnostics),
                **extra,
            }
        external = artifact if external_decisive and over_bound is None else None
        finalization = issue_conditional_decision_with_scope(
            unconditional_decision=decision,
            projection=projection,
            artifact=external,
            result=result,
            concrete_artifact=concrete if concrete_decisive else None,
            concrete_reliance=concrete_reliance if concrete_decisive else None,
        )
        receipt = finalization.receipt
        attach_conditional_decision(result, receipt, finalization.obligation_scope)
    except AnalysisLimitation as exc:
        # Issue #22 PR-22-D: lane は authority 確定の **後** に走る非 authoritative
        # な consumer。そこで上がった限界（式サイズ予算など）は lane 自身の台帳に
        # 閉じ（pair の台帳・判定・receipt は変わらない）、lane の結果だけを作らない。
        return _stopped_lane_diagnostic(exc, swallowed=False)
    except Exception as exc:  # noqa: BLE001
        # conditional 列は付けない。無条件の判定・reason・exit code は不変。
        return {
            "conditional_lane": "failed",
            "error": f"{type(exc).__name__}: {exc}",
        }
    discharged = 0
    if external is not None:
        discharged += len(conditional_discharged_causes(projection, result=result, artifact=external))
    if concrete_decisive:
        discharged += len(concrete_discharged_causes(projection, artifact=concrete))
    return {
        "conditional_lane": "issued",
        "conditional_outcome": receipt.conditional_outcome.value,
        "proof_kind": artifact.proof_kind if external is not None else None,
        "assumption_count": len(receipt.assumption_set),
        "discharged_cause_count": discharged,
        "non_decisive_reasons": list(artifact.non_decisive_reasons),
        "diagnostics": dict(artifact.diagnostics),
        **extra,
    }

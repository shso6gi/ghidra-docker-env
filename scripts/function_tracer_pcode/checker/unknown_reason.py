# -*- coding: utf-8 -*-
"""Typed UNKNOWN reason schema and registry."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

# Phase 7-1b-1 (#97): pure な定義層は proof.unknown_reason へ移動した。以下は (a) 本 module の実装が使う名前と
# (b) 旧 path `checker.unknown_reason` からの互換 import のための再輸出（同一 object。再定義しない）。
from scripts.function_tracer_pcode.core.json_encoding import (
    EVIDENCE,
    INT,
    TEXT,
    Column,
    as_dict,
    as_list,
    each,
    materialize,
    Reducer,
    row_items,
    source_converter,
)
from scripts.function_tracer_pcode.proof.unknown_reason import (  # noqa: F401
    UNKNOWN_TUPLE_MISSING,
    UnknownAggregationUnit,
    UnknownCountKind,
    UnknownDecisionEffect,
    UnknownReasonClass,
    UnknownReasonDefinition,
    UnknownReasonId,
    UnknownReasonScope,
    UnknownRecoveryActionStatus,
    UnknownRecoveryPlan,
    UnknownRecoveryProofKind,
    UnknownRecoveryProofObligation,
    _UNKNOWN_REASON_REGISTRY,
    _UNKNOWN_RECOVERY_PLAN_REGISTRY,
    _coerce_evidence_refs,
    _coerce_optional_tuple,
    _enum_value,
    _registered_recovery_proof_kind_values,
    build_proof_obligation_id,
    coerce_unknown_recovery_proof_obligation,
    coerce_unknown_recovery_proof_obligations,
    format_projection_detail,
    get_unknown_reason_definition,
    get_unknown_recovery_plan,
    normalize_recovery_proof_kind,
    normalize_unknown_reason_id,
    register_unknown_reason,
    register_unknown_recovery_plan,
)


# ---------------------------------------------------------------------------
# 行の schema（Issue #22 PR-22-D）
# ---------------------------------------------------------------------------
#
# reason / recovery action の行は **列ごとの上限** を型で持つ（`core/json_encoding.Column`）。
# 出力では語彙の列・自由文の列は文字数まで（超えた分は marker）、key / evidence の列は
# 有界な証拠（大きければ identity + 要約）になる。行の上限（`row_max_bytes`）は出力
# schema の headroom の根拠（`checker/output_schema.py`）。`to_dict()` は旧来の構造。

#: 登録語彙（reason class / scope / status など）の列の上限
VOCAB_MAX_CHARS = 64
#: 登録 id（reason id / target regression）の列の上限
ID_MAX_CHARS = 128
#: 短い自由文（stage / case / evidence kind / recovery action）の列の上限
LABEL_MAX_CHARS = 256
#: 自由文（detail）の列の上限
DETAIL_MAX_CHARS = 1024


#: `typed_cause_key` の列でそのまま置く大きさ（canonical reason の固定の形が必ず収まる）
TYPED_CAUSE_KEY_INLINE_BYTES = 4096


@source_converter
def _optional_dict(value: Any) -> Any:
    return as_dict(value) if value else None


@source_converter
def _dict_items(values: Any) -> Any:
    # 有界化した後の列は mapping のほかに `BoundedEvidence`（大きい要素）と件数の marker（文字列）
    # を持つ。mapping だけを旧 `to_dict` と同じく dict にし、それ以外はそのまま置く
    return each(values, _dict_item)


@source_converter
def _dict_item(value: Any) -> Any:
    return as_dict(value) if isinstance(value, Mapping) else value


UNKNOWN_RECOVERY_ACTION_ROW = (
    Column("count_kind", TEXT, VOCAB_MAX_CHARS),
    Column("reason_id", TEXT, ID_MAX_CHARS),
    Column("decision_effect", TEXT, VOCAB_MAX_CHARS),
    Column("reason_scope", TEXT, VOCAB_MAX_CHARS),
    Column("proof_kind", TEXT, VOCAB_MAX_CHARS),
    Column("proof_stage", TEXT, LABEL_MAX_CHARS),
    Column("status", TEXT, VOCAB_MAX_CHARS),
    Column("aggregation_unit", TEXT, VOCAB_MAX_CHARS),
    Column("stage", TEXT, LABEL_MAX_CHARS),
    Column("pair_or_case", TEXT, LABEL_MAX_CHARS),
    Column("required_evidence", EVIDENCE, legacy=as_list),
    Column("evidence_refs", EVIDENCE, legacy=as_list),
    Column("evidence_kind", TEXT, LABEL_MAX_CHARS),
    Column("object_target_key", EVIDENCE),
    Column("proof_obligation_id", EVIDENCE),
    Column("recovery_action", TEXT, LABEL_MAX_CHARS),
    Column("target_regression", TEXT, ID_MAX_CHARS),
    Column("detail", TEXT, DETAIL_MAX_CHARS),
    Column("object_evidence", EVIDENCE, omit_none=True),
)

UNKNOWN_REASON_ROW = (
    Column("count_kind", TEXT, VOCAB_MAX_CHARS),
    Column("reason_id", TEXT, ID_MAX_CHARS),
    Column("reason_class", TEXT, VOCAB_MAX_CHARS),
    Column("decision_effect", TEXT, VOCAB_MAX_CHARS),
    Column("reason_scope", TEXT, VOCAB_MAX_CHARS),
    Column("aggregation_unit", TEXT, VOCAB_MAX_CHARS),
    Column("stage", TEXT, LABEL_MAX_CHARS),
    Column("pair_or_case", TEXT, LABEL_MAX_CHARS),
    Column("evidence_refs", EVIDENCE, legacy=as_list),
    Column("recovery_proof_kind", TEXT, VOCAB_MAX_CHARS),
    Column("recovery_proof_obligations", EVIDENCE, legacy=each),
    Column("proof_stage", TEXT, LABEL_MAX_CHARS),
    Column("evidence_kind", TEXT, LABEL_MAX_CHARS),
    Column("object_target_key", EVIDENCE),
    Column("proof_obligation_id", EVIDENCE),
    # canonical reason の typed_cause_key は固定の形（digest 16 個）で、要約せずに置く
    Column("typed_cause_key", EVIDENCE, legacy=_optional_dict, inline_bytes=TYPED_CAUSE_KEY_INLINE_BYTES),
    Column("proof_requirement_ids", EVIDENCE, legacy=_dict_items),
    Column("recovery_action", TEXT, LABEL_MAX_CHARS),
    Column("action_status", TEXT, VOCAB_MAX_CHARS),
    Column("target_regression", TEXT, ID_MAX_CHARS),
    Column("detail", TEXT, DETAIL_MAX_CHARS),
    Column("object_evidence", EVIDENCE, omit_none=True),
)


def _evidence_identity(record: Any) -> Any:
    """大きい証拠を要約するときの identity。authority の projection なら cause id。"""

    typed_cause_key = getattr(record, "typed_cause_key", None)
    if isinstance(typed_cause_key, Mapping):
        cause_id = typed_cause_key.get("cause_id")
        if isinstance(cause_id, str) and cause_id:
            return "cause:" + cause_id
    return None


@dataclass(frozen=True)
class UnknownRecoveryAction:
    count_kind: str
    reason_id: str
    decision_effect: str
    reason_scope: str
    proof_kind: str
    proof_stage: str
    status: str
    aggregation_unit: str
    stage: Optional[str] = None
    pair_or_case: Optional[str] = None
    required_evidence: Tuple[str, ...] = ()
    evidence_refs: Tuple[str, ...] = ()
    evidence_kind: Optional[str] = None
    object_target_key: Optional[Tuple[Any, ...]] = None
    object_evidence: Optional[Any] = None
    proof_obligation_id: Optional[Tuple[Any, ...]] = None
    recovery_action: Optional[str] = None
    target_regression: Optional[str] = None
    detail: Optional[str] = None

    def json_items(self):
        return row_items(UNKNOWN_RECOVERY_ACTION_ROW, self, identity=_evidence_identity(self))

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "UnknownRecoveryAction":
        raw_reason_id = _enum_value(payload.get("reason_id"))
        reason_id = normalize_unknown_reason_id(raw_reason_id)
        if reason_id == UnknownReasonId.UNKNOWN.value and raw_reason_id:
            try:
                from scripts.function_tracer_pcode.authority.process.supervisor import (
                    PROCESS_DURABLE_REASON_REGISTRY,
                )

                PROCESS_DURABLE_REASON_REGISTRY.get(raw_reason_id)
            except KeyError:
                pass
            else:
                # Exact v2 compatibility diagnostics are reader-supported
                # without registering them as legacy decision reasons.  Keep
                # their identity and the already serialized typed fields.
                reason_id = raw_reason_id
        definition = get_unknown_reason_definition(reason_id)
        use_definition_defaults = (
            reason_id != UnknownReasonId.UNKNOWN.value
            and reason_id in _UNKNOWN_REASON_REGISTRY
        )
        return cls(
            count_kind=_enum_value(payload.get("count_kind")) or UnknownCountKind.PROOF_ACTION.value,
            reason_id=reason_id,
            decision_effect=str(
                payload.get("decision_effect")
                or (
                    definition.decision_effect
                    if use_definition_defaults
                    else UnknownDecisionEffect.DIAGNOSTIC_ONLY.value
                )
            ),
            reason_scope=str(
                payload.get("reason_scope")
                or (
                    definition.reason_scope
                    if use_definition_defaults
                    else UnknownReasonScope.GLOBAL.value
                )
            ),
            proof_kind=normalize_recovery_proof_kind(payload.get("proof_kind")) or UnknownRecoveryProofKind.NONE.value,
            proof_stage=str(payload.get("proof_stage") or "unspecified"),
            status=str(payload.get("status") or UnknownRecoveryActionStatus.PLANNED.value),
            aggregation_unit=str(
                payload.get("aggregation_unit")
                or (
                    definition.aggregation_unit
                    if use_definition_defaults
                    else UnknownAggregationUnit.RESULT.value
                )
            ),
            stage=payload.get("stage"),
            pair_or_case=payload.get("pair_or_case"),
            required_evidence=_coerce_evidence_refs(payload.get("required_evidence") or ()),
            evidence_refs=_coerce_evidence_refs(payload.get("evidence_refs") or ()),
            evidence_kind=payload.get("evidence_kind"),
            object_target_key=_coerce_optional_tuple(payload.get("object_target_key")),
            object_evidence=payload.get("object_evidence"),
            proof_obligation_id=_coerce_optional_tuple(payload.get("proof_obligation_id")),
            recovery_action=payload.get("recovery_action"),
            target_regression=(
                payload.get("target_regression")
                if payload.get("target_regression") is not None
                else definition.target_regression if use_definition_defaults else None
            ),
            detail=payload.get("detail"),
        )


@dataclass(frozen=True)
class UnknownReasonRecord:
    count_kind: str
    reason_id: str
    reason_class: str
    decision_effect: str
    reason_scope: str
    aggregation_unit: str
    stage: Optional[str] = None
    pair_or_case: Optional[str] = None
    evidence_refs: Tuple[str, ...] = ()
    recovery_proof_kind: str = UnknownRecoveryProofKind.NONE.value
    recovery_proof_obligations: Tuple[UnknownRecoveryProofObligation, ...] = ()
    proof_stage: Optional[str] = None
    evidence_kind: Optional[str] = None
    object_target_key: Optional[Tuple[Any, ...]] = None
    object_evidence: Optional[Any] = None
    proof_obligation_id: Optional[Tuple[Any, ...]] = None
    typed_cause_key: Optional[Mapping[str, Any]] = None
    proof_requirement_ids: Tuple[Mapping[str, Any], ...] = ()
    recovery_action: Optional[str] = None
    action_status: Optional[str] = None
    target_regression: Optional[str] = None
    detail: Optional[str] = None

    def json_items(self):
        return row_items(UNKNOWN_REASON_ROW, self, identity=_evidence_identity(self))

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "UnknownReasonRecord":
        constructor = make_unknown_reason
        raw_reason_id = _enum_value(payload.get("reason_id"))
        if raw_reason_id not in _UNKNOWN_REASON_REGISTRY:
            try:
                from scripts.function_tracer_pcode.authority.process.supervisor import (
                    PROCESS_DURABLE_REASON_REGISTRY,
                )

                PROCESS_DURABLE_REASON_REGISTRY.get(raw_reason_id)
            except KeyError:
                pass
            else:
                constructor = make_internal_v2_reason_diagnostic
        return constructor(
            payload.get("reason_id"),
            count_kind=payload.get("count_kind"),
            reason_class=payload.get("reason_class"),
            decision_effect=payload.get("decision_effect"),
            reason_scope=payload.get("reason_scope"),
            aggregation_unit=payload.get("aggregation_unit"),
            stage=payload.get("stage"),
            pair_or_case=payload.get("pair_or_case"),
            evidence_refs=payload.get("evidence_refs") or (),
            recovery_proof_kind=payload.get("recovery_proof_kind"),
            recovery_proof_obligations=payload.get("recovery_proof_obligations"),
            proof_stage=payload.get("proof_stage"),
            evidence_kind=payload.get("evidence_kind"),
            object_target_key=payload.get("object_target_key"),
            object_evidence=payload.get("object_evidence"),
            proof_obligation_id=payload.get("proof_obligation_id"),
            typed_cause_key=payload.get("typed_cause_key"),
            proof_requirement_ids=payload.get("proof_requirement_ids") or (),
            recovery_action=payload.get("recovery_action"),
            action_status=payload.get("action_status"),
            target_regression=payload.get("target_regression"),
            detail=payload.get("detail"),
        )


def make_unknown_reason(
    reason_id: Any,
    *,
    count_kind: Any = None,
    reason_class: Any = None,
    decision_effect: Any = None,
    reason_scope: Any = None,
    aggregation_unit: Any = None,
    stage: Optional[str] = None,
    pair_or_case: Optional[str] = None,
    evidence_refs: Optional[Sequence[Any]] = None,
    recovery_proof_kind: Any = None,
    recovery_proof_obligations: Optional[Sequence[Any]] = None,
    proof_stage: Optional[str] = None,
    evidence_kind: Optional[str] = None,
    object_target_key: Any = None,
    object_evidence: Any = None,
    proof_obligation_id: Any = None,
    typed_cause_key: Optional[Mapping[str, Any]] = None,
    proof_requirement_ids: Optional[Sequence[Mapping[str, Any]]] = None,
    recovery_action: Optional[str] = None,
    action_status: Any = None,
    target_regression: Optional[str] = None,
    detail: Optional[str] = None,
) -> UnknownReasonRecord:
    original_reason_id = _enum_value(reason_id)
    original_recovery_proof_kind = _enum_value(recovery_proof_kind)
    definition = get_unknown_reason_definition(reason_id)
    coerced_evidence_refs = _coerce_evidence_refs(evidence_refs)
    if (
        definition.reason_id == UnknownReasonId.UNKNOWN.value
        and original_reason_id
        and original_reason_id != UnknownReasonId.UNKNOWN.value
    ):
        coerced_evidence_refs = (original_reason_id,) + coerced_evidence_refs
        if detail is None:
            detail = original_reason_id
    normalized_recovery_proof_kind = normalize_recovery_proof_kind(recovery_proof_kind)
    if (
        original_recovery_proof_kind is not None
        and normalized_recovery_proof_kind == UnknownRecoveryProofKind.NONE.value
        and original_recovery_proof_kind not in _registered_recovery_proof_kind_values()
    ):
        coerced_evidence_refs = (f"invalid_recovery_proof_kind:{original_recovery_proof_kind}",) + coerced_evidence_refs
        if detail is None:
            detail = f"invalid recovery_proof_kind: {original_recovery_proof_kind}"
    if recovery_proof_obligations is None:
        coerced_recovery_obligations = get_unknown_recovery_plan(definition.reason_id).proof_obligations
    else:
        coerced_recovery_obligations = coerce_unknown_recovery_proof_obligations(
            recovery_proof_obligations
        )
    normalized_proof_kind = normalized_recovery_proof_kind or definition.recovery_proof_kind
    coerced_object_target_key = _coerce_optional_tuple(object_target_key)
    normalized_action_status = _enum_value(action_status)
    if normalized_action_status is not None:
        normalized_action_status = str(normalized_action_status)
    resolved_proof_stage = proof_stage
    if resolved_proof_stage is None and len(coerced_recovery_obligations) == 1:
        resolved_proof_stage = coerced_recovery_obligations[0].proof_stage
    resolved_evidence_kind = str(evidence_kind) if evidence_kind is not None else None
    coerced_proof_obligation_id = _coerce_optional_tuple(proof_obligation_id)
    if (
        coerced_proof_obligation_id is None
        and resolved_proof_stage is not None
        and resolved_evidence_kind is not None
        and coerced_object_target_key is not None
        and normalized_proof_kind != UnknownRecoveryProofKind.NONE.value
    ):
        coerced_proof_obligation_id = build_proof_obligation_id(
            definition.reason_id,
            resolved_proof_stage,
            normalized_proof_kind,
            resolved_evidence_kind,
            coerced_object_target_key,
        )
    return UnknownReasonRecord(
        count_kind=_enum_value(count_kind) or UnknownCountKind.REASON_RECORD.value,
        reason_id=definition.reason_id,
        reason_class=_enum_value(reason_class) or definition.reason_class,
        decision_effect=_enum_value(decision_effect) or definition.decision_effect,
        reason_scope=_enum_value(reason_scope) or definition.reason_scope,
        aggregation_unit=_enum_value(aggregation_unit) or definition.aggregation_unit,
        stage=stage,
        pair_or_case=pair_or_case,
        evidence_refs=coerced_evidence_refs,
        recovery_proof_kind=normalized_proof_kind,
        recovery_proof_obligations=coerced_recovery_obligations,
        proof_stage=resolved_proof_stage,
        evidence_kind=resolved_evidence_kind,
        object_target_key=coerced_object_target_key,
        object_evidence=object_evidence,
        proof_obligation_id=coerced_proof_obligation_id,
        typed_cause_key=dict(typed_cause_key) if typed_cause_key else None,
        proof_requirement_ids=tuple(dict(item) for item in (proof_requirement_ids or ())),
        recovery_action=recovery_action,
        action_status=normalized_action_status,
        target_regression=target_regression if target_regression is not None else definition.target_regression,
        detail=detail,
    )


def make_internal_v2_reason_diagnostic(
    reason_id: Any,
    **kwargs: Any,
) -> UnknownReasonRecord:
    """Build an internal legacy diagnostic from one exact sealed v2 reason.

    This value may support the pre-Phase-8 legacy decision path, but it is not a
    typed result projection and must never be serialized as canonical v2
    compatibility authority.
    """
    from scripts.function_tracer_pcode.authority.sites.activation import RETIRED_UMBRELLA_REASON_IDS
    from scripts.function_tracer_pcode.authority.process.supervisor import (
        PROCESS_DURABLE_REASON_REGISTRY,
    )

    exact_reason_id = _enum_value(reason_id)
    if exact_reason_id in RETIRED_UMBRELLA_REASON_IDS:
        raise ValueError("retired UNKNOWN umbrella is reader-only")
    definition = PROCESS_DURABLE_REASON_REGISTRY.get(exact_reason_id)
    class_map = {
        "proof_obligation": UnknownReasonClass.PROOF_OBLIGATION.value,
        "unsupported_semantics": UnknownReasonClass.OPERATIONAL_GAP.value,
        "semantic_safety_gate": UnknownReasonClass.UNSAFE_ANALYSIS.value,
        "semantic_partition_blocker": UnknownReasonClass.PROOF_OBLIGATION.value,
    }
    projected_reason_class = class_map.get(
        definition.reason_class, UnknownReasonClass.PROOF_OBLIGATION.value
    )
    provided_reason_class = _enum_value(kwargs.pop("reason_class", None))
    provided_decision_effect = _enum_value(kwargs.pop("decision_effect", None))
    provided_target_regression = kwargs.pop("target_regression", None)
    if provided_reason_class not in {None, projected_reason_class}:
        raise ValueError("typed compatibility reason class differs from v2 registry")
    if provided_decision_effect not in {None, definition.decision_effect}:
        raise ValueError("typed compatibility decision effect differs from v2 registry")
    if provided_target_regression not in {None, definition.reason_id}:
        raise ValueError("typed compatibility target differs from exact v2 reason")
    provided_proof_obligation_id = _coerce_optional_tuple(
        kwargs.get("proof_obligation_id")
    )
    projected = make_unknown_reason(
        UnknownReasonId.UNRESOLVED_VALUE_EXPRESSION,
        reason_class=projected_reason_class,
        decision_effect=definition.decision_effect,
        reason_scope=kwargs.pop("reason_scope", UnknownReasonScope.QUERY.value),
        aggregation_unit=kwargs.pop(
            "aggregation_unit", UnknownAggregationUnit.PAIR.value
        ),
        **kwargs,
    )
    exact_proof_obligation_id = projected.proof_obligation_id
    if (
        projected.proof_stage is not None
        and projected.evidence_kind is not None
        and projected.object_target_key is not None
        and projected.recovery_proof_kind != UnknownRecoveryProofKind.NONE.value
    ):
        exact_proof_obligation_id = build_proof_obligation_id(
            definition.reason_id,
            projected.proof_stage,
            projected.recovery_proof_kind,
            projected.evidence_kind,
            projected.object_target_key,
        )
        if (
            provided_proof_obligation_id is not None
            and provided_proof_obligation_id != exact_proof_obligation_id
        ):
            raise ValueError("typed compatibility proof ID differs from exact v2 reason")
    diagnostic_cause_key = dict(projected.typed_cause_key or {})
    diagnostic_cause_key["authority_class"] = "LEGACY_DIAGNOSTIC"
    return replace(
        projected,
        reason_id=definition.reason_id,
        reason_class=projected_reason_class,
        decision_effect=definition.decision_effect,
        proof_obligation_id=exact_proof_obligation_id,
        typed_cause_key=diagnostic_cause_key,
        target_regression=definition.reason_id,
    )


# ---------------------------------------------------------------------------
# 有界化（Issue #22 PR-22-D, B5）
# ---------------------------------------------------------------------------
#
# legacy reason / recovery action（A）の重い field は、authority 確定 **前**（G4-b）に
# 有界な表現へ置き換える。以後 authority の finish（projection の診断・legacy の照合）
# と出力は、置き換えた record しか読まない — 巨大な key を authority 後に辿り直さない。
#
# 有界化そのものも有界: 辿る作業（大きさの確認・fingerprint・長い文字列の hash）はすべて
# 呼ぶ側が渡す `work`（`JsonBudget`）へ数える。`work` を使い切ったら、それ以後の証拠は値を
# 辿らずに fingerprint の無い要約になる（legacy の重い field は診断にしか使われない）。
#
# * key / evidence（`object_target_key` / `object_evidence` / `proof_obligation_id` /
#   `typed_cause_key`）: `core/json_encoding.bounded_evidence`（小さければそのまま、大きければ
#   `BoundedEvidence` = 照合用の fingerprint + 種類）。
# * 列（`evidence_refs` / `required_evidence` / `proof_requirement_ids`）: 先頭の
#   `EVIDENCE_REFS_MAX_COUNT` 個まで（残りは件数の marker 1 つ）。1 つずつ有界にする。
# * 自由文（`detail` / `stage` / `pair_or_case`）: 行 schema の文字数まで（超えた分は明示の marker）。


#: 証拠の参照（evidence ref）1 つの文字数と、有界化した record が持つ参照の数。
#: 数は **引き出す要素の上限**（1M 要素の列を辿らない）で、出力の大きさはこの値に依らない
#: （列は `EVIDENCE` の規則: inline の上限を超えれば有界な要約）。固定の EqBench subset の
#: 観測の最大は evidence_refs 21 / proof_requirement_ids 5 / required_evidence 3（fec4b39）。
EVIDENCE_REF_MAX_CHARS = ID_MAX_CHARS
EVIDENCE_REFS_MAX_COUNT = 64


#: `PreparedSemanticPayload.raw_limitation_evidence` の行（legacy reason の有界な証拠）
LEGACY_REASON_EVIDENCE_ROW = (
    Column("reason_id", TEXT, ID_MAX_CHARS),
    Column("stage", TEXT, LABEL_MAX_CHARS),
    Column("pair_or_case", TEXT, LABEL_MAX_CHARS),
    Column("detail", TEXT, DETAIL_MAX_CHARS),
    Column("evidence_refs", EVIDENCE, legacy=as_list),
    Column("object_target_key", EVIDENCE),
    Column("proof_obligation_id", EVIDENCE),
)


class LegacyReasonEvidence:
    """legacy reason 1 件を `LEGACY_REASON_EVIDENCE_ROW` で書く view。"""

    __slots__ = ("_record",)

    def __init__(self, record: Any) -> None:
        self._record = record

    def __getattr__(self, name: str) -> Any:
        return getattr(self._record, name)

    def json_items(self):
        return row_items(LEGACY_REASON_EVIDENCE_ROW, self._record)


def _bounded_value(value: Any, *, work: Any, inline_bytes: Optional[int] = None) -> Any:
    from scripts.function_tracer_pcode.core.json_encoding import bounded_evidence

    return bounded_evidence(value, work=work, inline_bytes=inline_bytes)


def _bounded_text(value: Any, max_chars: int, *, work: Any) -> Any:
    """自由文の列: 文字列は文字数まで、文字列でない値（case の組など）は有界な証拠。"""

    from scripts.function_tracer_pcode.core.json_encoding import bounded_text

    if value is None or isinstance(value, str):
        return bounded_text(value, max_chars, work=work)
    return _bounded_value(value, work=work)


def bounded_prefix(items: Any, *, work: Any, limit: int = EVIDENCE_REFS_MAX_COUNT) -> Tuple[Any, ...]:
    """列の先頭 `limit` 個を、1 つずつ有界にして引き出す（残りは件数の marker 1 つ）。

    列全体を写さない（`tuple(items)` をしない）。大きさの分かる列なら残りの件数を、分からない
    列（iterator）なら「まだある」ことだけを marker にする。文字列の要素は文字数まで、それ
    以外は有界な証拠。
    """

    from itertools import islice

    if items is None:
        return ()
    if isinstance(items, (str, bytes)):
        items = (items,)
    kept = []
    try:
        iterator = iter(items)
    except TypeError:
        # 列でない値（producer の不備）: 1 つの有界な証拠として残す
        return (_bounded_value(items, work=work),)
    for item in islice(iterator, limit):
        if isinstance(item, str):
            kept.append(_bounded_text(item, EVIDENCE_REF_MAX_CHARS, work=work))
        else:
            kept.append(_bounded_value(item, work=work))
    try:
        total = len(items)
    except TypeError:
        total = None
    if total is not None:
        if total > limit:
            kept.append(f"…(+{total - limit} refs)")
    else:
        for _more in iterator:
            kept.append("…(+more refs)")
            break
    return tuple(kept)


def finitize_unknown_reason_record(record: UnknownReasonRecord, *, work: Any) -> UnknownReasonRecord:
    """legacy reason 1 件の重い field を有界な表現へ置き換える（reason id などは不変）。"""

    return replace(
        record,
        stage=_bounded_text(record.stage, LABEL_MAX_CHARS, work=work),
        pair_or_case=_bounded_text(record.pair_or_case, LABEL_MAX_CHARS, work=work),
        detail=_bounded_text(record.detail, DETAIL_MAX_CHARS, work=work),
        object_target_key=_bounded_value(record.object_target_key, work=work),
        object_evidence=_bounded_value(record.object_evidence, work=work),
        proof_obligation_id=_bounded_value(record.proof_obligation_id, work=work),
        typed_cause_key=_bounded_value(
            record.typed_cause_key, work=work, inline_bytes=TYPED_CAUSE_KEY_INLINE_BYTES,
        ),
        proof_requirement_ids=bounded_prefix(record.proof_requirement_ids, work=work),
        evidence_refs=bounded_prefix(record.evidence_refs, work=work),
    )


def finitize_unknown_recovery_action(action: UnknownRecoveryAction, *, work: Any) -> UnknownRecoveryAction:
    """recovery action 1 件の重い field を有界な表現へ置き換える。"""

    return replace(
        action,
        stage=_bounded_text(action.stage, LABEL_MAX_CHARS, work=work),
        pair_or_case=_bounded_text(action.pair_or_case, LABEL_MAX_CHARS, work=work),
        detail=_bounded_text(action.detail, DETAIL_MAX_CHARS, work=work),
        object_target_key=_bounded_value(action.object_target_key, work=work),
        object_evidence=_bounded_value(action.object_evidence, work=work),
        proof_obligation_id=_bounded_value(action.proof_obligation_id, work=work),
        evidence_refs=bounded_prefix(action.evidence_refs, work=work),
        required_evidence=bounded_prefix(action.required_evidence, work=work),
    )


def projection_diagnostic_work() -> Any:
    """finish 1 回の projection の診断（legacy との照合・cause key の要約）の作業量。

    上限は出力 schema の canonical reason の field の上限（診断はその行に書かれる）。
    """

    from scripts.function_tracer_pcode.checker.output_schema import authority_field_bounds
    from scripts.function_tracer_pcode.core.json_encoding import JsonBudget

    return JsonBudget(authority_field_bounds()["unknown_reasons"].max_bytes)


#: projection の診断に写す legacy reason の行数の上限。`detail` が使うのは先頭 2 行で、残りは
#: 読み手の手がかり（件数は `legacy_matched_count`）。診断は reason 行の `EVIDENCE` の列に
#: 置かれるので、出力の大きさはこの値に依らない。固定の EqBench subset の観測の最大は 1 行（fec4b39）。
PROJECTION_DIAGNOSTIC_LEGACY_ROWS = 8


def build_projection_diagnostic(
    receipt: Any,
    *,
    cause_occurrence: Any = None,
    legacy_reasons: Any = (),
    function_names: Mapping[str, Any] = None,
    binary_names: Mapping[str, Any] = None,
    projected_reason_counts: Mapping[str, int] = None,
    work: Any,
) -> Dict[str, Any]:
    """Human-readable, machine-aggregatable facts for one projected v2 cause.

    The projected record only carried digests (Issue #17).  This collects, in
    priority order, the typed cause occurrence (what semantic fact is missing,
    on which target kind and scope, from which producer site), the matching
    legacy strategy reason (site / case pair / free-text detail), and the
    function/binary names of the compared pair.  It is diagnostic data, not
    authority: no digest or receipt is derived from it.

    Issue #22 PR-22-D: 辿る作業（cause の key の要約・legacy との照合）は `work`
    （`projection_diagnostic_work()`。finish 1 回で共有）へ数える。
    """
    from scripts.function_tracer_pcode.authority.contracts import canonical_value

    diagnostic: Dict[str, Any] = {
        "schema": "unknown-reason-diagnostic-v1",
        "reason_id": getattr(receipt, "reason_id", None),
        "functions": {
            "function1": (function_names or {}).get("function1"),
            "function2": (function_names or {}).get("function2"),
        },
        "binaries": {
            "binary1": (binary_names or {}).get("binary1"),
            "binary2": (binary_names or {}).get("binary2"),
        },
    }
    if cause_occurrence is not None:
        cause_id = getattr(cause_occurrence, "cause_id", None)
        scope = getattr(cause_occurrence, "identity_scope", None)
        diagnostic["cause"] = {
            "occurrence_id": getattr(cause_occurrence, "occurrence_id", None),
            "target_kind": getattr(cause_occurrence, "target_kind", None),
            "identity_scope": getattr(scope, "value", scope),
            "producer_id": getattr(cause_occurrence, "producer_id", None),
            "evidence_kind": getattr(cause_occurrence, "evidence_kind", None),
            "evidence_refs": list(bounded_prefix(
                getattr(cause_occurrence, "evidence_refs", ()), work=work,
            )),
            # Issue #22 PR-22-D: cause の key は authority が封印した canonical な値。
            # 診断には有界な表現（大きければ cause id を identity にした要約）だけを置く
            "canonical_target_key": _bounded_cause_value(
                getattr(cause_id, "canonical_target_key", None), cause_id, column="canonical_target_key", work=work,
            ),
            "missing_semantic_fact": _bounded_cause_value(
                getattr(cause_id, "missing_semantic_fact", None), cause_id, column="missing_semantic_fact", work=work,
            ),
        }
    matched, match_kind = _match_legacy_reasons(
        diagnostic["reason_id"],
        cause_occurrence,
        legacy_reasons,
        projected_reason_counts or {},
        work=work,
    )
    if matched:
        diagnostic["legacy_match"] = match_kind
        if len(matched) > PROJECTION_DIAGNOSTIC_LEGACY_ROWS:
            # 診断に写す legacy の行は上限まで（件数は残す。`detail` が使うのは先頭 2 行）
            diagnostic["legacy_matched_count"] = len(matched)
            matched = matched[:PROJECTION_DIAGNOSTIC_LEGACY_ROWS]
        # legacy の行は有界化の primitive を通して写す（G4-b で有界化済みなら何もしない。
        # 有界化していない record でも入力に比例する写しをしない）
        diagnostic["legacy"] = [
            {
                "stage": _bounded_text(getattr(record, "stage", None), LABEL_MAX_CHARS, work=work),
                "pair_or_case": _bounded_text(getattr(record, "pair_or_case", None), LABEL_MAX_CHARS, work=work),
                "detail": _bounded_text(getattr(record, "detail", None), DETAIL_MAX_CHARS, work=work),
                "evidence_refs": list(bounded_prefix(getattr(record, "evidence_refs", ()), work=work)),
                "object_target_key": _canonical_summary(
                    _bounded_value(getattr(record, "object_target_key", None), work=work),
                ),
            }
            for record in matched
        ]
    return diagnostic


def _bounded_cause_value(value: Any, cause_id: Any, *, column: str, work: Any) -> Any:
    """cause の canonical な値を、小さければそのまま、大きければ cause id の要約にする。"""

    from scripts.function_tracer_pcode.authority.contracts import canonical_value
    from scripts.function_tracer_pcode.core.json_encoding import BoundedEvidence, bounded_evidence, column_identity

    if value is None:
        return None
    identity = getattr(cause_id, "value", None)
    bounded = bounded_evidence(
        value, work=work,
        identity=column_identity("cause:" + identity, column) if isinstance(identity, str) else None,
    )
    # 小さく plain な値（容器と基底型だけ）はそのまま: canonical な形も小さい
    return bounded if type(bounded) is BoundedEvidence else canonical_value(bounded)


#: `_match_legacy_reasons` の照合の種類（診断に書く。判定には使わない）
MATCH_EXACT = "exact"
MATCH_FINGERPRINT = "fingerprint"
MATCH_UNIQUE = "unique"


class _LegacyReasonGroup:
    """1 つの reason id の legacy record と、照合の key から record の位置への索引。"""

    __slots__ = ("records", "by_target", "by_fingerprint", "by_obligation")

    def __init__(self) -> None:
        self.records: List[Any] = []
        #: inline のまま残った `object_target_key` の canonical な値 → 位置
        self.by_target: Dict[Any, List[int]] = {}
        #: 有界な証拠になった `object_target_key` の canonical fingerprint → 位置
        self.by_fingerprint: Dict[str, List[int]] = {}
        #: inline のまま残った `proof_obligation_id` の canonical な値の文字列 → 位置
        self.by_obligation: Dict[str, List[int]] = {}


class LegacyReasonIndex:
    """projection の診断が照合する legacy reason の、reason id ごとの索引（finish 1 回で 1 つ）。

    照合の key（target・fingerprint・obligation）も作るときに 1 回だけ求め（`work` へ数える）、
    cause ごとの照合は索引を引くだけにする（cause × legacy の比較をしない）。
    `truncated` は件数の上限で残さなかった legacy reason があること（`legacy_reason_overflow`）か、
    索引を作る作業量を使い切ったこと。
    """

    __slots__ = ("_groups", "truncated")

    def __init__(self, groups: Dict[Any, _LegacyReasonGroup], truncated: bool) -> None:
        self._groups = groups
        self.truncated = truncated

    def group(self, reason_id: Any) -> Optional[_LegacyReasonGroup]:
        return self._groups.get(reason_id)

    def by_reason(self, reason_id: Any) -> Tuple[Any, ...]:
        group = self._groups.get(reason_id)
        return () if group is None else tuple(group.records)


def _canonical_summary(bounded: Any) -> Any:
    """有界化した値（inline の上限以下の plain な値か `BoundedEvidence`）の canonical な値。

    `bounded_evidence` の結果だけを受ける: plain な値は組み込みの容器だけ、`BoundedEvidence`
    の `to_authority_dict()` は固定の形の要約（O(1)）。
    """

    from scripts.function_tracer_pcode.authority.contracts import canonical_value

    return canonical_value(bounded)


def _inline_canonical(value: Any, *, work: Any) -> Any:
    """inline のまま残った小さい値の canonical な値（大きさを数えてから作る。作れなければ `None`）。"""

    from scripts.function_tracer_pcode.authority.contracts import canonical_value
    from scripts.function_tracer_pcode.core.json_encoding import PRODUCER_FAILURES, RESULT_JSON_POLICY

    try:
        # 容器（tuple / list / dict）と基底型だけから成る値だけを canonical にする（producer を
        # 持つ値は canonical_value が `to_authority_dict()` を呼ぶので索引に入れない）
        size = RESULT_JSON_POLICY.plain_bytes(value, max_bytes=work.remaining())
        if size is None:
            return None
        work.charge(1 + size)
        canonical = canonical_value(value)
        hash(canonical)
    except PRODUCER_FAILURES:
        return None
    return canonical


def legacy_reason_index(legacy_reasons: Any, *, work: Any, overflow: Any = 0) -> LegacyReasonIndex:
    """legacy reason を reason id ごとに 1 回だけ振り分け、照合の key を 1 回だけ求める。

    record 1 件ごと・key の大きさを `work` へ数える。診断なので例外を上げない: `work` を使い
    切ったら、そこまでの索引を `truncated` にして返す（authority の finish を止めない）。
    """

    from scripts.function_tracer_pcode.core.json_encoding import BoundedEvidence, JsonBudgetExhausted

    groups: Dict[Any, _LegacyReasonGroup] = {}
    truncated = bool(overflow)
    try:
        for record in legacy_reasons or ():
            work.charge(1)
            group = groups.get(getattr(record, "reason_id", None))
            if group is None:
                group = groups[getattr(record, "reason_id", None)] = _LegacyReasonGroup()
            position = len(group.records)
            group.records.append(record)
            target = getattr(record, "object_target_key", None)
            if type(target) is BoundedEvidence:
                if target.fingerprint_kind == "canonical_sha256":
                    group.by_fingerprint.setdefault(target.fingerprint, []).append(position)
            elif target is not None:
                canonical = _inline_canonical(target, work=work)
                if canonical is not None:
                    group.by_target.setdefault(canonical, []).append(position)
            obligation = getattr(record, "proof_obligation_id", None)
            if obligation is not None and type(obligation) is not BoundedEvidence:
                canonical = _inline_canonical(obligation, work=work)
                if canonical is not None:
                    group.by_obligation.setdefault(str(canonical), []).append(position)
    except JsonBudgetExhausted:
        truncated = True
    return LegacyReasonIndex(groups, truncated=truncated)


def _text_cost(item: Any, work: Any) -> int:
    """`str(item)` の手間（文字列は長さ、それ以外は `work` の残りの中で数えた JSON の byte）。"""

    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

    if isinstance(item, str):
        return len(item)
    return RESULT_JSON_POLICY.measure(item, max_bytes=work.remaining())


def _match_legacy_reasons(
    reason_id: Any,
    cause_occurrence: Any,
    legacy_reasons: Any,
    projected_reason_counts: Mapping[str, int],
    *,
    work: Any,
) -> Tuple[Tuple[Any, ...], Optional[str]]:
    """Pick the legacy records that describe *this* cause, never a sibling site.

    1. exact: the legacy ``object_target_key`` equals the cause's canonical
       target key (SAT-safety and other producers emit the record's key as the
       cause target), or the legacy proof obligation equals one of the cause's
       proof requirement ids.
    2. unique: no exact key is available, but the reason id has exactly one
       legacy record and exactly one projected cause, so the correspondence is
       1:1 by construction (only when no legacy record was dropped by the
       count bound: ``legacy_reason_overflow``).
    Otherwise nothing is attached; the typed cause occurrence alone is used.

    Issue #22 PR-22-D: legacy の重い field は authority 前に有界化されている。
    * 小さい値（そのまま残った値）は ``canonical_value`` の ``==`` で比べる（従来どおり）。
    * 大きい値（``BoundedEvidence``）は **fingerprint** で照合する（``MATCH_FINGERPRINT``。
      SHA-256 の衝突耐性に頼る照合の手がかりで、等しさの証明ではない。結果は診断にだけ
      使い、照合の種類を診断に明記する）。cause の key の fingerprint は ``work`` の中で
      1 回だけ求め、収まらなければ fingerprint では照合しない。
    * proof obligation は小さい値だけを requirement id と比べる（大きい obligation は
      requirement id になり得る長さの文字列と等しくならない）。
    """

    from scripts.function_tracer_pcode.core.canonical_digest import (
        CanonicalValueCycle,
        canonical_fingerprint,
    )
    from scripts.function_tracer_pcode.core.json_encoding import (
        PRODUCER_FAILURES,
        JsonBudgetExhausted,
        JsonValueRejected,
    )

    index = legacy_reasons if isinstance(legacy_reasons, LegacyReasonIndex) else legacy_reason_index(
        legacy_reasons, work=work,
    )
    group = index.group(reason_id)
    if group is None or not group.records:
        return (), None
    candidates = tuple(group.records)
    cause_id = getattr(cause_occurrence, "cause_id", None)
    cause_target = getattr(cause_id, "canonical_target_key", None) if cause_id is not None else None
    requirements = (
        getattr(cause_occurrence, "proof_requirement_ids", ()) or ()
        if cause_occurrence is not None else ()
    )

    def requirement_texts() -> frozenset:
        # cause の requirement id の文字列（cause 1 つにつき 1 回。大きさを数えてから文字列に
        # する。数えきれない・JSON にならない requirement は照合に使わない）
        texts = set()
        for item in requirements:
            try:
                cost = _text_cost(item, work)
            except JsonValueRejected:
                continue
            except JsonBudgetExhausted:
                # 残りを使い切った（数えた分を足して、以後は照合に使わない）
                remaining = work.remaining()
                if remaining is not None:
                    work.consumed += remaining
                break
            try:
                work.charge(1 + cost)
            except JsonBudgetExhausted:
                break
            texts.add(str(item))
        return frozenset(texts)

    # cause の key: canonical fingerprint を `work` の中で 1 回だけ求める（key の大きさを数えた
    # ことになる）。求められたときだけ、key で索引を引く（引く hash も key の大きさに比例する）
    cause_fingerprint = None
    if cause_target is not None:
        try:
            cause_fingerprint = canonical_fingerprint(cause_target, work=work)
        except (JsonBudgetExhausted, CanonicalValueCycle) + PRODUCER_FAILURES:
            cause_fingerprint = None
    by_target: set = set()
    by_fingerprint: set = set()
    if cause_fingerprint is not None:
        try:
            by_target = set(group.by_target.get(cause_target, ()))
        except TypeError:
            by_target = set()
        by_fingerprint = set(group.by_fingerprint.get(cause_fingerprint, ()))
    by_obligation: set = set()
    if requirements and group.by_obligation:
        for text_value in requirement_texts():
            by_obligation.update(group.by_obligation.get(text_value, ()))
    # 旧来の規則: key が一致した record と、fingerprint で一致しなかった record のうち obligation が
    # 一致したものが exact（元の並び）、fingerprint で一致したものはその後
    exact_positions = sorted(by_target | (by_obligation - by_fingerprint))
    fingerprint_positions = sorted(by_fingerprint)
    try:
        work.charge(len(exact_positions) + len(fingerprint_positions))
    except JsonBudgetExhausted:
        pass  # 引いた位置は数え済みの索引の中（使い切りは次の照合で分かる）
    exact = [group.records[position] for position in exact_positions]
    by_fingerprint_records = [group.records[position] for position in fingerprint_positions]
    if exact or by_fingerprint_records:
        return tuple(exact) + tuple(by_fingerprint_records), (MATCH_EXACT if exact else MATCH_FINGERPRINT)
    # 1:1 は legacy の reason を全部残したときだけ（先頭だけを残したなら、残さなかった record
    # にも同じ reason id があり得る）
    if (
        not index.truncated
        and len(candidates) == 1 and int(projected_reason_counts.get(reason_id, 0) or 0) == 1
    ):
        return candidates, MATCH_UNIQUE
    return (), None


def make_production_unknown_reason(
    projection_receipt: Any,
    *,
    projection_factory: Any,
    detail: Optional[str] = None,
    diagnostic: Optional[Mapping[str, Any]] = None,
    cause_occurrence: Any = None,
) -> UnknownReasonRecord:
    """Project one factory-owned active v2 cause to compatibility data.

    ``object_target_key`` は cause の封印済み canonical key そのもの（conditional lane が
    読む。写さない）。診断（``object_evidence``）は有界な表現だけを持つ。出力は行 schema
    が key を有界に書く（大きければ cause id の要約）。
    """

    from scripts.function_tracer_pcode.authority.sites.activation import (
        TypedResultProjectionFactory,
        TypedResultProjectionReceipt,
    )

    if type(projection_factory) is not TypedResultProjectionFactory:
        raise TypeError("production compatibility projection requires exact issuer")
    if type(projection_receipt) is not TypedResultProjectionReceipt:
        raise TypeError("production compatibility projection requires exact receipt")
    if not projection_factory.owns(projection_receipt):
        raise ValueError("production compatibility projection is not issuer-owned")
    receipt = projection_receipt
    definition = projection_factory.reason_definition_for(receipt)
    class_map = {
        "proof_obligation": UnknownReasonClass.PROOF_OBLIGATION.value,
        "unsupported_semantics": UnknownReasonClass.OPERATIONAL_GAP.value,
        "semantic_safety_gate": UnknownReasonClass.UNSAFE_ANALYSIS.value,
        "semantic_partition_blocker": UnknownReasonClass.PROOF_OBLIGATION.value,
        "semantic": UnknownReasonClass.PROOF_OBLIGATION.value,
    }
    return UnknownReasonRecord(
        count_kind=UnknownCountKind.REASON_RECORD.value,
        reason_id=receipt.reason_id,
        reason_class=class_map.get(
            definition.reason_class, UnknownReasonClass.PROOF_OBLIGATION.value
        ),
        decision_effect=definition.decision_effect,
        reason_scope=UnknownReasonScope.QUERY.value,
        aggregation_unit=UnknownAggregationUnit.RESULT.value,
        stage="V2_TYPED_RESULT_PROJECTION",
        evidence_refs=(receipt.event_digest, receipt.receipt_digest),
        typed_cause_key={
            "authority_class": "V2_FACTORY_PROJECTION",
            "projection_schema": receipt.projection_schema,
            "activation_id": receipt.activation_id,
            "expected_cause_slot_id": receipt.expected_cause_slot_id,
            "result_occurrence_id": receipt.result_occurrence_id,
            "occurrence_id": receipt.occurrence_id,
            "cause_id": receipt.cause_id,
            "reason_id": receipt.reason_id,
            "source_snapshot_fingerprint": receipt.source_snapshot_fingerprint,
            "event_digest": receipt.event_digest,
            "event_stream_digest": receipt.event_stream_digest,
            "semantic_projection_digest": receipt.semantic_projection_digest,
            "lifecycle_projection_digest": receipt.lifecycle_projection_digest,
            "reason_registry_digest": receipt.reason_registry_digest,
            "recovery_registry_digest": receipt.recovery_registry_digest,
            "receipt_digest": receipt.receipt_digest,
        },
        target_regression=receipt.reason_id,
        detail=detail if detail is not None else (
            format_projection_detail(diagnostic) if diagnostic else None
        ),
        pair_or_case=_first_legacy_field(diagnostic, "pair_or_case"),
        object_target_key=_production_target_key(cause_occurrence, diagnostic),
        object_evidence=dict(diagnostic) if diagnostic else None,
    )


def _production_target_key(cause_occurrence: Any, diagnostic: Optional[Mapping[str, Any]]) -> Any:
    """canonical reason の `object_target_key`（conditional lane が cause と照合する鍵）。

    従来どおり、診断が cause を持つとき（= cause occurrence が在り、診断を作れたとき）
    だけ設定する。値は診断の有界な写しではなく cause の封印済み canonical key そのもの
    （`CauseIdV2` が作成時に canonical 化した値で、従来の `canonical_value(...)` と等しい）。
    """

    if not diagnostic or diagnostic.get("cause") is None:
        return None
    cause_id = getattr(cause_occurrence, "cause_id", None)
    if cause_id is None:
        return None
    return getattr(cause_id, "canonical_target_key", None)


def _first_legacy_field(diagnostic: Optional[Mapping[str, Any]], field_name: str) -> Any:
    for item in (diagnostic or {}).get("legacy") or ():
        value = item.get(field_name)
        if value is not None:
            return value
    return None


def coerce_unknown_reason_record(value: Any) -> UnknownReasonRecord:
    if isinstance(value, UnknownReasonRecord):
        return value
    if isinstance(value, Mapping):
        return UnknownReasonRecord.from_dict(value)
    return make_unknown_reason(value)


def coerce_unknown_reason_records(values: Optional[Iterable[Any]]) -> Tuple[UnknownReasonRecord, ...]:
    return tuple(coerce_unknown_reason_record(value) for value in (values or ()))


def coerce_unknown_recovery_action(value: Any) -> UnknownRecoveryAction:
    if isinstance(value, UnknownRecoveryAction):
        return value
    if isinstance(value, Mapping):
        return UnknownRecoveryAction.from_dict(value)
    return UnknownRecoveryAction(
        count_kind=UnknownCountKind.PROOF_ACTION.value,
        reason_id=UnknownReasonId.UNKNOWN.value,
        decision_effect=UnknownDecisionEffect.DIAGNOSTIC_ONLY.value,
        reason_scope=UnknownReasonScope.GLOBAL.value,
        proof_kind=UnknownRecoveryProofKind.NONE.value,
        proof_stage="unspecified",
        status=UnknownRecoveryActionStatus.NO_REGISTERED_PLAN.value,
        aggregation_unit=UnknownAggregationUnit.RESULT.value,
        detail=str(value),
    )


def coerce_unknown_recovery_actions(values: Optional[Iterable[Any]]) -> Tuple[UnknownRecoveryAction, ...]:
    return tuple(coerce_unknown_recovery_action(value) for value in (values or ()))


def build_unknown_recovery_actions(
    values: Optional[Iterable[Any]],
    *,
    primary_by_aggregation_unit: bool = False,
) -> Tuple[UnknownRecoveryAction, ...]:
    return tuple(iter_unknown_recovery_actions(
        values, primary_by_aggregation_unit=primary_by_aggregation_unit,
    ))


def iter_unknown_recovery_actions(
    values: Optional[Iterable[Any]],
    *,
    primary_by_aggregation_unit: bool = False,
):
    """`build_unknown_recovery_actions` と同じ action を 1 つずつ作る（producer 時点の構築）。

    出力の準備は `recovery_actions_source`（walk の作業量へ数える）を使う。
    """

    from scripts.function_tracer_pcode.core.json_encoding import JsonBudget

    # producer 時点（出力の前）の構築: 出力の行数は finitize が判定の前に schema と比べる
    return _iter_recovery_actions(
        values, primary_by_aggregation_unit=primary_by_aggregation_unit, work=JsonBudget(None), for_output=False,
    )


def recovery_actions_source(
    values: Optional[Iterable[Any]],
    *,
    primary_by_aggregation_unit: bool = False,
) -> Any:
    """出力の準備用: `build_unknown_recovery_actions` と同じ action の列（walk の作業量へ数える）。

    読み飛ばす record・obligation・proof obligation id の key の写しを、作る **前** に walk の
    作業量へ数える（`metered`）。walker が action を引き出すたびの勘定だけでは、yield しない
    record の仕事が数えられない。
    """

    from scripts.function_tracer_pcode.core.json_encoding import each, metered

    return metered(lambda work: each(_iter_recovery_actions(
        values, primary_by_aggregation_unit=primary_by_aggregation_unit, work=work, for_output=True,
    )))


def _key_width(value: Any, work: Any) -> None:
    """`build_proof_obligation_id` が写す key（入れ子の list / tuple）の要素を、写す前に数える。"""

    pending = [value]
    while pending:
        item = pending.pop()
        if isinstance(item, (list, tuple)):
            work.charge(len(item) + 1)
            pending.extend(child for child in item if isinstance(child, list))
        else:
            work.charge(1)


def _iter_recovery_actions(
    values: Optional[Iterable[Any]], *, primary_by_aggregation_unit: bool, work: Any, for_output: bool,
):
    # producer 時点（判定が読む action）は従来の coercion、出力の準備は数えてから写す coercion
    primary = _PrimaryFilter() if primary_by_aggregation_unit else None
    for value in values or ():
        # 読み飛ばす record も 1 件ずつ数える
        work.charge(1)
        record = (
            _coerce_record_within(value, work=work) if for_output else coerce_unknown_reason_record(value)
        )
        if primary is not None and not primary.admit(record, work=work):
            continue
        obligations = record.recovery_proof_obligations
        if not obligations:
            plan = get_unknown_recovery_plan(record.reason_id)
            obligations = plan.proof_obligations
        if not obligations:
            if record.recovery_proof_kind == UnknownRecoveryProofKind.NONE.value:
                continue
            yield (
                UnknownRecoveryAction(
                    count_kind=UnknownCountKind.PROOF_ACTION.value,
                    reason_id=record.reason_id,
                    decision_effect=record.decision_effect,
                    reason_scope=record.reason_scope,
                    proof_kind=record.recovery_proof_kind,
                    proof_stage=record.proof_stage or "unspecified",
                    status=record.action_status or UnknownRecoveryActionStatus.NO_REGISTERED_PLAN.value,
                    aggregation_unit=record.aggregation_unit,
                    stage=record.stage,
                    pair_or_case=record.pair_or_case,
                    evidence_refs=record.evidence_refs,
                    evidence_kind=record.evidence_kind,
                    object_target_key=record.object_target_key,
                    object_evidence=record.object_evidence,
                    proof_obligation_id=record.proof_obligation_id,
                    recovery_action=record.recovery_action,
                    target_regression=record.target_regression,
                    detail=record.detail,
                )
            )
            continue
        for obligation in obligations:
            work.charge(1)
            proof_stage = record.proof_stage or obligation.proof_stage
            if (
                record.proof_stage is not None
                or record.evidence_kind is not None
                or record.recovery_action is not None
            ):
                proof_kind = record.recovery_proof_kind
                if proof_kind == UnknownRecoveryProofKind.NONE.value:
                    proof_kind = obligation.proof_kind
            else:
                proof_kind = obligation.proof_kind
            evidence_kind = record.evidence_kind
            if evidence_kind is None and obligation.required_evidence:
                evidence_kind = obligation.required_evidence[0]
            proof_obligation_id = record.proof_obligation_id
            if (
                proof_obligation_id is None
                and evidence_kind is not None
                and record.object_target_key is not None
            ):
                _key_width(record.object_target_key, work)
                proof_obligation_id = build_proof_obligation_id(
                    record.reason_id,
                    proof_stage,
                    proof_kind,
                    evidence_kind,
                    record.object_target_key,
                )
            yield (
                UnknownRecoveryAction(
                    count_kind=UnknownCountKind.PROOF_ACTION.value,
                    reason_id=record.reason_id,
                    decision_effect=record.decision_effect,
                    reason_scope=record.reason_scope,
                    proof_kind=proof_kind,
                    proof_stage=proof_stage,
                    status=record.action_status or UnknownRecoveryActionStatus.PLANNED.value,
                    aggregation_unit=record.aggregation_unit,
                    stage=record.stage,
                    pair_or_case=record.pair_or_case,
                    required_evidence=obligation.required_evidence,
                    evidence_refs=record.evidence_refs,
                    evidence_kind=evidence_kind,
                    object_target_key=record.object_target_key,
                    object_evidence=record.object_evidence,
                    proof_obligation_id=proof_obligation_id,
                    recovery_action=record.recovery_action,
                    target_regression=record.target_regression,
                    detail=obligation.description or record.detail,
                )
            )


def summarize_unknown_reason_counts(
    values: Optional[Iterable[Any]],
    *,
    primary_by_aggregation_unit: bool = False,
) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    records = coerce_unknown_reason_records(values)
    if primary_by_aggregation_unit:
        records = _select_primary_records_by_aggregation_unit(records)
    for record in records:
        counts[record.reason_id] = int(counts.get(record.reason_id, 0) or 0) + 1
    return counts


def _select_primary_records_by_aggregation_unit(
    records: Iterable[UnknownReasonRecord],
) -> Tuple[UnknownReasonRecord, ...]:
    primary_records: Dict[Tuple[str, Any], UnknownReasonRecord] = {}
    fallback_index = 0
    for record in records:
        aggregation_key = str(record.aggregation_unit or UnknownAggregationUnit.RESULT.value)
        unit_key = record.pair_or_case or record.stage
        if unit_key is None:
            # 単位の無い record は 1 件ずつ別の単位（文字列を作らない key）
            unit_key = ("record", fallback_index)
            fallback_index += 1
        primary_records.setdefault((aggregation_key, unit_key), record)
    return tuple(primary_records.values())


def summarize_unknown_recovery_backlog(
    values: Optional[Iterable[Any]],
    *,
    primary_by_aggregation_unit: bool = False,
) -> Dict[str, Dict[str, Any]]:
    records = coerce_unknown_reason_records(values)
    if primary_by_aggregation_unit:
        records = _select_primary_records_by_aggregation_unit(records)
    summary: Dict[str, Dict[str, Any]] = {}
    for record in records:
        entry = summary.setdefault(
            record.reason_id,
            {
                "count": 0,
                "target_regression": record.target_regression,
                "recovery_proof_kind": record.recovery_proof_kind,
                "proof_obligation_counts": {},
                "proof_obligations": [],
            },
        )
        entry["count"] = int(entry["count"]) + 1
        if entry.get("target_regression") is None:
            entry["target_regression"] = record.target_regression
        if (
            entry.get("recovery_proof_kind") == UnknownRecoveryProofKind.NONE.value
            and record.recovery_proof_kind != UnknownRecoveryProofKind.NONE.value
        ):
            entry["recovery_proof_kind"] = record.recovery_proof_kind
        seen_obligations = {
            (obligation["proof_kind"], obligation["proof_stage"])
            for obligation in entry["proof_obligations"]
        }
        proof_counts = entry["proof_obligation_counts"]
        for obligation in record.recovery_proof_obligations:
            proof_counts[obligation.proof_kind] = int(proof_counts.get(obligation.proof_kind, 0) or 0) + 1
            obligation_key = (obligation.proof_kind, obligation.proof_stage)
            if obligation_key not in seen_obligations:
                entry["proof_obligations"].append(obligation.to_dict())
                seen_obligations.add(obligation_key)
    return summary



# ---------------------------------------------------------------------------
# 集計の出力（Issue #22 PR-22-D）
# ---------------------------------------------------------------------------
#
# 出力の集計は **key を 1 つずつ** 作る: 初出順に key を 1 つ出すたびに、その key の
# 値を record を数え直して作る。作業中に持つのは「出し終えた key」の集合だけで、
# それは walker が既に数えた出力の大きさで抑えられる。値は `summarize_*` の dict と
# 同じ（key の並びも同じ）。


class _PrimaryFilter:
    """`_select_primary_records_by_aggregation_unit` を 1 件ずつ行う（単位ごとに最初の record）。"""

    __slots__ = ("seen", "fallback_index")

    def __init__(self) -> None:
        self.seen: set = set()
        self.fallback_index = 0

    def admit(self, record: UnknownReasonRecord, *, work: Any) -> bool:
        from scripts.function_tracer_pcode.core.json_encoding import builtin_str, hashable_key

        aggregation_key = builtin_str(record.aggregation_unit or UnknownAggregationUnit.RESULT.value)
        unit_key = record.pair_or_case or record.stage
        if unit_key is None:
            unit_key = ("record", self.fallback_index)
            self.fallback_index += 1
        # 単位の key は hash する前に数え、組み込みの値だけを値で比べる（有界化していない trace
        # の record もある。上書きした `__hash__` / `__eq__` を呼ばない）
        key = (hashable_key(aggregation_key, work), hashable_key(unit_key, work))
        if key in self.seen:
            return False
        self.seen.add(key)
        return True


def _coerce_record_within(value: Any, *, work: Any) -> UnknownReasonRecord:
    """出力の準備で読む reason の値を record にする（入力に比例する写しは数えてから）。

    record はそのまま、mapping は大きさを `work` の中で数えてから `from_dict`、reason id の
    文字列は長さを数えてから。それ以外（`str()` が producer になる object）は JSON にならない値。
    """

    from scripts.function_tracer_pcode.core.json_encoding import LEGACY, RESULT_JSON_POLICY

    if isinstance(value, UnknownReasonRecord):
        return value
    if type(value) is dict:
        work.charge(1 + RESULT_JSON_POLICY.measure(value, max_bytes=work.remaining(), mode=LEGACY))
        return UnknownReasonRecord.from_dict(value)
    if type(value) is str:
        work.charge(len(value))
        return make_unknown_reason(value)
    raise TypeError(f"{type(value).__name__} is not an unknown reason record")


class _ReasonCounts(Reducer):
    """`scan` の reducer: `summarize_unknown_reason_counts` と同じ件数（reason id の初出順）。"""

    __slots__ = ("primary", "counts")

    def __init__(self, primary_by_aggregation_unit: bool) -> None:
        self.primary = _PrimaryFilter() if primary_by_aggregation_unit else None
        self.counts: Dict[str, int] = {}

    def add(self, value: Any, *, work: Any) -> None:
        from scripts.function_tracer_pcode.core.json_encoding import hashable_key

        record = _coerce_record_within(value, work=work)
        if self.primary is not None and not self.primary.admit(record, work=work):
            return
        # reason id は hash する前に数える（組み込みの値だけを値で比べる）
        key = hashable_key(record.reason_id, work)
        self.counts[key] = self.counts.get(key, 0) + 1

    def result(self, *, work: Any) -> Any:
        from scripts.function_tracer_pcode.core.json_encoding import pairs_of

        return pairs_of(iter(self.counts.items()))


def unknown_reason_counts_source(
    values: Optional[Iterable[Any]],
    *,
    primary_by_aggregation_unit: bool = False,
) -> Any:
    """`summarize_unknown_reason_counts` と同じ object を、walker が数えながら 1 回で集計する source。"""

    from scripts.function_tracer_pcode.core.json_encoding import scan

    return scan(values, _ReasonCounts(primary_by_aggregation_unit))


#: backlog の 1 entry（reason id ごと）の列。obligation の件数・列は有界な証拠。
RECOVERY_BACKLOG_ENTRY_ROW = (
    Column("count", INT),
    Column("target_regression", TEXT, ID_MAX_CHARS),
    Column("recovery_proof_kind", TEXT, VOCAB_MAX_CHARS),
    Column("proof_obligation_counts", EVIDENCE),
    Column("proof_obligations", EVIDENCE),
)


class _BacklogEntryView:
    """backlog の 1 entry（`summarize_unknown_recovery_backlog` の値と同じ内容）。

    `_RecoveryBacklog`（`scan` の reducer）が record を 1 件ずつ畳み込んで作る（reason id
    ごとに全 record を数え直さない）。obligation の件数と重複の無い列も同じ 1 回で集める。
    """

    __slots__ = (
        "count", "target_regression", "recovery_proof_kind", "_kind_counts", "_distinct",
        "_distinct_keys",
    )

    def __init__(self) -> None:
        self.count = 0
        self.target_regression = None
        self.recovery_proof_kind = None
        self._kind_counts: Dict[Any, int] = {}
        self._distinct: List[Any] = []
        self._distinct_keys: set = set()

    def add(self, record: UnknownReasonRecord, *, work: Any) -> None:
        obligations = record.recovery_proof_obligations
        # 辿る obligation の数を先に数える（record の列は tuple）
        work.charge(len(obligations))
        if self.count == 0:
            self.target_regression = record.target_regression
            self.recovery_proof_kind = record.recovery_proof_kind
        else:
            if self.target_regression is None:
                self.target_regression = record.target_regression
            if (
                self.recovery_proof_kind == UnknownRecoveryProofKind.NONE.value
                and record.recovery_proof_kind != UnknownRecoveryProofKind.NONE.value
            ):
                self.recovery_proof_kind = record.recovery_proof_kind
        self.count += 1
        for obligation in obligations:
            self._kind_counts[obligation.proof_kind] = self._kind_counts.get(obligation.proof_kind, 0) + 1
            key = (obligation.proof_kind, obligation.proof_stage)
            if key not in self._distinct_keys:
                self._distinct_keys.add(key)
                self._distinct.append(obligation)

    @property
    def proof_obligation_counts(self) -> Any:
        from scripts.function_tracer_pcode.core.json_encoding import pairs_of

        return pairs_of(iter(self._kind_counts.items()))

    @property
    def proof_obligations(self) -> Any:
        from scripts.function_tracer_pcode.core.json_encoding import each

        return each(self._distinct)

    def json_items(self):
        return row_items(RECOVERY_BACKLOG_ENTRY_ROW, self)


class _RecoveryBacklog(Reducer):
    """`scan` の reducer: `summarize_unknown_recovery_backlog` と同じ entry（reason id の初出順）。"""

    __slots__ = ("primary", "entries")

    def __init__(self, primary_by_aggregation_unit: bool) -> None:
        self.primary = _PrimaryFilter() if primary_by_aggregation_unit else None
        self.entries: Dict[str, _BacklogEntryView] = {}

    def add(self, value: Any, *, work: Any) -> None:
        from scripts.function_tracer_pcode.core.json_encoding import hashable_key

        record = _coerce_record_within(value, work=work)
        if self.primary is not None and not self.primary.admit(record, work=work):
            return
        key = hashable_key(record.reason_id, work)
        entry = self.entries.get(key)
        if entry is None:
            entry = self.entries[key] = _BacklogEntryView()
        entry.add(record, work=work)

    def result(self, *, work: Any) -> Any:
        from scripts.function_tracer_pcode.core.json_encoding import pairs_of

        return pairs_of(iter(self.entries.items()))


def recovery_backlog_source(
    values: Optional[Iterable[Any]],
    *,
    primary_by_aggregation_unit: bool = False,
) -> Any:
    """`summarize_unknown_recovery_backlog` と同じ object を、walker が 1 回で集計する source。

    出力では entry は行の schema（`RECOVERY_BACKLOG_ENTRY_ROW`）で有界になる。entry の数は
    reason の行数以下。record・obligation を 1 つずつ作業量へ数えながら畳み込む。
    """

    from scripts.function_tracer_pcode.core.json_encoding import scan

    return scan(values, _RecoveryBacklog(primary_by_aggregation_unit))
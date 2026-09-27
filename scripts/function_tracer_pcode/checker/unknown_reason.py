# -*- coding: utf-8 -*-
"""Typed UNKNOWN reason schema and registry."""

from __future__ import annotations

from dataclasses import dataclass, fields, replace
from typing import Any, Dict, Iterable, Iterator, List, Mapping, Optional, Sequence, Tuple

# Phase 7-1b-1 (#97): pure な定義層は proof.unknown_reason へ移動した。以下は (a) 本 module の実装が使う名前と
# (b) 旧 path `checker.unknown_reason` からの互換 import のための再輸出（同一 object。再定義しない）。
from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.json_encoding import (
    EVIDENCE,
    INT,
    TEXT,
    Column,
    as_dict,
    as_list,
    builtin_str,
    each,
    materialize,
    Reducer,
    row_items,
    source_converter,
    value_token,
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
    _proof_obligation_id,
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
    # 真偽は live_values の規則で読む（上書きした `__bool__` / `__len__` を呼ばない）
    return as_dict(value) if live_values.as_bool(value) else None


@source_converter
def _dict_items(values: Any) -> Any:
    # 有界化した後の列は mapping のほかに `BoundedEvidence`（大きい要素）と件数の marker（文字列）
    # を持つ。mapping だけを旧 `to_dict` と同じく dict にし、それ以外はそのまま置く
    return each(values, _dict_item)


@source_converter
def _dict_item(value: Any) -> Any:
    # 組み込みの振る舞いの mapping だけを dict にする（`isinstance` は `__class__` を読む）
    return as_dict(value) if live_values.builtin_mapping(value) is not None else value


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


def _evidence_identity(typed_cause_key: Any) -> Any:
    """大きい証拠を要約するときの identity（record の `typed_cause_key`）。authority の projection なら cause id。

    値は live_values の規則だけで読む（組み込みの mapping の `cause_id` の文字列だけ）。
    """

    mapping = live_values.builtin_mapping(typed_cause_key)
    if mapping is None:
        return None
    cause_id = live_values.str_value(live_values.lookup(mapping, "cause_id"))
    if cause_id is not live_values.NOT_PLAIN and cause_id:
        return "cause:" + cause_id
    return None


def _plain_text(value: Any) -> str:
    """`str(value)`（scalar・組み込みのままの enum は同じ文字列。それ以外は組み込みの `str` の写し）。"""

    if type(value) is str:
        return value
    try:
        return live_values.as_str(value)
    except TypeError:
        return builtin_str(value)


def _plain_enum_value(value: Any) -> Optional[str]:
    """`_enum_value(value)` と同じ文字列を live_values の規則だけで求める（enum は `_value_`）。

    pure layer（`proof.unknown_reason`）の関数へ live な値を渡さずに、正規化した文字列を渡す。
    `_enum_value` は文字列をそのまま返すので、結果は元の値を渡したときと同じ。
    """

    if value is None:
        return None
    if type(value) is str:
        return value
    if live_values.is_enum(value):
        return _plain_text(live_values.enum_value(value))
    return _plain_text(value)


def _or(value: Any, default: Any) -> Any:
    """`value or default`（真偽は live_values の規則。自身の code でしか決まらない値は `TypeError`）。"""

    return value if live_values.as_bool(value) else default


def _text_or(value: Any, default: str) -> str:
    """`str(value or default)`（live_values の規則で読む）。"""

    if type(value) is str:
        return value or default
    if value is None or not live_values.as_bool(value):
        return default
    return _plain_text(value)


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
        # action は `typed_cause_key` を持たない（証拠の identity は無い）
        return row_items(UNKNOWN_RECOVERY_ACTION_ROW, self, identity=None)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "UnknownRecoveryAction":
        # payload は live な mapping: 組み込みの振る舞いの mapping の値だけを読む（真偽・文字列も
        # live_values の規則。`str(x or 既定)` と同じ文字列）
        fields_ = _payload_view(payload)
        raw_reason_id = _plain_enum_value(fields_.get("reason_id"))
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
        target_regression = fields_.get("target_regression")
        return cls(
            count_kind=_plain_enum_value(fields_.get("count_kind")) or UnknownCountKind.PROOF_ACTION.value,
            reason_id=reason_id,
            decision_effect=_text_or(
                fields_.get("decision_effect"),
                definition.decision_effect if use_definition_defaults
                else UnknownDecisionEffect.DIAGNOSTIC_ONLY.value,
            ),
            reason_scope=_text_or(
                fields_.get("reason_scope"),
                definition.reason_scope if use_definition_defaults else UnknownReasonScope.GLOBAL.value,
            ),
            proof_kind=(
                normalize_recovery_proof_kind(_plain_enum_value(fields_.get("proof_kind")))
                or UnknownRecoveryProofKind.NONE.value
            ),
            proof_stage=_text_or(fields_.get("proof_stage"), "unspecified"),
            status=_text_or(fields_.get("status"), UnknownRecoveryActionStatus.PLANNED.value),
            aggregation_unit=_text_or(
                fields_.get("aggregation_unit"),
                definition.aggregation_unit if use_definition_defaults
                else UnknownAggregationUnit.RESULT.value,
            ),
            stage=fields_.get("stage"),
            pair_or_case=fields_.get("pair_or_case"),
            required_evidence=_coerce_evidence_refs(fields_.get("required_evidence")),
            evidence_refs=_coerce_evidence_refs(fields_.get("evidence_refs")),
            evidence_kind=fields_.get("evidence_kind"),
            object_target_key=_coerce_optional_tuple(fields_.get("object_target_key")),
            object_evidence=fields_.get("object_evidence"),
            proof_obligation_id=_coerce_optional_tuple(fields_.get("proof_obligation_id")),
            recovery_action=fields_.get("recovery_action"),
            target_regression=(
                target_regression
                if target_regression is not None
                else definition.target_regression if use_definition_defaults else None
            ),
            detail=fields_.get("detail"),
        )


def _payload_view(payload: Any) -> Dict[str, Any]:
    """live な mapping の (key の文字列, 値) の dict（組み込みの振る舞いの mapping だけ）。"""

    if type(payload) is dict:
        return payload
    view: Dict[str, Any] = {}
    for key, value in live_values.items_of(payload):
        view[_plain_text(key)] = value
    return view


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
        return row_items(UNKNOWN_REASON_ROW, self, identity=_evidence_identity(self.typed_cause_key))

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "UnknownReasonRecord":
        constructor = make_unknown_reason
        payload = _payload_view(payload)
        # reason id は `_enum_value` と同じ文字列を live_values の規則で求める（真偽も同じ規則）
        raw_reason_id = _plain_enum_value(payload.get("reason_id"))
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
            evidence_refs=_or(payload.get("evidence_refs"), ()),
            recovery_proof_kind=payload.get("recovery_proof_kind"),
            recovery_proof_obligations=payload.get("recovery_proof_obligations"),
            proof_stage=payload.get("proof_stage"),
            evidence_kind=payload.get("evidence_kind"),
            object_target_key=payload.get("object_target_key"),
            object_evidence=payload.get("object_evidence"),
            proof_obligation_id=payload.get("proof_obligation_id"),
            typed_cause_key=payload.get("typed_cause_key"),
            proof_requirement_ids=_or(payload.get("proof_requirement_ids"), ()),
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
    # 値は owner の規則で読む（`str()` は scalar と組み込みのままの enum の値の文字列だけ）
    normalized_action_status = _enum_value(action_status)
    resolved_proof_stage = proof_stage
    if resolved_proof_stage is None and live_values.size(coerced_recovery_obligations) == 1:
        (only_obligation,) = tuple(live_values.elements_of(coerced_recovery_obligations))
        resolved_proof_stage = live_values.attribute(only_obligation, "proof_stage")
    resolved_evidence_kind = _plain_text(evidence_kind) if evidence_kind is not None else None
    coerced_proof_obligation_id = _coerce_optional_tuple(proof_obligation_id)
    if (
        coerced_proof_obligation_id is None
        and resolved_proof_stage is not None
        and resolved_evidence_kind is not None
        and coerced_object_target_key is not None
        and normalized_proof_kind != UnknownRecoveryProofKind.NONE.value
    ):
        # key は元の値を渡す（`build_proof_obligation_id` が同じ `_coerce_optional_tuple` を掛ける。
        # 写しは冪等なので `coerced_object_target_key` を渡すのと同じ id）
        coerced_proof_obligation_id = build_proof_obligation_id(
            definition.reason_id,
            resolved_proof_stage,
            normalized_proof_kind,
            resolved_evidence_kind,
            object_target_key,
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
        typed_cause_key=(
            live_values.merged_mappings(typed_cause_key)
            if typed_cause_key is not None and live_values.as_bool(typed_cause_key) else None
        ),
        proof_requirement_ids=tuple(
            live_values.merged_mappings(item) for item in _elements_or_empty(proof_requirement_ids)
        ),
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
    provided_target_regression = _plain_enum_value(kwargs.pop("target_regression", None))
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
        and _plain_enum_value(projected.recovery_proof_kind) != UnknownRecoveryProofKind.NONE.value
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
            # 値の印で比べる（tuple の葉の `__eq__` を呼ばない。plain な値なら `!=` と同じ）
            and value_token(provided_proof_obligation_id) != value_token(exact_proof_obligation_id)
        ):
            raise ValueError("typed compatibility proof ID differs from exact v2 reason")
    diagnostic_cause_key: Dict[str, Any] = {}
    typed = projected.typed_cause_key
    if typed is not None and live_values.as_bool(typed):
        for key, value in live_values.items_of(typed):
            diagnostic_cause_key[_plain_text(key)] = value
    diagnostic_cause_key["authority_class"] = "LEGACY_DIAGNOSTIC"
    # `dataclasses.replace` と同じ record（field は instance の値だけで読む）
    values = _field_values(projected, _UNKNOWN_REASON_FIELDS)
    values["reason_id"] = definition.reason_id
    values["reason_class"] = projected_reason_class
    values["decision_effect"] = definition.decision_effect
    values["proof_obligation_id"] = exact_proof_obligation_id
    values["typed_cause_key"] = diagnostic_cause_key
    values["target_regression"] = definition.reason_id
    return UnknownReasonRecord(**values)


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

    # 型は `type(x)` の MRO で調べる（`isinstance` は上書きした `__class__` を読む）
    if value is None or live_values.is_kind(value, str):
        return bounded_text(value, max_chars, work=work)
    return _bounded_value(value, work=work)


def bounded_prefix(items: Any, *, work: Any, limit: int = EVIDENCE_REFS_MAX_COUNT) -> Tuple[Any, ...]:
    """列の先頭 `limit` 個を、1 つずつ有界にして引き出す（残りは件数の marker 1 つ）。

    列全体を写さない（`tuple(items)` をしない）。大きさの分かる列なら残りの件数を、分からない
    列（iterator）なら「まだある」ことだけを marker にする。文字列の要素は文字数まで、それ
    以外は有界な証拠。
    """

    from scripts.function_tracer_pcode.core.json_encoding import _walk_iter

    if items is None:
        return ()
    if live_values.is_kind(items, str) or live_values.is_kind(items, bytes):
        items = (items,)
    kept = []
    try:
        # 辿るのは walker と同じ列だけ（組み込みの振る舞いの容器・その iterator・package の
        # generator。上書きした `__iter__` を呼ばない）
        iterator = _walk_iter(items)
    except TypeError:
        # 列でない値（producer の不備）: 1 つの有界な証拠として残す
        return (_bounded_value(items, work=work),)
    more = False
    for item in iterator:
        if len(kept) >= limit:
            # 上限の次の要素が在る（大きさの分からない列の marker に使う）
            more = True
            break
        if live_values.is_kind(item, str):
            kept.append(_bounded_text(item, EVIDENCE_REF_MAX_CHARS, work=work))
        else:
            kept.append(_bounded_value(item, work=work))
    try:
        total = live_values.size(items)
    except TypeError:
        total = None
    if total is not None:
        if total > limit:
            kept.append(f"…(+{total - limit} refs)")
    elif more:
        kept.append("…(+more refs)")
    return tuple(kept)


def finitize_unknown_reason_record(record: UnknownReasonRecord, *, work: Any) -> UnknownReasonRecord:
    """legacy reason 1 件の重い field を有界な表現へ置き換える（reason id などは不変）。

    `dataclasses.replace` と同じ record を、field を instance の値だけで読んで作る（exact な型だけ）。
    """

    if type(record) is not UnknownReasonRecord:
        raise TypeError(f"{live_values.type_name(type(record))} is not an unknown reason record")
    values = _field_values(record, _UNKNOWN_REASON_FIELDS)
    values["stage"] = _bounded_text(record.stage, LABEL_MAX_CHARS, work=work)
    values["pair_or_case"] = _bounded_text(record.pair_or_case, LABEL_MAX_CHARS, work=work)
    values["detail"] = _bounded_text(record.detail, DETAIL_MAX_CHARS, work=work)
    values["object_target_key"] = _bounded_value(record.object_target_key, work=work)
    values["object_evidence"] = _bounded_value(record.object_evidence, work=work)
    values["proof_obligation_id"] = _bounded_value(record.proof_obligation_id, work=work)
    values["typed_cause_key"] = _bounded_value(
        record.typed_cause_key, work=work, inline_bytes=TYPED_CAUSE_KEY_INLINE_BYTES,
    )
    values["proof_requirement_ids"] = bounded_prefix(record.proof_requirement_ids, work=work)
    values["evidence_refs"] = bounded_prefix(record.evidence_refs, work=work)
    return UnknownReasonRecord(**values)


def finitize_unknown_recovery_action(action: UnknownRecoveryAction, *, work: Any) -> UnknownRecoveryAction:
    """recovery action 1 件の重い field を有界な表現へ置き換える（`dataclasses.replace` と同じ record）。"""

    if type(action) is not UnknownRecoveryAction:
        raise TypeError(f"{live_values.type_name(type(action))} is not an unknown recovery action")
    values = _field_values(action, _UNKNOWN_RECOVERY_ACTION_FIELDS)
    values["stage"] = _bounded_text(action.stage, LABEL_MAX_CHARS, work=work)
    values["pair_or_case"] = _bounded_text(action.pair_or_case, LABEL_MAX_CHARS, work=work)
    values["detail"] = _bounded_text(action.detail, DETAIL_MAX_CHARS, work=work)
    values["object_target_key"] = _bounded_value(action.object_target_key, work=work)
    values["object_evidence"] = _bounded_value(action.object_evidence, work=work)
    values["proof_obligation_id"] = _bounded_value(action.proof_obligation_id, work=work)
    values["evidence_refs"] = bounded_prefix(action.evidence_refs, work=work)
    values["required_evidence"] = bounded_prefix(action.required_evidence, work=work)
    return UnknownRecoveryAction(**values)


#: record / action の field の名前（`dataclasses.fields` の順。有界化は同じ型で作り直す）
_UNKNOWN_REASON_FIELDS = tuple(item.name for item in fields(UnknownReasonRecord))
_UNKNOWN_RECOVERY_ACTION_FIELDS = tuple(item.name for item in fields(UnknownRecoveryAction))


def _field_values(value: Any, names: Tuple[str, ...]) -> Dict[str, Any]:
    """dataclass の field の値（instance の値だけ。descriptor・`__getattr__` を呼ばない）。"""

    return {name: live_values.field_value(value, name) for name in names}


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
    # receipt・cause・legacy の record・名前の mapping は live_values の規則だけで読む（instance の
    # 値と package の property だけ。`__getattr__` / 上書きした `get` を呼ばない）
    reason_id = live_values.attribute(receipt, "reason_id")
    diagnostic: Dict[str, Any] = {
        "schema": "unknown-reason-diagnostic-v1",
        "reason_id": reason_id,
        "functions": {
            "function1": _name_of(function_names, "function1"),
            "function2": _name_of(function_names, "function2"),
        },
        "binaries": {
            "binary1": _name_of(binary_names, "binary1"),
            "binary2": _name_of(binary_names, "binary2"),
        },
    }
    if cause_occurrence is not None:
        cause_id = live_values.attribute(cause_occurrence, "cause_id")
        scope = live_values.attribute(cause_occurrence, "identity_scope")
        diagnostic["cause"] = {
            "occurrence_id": live_values.attribute(cause_occurrence, "occurrence_id"),
            "target_kind": live_values.attribute(cause_occurrence, "target_kind"),
            # enum は `_value_`（`value` の property を呼ばない）
            "identity_scope": (
                live_values.enum_value(scope) if live_values.is_enum(scope) else live_values.attribute(scope, "value", scope)
            ),
            "producer_id": live_values.attribute(cause_occurrence, "producer_id"),
            "evidence_kind": live_values.attribute(cause_occurrence, "evidence_kind"),
            "evidence_refs": list(bounded_prefix(
                live_values.attribute(cause_occurrence, "evidence_refs", ()), work=work,
            )),
            # Issue #22 PR-22-D: cause の key は authority が封印した canonical な値。
            # 診断には有界な表現（大きければ cause id を identity にした要約）だけを置く
            "canonical_target_key": _bounded_cause_value(
                live_values.attribute(cause_id, "canonical_target_key"), cause_id, column="canonical_target_key", work=work,
            ),
            "missing_semantic_fact": _bounded_cause_value(
                live_values.attribute(cause_id, "missing_semantic_fact"), cause_id, column="missing_semantic_fact", work=work,
            ),
        }
    matched, match_kind = _match_legacy_reasons(
        reason_id,
        cause_occurrence,
        legacy_reasons,
        projected_reason_counts or {},
        work=work,
    )
    if live_values.as_bool(matched):
        diagnostic["legacy_match"] = match_kind
        matched_count = live_values.size(matched)
        if matched_count > PROJECTION_DIAGNOSTIC_LEGACY_ROWS:
            # 診断に写す legacy の行は上限まで（件数は残す。`detail` が使うのは先頭 2 行）
            diagnostic["legacy_matched_count"] = matched_count
        # legacy の行は有界化の primitive を通して写す（G4-b で有界化済みなら何もしない。
        # 有界化していない record でも入力に比例する写しをしない）
        rows: List[Dict[str, Any]] = []
        for record in live_values.elements_of(matched):
            if len(rows) >= PROJECTION_DIAGNOSTIC_LEGACY_ROWS:
                break
            rows.append({
                "stage": _bounded_text(live_values.attribute(record, "stage"), LABEL_MAX_CHARS, work=work),
                "pair_or_case": _bounded_text(live_values.attribute(record, "pair_or_case"), LABEL_MAX_CHARS, work=work),
                "detail": _bounded_text(live_values.attribute(record, "detail"), DETAIL_MAX_CHARS, work=work),
                "evidence_refs": list(bounded_prefix(live_values.attribute(record, "evidence_refs", ()), work=work)),
                "object_target_key": _canonical_summary(
                    _bounded_value(live_values.attribute(record, "object_target_key"), work=work),
                ),
            })
        diagnostic["legacy"] = rows
    return diagnostic


def _name_of(names: Any, key: str) -> Any:
    """`(names or {}).get(key)`（組み込みの振る舞いの mapping だけ。基底型の `get` で引く）。"""

    if names is None:
        return None
    return live_values.lookup(names, key)


def _bounded_cause_value(value: Any, cause_id: Any, *, column: str, work: Any) -> Any:
    """cause の canonical な値を、小さければそのまま、大きければ cause id の要約にする。"""

    from scripts.function_tracer_pcode.authority.contracts import canonical_value
    from scripts.function_tracer_pcode.core.json_encoding import BoundedEvidence, bounded_evidence, column_identity

    if value is None:
        return None
    identity = live_values.str_value(live_values.attribute(cause_id, "value"))
    bounded = bounded_evidence(
        value, work=work,
        identity=column_identity("cause:" + identity, column) if identity is not live_values.NOT_PLAIN else None,
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
        # 索引の key は `_group_key` の plain な値（live な reason id の `__hash__` / `__eq__` を呼ばない）
        groups = self._groups
        if type(groups) is not dict:
            return None
        return groups.get(_group_key(reason_id))

    def by_reason(self, reason_id: Any) -> Tuple[Any, ...]:
        group = self.group(reason_id)
        if type(group) is not _LegacyReasonGroup:
            return ()
        records = group.records
        return tuple(records) if type(records) is list else ()


def _group_key(reason_id: Any) -> Any:
    """索引の key にする reason id（文字列はそのまま、それ以外は値で比べてよい決定的な印）。"""

    return reason_id if type(reason_id) is str else value_token(reason_id)


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
    from scripts.function_tracer_pcode.core.json_encoding import PRODUCER_FAILURES, RESULT_JSON_POLICY, builtin_view

    try:
        # 容器（tuple / list / dict）と基底型だけから成る値だけを canonical にする（producer を
        # 持つ値は canonical_value が `to_authority_dict()` を呼ぶので索引に入れない）
        # plain でないと分かるまでに辿った分も `work` へ数える（`None` で返っても作業は残る）
        size = RESULT_JSON_POLICY.plain_bytes(value, max_bytes=work.remaining(), work=work)
        if size is None:
            return None
        work.charge(1 + size)
        # canonical にするのは組み込みの値だけで書き直した写し（数え済みの plain な値と同じ形）
        ok, view = builtin_view(value)
        if not ok:
            return None
        canonical = canonical_value(view)
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

    from scripts.function_tracer_pcode.core.json_encoding import _walk_iter

    groups: Dict[Any, _LegacyReasonGroup] = {}
    truncated = live_values.as_bool(overflow)
    # 辿るのは walker と同じ列だけ（組み込みの振る舞いの容器・その iterator・package の generator）
    records = () if legacy_reasons is None else _walk_iter(legacy_reasons)
    try:
        for record in records:
            work.charge(1)
            # record は live_values の規則だけで読む（instance の値。`__getattr__` を呼ばない）
            key = _group_key(live_values.attribute(record, "reason_id"))
            group = groups.get(key)
            if group is None:
                group = groups[key] = _LegacyReasonGroup()
            position = len(group.records)
            group.records.append(record)
            target = live_values.attribute(record, "object_target_key")
            if type(target) is BoundedEvidence:
                # 要約の field は構築時に exact な str と確かめ済み（`BoundedEvidence.__post_init__`）
                fingerprint_kind = target.fingerprint_kind
                fingerprint = target.fingerprint
                if type(fingerprint_kind) is str and type(fingerprint) is str:
                    if fingerprint_kind == "canonical_sha256":
                        group.by_fingerprint.setdefault(fingerprint, []).append(position)
            elif target is not None:
                canonical = _inline_canonical(target, work=work)
                if canonical is not None:
                    group.by_target.setdefault(canonical, []).append(position)
            obligation = live_values.attribute(record, "proof_obligation_id")
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

    text = live_values.str_value(item)
    if text is not live_values.NOT_PLAIN:
        return len(text)
    return RESULT_JSON_POLICY.measure(item, max_bytes=work.remaining())


def _requirement_texts(requirements: Any, work: Any) -> frozenset:
    """cause の requirement id の文字列（cause 1 つにつき 1 回。大きさを数えてから文字列にする）。

    数えきれない・JSON にならない requirement は照合に使わない。文字列は組み込みの `str` の写し
    （上書きした `__str__` を呼ばない）。
    """

    from scripts.function_tracer_pcode.core.json_encoding import (
        JsonBudgetExhausted,
        JsonValueRejected,
        _walk_iter,
    )

    texts = set()
    for item in _walk_iter(requirements):
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
        texts.add(builtin_str(item))
    return frozenset(texts)


def _index_positions(index: Any, key: Any, work: Any) -> set:
    """索引（dict: key → 位置の list）の `key` の位置。key が plain な値でなければ空。

    key の `__hash__` / `__eq__` は組み込みの値のものだけ（`live_values.lookup` が確かめる）。索引・
    key の storage の読みは照合の作業量 `work` で数える（固定の上限を超えた分。使い切れば一致しない）。
    """

    from scripts.function_tracer_pcode.core.json_encoding import JsonBudgetExhausted

    found: set = set()
    if type(index) is not dict:
        return found
    try:
        with live_values.metered_storage_reads(work):
            positions = live_values.lookup(index, key, ())
    except (TypeError, JsonBudgetExhausted):
        # 診断の照合: 安全に引けない key と、作業量の中で引けない索引は「exact には一致しない」
        # （fingerprint の照合が引き受ける。判定には使わない）
        return found
    if type(positions) is list:
        for position in positions:
            if type(position) is int:
                found.add(position)
    return found


def _count_of(counts: Any, key: Any, work: Any) -> int:
    """`int(counts.get(key, 0) or 0)`（組み込みの mapping と plain な key だけ。それ以外は 0）。
    storage の読みは照合の作業量 `work` で数える（使い切れば 0 件）。"""

    from scripts.function_tracer_pcode.core.json_encoding import JsonBudgetExhausted

    try:
        with live_values.metered_storage_reads(work):
            value = live_values.lookup(counts, key, 0)
    except (TypeError, JsonBudgetExhausted):
        # 診断の数え上げ: 安全に引けない key / mapping と、作業量の中で引けない mapping は 0 件
        # （判定には使わない）
        return 0
    return live_values.as_int(value) if live_values.as_bool(value) else 0


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
    )

    if type(legacy_reasons) is LegacyReasonIndex:
        index = legacy_reasons
    else:
        index = legacy_reason_index(legacy_reasons, work=work)
    if type(index) is not LegacyReasonIndex:
        raise TypeError(f"{live_values.type_name(type(index))} is not a legacy reason index")
    key = _group_key(reason_id)
    group = index.group(reason_id)
    if type(group) is not _LegacyReasonGroup:
        return (), None
    records = group.records
    if type(records) is not list:
        return (), None
    if not records:
        return (), None
    # cause は live_values の規則だけで読む（instance の値。`__getattr__` を呼ばない）
    cause_id = live_values.attribute(cause_occurrence, "cause_id")
    cause_target = live_values.attribute(cause_id, "canonical_target_key") if cause_id is not None else None
    requirements = (
        live_values.attribute(cause_occurrence, "proof_requirement_ids", ())
        if cause_occurrence is not None else ()
    )
    has_requirements = requirements is not None and live_values.as_bool(requirements)

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
        # 索引は key を plain な値の間だけで比べる（cause の key が plain でなければ一致しない）
        by_target = _index_positions(group.by_target, cause_target, work)
        by_fingerprint = _index_positions(group.by_fingerprint, cause_fingerprint, work)
    by_obligation: set = set()
    obligation_index = group.by_obligation
    if has_requirements and type(obligation_index) is dict:
        if obligation_index:
            for text_value in _requirement_texts(requirements, work):
                by_obligation.update(_index_positions(obligation_index, text_value, work))
    # 旧来の規則: key が一致した record と、fingerprint で一致しなかった record のうち obligation が
    # 一致したものが exact（元の並び）、fingerprint で一致したものはその後
    exact_positions = sorted(by_target | (by_obligation - by_fingerprint))
    fingerprint_positions = sorted(by_fingerprint)
    try:
        work.charge(len(exact_positions) + len(fingerprint_positions))
    except JsonBudgetExhausted:
        pass  # 引いた位置は数え済みの索引の中（使い切りは次の照合で分かる）
    exact = [records[position] for position in exact_positions]
    by_fingerprint_records = [records[position] for position in fingerprint_positions]
    if exact or by_fingerprint_records:
        return tuple(exact) + tuple(by_fingerprint_records), (MATCH_EXACT if exact else MATCH_FINGERPRINT)
    # 1:1 は legacy の reason を全部残したときだけ（先頭だけを残したなら、残さなかった record
    # にも同じ reason id があり得る）
    if (
        not live_values.as_bool(index.truncated)
        and len(records) == 1 and _count_of(projected_reason_counts, key, work) == 1
    ):
        # 1 件だけの group（写すのは定数の大きさ。group の record 全体を照合ごとに写さない）
        return (records[0],), MATCH_UNIQUE
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
    # 型は `type(x)` で決める（`isinstance` は上書きした `__class__` を読む）。reason id は
    # `_enum_value` と同じ文字列にしてから渡す（pure layer に live な値を渡さない）
    if type(value) is UnknownReasonRecord:
        return value
    if live_values.builtin_mapping(value) is not None:
        return UnknownReasonRecord.from_dict(value)
    return make_unknown_reason(_plain_enum_value(value))


def coerce_unknown_reason_records(values: Optional[Iterable[Any]]) -> Tuple[UnknownReasonRecord, ...]:
    return tuple(coerce_unknown_reason_record(value) for value in _elements_or_empty(values))


def _elements_or_empty(values: Any) -> Iterator[Any]:
    """`values or ()` の要素（真偽と反復は live_values の規則。上書きした `__iter__` を呼ばない）。"""

    if values is None or not live_values.as_bool(values):
        return iter(())
    return live_values.elements_of(values)


def coerce_unknown_recovery_action(value: Any) -> UnknownRecoveryAction:
    if live_values.is_kind(value, UnknownRecoveryAction):
        return value
    if live_values.builtin_mapping(value) is not None:
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
        detail=_plain_text(value),
    )


def coerce_unknown_recovery_actions(values: Optional[Iterable[Any]]) -> Tuple[UnknownRecoveryAction, ...]:
    return tuple(coerce_unknown_recovery_action(value) for value in _elements_or_empty(values))


def build_unknown_recovery_actions(
    values: Optional[Iterable[Any]],
    *,
    primary_by_aggregation_unit: bool = False,
    work: Any = None,
) -> Tuple[UnknownRecoveryAction, ...]:
    return tuple(iter_unknown_recovery_actions(
        values, primary_by_aggregation_unit=primary_by_aggregation_unit, work=work,
    ))


def iter_unknown_recovery_actions(
    values: Optional[Iterable[Any]],
    *,
    primary_by_aggregation_unit: bool = False,
    work: Any = None,
):
    """`build_unknown_recovery_actions` と同じ action を 1 つずつ作る（producer 時点の構築）。

    出力の準備は `recovery_actions_source`（walk の作業量へ数える）を使う。診断（原因集計）が
    作るときは、その作業量（`work`）へ数える。
    """

    from scripts.function_tracer_pcode.core.json_encoding import JsonBudget

    # producer 時点（出力の前）の構築: 出力の行数は finitize が判定の前に schema と比べる
    return _iter_recovery_actions(
        values, primary_by_aggregation_unit=primary_by_aggregation_unit,
        work=JsonBudget(None) if work is None else work,
    )


def recovery_actions_source(
    values: Optional[Iterable[Any]],
    *,
    primary_by_aggregation_unit: bool = False,
) -> Any:
    """出力の準備用: `build_unknown_recovery_actions` と同じ action の列（walker が数えながら畳む）。

    読み飛ばす record・obligation・proof obligation id の key の写しを、作る **前** に walk の
    作業量へ数える（`scan` + `_RecoveryActions`。任意の callable を渡さない）。
    """

    from scripts.function_tracer_pcode.core.json_encoding import scan

    return scan(values, recovery_actions_reducer(primary_by_aggregation_unit))


def recovery_actions_reducer(primary_by_aggregation_unit: bool = False) -> "Reducer":
    return _RecoveryActions(primary_by_aggregation_unit)


class _RecoveryActions(Reducer):
    """`scan` の reducer: record を 1 件ずつ action へ（`build_unknown_recovery_actions` と同じ action）。

    record の読み直し・単位の key・obligation・key の写しは作る前に作業量へ数える（action の数は
    数えた obligation の数以下）。`result` は畳んだ action の列。
    """

    __slots__ = ("primary", "actions")

    def __init__(self, primary_by_aggregation_unit: bool) -> None:
        self.primary = _PrimaryFilter() if primary_by_aggregation_unit else None
        self.actions: List[UnknownRecoveryAction] = []

    def add(self, value: Any, *, work: Any) -> None:
        record = _coerce_record_within(value, work=work)
        primary = self.primary
        if primary is not None and not _PrimaryFilter.admit(primary, record, work=work):
            return
        for action in _record_actions(record, work):
            work.charge(1)
            self.actions.append(action)

    def result(self, *, work: Any) -> Any:
        from scripts.function_tracer_pcode.core.json_encoding import each

        return each(self.actions)


def _key_width(value: Any, work: Any) -> None:
    """`build_proof_obligation_id` が写す key（入れ子の list / tuple）の要素を、写す前に数える。"""

    # 辿るのは組み込みの振る舞いの list / tuple だけ（`_optional_tuple_of` が写すものと同じ）
    pending = [value]
    while pending:
        item = pending.pop()
        if live_values.builtin_sequence(item):
            work.charge(live_values.size(item) + 1)
            pending.extend(child for child in item if live_values.is_kind(child, list))
        else:
            work.charge(1)


def _optional_tuple_of(value: Any) -> Optional[Tuple[Any, ...]]:
    """`_coerce_optional_tuple` と同じ tuple を live_values の規則だけで作る（入れ子の list も tuple に）。

    辿るのは組み込みの振る舞いの list / tuple だけ（上書きした `__iter__` を呼ばない）。組み込みの
    振る舞いでない入れ子の list はそのまま置く（`_key_width` はそれを 1 つと数える）。
    """

    if value is None:
        return None
    if live_values.builtin_sequence(value):
        return tuple(
            _optional_tuple_of(item)
            if live_values.is_kind(item, list) and live_values.builtin_sequence(item) else item
            for item in value
        )
    return (value,)


def _iter_recovery_actions(
    values: Optional[Iterable[Any]], *, primary_by_aggregation_unit: bool, work: Any,
):
    """producer 時点（判定が読む action）の構築。出力の準備は `_RecoveryActions`（walker が数える）。"""

    primary = _PrimaryFilter() if primary_by_aggregation_unit else None
    for value in _elements_or_empty(values):
        # 読み飛ばす record も 1 件ずつ数える
        work.charge(1)
        record = coerce_unknown_reason_record(value)
        if primary is not None and not primary.admit(record, work=work):
            continue
        yield from _record_actions(record, work)


def _record_actions(record: "UnknownReasonRecord", work: Any):
    """record 1 件の recovery action（obligation ごとに作る前に `work` へ数える）。

    record の field は live な値として扱う: 真偽・比較・正規化は live_values の規則で読み、
    pure layer（`proof.unknown_reason`）へは正規化した文字列だけを渡す。
    """

    if type(record) is not UnknownReasonRecord:
        raise TypeError(f"{live_values.type_name(type(record))} is not an unknown reason record")
    none_kind = UnknownRecoveryProofKind.NONE.value
    obligations = record.recovery_proof_obligations
    if not live_values.as_bool(obligations):
        plan = get_unknown_recovery_plan(_plain_enum_value(record.reason_id))
        obligations = plan.proof_obligations
    if not live_values.as_bool(obligations):
        if _plain_enum_value(record.recovery_proof_kind) == none_kind:
            return
        yield (
            UnknownRecoveryAction(
                count_kind=UnknownCountKind.PROOF_ACTION.value,
                reason_id=record.reason_id,
                decision_effect=record.decision_effect,
                reason_scope=record.reason_scope,
                proof_kind=record.recovery_proof_kind,
                proof_stage=_or(record.proof_stage, "unspecified"),
                status=_or(record.action_status, UnknownRecoveryActionStatus.NO_REGISTERED_PLAN.value),
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
        return
    for obligation in live_values.elements_of(obligations):
        work.charge(1)
        obligation_kind, obligation_stage, required_evidence, description = _obligation_fields(obligation)
        proof_stage = _or(record.proof_stage, obligation_stage)
        if (
            record.proof_stage is not None
            or record.evidence_kind is not None
            or record.recovery_action is not None
        ):
            proof_kind = record.recovery_proof_kind
            if _plain_enum_value(proof_kind) == none_kind:
                proof_kind = obligation_kind
        else:
            proof_kind = obligation_kind
        evidence_kind = record.evidence_kind
        if evidence_kind is None and live_values.as_bool(required_evidence):
            evidence_kind = next(live_values.elements_of(required_evidence))
        proof_obligation_id = record.proof_obligation_id
        target = record.object_target_key
        if (
            proof_obligation_id is None
            and evidence_kind is not None
            and target is not None
        ):
            _key_width(target, work)
            # `build_proof_obligation_id` と同じ id（部分を live_values の規則で正規化してから組む）
            proof_obligation_id = _proof_obligation_id(
                normalize_unknown_reason_id(_plain_enum_value(record.reason_id)),
                _text_or(proof_stage, UNKNOWN_TUPLE_MISSING),
                normalize_recovery_proof_kind(_plain_enum_value(proof_kind)) or none_kind,
                _text_or(evidence_kind, UNKNOWN_TUPLE_MISSING),
                _optional_tuple_of(target),
            )
        yield (
            UnknownRecoveryAction(
                count_kind=UnknownCountKind.PROOF_ACTION.value,
                reason_id=record.reason_id,
                decision_effect=record.decision_effect,
                reason_scope=record.reason_scope,
                proof_kind=proof_kind,
                proof_stage=proof_stage,
                status=_or(record.action_status, UnknownRecoveryActionStatus.PLANNED.value),
                aggregation_unit=record.aggregation_unit,
                stage=record.stage,
                pair_or_case=record.pair_or_case,
                required_evidence=required_evidence,
                evidence_refs=record.evidence_refs,
                evidence_kind=evidence_kind,
                object_target_key=target,
                object_evidence=record.object_evidence,
                proof_obligation_id=proof_obligation_id,
                recovery_action=record.recovery_action,
                target_regression=record.target_regression,
                detail=_or(description, record.detail),
            )
        )


def _obligation_fields(obligation: Any) -> Tuple[Any, Any, Any, Any]:
    """recovery proof obligation の (proof_kind, proof_stage, required_evidence, description)。

    exact な `UnknownRecoveryProofObligation` は field をそのまま、それ以外は live_values の規則で読む。
    """

    if type(obligation) is UnknownRecoveryProofObligation:
        return obligation.proof_kind, obligation.proof_stage, obligation.required_evidence, obligation.description
    return (
        live_values.attribute(obligation, "proof_kind"),
        live_values.attribute(obligation, "proof_stage"),
        live_values.attribute(obligation, "required_evidence", ()),
        live_values.attribute(obligation, "description"),
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
        from scripts.function_tracer_pcode.core.json_encoding import hashable_key

        if type(record) is not UnknownReasonRecord:
            raise TypeError(f"{live_values.type_name(type(record))} is not an unknown reason record")
        # 真偽は live_values の規則で読む（上書きした `__bool__` / `__len__` を呼ばない）
        aggregation_key = builtin_str(_or(record.aggregation_unit, UnknownAggregationUnit.RESULT.value))
        unit_key = _or(record.pair_or_case, record.stage)
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

    if type(value) is dict:
        work.charge(1 + RESULT_JSON_POLICY.measure(value, max_bytes=work.remaining(), mode=LEGACY))
        record = UnknownReasonRecord.from_dict(value)
    elif type(value) is str:
        work.charge(len(value))
        record = make_unknown_reason(value)
    else:
        record = value
    # 型は `type(x)` で決める（`isinstance` は上書きした `__class__` を読む）
    if type(record) is not UnknownReasonRecord:
        raise TypeError(f"{live_values.type_name(type(record))} is not an unknown reason record")
    return record


class _ReasonCounts(Reducer):
    """`scan` の reducer: `summarize_unknown_reason_counts` と同じ件数（reason id の初出順）。"""

    __slots__ = ("primary", "counts")

    def __init__(self, primary_by_aggregation_unit: bool) -> None:
        self.primary = _PrimaryFilter() if primary_by_aggregation_unit else None
        self.counts: Dict[str, int] = {}

    def add(self, value: Any, *, work: Any) -> None:
        from scripts.function_tracer_pcode.core.json_encoding import hashable_key

        record = _coerce_record_within(value, work=work)
        primary = self.primary
        if primary is not None and not _PrimaryFilter.admit(primary, record, work=work):
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

    return scan(values, unknown_reason_counts_reducer(primary_by_aggregation_unit))


def unknown_reason_counts_reducer(primary_by_aggregation_unit: bool = False) -> "Reducer":
    return _ReasonCounts(primary_by_aggregation_unit)


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
        if type(record) is not UnknownReasonRecord:
            raise TypeError(f"{live_values.type_name(type(record))} is not an unknown reason record")
        obligations = record.recovery_proof_obligations
        # 辿る obligation の数を先に数える（record の列は組み込みの振る舞いの列だけ）
        work.charge(live_values.size(obligations))
        none_kind = UnknownRecoveryProofKind.NONE.value
        if self.count == 0:
            self.target_regression = record.target_regression
            self.recovery_proof_kind = record.recovery_proof_kind
        else:
            if self.target_regression is None:
                self.target_regression = record.target_regression
            if (
                _plain_enum_value(self.recovery_proof_kind) == none_kind
                and _plain_enum_value(record.recovery_proof_kind) != none_kind
            ):
                self.recovery_proof_kind = record.recovery_proof_kind
        self.count += 1
        for obligation in live_values.elements_of(obligations):
            proof_kind, proof_stage, _required, _description = _obligation_fields(obligation)
            # 件数・重複の key は plain な値だけ（live な値の `__hash__` / `__eq__` を呼ばない）
            kind_key = _group_key(proof_kind)
            self._kind_counts[kind_key] = self._kind_counts.get(kind_key, 0) + 1
            key = (kind_key, _group_key(proof_stage))
            if key not in self._distinct_keys:
                self._distinct_keys.add(key)
                self._distinct.append(obligation)

    @live_values.readable_property
    def proof_obligation_counts(self) -> Any:
        from scripts.function_tracer_pcode.core.json_encoding import pairs_of

        return pairs_of(live_values.items_of(self._kind_counts))

    @live_values.readable_property
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
        primary = self.primary
        if primary is not None and not _PrimaryFilter.admit(primary, record, work=work):
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

    return scan(values, recovery_backlog_reducer(primary_by_aggregation_unit))


def recovery_backlog_reducer(primary_by_aggregation_unit: bool = False) -> "Reducer":
    return _RecoveryBacklog(primary_by_aggregation_unit)
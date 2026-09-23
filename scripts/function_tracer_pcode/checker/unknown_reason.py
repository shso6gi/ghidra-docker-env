# -*- coding: utf-8 -*-
"""Typed UNKNOWN reason schema and registry."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace
from typing import Any, Dict, Iterable, Mapping, Optional, Sequence, Tuple

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
    row_items,
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


def _optional_dict(value: Any) -> Any:
    return as_dict(value) if value else None


def _dict_items(values: Any) -> Any:
    return each(values, as_dict)


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
    Column("typed_cause_key", EVIDENCE, legacy=_optional_dict),
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
# * key / evidence（`object_target_key` / `object_evidence` / `proof_obligation_id` /
#   `typed_cause_key` / `proof_requirement_ids` の各要素）: 小さければそのまま、大きければ
#   `BoundedEvidence`（DAG-aware な Merkle digest + distinct な node 数 + 種類）。照合用に
#   `canonical_value` の digest を 2 つ付ける（`authority` = Merkle digest、`canonical_str`
#   = `str(canonical_value(...))` の sha256）。
# * 自由文（`detail` / `stage` / `pair_or_case`）: 行 schema の文字数まで（超えた分は
#   明示の marker）。


#: 照合用 digest の名前
MATCH_AUTHORITY_DIGEST = "authority"
MATCH_CANONICAL_STR_DIGEST = "canonical_str"


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


#: `canonical_str` digest（文字列の id との照合）で木として辿る event の上限
_CANONICAL_STR_MAX_EVENTS = 1 << 20


def bounded_match_evidence(value: Any) -> Any:
    """`value` が大きければ照合用 digest つきの `BoundedEvidence`、小さければ `value`。

    identity は `canonical_value` の形の **DAG-aware な Merkle digest**（共有部分を 1 回
    だけ辿る）で、distinct な node の数も持つ。照合用 digest は 2 つ: `authority`（同じ
    Merkle digest。等しさ ⇔ `canonical_value` の `==`）と `canonical_str`（文字列の id
    との照合。辿る数が上限を超える値には付けない）。
    """

    from scripts.function_tracer_pcode.authority.contracts import (
        CanonicalWalkLimitExceeded,
        streaming_canonical_str_digest,
    )
    from scripts.function_tracer_pcode.core.canonical_digest import canonical_merkle_digest
    from scripts.function_tracer_pcode.core.json_encoding import (
        EVIDENCE_INLINE_BYTES,
        LEGACY,
        RESULT_JSON_POLICY,
        BoundedEvidence,
        JsonBudgetExhausted,
        evidence_kind,
    )

    if value is None or type(value) is BoundedEvidence:
        return value
    try:
        RESULT_JSON_POLICY.measure(value, max_bytes=EVIDENCE_INLINE_BYTES, mode=LEGACY)
        return value
    except JsonBudgetExhausted:
        pass
    kind = evidence_kind(value)
    try:
        merkle, distinct = canonical_merkle_digest(value)
    except (TypeError, UnicodeError):
        # authority の値にならない証拠（Expression など）は照合に使えない: 型つき token の digest
        summary = RESULT_JSON_POLICY.bounded_evidence(value)
        return BoundedEvidence(
            identity=summary.identity, identity_kind=summary.identity_kind, kind=kind,
        )
    digests = [(MATCH_AUTHORITY_DIGEST, merkle)]
    try:
        digests.append((
            MATCH_CANONICAL_STR_DIGEST,
            streaming_canonical_str_digest(value, max_events=_CANONICAL_STR_MAX_EVENTS),
        ))
    except (CanonicalWalkLimitExceeded, UnicodeError):
        pass
    return BoundedEvidence(
        identity=merkle,
        identity_kind="canonical_merkle_sha256",
        kind=kind,
        match_digests=tuple(digests),
        distinct_nodes=distinct,
    )


def match_digest(value: Any, name: str) -> Optional[str]:
    """照合用 digest（有界化した証拠なら付けた値、それ以外は今求める）。"""

    from scripts.function_tracer_pcode.authority.contracts import (
        CanonicalWalkLimitExceeded,
        streaming_canonical_str_digest,
    )
    from scripts.function_tracer_pcode.core.canonical_digest import canonical_merkle_digest
    from scripts.function_tracer_pcode.core.json_encoding import BoundedEvidence

    if value is None:
        return None
    if type(value) is BoundedEvidence:
        return value.match_digest(name)
    try:
        if name == MATCH_AUTHORITY_DIGEST:
            return canonical_merkle_digest(value)[0]
        return streaming_canonical_str_digest(value, max_events=_CANONICAL_STR_MAX_EVENTS)
    except (TypeError, UnicodeError, CanonicalWalkLimitExceeded):
        return None


def _bounded_text(value: Any, max_chars: int) -> Any:
    from scripts.function_tracer_pcode.core.json_encoding import bounded_text

    return bounded_text(value, max_chars)


def finitize_unknown_reason_record(record: UnknownReasonRecord) -> UnknownReasonRecord:
    """legacy reason 1 件の重い field を有界な表現へ置き換える（reason id などは不変）。"""

    return replace(
        record,
        stage=_bounded_text(record.stage, LABEL_MAX_CHARS),
        pair_or_case=_bounded_text(record.pair_or_case, LABEL_MAX_CHARS),
        detail=_bounded_text(record.detail, DETAIL_MAX_CHARS),
        object_target_key=bounded_match_evidence(record.object_target_key),
        object_evidence=bounded_match_evidence(record.object_evidence),
        proof_obligation_id=bounded_match_evidence(record.proof_obligation_id),
        typed_cause_key=bounded_match_evidence(record.typed_cause_key),
        proof_requirement_ids=tuple(
            bounded_match_evidence(item) for item in record.proof_requirement_ids
        ),
    )


def finitize_unknown_recovery_action(action: UnknownRecoveryAction) -> UnknownRecoveryAction:
    """recovery action 1 件の重い field を有界な表現へ置き換える。"""

    return replace(
        action,
        stage=_bounded_text(action.stage, LABEL_MAX_CHARS),
        pair_or_case=_bounded_text(action.pair_or_case, LABEL_MAX_CHARS),
        detail=_bounded_text(action.detail, DETAIL_MAX_CHARS),
        object_target_key=bounded_match_evidence(action.object_target_key),
        object_evidence=bounded_match_evidence(action.object_evidence),
        proof_obligation_id=bounded_match_evidence(action.proof_obligation_id),
    )


def build_projection_diagnostic(
    receipt: Any,
    *,
    cause_occurrence: Any = None,
    legacy_reasons: Sequence[Any] = (),
    function_names: Mapping[str, Any] = None,
    binary_names: Mapping[str, Any] = None,
    projected_reason_counts: Mapping[str, int] = None,
) -> Dict[str, Any]:
    """Human-readable, machine-aggregatable facts for one projected v2 cause.

    The projected record only carried digests (Issue #17).  This collects, in
    priority order, the typed cause occurrence (what semantic fact is missing,
    on which target kind and scope, from which producer site), the matching
    legacy strategy reason (site / case pair / free-text detail), and the
    function/binary names of the compared pair.  It is diagnostic data, not
    authority: no digest or receipt is derived from it.
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
            "evidence_refs": list(getattr(cause_occurrence, "evidence_refs", ()) or ()),
            # Issue #22 PR-22-D: cause の key は authority が封印した canonical な値。
            # 診断には有界な表現（大きければ cause id を identity にした要約）だけを置く
            "canonical_target_key": _bounded_cause_value(
                getattr(cause_id, "canonical_target_key", None), cause_id,
            ),
            "missing_semantic_fact": _bounded_cause_value(
                getattr(cause_id, "missing_semantic_fact", None), cause_id,
            ),
        }
    matched, match_kind = _match_legacy_reasons(
        diagnostic["reason_id"],
        cause_occurrence,
        legacy_reasons,
        projected_reason_counts or {},
    )
    if matched:
        diagnostic["legacy_match"] = match_kind
        diagnostic["legacy"] = [
            {
                "stage": getattr(record, "stage", None),
                "pair_or_case": getattr(record, "pair_or_case", None),
                "detail": getattr(record, "detail", None),
                "evidence_refs": list(getattr(record, "evidence_refs", ()) or ()),
                "object_target_key": canonical_value(getattr(record, "object_target_key", None)),
            }
            for record in matched
        ]
    return diagnostic


def _bounded_cause_value(value: Any, cause_id: Any) -> Any:
    """cause の canonical な値を、小さければそのまま、大きければ cause id の要約にする。"""

    from scripts.function_tracer_pcode.authority.contracts import canonical_value
    from scripts.function_tracer_pcode.core.json_encoding import (
        EVIDENCE_INLINE_BYTES,
        LEGACY,
        RESULT_JSON_POLICY,
        BoundedEvidence,
        JsonBudgetExhausted,
    )

    if value is None:
        return None
    try:
        RESULT_JSON_POLICY.measure(value, max_bytes=EVIDENCE_INLINE_BYTES, mode=LEGACY)
    except JsonBudgetExhausted:
        identity = getattr(cause_id, "value", None)
        summary = RESULT_JSON_POLICY.bounded_evidence(
            value, identity=("cause:" + identity) if isinstance(identity, str) else None,
        )
        return summary if type(summary) is BoundedEvidence else canonical_value(value)
    return canonical_value(value)


def _match_legacy_reasons(
    reason_id: Any,
    cause_occurrence: Any,
    legacy_reasons: Sequence[Any],
    projected_reason_counts: Mapping[str, int],
) -> Tuple[Tuple[Any, ...], Optional[str]]:
    """Pick the legacy records that describe *this* cause, never a sibling site.

    1. exact: the legacy ``object_target_key`` equals the cause's canonical
       target key (SAT-safety and other producers emit the record's key as the
       cause target), or the legacy proof obligation / evidence refs equal the
       cause's proof requirement ids / evidence refs.
    2. unique: no exact key is available, but the reason id has exactly one
       legacy record and exactly one projected cause, so the correspondence is
       1:1 by construction.
    Otherwise nothing is attached; the typed cause occurrence alone is used.

    Issue #22 PR-22-D: 等しさは ``canonical_value`` の digest で比べる（legacy の key は
    authority 前に有界化され、照合用 digest だけを持つ。cause の key も写しを作らずに
    digest する）。digest の等しさは ``canonical_value`` の等しさと同じ関係。
    """

    candidates = tuple(
        record for record in (legacy_reasons or ())
        if getattr(record, "reason_id", None) == reason_id
    )
    if not candidates:
        return (), None
    cause_id = getattr(cause_occurrence, "cause_id", None)
    cause_target = (
        match_digest(getattr(cause_id, "canonical_target_key", None), MATCH_AUTHORITY_DIGEST)
        if cause_id is not None else None
    )
    cause_requirements = set(getattr(cause_occurrence, "proof_requirement_ids", ()) or ()) if cause_occurrence is not None else set()
    requirement_digests = {
        hashlib.sha256(str(item).encode("utf-8")).hexdigest() for item in cause_requirements
    }
    exact = []
    for record in candidates:
        record_target = match_digest(
            getattr(record, "object_target_key", None), MATCH_AUTHORITY_DIGEST,
        )
        if cause_target is not None and record_target is not None and record_target == cause_target:
            exact.append(record)
            continue
        record_obligation = getattr(record, "proof_obligation_id", None)
        if record_obligation is not None and requirement_digests and match_digest(
            record_obligation, MATCH_CANONICAL_STR_DIGEST,
        ) in requirement_digests:
            exact.append(record)
            continue
    if exact:
        return tuple(exact), "exact"
    if len(candidates) == 1 and int(projected_reason_counts.get(reason_id, 0) or 0) == 1:
        return candidates, "unique"
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
    cause_id = getattr(cause_occurrence, "cause_id", None)
    if cause_id is not None:
        return getattr(cause_id, "canonical_target_key", None)
    return (diagnostic.get("cause") or {}).get("canonical_target_key") if diagnostic else None


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
    """`build_unknown_recovery_actions` と同じ action を 1 つずつ作る（出力の準備が引き出す）。"""

    records = coerce_unknown_reason_records(values)
    if primary_by_aggregation_unit:
        records = _select_primary_records_by_aggregation_unit(records)
    for record in records:
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


def _primary_or_all(values: Optional[Iterable[Any]], primary_by_aggregation_unit: bool):
    records = coerce_unknown_reason_records(values)
    if primary_by_aggregation_unit:
        records = _select_primary_records_by_aggregation_unit(records)
    return records


def _first_seen_reason_ids(records: Sequence[UnknownReasonRecord]):
    seen = set()
    for record in records:
        if record.reason_id not in seen:
            seen.add(record.reason_id)
            yield record.reason_id


def unknown_reason_counts_source(
    values: Optional[Iterable[Any]],
    *,
    primary_by_aggregation_unit: bool = False,
) -> Any:
    """`summarize_unknown_reason_counts` と同じ object を key ごとに作る source。"""

    from scripts.function_tracer_pcode.core.json_encoding import pairs_of

    records = _primary_or_all(values, primary_by_aggregation_unit)
    return pairs_of(
        (reason_id, sum(1 for record in records if record.reason_id == reason_id))
        for reason_id in _first_seen_reason_ids(records)
    )


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

    件数・代表値は record を 1 回数えて決め、obligation の件数と列は walker が
    引き出すときに 1 つずつ作る。
    """

    __slots__ = ("_records", "count", "target_regression", "recovery_proof_kind")

    def __init__(self, records: Sequence[UnknownReasonRecord], reason_id: str) -> None:
        self._records = tuple(record for record in records if record.reason_id == reason_id)
        self.count = len(self._records)
        self.target_regression = None
        self.recovery_proof_kind = None
        for index, record in enumerate(self._records):
            if index == 0:
                self.target_regression = record.target_regression
                self.recovery_proof_kind = record.recovery_proof_kind
                continue
            if self.target_regression is None:
                self.target_regression = record.target_regression
            if (
                self.recovery_proof_kind == UnknownRecoveryProofKind.NONE.value
                and record.recovery_proof_kind != UnknownRecoveryProofKind.NONE.value
            ):
                self.recovery_proof_kind = record.recovery_proof_kind

    @property
    def proof_obligation_counts(self) -> Any:
        from scripts.function_tracer_pcode.core.json_encoding import pairs_of

        def kinds():
            seen = set()
            for record in self._records:
                for obligation in record.recovery_proof_obligations:
                    if obligation.proof_kind not in seen:
                        seen.add(obligation.proof_kind)
                        yield obligation.proof_kind

        return pairs_of(
            (
                kind,
                sum(
                    1
                    for record in self._records
                    for obligation in record.recovery_proof_obligations
                    if obligation.proof_kind == kind
                ),
            )
            for kind in kinds()
        )

    @property
    def proof_obligations(self) -> Any:
        from scripts.function_tracer_pcode.core.json_encoding import each

        def distinct():
            seen = set()
            for record in self._records:
                for obligation in record.recovery_proof_obligations:
                    key = (obligation.proof_kind, obligation.proof_stage)
                    if key not in seen:
                        seen.add(key)
                        yield obligation

        return each(distinct())

    def json_items(self):
        return row_items(RECOVERY_BACKLOG_ENTRY_ROW, self)


def recovery_backlog_source(
    values: Optional[Iterable[Any]],
    *,
    primary_by_aggregation_unit: bool = False,
) -> Any:
    """`summarize_unknown_recovery_backlog` と同じ object を reason id ごとに作る source。

    出力では entry は行の schema（`RECOVERY_BACKLOG_ENTRY_ROW`）で有界になる。entry の数は
    reason の行数以下。
    """

    from scripts.function_tracer_pcode.core.json_encoding import pairs_of

    records = _primary_or_all(values, primary_by_aggregation_unit)
    return pairs_of(
        (reason_id, _BacklogEntryView(records, reason_id))
        for reason_id in _first_seen_reason_ids(records)
    )
# -*- coding: utf-8 -*-
"""結果 JSON の authority 後 field（B / C）の大きさの契約（Issue #22 PR-22-D）。

出力の準備（authority 確定 **前**）は、authority 確定 **後** に足される field のために
`BudgetPolicy.envelope_headroom_bytes` を空けておく。その値が足りることは **この
schema から導く**:

```text
required = Σ B field の上限（固定 field + 最大行数 × 行の上限 + receipt）
         + Σ C field の上限（切り詰めない値 + 切り詰めてよい診断の marker）
         + object の framing（これらの member の key と区切り）
```

* 行の上限は各 record の行 schema（`core/json_encoding.Column` の列）から求める
  （`row_max_bytes`）。reason / action の行は列ごとに上限を持つ（語彙・自由文は文字数、
  key / evidence は有界な証拠）。
* 最大行数（`MAX_*_ROWS`）は authority が 1 pair で出してよい件数の契約。超えた出力は
  切り詰めず、出力の契約違反（`OutputEnvelopeInvariantViolation`）になる。
* B の field は準備のたびに **その field の上限** を上限にして準備する（schema を
  破る値は headroom が余っていても違反）。

`envelope_headroom_bytes >= required_headroom_bytes()` は checker の構築時に確かめる
（`validate_envelope_headroom`）。field を足すときはここへ上限を 1 行足す — authority・
identity・solver 側は変わらない（M-3）。

finalization bundle（`canonical_result_finalization_bundle`）は preimage（A + B + C）
全体の digest を持つ封印で、payload の予算の **外** に付ける attachment（大きさの
上限は authority の event stream の契約、#110）。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.core.json_encoding import (
    EVIDENCE_INLINE_BYTES,
    INT_MAX_BYTES,
    RESULT_JSON_POLICY,
    TEXT,
    TEXT_MARKER_MAX_CHARS,
    Column,
    JsonEncodingPolicy,
    row_max_bytes,
)
from scripts.function_tracer_pcode.checker.unknown_reason import (
    ID_MAX_CHARS,
    LABEL_MAX_CHARS,
    RECOVERY_BACKLOG_ENTRY_ROW,
    UNKNOWN_REASON_ROW,
    UNKNOWN_RECOVERY_ACTION_ROW,
    VOCAB_MAX_CHARS,
)


#: authority が 1 pair で出してよい canonical reason の行数（実測の最大 23 の 11 倍）
MAX_UNKNOWN_REASON_ROWS = 256
#: recovery action の行数（実測の最大 6。reason 1 件から複数 action が出るので reason と同じ上限）
MAX_RECOVERY_ACTION_ROWS = 256
#: relation（`c_active_base` / `q_open_base`）の行数（実測の最大 28 の 18 倍）
MAX_RELATION_ROWS = 512
#: conditional receipt が運ぶ仮定（premise）の数と 1 つの上限
MAX_ASSUMPTION_PREMISES = 64
ASSUMPTION_PREMISE_MAX_BYTES = 4096
#: 失敗の自由文（`error_message` / `failure_message`）の文字数
MESSAGE_MAX_CHARS = 2048


def _text_bytes(policy: JsonEncodingPolicy, max_chars: int) -> int:
    return max(4, policy.max_string_bytes(max_chars + TEXT_MARKER_MAX_CHARS))


def _array_bytes(policy: JsonEncodingPolicy, rows: int, row_bytes: int) -> int:
    return policy.container_frame_bytes(rows) + rows * row_bytes


def _object_bytes(policy: JsonEncodingPolicy, members: Mapping[str, int]) -> int:
    return policy.object_bytes(
        policy.member_bytes(key, size) for key, size in members.items()
    )


#: relation 行の列（authority の sealed dataclass の field。すべて id / 語彙の文字列）
C_ACTIVE_BASE_ROW = tuple(
    Column(name, TEXT, ID_MAX_CHARS)
    for name in (
        "result_occurrence_id", "occurrence_id", "cause_id", "reason_id",
        "domain", "decision_effect", "target_kind",
    )
)
Q_OPEN_BASE_ROW = tuple(
    Column(name, TEXT, ID_MAX_CHARS)
    for name in (
        "result_occurrence_id", "occurrence_id", "cause_id",
        "proof_requirement_id", "proof_kind", "semantic_target_digest",
    )
)
#: `decision_receipt_payload` の列
DECISION_RECEIPT_ROW = tuple(
    Column(name, TEXT, ID_MAX_CHARS)
    for name in (
        "result_occurrence_id", "outcome", "lifecycle_projection_digest",
        "authority_input_digest", "receipt_digest",
    )
)
#: `conditional_decision_receipt_payload` の固定の列（`assumption_set` は別に数える）
CONDITIONAL_RECEIPT_FIXED_ROW = tuple(
    Column(name, TEXT, ID_MAX_CHARS)
    for name in (
        "result_occurrence_id", "conditional_outcome", "unconditional_outcome",
        "unconditional_receipt_digest", "lifecycle_projection_digest",
        "assumption_set_digest", "authority_input_digest", "receipt_digest",
    )
)


@dataclass(frozen=True)
class FieldBound:
    """B / C の 1 field の出力上の上限（JSON byte）と、その導き方。

    `max_rows` は行の列の field（reason・relation など）の最大行数。`rows_attr` はその
    行を持つ結果の属性（行数は準備の前に数える）。
    """

    key: str
    max_bytes: int
    derivation: str
    max_rows: Optional[int] = None
    rows_attr: Optional[str] = None


class OutputSchemaMissing(KeyError):
    """出力 field に schema の上限が無い（field を足したら `output_schema` にも 1 行足す）。"""


def _truncation_marker_max_bytes(policy: JsonEncodingPolicy, key: str) -> int:
    """`output_preparation._truncation_marker` の上限（切り詰めた診断の代わりの値）。"""

    return _object_bytes(policy, {
        "truncated": 5,
        "field": policy.string_bytes(key),
        "reason": _text_bytes(policy, VOCAB_MAX_CHARS),
        "exceeded_bytes": INT_MAX_BYTES,
        "original_items": INT_MAX_BYTES,
        "rejected_at": policy.max_string_bytes(200),
    })


def authority_field_bounds(policy: JsonEncodingPolicy = RESULT_JSON_POLICY) -> Dict[str, FieldBound]:
    """B の field ごとの上限（`RESULT_FIELDS` の B と 1 対 1。bundle は payload の外）。"""

    reason_row = row_max_bytes(UNKNOWN_REASON_ROW, policy)
    action_row = row_max_bytes(UNKNOWN_RECOVERY_ACTION_ROW, policy)
    backlog_entry = row_max_bytes(RECOVERY_BACKLOG_ENTRY_ROW, policy)
    conditional_receipt = (
        row_max_bytes(CONDITIONAL_RECEIPT_FIXED_ROW, policy)
        + policy.member_bytes("assumption_set", _array_bytes(
            policy, MAX_ASSUMPTION_PREMISES, ASSUMPTION_PREMISE_MAX_BYTES,
        ))
    )
    rows = (
        FieldBound("is_equivalent", 5, "bool / null"),
        FieldBound("error_message", _text_bytes(policy, MESSAGE_MAX_CHARS),
                   f"text ≤ {MESSAGE_MAX_CHARS} chars + marker"),
        FieldBound("failure_status", _text_bytes(policy, VOCAB_MAX_CHARS), "vocabulary"),
        FieldBound("failure_message", _text_bytes(policy, MESSAGE_MAX_CHARS),
                   f"text ≤ {MESSAGE_MAX_CHARS} chars + marker"),
        FieldBound("is_timeout", 5, "bool"),
        FieldBound("final_outcome", _text_bytes(policy, VOCAB_MAX_CHARS), "vocabulary"),
        FieldBound("decision_receipt", row_max_bytes(DECISION_RECEIPT_ROW, policy),
                   "decision receipt row"),
        FieldBound("conditional_outcome", _text_bytes(policy, VOCAB_MAX_CHARS), "vocabulary"),
        FieldBound("conditional_decision_receipt", conditional_receipt,
                   f"fixed row + ≤ {MAX_ASSUMPTION_PREMISES} premises × "
                   f"{ASSUMPTION_PREMISE_MAX_BYTES} B"),
        FieldBound("c_active_base", _array_bytes(
            policy, MAX_RELATION_ROWS, row_max_bytes(C_ACTIVE_BASE_ROW, policy),
        ), f"≤ {MAX_RELATION_ROWS} relation rows",
            max_rows=MAX_RELATION_ROWS, rows_attr="canonical_c_active_base"),
        FieldBound("q_open_base", _array_bytes(
            policy, MAX_RELATION_ROWS, row_max_bytes(Q_OPEN_BASE_ROW, policy),
        ), f"≤ {MAX_RELATION_ROWS} relation rows",
            max_rows=MAX_RELATION_ROWS, rows_attr="canonical_q_open_base"),
        FieldBound("unknown_reasons", _array_bytes(
            policy, MAX_UNKNOWN_REASON_ROWS, reason_row,
        ), f"≤ {MAX_UNKNOWN_REASON_ROWS} reason rows × {reason_row} B",
            max_rows=MAX_UNKNOWN_REASON_ROWS, rows_attr="unknown_reasons"),
        FieldBound("unknown_recovery_actions", _array_bytes(
            policy, MAX_RECOVERY_ACTION_ROWS, action_row,
        ), f"≤ {MAX_RECOVERY_ACTION_ROWS} action rows × {action_row} B",
            max_rows=MAX_RECOVERY_ACTION_ROWS, rows_attr="unknown_recovery_actions"),
        FieldBound("unknown_recovery_backlog", policy.container_frame_bytes(
            MAX_UNKNOWN_REASON_ROWS,
        ) + MAX_UNKNOWN_REASON_ROWS * policy.max_member_bytes(ID_MAX_CHARS, backlog_entry),
            f"≤ {MAX_UNKNOWN_REASON_ROWS} reason ids × backlog entry {backlog_entry} B"),
        FieldBound("decision_gated_by_pending_proof", 5, "bool"),
    )
    return {row.key: row for row in rows}


def metadata_field_bounds(policy: JsonEncodingPolicy = RESULT_JSON_POLICY) -> Dict[str, FieldBound]:
    """C の field ごとの上限。切り詰めてよい診断は marker の上限（残りの予算で本体を出す）。"""

    identity = policy.container_frame_bytes(2) + 2 * policy.max_string_bytes(ID_MAX_CHARS)
    rows = [
        FieldBound("binary1_content_identity", identity, "(algorithm, digest)"),
        FieldBound("binary2_content_identity", identity, "(algorithm, digest)"),
        FieldBound("total_time", 24, "float"),
    ]
    for key in (
        "pairwise_stats", "pairwise_debug_stats", "stage_path", "diagnostics",
        "unknown_cause_aggregate",
    ):
        rows.append(FieldBound(
            key, _truncation_marker_max_bytes(policy, key), "truncation marker at least",
        ))
    return {row.key: row for row in rows}


def required_headroom_bytes(policy: JsonEncodingPolicy = RESULT_JSON_POLICY) -> int:
    """authority 確定後の field が必ず収まるのに要る headroom（schema から導く）。

    A の object に B / C の member を足したときに増える byte（区切り・key・値の上限）。
    """

    bounds = {**authority_field_bounds(policy), **metadata_field_bounds(policy)}
    return sum(
        policy.added_member_bytes(key, bound.max_bytes) for key, bound in bounds.items()
    )


class EnvelopeHeadroomTooSmall(ValueError):
    """設定した headroom が出力 schema から導いた最小値より小さい（設定の誤り）。"""


def validate_envelope_headroom(budget_policy, policy: JsonEncodingPolicy = RESULT_JSON_POLICY) -> None:
    """`budget_policy.envelope_headroom_bytes >= required_headroom_bytes()` を確かめる。

    直列化の予算が無制限なら headroom は使わない（どれだけでも収まる）。
    """

    if budget_policy.prepared_payload_limit() is None:
        return
    required = required_headroom_bytes(policy)
    configured = int(budget_policy.envelope_headroom_bytes)
    if configured < required:
        raise EnvelopeHeadroomTooSmall(
            f"envelope headroom {configured} bytes is below the {required} bytes "
            "the authority/metadata output schema requires"
        )


def schema_diagnostic(policy: JsonEncodingPolicy = RESULT_JSON_POLICY) -> Dict[str, object]:
    """schema から導いた上限の内訳（診断・PR の説明用）。"""

    return {
        "required_headroom_bytes": required_headroom_bytes(policy),
        "authority": {key: bound.max_bytes for key, bound in authority_field_bounds(policy).items()},
        "metadata": {key: bound.max_bytes for key, bound in metadata_field_bounds(policy).items()},
        "evidence_inline_bytes": EVIDENCE_INLINE_BYTES,
        "label_max_chars": LABEL_MAX_CHARS,
    }


__all__ = [
    "ASSUMPTION_PREMISE_MAX_BYTES",
    "C_ACTIVE_BASE_ROW",
    "CONDITIONAL_RECEIPT_FIXED_ROW",
    "DECISION_RECEIPT_ROW",
    "EnvelopeHeadroomTooSmall",
    "FieldBound",
    "MAX_ASSUMPTION_PREMISES",
    "MAX_RECOVERY_ACTION_ROWS",
    "MAX_RELATION_ROWS",
    "MAX_UNKNOWN_REASON_ROWS",
    "MESSAGE_MAX_CHARS",
    "OutputSchemaMissing",
    "Q_OPEN_BASE_ROW",
    "authority_field_bounds",
    "metadata_field_bounds",
    "required_headroom_bytes",
    "schema_diagnostic",
    "validate_envelope_headroom",
]

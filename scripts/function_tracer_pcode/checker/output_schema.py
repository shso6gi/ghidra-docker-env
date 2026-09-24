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
* 最大行数（`MAX_*_ROWS`）は field の byte 上限を導く parameter（行数そのものは数えない）。
  強制するのは field の **byte 上限**: B の field は準備のたびにその上限を上限にして準備し
  （headroom が余っていても超えれば違反。切り詰めない）、authority 確定前に分かる field
  （recovery action、pilot 無しの reason）は G4-b で同じ上限と比べて、超えれば判定の前に
  限界にする（`output_preparation.check_prepared_field_bounds`）。

`envelope_headroom_bytes >= required_headroom_bytes()` は checker の構築時に確かめる
（`validate_envelope_headroom`）。field を足すときはここへ上限を 1 行足す — authority・
identity・solver 側は変わらない（M-3）。

finalization bundle（`canonical_result_finalization_bundle`）は preimage（A + B + C）
全体の digest を持つ receipt で、最終 JSON の予算の **中** にある（切り詰めない）。その大きさの
上限は authority の event stream の契約（#110）が無いと schema から導けないので、headroom は
bundle 以外の field だけを予約し、bundle は最終 envelope の残りに収まるかを出力時に確かめる。
"""

from __future__ import annotations

from dataclasses import dataclass, fields
from typing import Dict, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.authority.contracts import CActiveBaseRow, QOpenBaseRow

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


#: authority が 1 pair で出してよい canonical reason の行数（固定 subset の実測の最大 34 の 7.5 倍。
#: main `b302389` を merge した後の値）
MAX_UNKNOWN_REASON_ROWS = 256
#: recovery action の行数（実測の最大 6。reason 1 件から複数 action が出るので reason と同じ上限）
MAX_RECOVERY_ACTION_ROWS = 256
#: relation（`c_active_base` / `q_open_base`）の行数（同じく実測の最大 34 の 15 倍）
MAX_RELATION_ROWS = 512
#: conditional receipt が運ぶ仮定（premise）の数と 1 つの上限: receipt の契約の owner
#: （`authority/decision/conditional`）の値。lane は発行の前に同じ上限で確かめる
from scripts.function_tracer_pcode.authority.decision.conditional import (  # noqa: E402
    ASSUMPTION_PREMISE_MAX_BYTES,
    MAX_ASSUMPTION_PREMISES,
)
#: 失敗の自由文（`error_message` / `failure_message`）の文字数
MESSAGE_MAX_CHARS = 2048
#: 切り詰めた診断の marker に残す、JSON にならない値を拒んだ場所（path）の文字数
MARKER_PATH_MAX_CHARS = 200


def _text_bytes(policy: JsonEncodingPolicy, max_chars: int) -> int:
    return max(4, policy.max_string_bytes(max_chars + TEXT_MARKER_MAX_CHARS))


def _array_bytes(policy: JsonEncodingPolicy, rows: int, row_bytes: int) -> int:
    return policy.container_frame_bytes(rows) + rows * row_bytes


def _object_bytes(policy: JsonEncodingPolicy, members: Mapping[str, int]) -> int:
    return policy.object_bytes(
        policy.member_bytes(key, size) for key, size in members.items()
    )


def _relation_row(row_type: type) -> Tuple[Column, ...]:
    """relation 行の列を authority の sealed dataclass の field から作る（写し書きしない）。

    field はすべて id / 語彙の exact str（`__post_init__` が型を確かめる）。field を足すと
    この行と上限が自動で追従する（出力 schema の変更は 0 行）。
    """

    return tuple(
        Column(item.name, TEXT, ID_MAX_CHARS)
        for item in fields(row_type) if not item.name.startswith("_")
    )


C_ACTIVE_BASE_ROW = _relation_row(CActiveBaseRow)
Q_OPEN_BASE_ROW = _relation_row(QOpenBaseRow)
#: `decision_receipt_payload` の列（key の一致は `tests/unit/test_issue22d_compositional_boundedness`
#: が本物の receipt の payload と照らして固定する）
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

    `max_rows` は行の列の field（reason・relation など）の最大行数（`max_bytes` を導く
    parameter。強制するのは `max_bytes`）。`rows_attr` はその行を持つ結果の属性。
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
        "rejected_at": policy.max_string_bytes(MARKER_PATH_MAX_CHARS),
    })


def authority_field_bounds(policy: JsonEncodingPolicy = RESULT_JSON_POLICY) -> Dict[str, FieldBound]:
    """B の field ごとの上限（`RESULT_FIELDS` の B と 1 対 1。bundle を除く）。

    finalization bundle は authority の event stream を持つ receipt で、その大きさの上限は
    event stream の契約（#110）が無いと schema から導けない。headroom は bundle 以外の B と
    C の上限だけを予約し、bundle は最終 envelope の残りの予算に収まるかを出力時に確かめる
    （収まらなければ出力の契約違反の ERROR。`output_preparation.build_final_result_envelope`）。
    """

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
        FieldBound("superseded_decision_receipt", _object_bytes(policy, {
            "decision_receipt": row_max_bytes(DECISION_RECEIPT_ROW, policy),
            "conditional_decision_receipt": conditional_receipt,
        }), "{decision receipt row, conditional receipt} (output-contract ERROR only)"),
    )
    return {row.key: row for row in rows}


def metadata_field_bounds(policy: JsonEncodingPolicy = RESULT_JSON_POLICY) -> Dict[str, FieldBound]:
    """C の field ごとの上限。切り詰めてよい診断は marker の上限（残りの予算で本体を出す）。"""

    from scripts.function_tracer_pcode.checker.output_preparation import (
        RESULT_FIELDS,
        FieldOwner,
        Overflow,
    )

    identity = policy.container_frame_bytes(2) + 2 * policy.max_string_bytes(ID_MAX_CHARS)
    invariant = {
        "binary1_content_identity": FieldBound("binary1_content_identity", identity, "(algorithm, digest)"),
        "binary2_content_identity": FieldBound("binary2_content_identity", identity, "(algorithm, digest)"),
        "total_time": FieldBound("total_time", 24, "float"),
    }
    rows: Dict[str, FieldBound] = {}
    for item in RESULT_FIELDS:
        if item.owner is not FieldOwner.METADATA:
            continue
        if item.overflow is Overflow.TRUNCATE:
            # 切り詰めてよい診断: 予約するのは marker の分（本体は残りの予算で出す）
            rows[item.key] = FieldBound(
                item.key, _truncation_marker_max_bytes(policy, item.key), "truncation marker",
            )
        else:
            bound = invariant.get(item.key)
            if bound is None:
                raise OutputSchemaMissing(
                    f"{item.key} is an untruncatable metadata field without a schema bound"
                )
            rows[item.key] = bound
    return rows


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
    "validate_envelope_headroom",
]

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
from typing import Any, Dict, Mapping, Optional, Tuple

from scripts.function_tracer_pcode.authority.contracts import CActiveBaseRow, QOpenBaseRow

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.json_encoding import (
    EVIDENCE_INLINE_BYTES,
    INT_MAX_BYTES,
    RESULT_JSON_POLICY,
    TEXT,
    TEXT_MARKER_MAX_CHARS,
    builtin_str,
    text_value_max_bytes,
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


#: 行数の上限の owner は authority の event の契約（Issue #110: authority は 1 pair の cause occurrence と
#: relation の行を、event を作る時点でこの上限の中に抑える）。出力の schema はその値を読むだけ
from scripts.function_tracer_pcode.authority.event_contract import (  # noqa: E402
    AUTHORITY_EVENT_CONTRACT as _AUTHORITY_EVENT_CONTRACT,
)

#: authority が 1 pair で出してよい canonical reason の行数（cause occurrence の上限）
MAX_UNKNOWN_REASON_ROWS = _AUTHORITY_EVENT_CONTRACT.max_cause_occurrences
#: recovery action の行数（固定 subset の実測の最大 6）。action はそのまま出力の行になるので、上限を
#: 超える列は切り詰めず、G4-b（`finitize_legacy_reasons`）が判定の前に pair terminal な限界にする。
#: 数値は canonical reason の行と同じ契約の値を使う（action ごとの別の上限の owner を作らない）
MAX_RECOVERY_ACTION_ROWS = MAX_UNKNOWN_REASON_ROWS
#: relation（`c_active_base` / `q_open_base`）の行数（relation の行の上限）
MAX_RELATION_ROWS = _AUTHORITY_EVENT_CONTRACT.max_relation_rows
#: conditional receipt が運ぶ仮定（premise）の数と 1 つの上限: receipt の契約の owner
#: （`authority/decision/conditional`）の値。lane は発行の前に同じ上限で確かめる
from scripts.function_tracer_pcode.authority.decision.conditional import (  # noqa: E402
    CONDITIONAL_RECEIPT_FIXED_FIELDS,
    assumption_premise_max_bytes,
    max_assumption_premises,
)
#: 失敗の自由文（`error_message` / `failure_message`）の文字数
MESSAGE_MAX_CHARS = 2048
#: 切り詰めた診断の marker に残す、JSON にならない値を拒んだ場所（path）の文字数
MARKER_PATH_MAX_CHARS = 200


def _text_bytes(policy: JsonEncodingPolicy, max_chars: int) -> int:
    return text_value_max_bytes(policy, max_chars)


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
#: `conditional_decision_receipt_payload` の固定の列（名前は receipt の owner の
#: `CONDITIONAL_RECEIPT_FIXED_FIELDS`。`assumption_set` は別に数える）
CONDITIONAL_RECEIPT_FIXED_ROW = tuple(Column(name, TEXT, ID_MAX_CHARS) for name in CONDITIONAL_RECEIPT_FIXED_FIELDS)


def conditional_receipt_max_bytes(policy: JsonEncodingPolicy) -> int:
    """conditional receipt の payload 1 つの byte の上限（固定の列 + 仮定の集合。member 9 つの object）。"""

    members = [policy.member_bytes(column.key, column.max_value_bytes(policy)) for column in CONDITIONAL_RECEIPT_FIXED_ROW]
    members.append(policy.member_bytes("assumption_set", _array_bytes(
        policy, max_assumption_premises(), assumption_premise_max_bytes(),
    )))
    return policy.object_bytes(members)


#: `superseded_decision_receipt_record` の、receipt を写せなかったときの形の語彙の上限
SUPERSEDED_UNAVAILABLE_MAX_CHARS = 64


def superseded_decision_receipt_record(result: Any) -> Optional[Dict[str, Any]]:
    """出力の契約違反の ERROR が持つ、取って代わられた判定（無条件と conditional の receipt）。

    receipt の payload を作れない（exact な receipt でない・検証に落ちる）ときは、receipt の
    digest と作れなかった理由の型名だけの形（`superseded_digest_record`）。**例外を上げない**:
    ERROR の出力はこれに依存するので、元の出力の失敗と同じ失敗を繰り返さない。
    """

    from scripts.function_tracer_pcode.authority.decision.conditional import (
        conditional_decision_receipt_payload,
    )
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        decision_receipt_payload,
    )

    # 結果は live_values の規則だけで読む（instance の値と package の property。`__getattr__` を
    # 呼ばない）。receipt の payload は receipt の owner が exact な型を確かめてから作る
    receipt = live_values.attribute(result, "decision_receipt")
    if receipt is None:
        return None
    from scripts.function_tracer_pcode.authority.decision.conditional import ConditionalDecisionReceipt
    from scripts.function_tracer_pcode.authority.decision.decision import DecisionReceipt

    try:
        # receipt の owner へは exact な receipt の型だけを渡す（それ以外は作れなかった形）
        if type(receipt) is not DecisionReceipt:
            raise TypeError("superseded decision receipt is not an exact DecisionReceipt")
        record: Dict[str, Any] = {"decision_receipt": decision_receipt_payload(receipt)}
        conditional = live_values.attribute(result, "conditional_decision_receipt")
        if conditional is not None:
            if type(conditional) is not ConditionalDecisionReceipt:
                raise TypeError("superseded conditional receipt is not an exact ConditionalDecisionReceipt")
            record["conditional_decision_receipt"] = conditional_decision_receipt_payload(conditional)
        return record
    except SUPERSEDED_PAYLOAD_FAILURES as exc:
        return superseded_digest_record(result, unavailable=live_values.type_name(type(exc)))


#: receipt の payload を作るときの失敗（exact でない receipt・検証の失敗・壊れた値）
SUPERSEDED_PAYLOAD_FAILURES = (TypeError, ValueError, AttributeError, LookupError, ArithmeticError, RuntimeError)


def superseded_digest_record(result: Any, *, unavailable: str) -> Dict[str, Any]:
    """取って代わられた判定の receipt の digest だけの形（固定長。payload を作らない）。"""

    receipt = live_values.attribute(result, "decision_receipt")
    digest = live_values.attribute(receipt, "receipt_digest") if receipt is not None else None
    if type(digest) is str:
        if len(digest) > ID_MAX_CHARS:
            digest = None
    else:
        digest = None
    return {
        "decision_receipt_digest": digest,
        "payload_unavailable": builtin_str(unavailable)[:SUPERSEDED_UNAVAILABLE_MAX_CHARS],
    }


def _superseded_max_bytes(policy: JsonEncodingPolicy) -> int:
    full = _object_bytes(policy, {
        "decision_receipt": row_max_bytes(DECISION_RECEIPT_ROW, policy),
        "conditional_decision_receipt": conditional_receipt_max_bytes(policy),
    })
    digest_only = _object_bytes(policy, {
        "decision_receipt_digest": policy.max_string_bytes(ID_MAX_CHARS),
        "payload_unavailable": policy.max_string_bytes(SUPERSEDED_UNAVAILABLE_MAX_CHARS),
    })
    return max(full, digest_only)


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
    #: 同じ結果で同時には値を持たない field の組の名前（headroom は組の中の最大の値だけを予約し、
    #: 他は `null` の分。出力の準備が「組の中で値を持つのは高々 1 つ」を確かめる）
    exclusive_group: Optional[str] = None


#: 確定した判定の conditional receipt と、出力の契約違反の ERROR が持つ取って代わられた receipt は
#: 同じ結果に同時には現れない（ERROR の結果は conditional receipt を持たない）
RECEIPT_VARIANT = "receipt_variant"


class OutputSchemaMissing(KeyError):
    """出力 field に schema の上限が無い（field を足したら `output_schema` にも 1 行足す）。"""


def truncation_marker_max_bytes(policy: JsonEncodingPolicy, key: str) -> int:
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
    conditional_receipt = conditional_receipt_max_bytes(policy)
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
                   f"fixed row + ≤ {max_assumption_premises()} premises × "
                   f"{assumption_premise_max_bytes()} B", exclusive_group=RECEIPT_VARIANT),
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
        FieldBound("superseded_decision_receipt", _superseded_max_bytes(policy),
                   "{decision receipt row, conditional receipt} or {receipt digest, reason} "
                   "(output-contract ERROR only)", exclusive_group=RECEIPT_VARIANT),
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
                item.key, truncation_marker_max_bytes(policy, item.key), "truncation marker",
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
    total = 0
    extra: Dict[str, int] = {}
    for key, bound in bounds.items():
        added = policy.added_member_bytes(key, bound.max_bytes)
        if bound.exclusive_group is None:
            total += added
            continue
        # 同時に値を持たない field の組: どの field も `null` で出得るので `null` の分を足し、
        # 値を持つ高々 1 つの分（値と `null` の差）は組の中の最大だけを予約する
        null = policy.added_member_bytes(key, 4)
        total += null
        extra[bound.exclusive_group] = max(extra.get(bound.exclusive_group, 0), added - null)
    return total + sum(extra.values())


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
    "C_ACTIVE_BASE_ROW",
    "CONDITIONAL_RECEIPT_FIXED_ROW",
    "DECISION_RECEIPT_ROW",
    "EnvelopeHeadroomTooSmall",
    "FieldBound",
    "MAX_RECOVERY_ACTION_ROWS",
    "MAX_RELATION_ROWS",
    "MAX_UNKNOWN_REASON_ROWS",
    "MESSAGE_MAX_CHARS",
    "OutputSchemaMissing",
    "Q_OPEN_BASE_ROW",
    "SUPERSEDED_PAYLOAD_FAILURES",
    "authority_field_bounds",
    "conditional_receipt_max_bytes",
    "metadata_field_bounds",
    "superseded_decision_receipt_record",
    "superseded_digest_record",
    "truncation_marker_max_bytes",
    "required_headroom_bytes",
    "validate_envelope_headroom",
]

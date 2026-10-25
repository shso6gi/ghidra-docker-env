# -*- coding: utf-8 -*-
"""評価 wrapper の契約の唯一の置き場所（評価計画 v2 PR-D、標準 library だけ）。

``eval/summarize.py``（読み取り専用の container の中で応答を作る側）と ``eval/wrapper.py``
（host で応答を受理し、判断する側）の両方がここを読む。契約を 2 箇所で解釈させない。

**1. 完了の判定の理由と分類**（``REASONS``）

分類は「この評価（同じ出力先・同じ条件）が正式な完了に到達できるか」で決める:

==============  ===========================================================================
分類            意味
==============  ===========================================================================
resumable       同じ条件で runner を再び動かせば進む（出力先が無い・連鎖が OPEN・full verdict が無い・
                最新の execution の commit が HEAD と照合できない）
blocking        この評価への運用の操作（``stop`` での回収）が先に要る。操作の後は続けられる
permanent       この評価は正式な完了に到達できない。記録は残し、別の評価（別の ``--tag``）として
                始め直す
unverifiable    判定できない（読めない・壊れている・観測していない）
==============  ===========================================================================

``start`` の決定（``start_decision``）は優先順位で決まる。理由の組合せは問わない:
COMPLETE → 何もしない／unverifiable・permanent・blocking・未知の分類が 1 つでもある → 拒否
（permanent は「別の評価として」）／resumable だけ → 再開。

**2. reader の応答の受理**（``accept``）

reader（使い捨ての container で動く ``summarize.py``）の応答は、**要求ごとに決めた終了コードと、
その要求に対応する応答の形の両方** を満たすときだけ受理する。どちらかを欠く応答・途中で切れた
応答・判定できない応答は ``Rejected``。呼び出し側は受理しなかった応答から何も確定しない（記録しない、
container を消さない）。
"""

from __future__ import annotations

import json
from typing import Any, Callable, Dict, Iterable, Mapping, Optional, Tuple

# ---------------------------------------------------------------------------
# 完了の判定
# ---------------------------------------------------------------------------

VERDICT_COMPLETE = "COMPLETE"
VERDICT_INCOMPLETE = "INCOMPLETE"
VERDICT_UNVERIFIABLE = "UNVERIFIABLE"
VERDICTS = (VERDICT_COMPLETE, VERDICT_INCOMPLETE, VERDICT_UNVERIFIABLE)
EXIT_BY_VERDICT = {VERDICT_COMPLETE: 0, VERDICT_INCOMPLETE: 1, VERDICT_UNVERIFIABLE: 2}

RESUMABLE = "resumable"
BLOCKING = "blocking"
PERMANENT = "permanent"
UNVERIFIABLE = "unverifiable"
CATEGORIES = (RESUMABLE, BLOCKING, PERMANENT, UNVERIFIABLE)

#: 理由 code → 分類（唯一の登録表。completion はここから分類を引く）。
REASONS: Dict[str, str] = {
    "output_absent": RESUMABLE,
    "chain_open": RESUMABLE,
    "no_full_verdict": RESUMABLE,
    # ledger の HEAD の照合（最新の execution が記録した commit と dirty）。start は worktree が
    # clean で HEAD が freeze であることを先に確かめるので、次の execution はその commit を記録し、
    # 照合は進む（worktree が違えば start の preflight が別に拒否する）。
    "head_mismatch": RESUMABLE,
    "container_present": BLOCKING,
    "unfinished_launch": BLOCKING,
    # 別の条件で動いた execution の開始の記録は消えないので、検証器はこの出力先を CLOSED に
    # しない（execution_conditions_differ）。走らせても直らない。
    "foreign_execution": PERMANENT,
    # container の終了を観測できなかった launch の証拠は、後から得られない。
    "exit_unobserved": PERMANENT,
    "meta_unreadable": UNVERIFIABLE,
    "container_unobserved": UNVERIFIABLE,
    "records_damaged": UNVERIFIABLE,
    "execution_attribution": UNVERIFIABLE,
    "source_digest_unreadable": UNVERIFIABLE,
    "verify_failed": UNVERIFIABLE,
    "start_records_unreadable": UNVERIFIABLE,
    "ledger_failed": UNVERIFIABLE,
}

DECISION_COMPLETE = "complete"
DECISION_LAUNCH = "launch"
DECISION_REFUSE = "refuse"


def verdict_of(categories: Iterable[str]) -> str:
    categories = set(categories)
    if UNVERIFIABLE in categories or not categories <= set(CATEGORIES):
        return VERDICT_UNVERIFIABLE
    return VERDICT_INCOMPLETE if categories else VERDICT_COMPLETE


def start_decision(completion: Optional[Mapping[str, Any]]) -> Tuple[str, str]:
    """``(complete | launch | refuse, 説明)``。completion の verdict と理由の分類だけを見る。"""
    if completion is None:
        return DECISION_LAUNCH, "first launch"
    verdict = completion.get("verdict")
    reasons = list(completion.get("reasons") or [])
    text = "; ".join(f"{r.get('code')}: {r.get('detail')}" for r in reasons)
    categories = {r.get("category") for r in reasons}
    if verdict == VERDICT_COMPLETE and not reasons:
        return DECISION_COMPLETE, ""
    if verdict != VERDICT_INCOMPLETE or UNVERIFIABLE in categories:
        return DECISION_REFUSE, f"the evaluation cannot be judged ({verdict}): {text}"
    if not categories <= set(CATEGORIES):
        return DECISION_REFUSE, f"unknown reason categories {sorted(map(str, categories))}: {text}"
    if PERMANENT in categories:
        return DECISION_REFUSE, (
            "this evaluation can never become formally complete; its records are kept. Start a "
            f"separate evaluation (another --tag) instead: {text}")
    if BLOCKING in categories:
        return DECISION_REFUSE, f"resolve these first (for example `stop`): {text}"
    return DECISION_LAUNCH, text


# ---------------------------------------------------------------------------
# reader の応答の契約
# ---------------------------------------------------------------------------

COMPLETION_SCHEMA = "eval-completion-v1"
SUMMARY_SCHEMA = "eval-summary-v2"
EVIDENCE_SCHEMA = "eval-launch-evidence-v1"
VERIFY_SCHEMA = "eval-verify-v1"

UNTERMINATED_KINDS = ("concluded_incomplete", "interrupted_running", "unreadable_receipt")


class Rejected(ValueError):
    """受理しなかった応答（終了コードか形が契約に合わない）。"""


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise Rejected(message)


def validate_reasons(value: Any) -> None:
    _require(isinstance(value, dict), "not an object")
    _require(value.get("verdict") in VERDICTS, f"verdict {value.get('verdict')!r}")
    reasons = value.get("reasons")
    _require(isinstance(reasons, list), "reasons is not a list")
    for item in reasons:
        _require(isinstance(item, dict) and isinstance(item.get("detail"), str),
                 f"malformed reason {item!r}")
        _require(REASONS.get(item.get("code")) == item.get("category"),
                 f"reason {item.get('code')!r} is not registered as {item.get('category')!r}")
    _require(verdict_of(item["category"] for item in reasons) == value["verdict"],
             "the verdict does not follow from the reasons")


def validate_completion(value: Any) -> None:
    validate_reasons(value)
    _require(value.get("schema") == COMPLETION_SCHEMA, f"schema {value.get('schema')!r}")


def validate_summary(value: Any) -> None:
    validate_reasons(value)
    _require(value.get("schema") == SUMMARY_SCHEMA, f"schema {value.get('schema')!r}")
    _require(isinstance(value.get("report_errors"), list), "report_errors is not a list")


def validate_evidence(value: Any) -> None:
    _require(isinstance(value, dict), "not an object")
    _require(value.get("schema") == EVIDENCE_SCHEMA, f"schema {value.get('schema')!r}")
    _require(isinstance(value.get("captured_at_epoch"), (int, float)), "no capture time")
    rows = value.get("unterminated_pairs")
    _require(isinstance(rows, list), "unterminated_pairs is not a list")
    for row in rows:
        _require(isinstance(row, dict) and isinstance(row.get("pair"), str)
                 and row.get("kind") in UNTERMINATED_KINDS, f"malformed pair row {row!r}")
    _require(value.get("verify") is None or isinstance(value.get("verify"), dict),
             "verify is not an object")
    _require(value.get("verify") is not None or isinstance(value.get("verify_error"), str),
             "neither a verify result nor its error")


def validate_verify(value: Any) -> None:
    _require(isinstance(value, dict), "not an object")
    _require(value.get("schema") == VERIFY_SCHEMA, f"schema {value.get('schema')!r}")
    _require(isinstance(value.get("verify"), dict) or isinstance(value.get("verify_error"), str),
             "neither a verify result nor its error")


def summary_exit_code(value: Mapping[str, Any]) -> int:
    """``report`` の終了コード: 集計の欄が作れなければ 2、それ以外は verdict から。"""
    if value.get("report_errors"):
        return EXIT_BY_VERDICT[VERDICT_UNVERIFIABLE]
    return EXIT_BY_VERDICT[value["verdict"]]


#: 要求 → (受理する終了コード, 応答の形の検査, 終了コードと内容の整合)
CONTRACTS: Dict[str, Tuple[frozenset, Callable[[Any], None],
                           Optional[Callable[[Any], int]]]] = {
    "completion": (frozenset({0}), validate_completion, None),
    "launch-evidence": (frozenset({0}), validate_evidence, None),
    "verify": (frozenset({0}), validate_verify, None),
    "report": (frozenset({0, 1, 2}), validate_summary, summary_exit_code),
}


def accept(request: str, returncode: Any, stdout: str) -> Dict[str, Any]:
    """reader の応答を受理する（終了コードと形の両方）。受理しなければ ``Rejected``。"""
    codes, validate, expected_code = CONTRACTS[request]
    _require(returncode in codes, f"{request} exited {returncode}")
    try:
        value = json.loads(stdout)
    except ValueError as exc:
        raise Rejected(f"{request} output is not JSON ({exc})")
    validate(value)
    if expected_code is not None:
        _require(expected_code(value) == returncode,
                 f"{request} exited {returncode} but its result says {expected_code(value)}")
    return value

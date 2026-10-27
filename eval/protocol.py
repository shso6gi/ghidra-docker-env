# -*- coding: utf-8 -*-
"""評価 wrapper の契約の唯一の置き場所（評価計画 v2 PR-D、標準 library だけ）。

``eval/summarize.py``（読み取り専用の container の中で応答を作る側）と ``eval/wrapper.py``
（host で応答を受理し、判断する側）の両方がここを読む。契約を 2 箇所で解釈させない。

**1. 完了の判定の理由と分類**（``REASONS``）

分類は「この評価（同じ出力先・同じ条件）が正式な完了に到達できるか」で決める:

==============  ===========================================================================
分類            意味
==============  ===========================================================================
resumable       同じ条件で runner を再び動かせば進む（出力先が無い・連鎖が OPEN で理由がすべて次の
                execution が書き直すもの（``CHAIN_REASONS_REWRITTEN_BY_RESUME``）・full verdict が無い・
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
    # 評価がまだ始まっていない（wrapper の記録も出力も無い、または出力が空）。
    "evaluation_not_started": RESUMABLE,
    "output_absent": RESUMABLE,
    # 出力が、開始の記録を残す前に止まった execution のものだけ（start が退避して新規に始める）。
    "output_never_started": RESUMABLE,
    # 検証器が OPEN と言った理由のうち、次の execution が書き直すものだけ（下の CHAIN_REASONS）。
    "chain_open": RESUMABLE,
    # 検証器が OPEN と言った理由のうち、どの execution も書き直さない確定した証跡によるもの
    # （再開しても CLOSED にならない）。全件の処理を再開させない。
    "chain_blocked_by_evidence": PERMANENT,
    # 検証器の理由が下の分類表に無い（分類されていない新しい理由は再開の根拠にしない）。
    "chain_reason_unclassified": UNVERIFIABLE,
    # pair の binary と build receipt が食い違い、再開で直るかがどちらの側が違うかで決まる。
    "chain_inputs_disagree": UNVERIFIABLE,
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
    # 出力に wrapper の記録が無い（この wrapper が始めた評価ではない）。
    "output_without_records": PERMANENT,
    # 出力の開始の記録が、今の worktree と別の analysis source のもの。
    "source_differs": PERMANENT,
    # launch・container が、この評価の条件（meta の fingerprint）と別の条件で要求・起動された。
    "launch_conditions_differ": PERMANENT,
    # meta.json が無い（wrapper の dir はある）・読めない・形が違う・要約が条件と合わない。
    "meta_invalid": UNVERIFIABLE,
    # 出力の確定した証跡（execution の開始・issue・seal の記録）が欠けている・壊れている・
    # 未知の entry がある（``execution_chain.read_chain_records`` の分類）。退避も再開もしない。
    "output_damaged": UNVERIFIABLE,
    "container_unobserved": UNVERIFIABLE,
    "records_damaged": UNVERIFIABLE,
    "execution_attribution": UNVERIFIABLE,
    "source_digest_unreadable": UNVERIFIABLE,
    "verify_failed": UNVERIFIABLE,
    "start_records_unreadable": UNVERIFIABLE,
    "ledger_failed": UNVERIFIABLE,
}

#: 実行の連鎖の検証器（``reporting.execution_chain.verify_execution_chain``）の OPEN の理由を、
#: 同じ条件で runner を再開したとき次の execution が直すかで分ける（検証器の条件はそのまま）。
#: 根拠は次の execution の振る舞い（runner と ``pair_status_authority`` の再開の判定）:
#:
#: * 次の execution は top level の manifest・publication・receipt・seal を書き直し、
#:   ``prior_executions`` と census を出力の記録から作り直す（latest / publication の理由）。
#: * pair は ``pair_status_file_skip_decision`` が SKIP と言うもの（署名・期待した target・
#:   正規の終端）だけを再利用し、それ以外（未決定・壊れた・別の target）は再実行して
#:   上書きする。
#: * execution の記録（開始・issue・seal）は確定したら消えない。再利用の判定は帰属（issue の
#:   記録）と build receipt との一致を見ないので、帰属できない・同じ nonce の issue が複数ある・
#:   build receipt と食い違う status は再利用され、同じ理由が残る。開始の条件の違う execution の
#:   開始の記録も残る。
#:
#: 分類表に無い理由は再開の根拠にしない（``chain_reason_unclassified``）。
CHAIN_REASONS_REWRITTEN_BY_RESUME = frozenset({
    "latest_publication_invalid", "publication_has_no_execution_chain",
    "latest_execution_binding_failed", "latest_start_record_missing_or_differs",
    "latest_execution_seal_missing_or_differs", "prior_executions_differ_from_records",
    "pair_census_inconsistent", "pair_status_not_decided", "pair_target_identity_differs",
    "pair_status_path_differs_from_target", "executed_pair_not_produced_by_latest_execution",
    "reused_pair_produced_by_latest_execution", "reused_pair_evidence_differs",
})
CHAIN_REASONS_FROM_EVIDENCE = frozenset({
    "unrecognised_execution_record", "execution_has_no_start_record", "execution_record_damaged",
    "sealed_execution_invalid", "execution_conditions_differ",
    "pair_status_not_attributed_to_an_execution", "execution_nonce_issued_more_than_once",
    "producing_execution_has_no_start_record",
})
#: どちらの側が違うかで変わる: pair の binary の sha と publication の build receipt が食い違う。
#: status の側が違えば期待した target と一致せず再実行で直り、build receipt の側が違えば
#: （#279）status は再利用されて残る。どちらとも確定できないので再開の根拠にしない。
CHAIN_REASONS_DEPEND_ON_INPUTS = frozenset({"binary_sha_differs_from_build_receipt"})
#: 読めなかった（判定できない）。
CHAIN_REASONS_UNOBSERVED = frozenset({"execution_records_unreadable"})
CHAIN_REASON_KINDS = (("rewritten", CHAIN_REASONS_REWRITTEN_BY_RESUME),
                      ("evidence", CHAIN_REASONS_FROM_EVIDENCE),
                      ("inputs", CHAIN_REASONS_DEPEND_ON_INPUTS),
                      ("unobserved", CHAIN_REASONS_UNOBSERVED))


def classify_chain_reasons(reasons: Iterable[str]) -> Dict[str, list]:
    """検証器の OPEN の理由を ``CHAIN_REASON_KINDS`` の種類と ``unclassified`` に分ける。"""
    result: Dict[str, list] = {kind: [] for kind, _codes in CHAIN_REASON_KINDS}
    result["unclassified"] = []
    for reason in sorted(set(reasons)):
        kind = next((k for k, codes in CHAIN_REASON_KINDS if reason in codes), "unclassified")
        result[kind].append(reason)
    return result


#: completion が必ず実施する検査（実施した ``done`` か、該当しない理由付きの ``not_applicable``）。
#: どれかが欠けた応答は受理しない: 呼び出し側が特別な経路で検査を省略できないようにする。
MANDATORY_CHECKS = ("meta", "container", "records", "permanent", "conditions", "attribution",
                    "output", "chain", "fingerprints", "source", "ledger")
CHECK_DONE = "done"
CHECK_NOT_APPLICABLE = "not_applicable"

#: 出力の状態（``records.classify_output`` が ``execution_chain.read_chain_records`` の分類から
#: 決める）。退避してよいのは ``never_started`` だけで、再開してよいかは決めない。
OUTPUT_ABSENT = "absent"
OUTPUT_EMPTY = "empty"
OUTPUT_NEVER_STARTED = "never_started"
OUTPUT_STARTED = "started"
OUTPUT_DAMAGED = "damaged"
OUTPUT_STATES = (OUTPUT_ABSENT, OUTPUT_EMPTY, OUTPUT_NEVER_STARTED, OUTPUT_STARTED,
                 OUTPUT_DAMAGED)

DECISION_COMPLETE = "complete"
DECISION_LAUNCH = "launch"
DECISION_REFUSE = "refuse"


def verdict_of(categories: Iterable[str]) -> str:
    categories = set(categories)
    if UNVERIFIABLE in categories or not categories <= set(CATEGORIES):
        return VERDICT_UNVERIFIABLE
    return VERDICT_INCOMPLETE if categories else VERDICT_COMPLETE


def start_decision(completion: Any) -> Tuple[str, str]:
    """``(complete | launch | refuse, 説明)``。completion の verdict と理由の分類だけを見る。

    入力は ``completion`` の応答の契約（必須の検査をすべて含む）を満たさなければならない。
    省略（``None``）や一部だけの判定は受け付けず、拒否する: 初回や退避対象の出力も、同じ
    completion を経て決める。
    """
    try:
        validate_completion(completion)
    except Rejected as exc:
        return DECISION_REFUSE, f"no complete judgement of the evaluation was given ({exc})"
    verdict = completion.get("verdict")
    reasons = list(completion.get("reasons") or [])
    text = "; ".join(f"{r.get('code')}: {r.get('detail')}" for r in reasons)
    categories = {r.get("category") for r in reasons}
    if verdict == VERDICT_COMPLETE and not reasons:
        return DECISION_COMPLETE, ""
    # 未知の分類は validate_completion（登録表との照合）が上で拒否している。
    if verdict != VERDICT_INCOMPLETE or UNVERIFIABLE in categories:
        return DECISION_REFUSE, f"the evaluation cannot be judged ({verdict}): {text}"
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


def validate_checks(value: Any) -> None:
    """必須の検査がすべて実施（または該当なしと明示）され、出力の状態が報告されていること。"""
    checks = value.get("checks")
    _require(isinstance(checks, dict), "checks is not an object")
    missing = [name for name in MANDATORY_CHECKS if name not in checks]
    _require(not missing, f"mandatory checks missing: {missing}")
    for name in MANDATORY_CHECKS:
        entry = checks[name]
        _require(isinstance(entry, dict) and entry.get("status") in (CHECK_DONE, CHECK_NOT_APPLICABLE),
                 f"check {name} has no status")
        if entry["status"] == CHECK_NOT_APPLICABLE:
            _require(isinstance(entry.get("because"), str) and entry["because"],
                     f"check {name} is not applicable without a reason")
    _require(value.get("output_state") in OUTPUT_STATES,
             f"output_state {value.get('output_state')!r}")


def validate_completion(value: Any) -> None:
    validate_reasons(value)
    _require(value.get("schema") == COMPLETION_SCHEMA, f"schema {value.get('schema')!r}")
    validate_checks(value)


def validate_summary(value: Any) -> None:
    validate_reasons(value)
    _require(value.get("schema") == SUMMARY_SCHEMA, f"schema {value.get('schema')!r}")
    validate_checks(value)
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

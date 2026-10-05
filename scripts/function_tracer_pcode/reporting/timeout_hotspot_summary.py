# -*- coding: utf-8 -*-
"""TIMEOUT pair の `timeout_kind` と hotspot を集計する（Issue #124 PR-124-C）。

読むのは **run dir に残る file だけ**なので、`process_authority_cleanup` の後でも
run 終了後でも同じ結果が再現できる。

| 入力 | 何に使うか |
|---|---|
| `<pair>.pair-status.json` | 最終 outcome と supervisor の終了証拠（P） |
| `<pair>.log` の結果 JSON | 子の canonical bundle（S）。検証してから使う |
| `<pair>.stage.jsonl` | 最後に完了した stage / 進行中の stage |
| `.runtime-metrics/<pair>.stack-dump.txt` | 全 thread の候補 frame |
| `.runtime-metrics/<pair>.stack-dump.status.json` | registration / 送信 / 観測 / 退避 |

## 分類しないこと

* **payload の有無・log の文字列・returncode 単独から推定しない。** P（supervisor の
  process deadline）と S（子の solver timeout）は独立した必須証拠から別々に判定し、
  足りなければ `unknown` に落とす。
* **候補 frame を root cause と断定しない。** `candidate_frames` は「kill された
  瞬間にその thread がいた最内 frame」でしかない。待機中の frame には
  `waiting: true` を付けるが、それも原因の決定ではない。
* #129（異常終了の分類）と #106（analysis budget）はここに混ぜない。TIMEOUT 以外の
  outcome は `not_applicable`。
* 出力は診断で、decision authority へは接続しない。
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.authority.decision.canonical_result import (
    validate_canonical_result_finalization_bundle,
)
from scripts.function_tracer_pcode.authority.process import child_exit
from scripts.function_tracer_pcode.authority.process.stack_dump_diagnostic import (
    read_stack_dump_status,
)
from scripts.function_tracer_pcode.core.stage_journal_reader import (
    SUMMARY_READ_LIMIT_BYTES,
    read_stage_journal,
    segment_stages,
    select_current_segment,
)
from scripts.function_tracer_pcode.reporting.pair_outcomes import (
    PAIR_STATUS_SUFFIX,
    iter_pair_outcomes,
)
from scripts.function_tracer_pcode.reporting.result_summary import (
    TIMEOUT_DIAGNOSTICS_KEY,
    format_run_health_summary,
)

SUMMARY_SCHEMA = "timeout-hotspot-summary-v1"

#: `run_health_summary.json` に merge するときの key。
HEALTH_KEY = TIMEOUT_DIAGNOSTICS_KEY

TIMEOUT_OUTCOME = "TIMEOUT"

# `timeout_kind` の 5 値（v4 §5.B C-4）。
KIND_PROCESS_WALL_CLOCK = "process_wall_clock"
KIND_CHILD_SOLVER_TIMEOUT = "child_solver_timeout"
KIND_BOTH_SIGNALS = "both_signals"
KIND_UNKNOWN = "unknown"
KIND_NOT_APPLICABLE = "not_applicable"
TIMEOUT_KIND_ORDER = (
    KIND_PROCESS_WALL_CLOCK,
    KIND_CHILD_SOLVER_TIMEOUT,
    KIND_BOTH_SIGNALS,
    KIND_UNKNOWN,
    KIND_NOT_APPLICABLE,
)
#: supervisor の process deadline が終端を決めた（= process TIMEOUT）と読める `timeout_kind`。
#: 「TIMEOUT だから process が kill された」と読まないため、consumer はこの集合で判断する
#: （Issue #106 PR-106-B: margin の測定・targeted pair の受理）。
PROCESS_DEADLINE_KINDS = frozenset({KIND_PROCESS_WALL_CLOCK, KIND_BOTH_SIGNALS})

# 証拠の状態。`absent`（そもそも残っていない）と `invalid`（残っているが
# 検証に落ちた / 矛盾している）を潰さない。
EVIDENCE_CONFIRMED = "confirmed"
EVIDENCE_ABSENT = "absent"
EVIDENCE_INVALID = "invalid"

# S 証拠をどこから取り、どこまで検証したか。強さの違う 2 経路を混ぜない。
SOURCE_SIDECAR = "diagnostic_status_sidecar"
SOURCE_PAIR_LOG = "pair_log_result_payload"
#: supervisor signing key で署名まで検証した（sidecar、または key を渡された呼び出し）。
VERIFICATION_SUPERVISOR_KEY = "supervisor_key_verified"
#: 封のある bundle を digest + replay だけで見た。真正性は未確認。
VERIFICATION_REPLAY_ONLY = "replay_only_unsigned"
#: そもそも封が無い bundle（`bundle_seal_key_id` が null）。digest + replay が全て。
VERIFICATION_UNSEALED = "unsealed_bundle"

SUPERVISOR_TIMEOUT_AUTHORITY_KIND = "DurableTimeoutFinalizationBundle"

RESULT_JSON_BEGIN = "=== EQUIVALENCE_RESULT_JSON_BEGIN ==="
RESULT_JSON_END = "=== EQUIVALENCE_RESULT_JSON_END ==="

#: 読み込みで起こり得る失敗（`except Exception` は使わない）。
_READ_ERRORS = (KeyError, OSError, RecursionError, TypeError, ValueError)

def _bundle_work_exceeded() -> type:
    """封印の検証が作業量・契約の外で止まった失敗（Issue #110。読み取りの失敗と同じく記録する）。"""

    from scripts.function_tracer_pcode.authority.seal_work import BundleWorkExceeded

    return BundleWorkExceeded


#: 待機中と読める frame の関数名（`waiting` 印を付けるだけで原因ではない）。
WAITING_FRAME_MARKERS = ("wait", "acquire", "select", "poll")

UNKNOWN_LABEL = "(unknown)"
NONE_LABEL = "(none)"

# 「進行中の stage」をどの瞬間から取ったか。dump と同じ瞬間で切れたのか、
# journal の末尾なのか、そもそも開いた region が無かったのかを区別する。
IN_PROGRESS_AT_STACK_DUMP = "at_stack_dump"
IN_PROGRESS_AT_JOURNAL_END = "journal_end"
IN_PROGRESS_NONE_OPEN = "none_open"

_FRAME_RE = re.compile(
    r'\A\s*File "(?P<file>.*)", line (?P<line>\d+) in (?P<function>.+?)\s*\Z'
)
_THREAD_HEADER_RE = re.compile(
    r"\A(?P<current>Current thread|Thread) (?P<thread_id>0x[0-9a-fA-F]+)"
)


# ---------------------------------------------------------------------------
# 証拠
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Evidence:
    """1 本の必須証拠の評価結果。"""

    status: str
    missing: Tuple[str, ...] = ()
    violations: Tuple[str, ...] = ()
    detail: Mapping[str, Any] = field(default_factory=dict)

    @property
    def confirmed(self) -> bool:
        return self.status == EVIDENCE_CONFIRMED

    def to_dict(self) -> Dict[str, Any]:
        return {
            "status": self.status,
            "missing": list(self.missing),
            "violations": list(self.violations),
            "detail": dict(self.detail),
        }


def _evidence(
    missing: Sequence[str], violations: Sequence[str], detail: Mapping[str, Any],
) -> Evidence:
    if violations:
        status = EVIDENCE_INVALID
    elif missing:
        status = EVIDENCE_ABSENT
    else:
        status = EVIDENCE_CONFIRMED
    return Evidence(
        status=status,
        missing=tuple(missing),
        violations=tuple(violations),
        detail=dict(detail),
    )


def supervisor_deadline_evidence(pair_status: Mapping[str, Any]) -> Evidence:
    """P: supervisor の process deadline が最終終了の authority だったか。

    必須証拠は「canonical outcome が TIMEOUT」「supervisor_status が TIMEOUT」
    「supervisor authority が `DurableTimeoutFinalizationBundle`」
    「`child_exit_disposition` が deadline 経路の全 disposition のどれかに完全一致」
    「`child_returncode` が既存 validator と一致」「`classification_valid`」。
    無関係な field が増えても評価は変わらない。
    """
    if not isinstance(pair_status, Mapping):
        return _evidence(["pair_status"], [], {})
    missing: List[str] = []
    violations: List[str] = []
    absent = object()

    def _required(name: str) -> Any:
        value = pair_status.get(name, absent)
        if value is absent:
            missing.append(name)
            return absent
        return value

    outcome = _required("canonical_outcome")
    supervisor_status = _required("supervisor_status")
    authority_kind = _required("supervisor_authority_kind")
    disposition = _required("child_exit_disposition")
    observation_kind = _required("child_returncode_observation_kind")
    returncode = _required("child_returncode")
    classification_valid = _required("classification_valid")

    if outcome is not absent and outcome != TIMEOUT_OUTCOME:
        violations.append("canonical_outcome")
    if supervisor_status is not absent and supervisor_status != TIMEOUT_OUTCOME:
        violations.append("supervisor_status")
    if (
        authority_kind is not absent
        and authority_kind != SUPERVISOR_TIMEOUT_AUTHORITY_KIND
    ):
        violations.append("supervisor_authority_kind")
    if disposition is not absent and (
        not child_exit.is_deadline_disposition(disposition)
    ):
        violations.append("child_exit_disposition")
    if observation_kind is not absent and observation_kind not in child_exit.OBSERVATION_KINDS:
        violations.append("child_returncode_observation_kind")
    if classification_valid is not absent and classification_valid is not True:
        violations.append("classification_valid")
    if (
        disposition is not absent
        and observation_kind is not absent
        and returncode is not absent
        and "child_exit_disposition" not in violations
        and "child_returncode_observation_kind" not in violations
    ):
        try:
            child_exit.validate_durable_child_returncode_observation(
                child_exit_disposition=disposition,
                child_returncode=returncode,
                observation_kind=observation_kind,
            )
        except (TypeError, ValueError):
            violations.append("child_returncode")
    return _evidence(missing, violations, {
        "supervisor_status": pair_status.get("supervisor_status"),
        "supervisor_authority_kind": pair_status.get("supervisor_authority_kind"),
        "child_exit_disposition": pair_status.get("child_exit_disposition"),
        "child_returncode": pair_status.get("child_returncode"),
        "child_returncode_observation_kind": pair_status.get(
            "child_returncode_observation_kind"
        ),
    })


def _identity_binds(identity: Mapping[str, Any], pair_status: Mapping[str, Any]) -> bool:
    """子の bundle が **この pair のこの execution** のものか。"""
    for bundle_key, status_key in (
        ("result_occurrence_id", "result_occurrence_id"),
        ("stream_id", "stream_id"),
        ("source_snapshot_fingerprint", "source_snapshot_fingerprint"),
    ):
        expected = pair_status.get(status_key)
        if not isinstance(expected, str) or not expected:
            return False
        if identity.get(bundle_key) != expected:
            return False
    return True


def terminal_timeout_requirement_ids(receipts: Any) -> frozenset:
    """`terminal_timeout_receipts` の requirement id 集合。

    bundle の受領書は codec で ``{"object_type", "payload"}`` に包まれている。
    sidecar 側は平らな dict なので、両方の形を受ける。
    """
    if not isinstance(receipts, (list, tuple)):
        return frozenset()
    ids = set()
    for item in receipts:
        if not isinstance(item, Mapping):
            continue
        body = item.get("payload") if isinstance(item.get("payload"), Mapping) else item
        value = body.get("proof_requirement_id")
        if isinstance(value, str) and value:
            ids.add(value)
    return frozenset(ids)


def _solver_identified_terminal_timeout(bundle: Mapping[str, Any]) -> Optional[str]:
    """terminal timeout を solver と識別できるか。できれば invocation id を返す。"""
    receipts = bundle.get("terminal_timeout_receipts")
    if not isinstance(receipts, (list, tuple)) or not receipts:
        return None
    requirement_ids = terminal_timeout_requirement_ids(receipts)
    if not requirement_ids:
        return None
    selection = bundle.get("terminal_timeout_candidate_selection_receipt")
    if not isinstance(selection, Mapping):
        return None
    invocation = selection.get("solver_invocation_id")
    if not isinstance(invocation, str) or not invocation:
        return None
    if selection.get("proof_requirement_id") not in requirement_ids:
        return None
    return invocation


def _sidecar_child_evidence(
    pair_status: Mapping[str, Any], recorded: Mapping[str, Any],
    detail: Dict[str, Any],
) -> Evidence:
    """cleanup 前に supervisor が **signing key つきで**検証した子の証拠。"""
    detail.update({
        "source": SOURCE_SIDECAR,
        "verification": VERIFICATION_SUPERVISOR_KEY,
        "canonical_outcome": recorded.get("canonical_outcome"),
        "bundle_digest": recorded.get("bundle_digest"),
        "validation_error": recorded.get("validation_error"),
    })
    if recorded.get("validated") is not True:
        return _evidence([], ["validated"], detail)
    if not _identity_binds(recorded, pair_status):
        return _evidence([], ["execution_identity"], detail)
    if recorded.get("canonical_outcome") != TIMEOUT_OUTCOME:
        return _evidence([], ["canonical_outcome"], detail)
    invocation = recorded.get("terminal_timeout_solver_invocation_id")
    if not isinstance(invocation, str) or not invocation:
        return _evidence(["terminal_timeout_solver_invocation_id"], [], detail)
    detail["terminal_timeout_solver_invocation_id"] = invocation
    return _evidence([], [], detail)


def _pair_log_child_evidence(
    pair_status: Mapping[str, Any], bundle: Mapping[str, Any],
    result_payload: Mapping[str, Any], detail: Dict[str, Any],
    *, key_id: Optional[str], key: Optional[bytes],
) -> Evidence:
    """pair log に残った子の bundle。**署名の検証には key が要る。**

    key を渡されなければ `validate_canonical_result_finalization_bundle` は
    digest と event stream の replay しか見ない（`bundle_signature` は無視される）。
    封をした bundle（`bundle_seal_key_id` あり）をその状態で「検証済み」とは
    呼べないので、`supervisor_key_verification` を欠落として fail-closed にする。
    """
    detail["source"] = SOURCE_PAIR_LOG
    sealed = bundle.get("bundle_seal_key_id") is not None
    verified_with_key = sealed and key is not None and key_id is not None
    detail["verification"] = (
        VERIFICATION_SUPERVISOR_KEY if verified_with_key
        else VERIFICATION_UNSEALED if not sealed
        else VERIFICATION_REPLAY_ONLY
    )
    preimage = {
        key_name: value for key_name, value in result_payload.items()
        if key_name != "canonical_result_finalization_bundle"
    }
    try:
        from scripts.function_tracer_pcode.authority.seal_work import SealWorkBudget

        validated = validate_canonical_result_finalization_bundle(
            dict(bundle),
            work=SealWorkBudget.for_result(),
            result_payload_preimage=preimage,
            bundle_verification_key_id=key_id if verified_with_key else None,
            bundle_verification_key=key if verified_with_key else None,
        )
    except _READ_ERRORS + (_bundle_work_exceeded(),) as exc:
        detail["validation_error"] = type(exc).__name__
        return _evidence([], ["canonical_result_finalization_bundle"], detail)
    identity = validated["execution_identity"]
    detail["bundle_digest"] = validated["bundle_digest"]
    detail["canonical_outcome"] = validated["outcome"]
    if not _identity_binds(identity, pair_status):
        return _evidence([], ["execution_identity"], detail)
    if validated["outcome"] != TIMEOUT_OUTCOME:
        return _evidence([], ["canonical_outcome"], detail)
    invocation = _solver_identified_terminal_timeout(bundle)
    if invocation is None:
        return _evidence(["terminal_timeout_solver_invocation_id"], [], detail)
    detail["terminal_timeout_solver_invocation_id"] = invocation
    if not verified_with_key and sealed:
        # digest も replay も通ったが、封の真正性は確かめていない。
        # 「検証済み S evidence」としては採用しない。
        return _evidence(["supervisor_key_verification"], [], detail)
    return _evidence([], [], detail)


def child_solver_timeout_evidence(
    pair_status: Mapping[str, Any],
    *,
    result_payload: Optional[Mapping[str, Any]] = None,
    status_sidecar: Optional[Mapping[str, Any]] = None,
    bundle_verification_key_id: Optional[str] = None,
    bundle_verification_key: Optional[bytes] = None,
) -> Evidence:
    """S: 子自身が solver の terminal timeout で TIMEOUT を確定したか。

    根拠は **検証済みの** canonical bundle だけ。`RESOLVED + returncode=3` や
    「result payload がある」ことだけでは solver 由来と断定しない。
    根拠が残っていない（cleanup 済みで log にも payload が無い）run では `absent`。

    **どこまで検証したかを混ぜない。** 2 つの経路は強さが違う:

    1. supervisor が cleanup 前に signing key で検証し sidecar に残した証拠
       （`verification: supervisor_key_verified`）。**こちらを優先する。**
    2. pair log に残った bundle。ここでは signing key を持たないのが既定なので、
       封のある bundle は digest と replay しか確かめられない
       （`verification: replay_only_unsigned`）。その場合は
       `supervisor_key_verification` を欠落として **confirmed にしない**。
       key を渡された呼び出し（調査用）だけが 1 と同じ強さになる。

    どちらの経路も reporting / diagnostic 専用で、semantic authority や
    outcome 判定へは接続しない。
    """
    detail: Dict[str, Any] = {"source": None, "verification": None}
    if isinstance(status_sidecar, Mapping):
        recorded = status_sidecar.get("child_timeout_evidence")
        if isinstance(recorded, Mapping):
            return _sidecar_child_evidence(pair_status, recorded, detail)
    if isinstance(result_payload, Mapping):
        bundle = result_payload.get("canonical_result_finalization_bundle")
        if isinstance(bundle, Mapping):
            return _pair_log_child_evidence(
                pair_status, bundle, result_payload, detail,
                key_id=bundle_verification_key_id, key=bundle_verification_key,
            )
    return _evidence(["child_canonical_timeout_evidence"], [], detail)


@dataclass(frozen=True)
class TimeoutKindReport:
    kind: str
    process_deadline: Evidence
    child_solver: Evidence

    def to_dict(self) -> Dict[str, Any]:
        return {
            "timeout_kind": self.kind,
            "process_deadline_evidence": self.process_deadline.to_dict(),
            "child_solver_evidence": self.child_solver.to_dict(),
        }


def classify_timeout_kind(
    pair_status: Mapping[str, Any],
    *,
    result_payload: Optional[Mapping[str, Any]] = None,
    status_sidecar: Optional[Mapping[str, Any]] = None,
    bundle_verification_key_id: Optional[str] = None,
    bundle_verification_key: Optional[bytes] = None,
) -> TimeoutKindReport:
    """P と S を**独立に**評価して 5 値のどれかへ落とす。"""
    process = supervisor_deadline_evidence(pair_status)
    child = child_solver_timeout_evidence(
        pair_status, result_payload=result_payload, status_sidecar=status_sidecar,
        bundle_verification_key_id=bundle_verification_key_id,
        bundle_verification_key=bundle_verification_key,
    )
    outcome = (
        pair_status.get("canonical_outcome")
        if isinstance(pair_status, Mapping) else None
    )
    if isinstance(outcome, str) and outcome and outcome != TIMEOUT_OUTCOME:
        # 検証済みの最終 outcome が TIMEOUT 以外。#129 の異常終了分類へ広げない。
        return TimeoutKindReport(KIND_NOT_APPLICABLE, process, child)
    if not isinstance(outcome, str) or not outcome:
        # outcome 自体が欠けている（pair-status が壊れている等）。
        return TimeoutKindReport(KIND_UNKNOWN, process, child)
    if process.confirmed and child.confirmed:
        return TimeoutKindReport(KIND_BOTH_SIGNALS, process, child)
    if process.confirmed:
        return TimeoutKindReport(KIND_PROCESS_WALL_CLOCK, process, child)
    if child.confirmed:
        return TimeoutKindReport(KIND_CHILD_SOLVER_TIMEOUT, process, child)
    return TimeoutKindReport(KIND_UNKNOWN, process, child)


# ---------------------------------------------------------------------------
# stack dump
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class DumpFrame:
    thread_id: str
    current_thread: bool
    function: str
    file: str
    line: int
    waiting: bool

    @property
    def label(self) -> str:
        return f"{self.function} ({Path(self.file).name}:{self.line})"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "thread_id": self.thread_id,
            "current_thread": self.current_thread,
            "function": self.function,
            "file": self.file,
            "line": self.line,
            "waiting": self.waiting,
            "label": self.label,
        }


@dataclass(frozen=True)
class StackDumpRead:
    path: Optional[str]
    present: bool = False
    bytes: Optional[int] = None
    thread_blocks: int = 0
    dump_sections: int = 0
    candidate_frames: Tuple[DumpFrame, ...] = ()
    unavailable_reason: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "path": self.path,
            "present": self.present,
            "bytes": self.bytes,
            "thread_blocks": self.thread_blocks,
            "dump_sections": self.dump_sections,
            "candidate_frames": [frame.to_dict() for frame in self.candidate_frames],
            "unavailable_reason": self.unavailable_reason,
        }


def _frame_is_waiting(function: str) -> bool:
    lowered = function.lower()
    return any(marker in lowered for marker in WAITING_FRAME_MARKERS)


def read_stack_dump(path: Any) -> StackDumpRead:
    """faulthandler の dump を **全 thread** 解析する。

    `Current thread` だけに限定しない（solver worker thread がどこで止まって
    いたかは `Thread 0x…` の block にしかない）。block の**最内 frame**
    （`most recent call first` なので先頭の `File` 行）を候補として返す。
    """
    resolved = None if path is None else str(path)
    if resolved is None:
        return StackDumpRead(path=None, unavailable_reason="stack_dump_not_configured")
    file_path = Path(resolved)
    try:
        if not file_path.is_file():
            return StackDumpRead(path=resolved, unavailable_reason="stack_dump_missing")
        text = file_path.read_text(encoding="utf-8", errors="replace")
    except _READ_ERRORS as exc:
        return StackDumpRead(
            path=resolved, unavailable_reason=f"stack_dump_unreadable:{type(exc).__name__}",
        )
    if not text.strip():
        return StackDumpRead(
            path=resolved, present=True, bytes=len(text.encode("utf-8", "replace")),
            unavailable_reason="stack_dump_empty",
        )
    blocks: List[Tuple[str, bool, List[DumpFrame]]] = []
    header: Optional[Tuple[str, bool]] = None
    frames: List[DumpFrame] = []
    for line in text.splitlines():
        match = _THREAD_HEADER_RE.match(line)
        if match is not None:
            if header is not None:
                blocks.append((header[0], header[1], frames))
            header = (match.group("thread_id"), match.group("current") == "Current thread")
            frames = []
            continue
        if header is None:
            continue
        frame_match = _FRAME_RE.match(line)
        if frame_match is None:
            continue
        function = frame_match.group("function")
        frames.append(DumpFrame(
            thread_id=header[0],
            current_thread=header[1],
            function=function,
            file=frame_match.group("file"),
            line=int(frame_match.group("line")),
            waiting=_frame_is_waiting(function),
        ))
    if header is not None:
        blocks.append((header[0], header[1], frames))
    if not blocks:
        return StackDumpRead(
            path=resolved, present=True, bytes=len(text.encode("utf-8", "replace")),
            unavailable_reason="stack_dump_has_no_thread_block",
        )
    # 同じ thread id が再び現れたら別の dump（同じ signal を 2 回送った場合）。
    # 最後の dump だけを候補にし、何 section あったかは残す。
    sections: List[List[Tuple[str, bool, List[DumpFrame]]]] = [[]]
    seen: set = set()
    for block in blocks:
        if block[0] in seen:
            sections.append([])
            seen = set()
        seen.add(block[0])
        sections[-1].append(block)
    last = sections[-1]
    candidates = tuple(block[2][0] for block in last if block[2])
    return StackDumpRead(
        path=resolved,
        present=True,
        bytes=len(text.encode("utf-8", "replace")),
        thread_blocks=len(last),
        dump_sections=len(sections),
        candidate_frames=candidates,
    )


# ---------------------------------------------------------------------------
# pair ごとの集計
# ---------------------------------------------------------------------------


def read_result_payload(log_path: Any) -> Optional[Dict[str, Any]]:
    """pair log に残っている結果 JSON（最後のもの）を返す。無ければ `None`。"""
    if log_path is None:
        return None
    try:
        path = Path(str(log_path))
        if not path.is_file():
            return None
        text = path.read_text(encoding="utf-8", errors="replace")
    except _READ_ERRORS:
        return None
    if RESULT_JSON_BEGIN not in text or RESULT_JSON_END not in text:
        return None
    raw = text.rsplit(RESULT_JSON_BEGIN, 1)[1].split(RESULT_JSON_END, 1)[0].strip()
    try:
        payload = json.loads(raw)
    except ValueError:
        return None
    return payload if isinstance(payload, dict) else None


@dataclass(frozen=True)
class PairPaths:
    pair_status: Path
    log: Path
    journal: Path
    stack_dump: Path
    diagnostic_status: Path


def pair_paths(status_path: Any) -> PairPaths:
    """pair-status の path から、同じ pair の診断 file 一式を導く。"""
    path = Path(str(status_path))
    stem = path.name[: -len(PAIR_STATUS_SUFFIX)]
    metrics = path.parent / ".runtime-metrics"
    return PairPaths(
        pair_status=path,
        log=path.parent / f"{stem}.log",
        journal=path.parent / f"{stem}.stage.jsonl",
        stack_dump=metrics / f"{stem}.stack-dump.txt",
        diagnostic_status=metrics / f"{stem}.stack-dump.status.json",
    )


@dataclass(frozen=True)
class TimeoutPairRow:
    sample_identity: str
    function_name: str
    left_binary_id: str
    right_binary_id: str
    outcome: str
    timeout_kind: str
    kind_report: TimeoutKindReport
    handler_registered: Optional[bool]
    signal_sent: Optional[bool]
    signal_start_state: Optional[str]
    dump_observed: Optional[bool]
    sent_but_unobserved: Optional[bool]
    unavailable_reason: Optional[str]
    artifact_status: Optional[str]
    artifact_bytes: Optional[int]
    last_completed_stage: Optional[str]
    in_progress_stage: Optional[str]
    in_progress_stage_basis: str
    longest_completed_stage: Optional[str]
    longest_completed_seconds: Optional[float]
    diagnostic_status_present: bool
    journal_state: Mapping[str, Any]
    journal_unavailable_reason: Optional[str]
    stack: StackDumpRead
    paths: PairPaths

    @property
    def pair_id(self) -> str:
        return f"{self.left_binary_id}_{self.right_binary_id}"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "sample_identity": self.sample_identity,
            "function_name": self.function_name,
            "left_binary_id": self.left_binary_id,
            "right_binary_id": self.right_binary_id,
            "pair_id": self.pair_id,
            "canonical_outcome": self.outcome,
            **self.kind_report.to_dict(),
            "handler_registered": self.handler_registered,
            "signal_sent": self.signal_sent,
            "signal_start_state": self.signal_start_state,
            "dump_observed": self.dump_observed,
            "sent_but_unobserved": self.sent_but_unobserved,
            "unavailable_reason": self.unavailable_reason,
            "artifact_status": self.artifact_status,
            "artifact_bytes": self.artifact_bytes,
            "last_completed_stage": self.last_completed_stage,
            "in_progress_stage": self.in_progress_stage,
            "in_progress_stage_basis": self.in_progress_stage_basis,
            "longest_completed_stage": self.longest_completed_stage,
            "longest_completed_seconds": self.longest_completed_seconds,
            "diagnostic_status_present": self.diagnostic_status_present,
            "journal": dict(self.journal_state),
            "journal_unavailable_reason": self.journal_unavailable_reason,
            "stack_dump": self.stack.to_dict(),
            "paths": {
                "pair_status": str(self.paths.pair_status),
                "log": str(self.paths.log),
                "journal": str(self.paths.journal),
                "stack_dump": str(self.paths.stack_dump),
                "diagnostic_status": str(self.paths.diagnostic_status),
            },
        }


def _optional_bool(sidecar: Optional[Mapping[str, Any]], key: str) -> Optional[bool]:
    """sidecar が無い run では `None`（**`False` に潰さない**）。"""
    if not isinstance(sidecar, Mapping):
        return None
    value = sidecar.get(key)
    return value if isinstance(value, bool) else None


@dataclass(frozen=True)
class PairEvidence:
    """1 pair の終了の証拠（pair status・supervisor の診断 sidecar・結果 payload）。

    読めない file は空（pair status）/ ``None``（sidecar・payload）。推定で埋めない。
    """

    paths: PairPaths
    pair_status: Mapping[str, Any]
    sidecar: Optional[Mapping[str, Any]]
    result_payload: Optional[Mapping[str, Any]]

    def timeout_kind_report(self) -> "TimeoutKindReport":
        return classify_timeout_kind(
            self.pair_status, result_payload=self.result_payload,
            status_sidecar=self.sidecar,
        )


def load_pair_evidence(status_path: Any) -> PairEvidence:
    """pair-status の path から、その pair の終了の証拠を読む（例外は投げない）。"""
    paths = pair_paths(status_path)
    try:
        pair_status = json.loads(paths.pair_status.read_text(encoding="utf-8"))
    except _READ_ERRORS:
        pair_status = {}
    if not isinstance(pair_status, Mapping):
        pair_status = {}
    return PairEvidence(
        paths=paths,
        pair_status=pair_status,
        sidecar=read_stack_dump_status(paths.diagnostic_status),
        result_payload=read_result_payload(paths.log),
    )


def build_timeout_pair_row(
    outcome_record: Any, *, include_non_timeout: bool = False,
) -> Optional[TimeoutPairRow]:
    """1 pair 分の診断行を作る。TIMEOUT でなければ既定では `None`。"""
    if outcome_record.outcome != TIMEOUT_OUTCOME and not include_non_timeout:
        return None
    evidence = load_pair_evidence(outcome_record.status_path)
    paths = evidence.paths
    sidecar = evidence.sidecar
    report = evidence.timeout_kind_report()
    journal = read_stage_journal(paths.journal, max_bytes=SUMMARY_READ_LIMIT_BYTES)
    # sidecar が現在の child の pid / start_token を残していればそれで一意に選ぶ。
    # 無い run（sidecar 以前）では、混在の兆候が無い journal だけを使う。
    segment, journal_reason = select_current_segment(
        journal,
        pid=(sidecar or {}).get("child_pid"),
        start_token=(sidecar or {}).get("child_start_token"),
    )
    stages = segment_stages(segment) if segment is not None else None
    # SIGTERM を受けた child は後始末まで走るので、journal の末尾では region が
    # 全部閉じている。stack dump を撮った瞬間（sidecar の `signal_sent_epoch`）で
    # 切ると、その時点で開いていた region が残る。候補 frame と同じ瞬間なので、
    # 表の `active` と `frame` が同じ観測時刻を指す。
    signal_epoch = (sidecar or {}).get("signal_sent_epoch")
    stages_at_signal = None
    if segment is not None and isinstance(signal_epoch, (int, float)):
        stages_at_signal = segment_stages(segment, as_of_epoch=float(signal_epoch))
    if stages_at_signal is not None and stages_at_signal.in_progress_stage is not None:
        in_progress = stages_at_signal.in_progress_stage
        in_progress_basis = IN_PROGRESS_AT_STACK_DUMP
    elif stages is not None and stages.in_progress_stage is not None:
        in_progress = stages.in_progress_stage
        in_progress_basis = IN_PROGRESS_AT_JOURNAL_END
    else:
        in_progress = None
        in_progress_basis = (
            IN_PROGRESS_NONE_OPEN if stages is not None else UNKNOWN_LABEL
        )
    stack = read_stack_dump(paths.stack_dump)
    artifact_status = None
    artifact_bytes = None
    if isinstance(sidecar, Mapping):
        declared = sidecar.get("artifact_status")
        artifact_status = declared if isinstance(declared, str) else None
        declared_bytes = sidecar.get("artifact_bytes")
        artifact_bytes = declared_bytes if isinstance(declared_bytes, int) else None
    return TimeoutPairRow(
        sample_identity=outcome_record.sample_identity,
        function_name=outcome_record.function_name,
        left_binary_id=outcome_record.left_binary_id,
        right_binary_id=outcome_record.right_binary_id,
        outcome=outcome_record.outcome,
        timeout_kind=report.kind,
        kind_report=report,
        handler_registered=_optional_bool(sidecar, "handler_registered"),
        signal_sent=_optional_bool(sidecar, "signal_sent"),
        signal_start_state=(
            sidecar.get("signal_start_state") if isinstance(sidecar, Mapping) else None
        ),
        dump_observed=_optional_bool(sidecar, "dump_observed"),
        sent_but_unobserved=_optional_bool(sidecar, "sent_but_unobserved"),
        unavailable_reason=(
            sidecar.get("unavailable_reason") if isinstance(sidecar, Mapping) else None
        ),
        artifact_status=artifact_status,
        artifact_bytes=artifact_bytes,
        last_completed_stage=None if stages is None else stages.last_completed_stage,
        in_progress_stage=in_progress,
        in_progress_stage_basis=in_progress_basis,
        longest_completed_stage=(
            None if stages is None else stages.longest_completed_stage
        ),
        longest_completed_seconds=(
            None if stages is None else stages.longest_completed_seconds
        ),
        diagnostic_status_present=isinstance(sidecar, Mapping),
        journal_state=journal.state(),
        journal_unavailable_reason=journal_reason,
        stack=stack,
        paths=paths,
    )


def _bucket(value: Optional[bool]) -> str:
    """3 値を潰さずに数えるための label。"""
    if value is None:
        return UNKNOWN_LABEL
    return "true" if value else "false"


def _count(table: Dict[str, int], key: str) -> None:
    table[key] = table.get(key, 0) + 1


@dataclass(frozen=True)
class TimeoutHotspotReport:
    roots: Tuple[str, ...]
    rows: Tuple[TimeoutPairRow, ...]
    total_pairs: int

    @property
    def timeout_pairs(self) -> int:
        return len(self.rows)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "schema": SUMMARY_SCHEMA,
            "roots": list(self.roots),
            **self.health_section(),
            "pairs_detail": [row.to_dict() for row in self.rows],
        }

    def health_section(self) -> Dict[str, Any]:
        """`run_health_summary.json` に merge する compact block。

        どの次元も **TIMEOUT pair 数と総和が一致する**ように、値が無い pair は
        `(unknown)` bucket に入れる（0 件として消さない）。
        """
        kinds: Dict[str, int] = {}
        handler: Dict[str, int] = {}
        signal_sent: Dict[str, int] = {}
        signal_start: Dict[str, int] = {}
        dump_observed: Dict[str, int] = {}
        sent_but_unobserved: Dict[str, int] = {}
        unavailable: Dict[str, int] = {}
        artifact: Dict[str, int] = {}
        last_stage: Dict[str, int] = {}
        active_stage: Dict[str, int] = {}
        active_basis: Dict[str, int] = {}
        longest_stage: Dict[str, int] = {}
        frames: Dict[str, int] = {}
        hotspots: Dict[str, int] = {}
        evidence = {
            "journal_current_segment": 0,
            "journal_unavailable": 0,
            "diagnostic_status": 0,
            "diagnostic_status_missing": 0,
            "stack_dump": 0,
            "stack_dump_missing": 0,
        }
        for row in self.rows:
            _count(kinds, row.timeout_kind)
            _count(handler, _bucket(row.handler_registered))
            _count(signal_sent, _bucket(row.signal_sent))
            # 「送信権を取ったが syscall が失敗した」と「cancel に先を越された」を
            # 同じ `signal_sent=false` に潰さない。
            _count(signal_start, row.signal_start_state or UNKNOWN_LABEL)
            _count(dump_observed, _bucket(row.dump_observed))
            _count(sent_but_unobserved, _bucket(row.sent_but_unobserved))
            if not row.diagnostic_status_present:
                # sidecar が無い run。「理由なし」ではなく「観測していない」。
                _count(unavailable, UNKNOWN_LABEL)
            else:
                _count(unavailable, row.unavailable_reason or NONE_LABEL)
            _count(artifact, row.artifact_status or UNKNOWN_LABEL)
            _count(last_stage, row.last_completed_stage or UNKNOWN_LABEL)
            _count(active_stage, row.in_progress_stage or UNKNOWN_LABEL)
            _count(active_basis, row.in_progress_stage_basis)
            _count(longest_stage, row.longest_completed_stage or UNKNOWN_LABEL)
            if row.journal_unavailable_reason is None:
                evidence["journal_current_segment"] += 1
            else:
                evidence["journal_unavailable"] += 1
            if row.diagnostic_status_present:
                evidence["diagnostic_status"] += 1
            else:
                evidence["diagnostic_status_missing"] += 1
            if row.stack.candidate_frames:
                evidence["stack_dump"] += 1
            else:
                evidence["stack_dump_missing"] += 1
            if row.stack.candidate_frames:
                for frame in row.stack.candidate_frames:
                    _count(frames, frame.label + (" [waiting]" if frame.waiting else ""))
                    _count(hotspots, (
                        f"last={row.last_completed_stage or UNKNOWN_LABEL} "
                        f"active={row.in_progress_stage or UNKNOWN_LABEL} "
                        f"frame={frame.label}"
                        + (" [waiting]" if frame.waiting else "")
                    ))
            else:
                _count(hotspots, (
                    f"last={row.last_completed_stage or UNKNOWN_LABEL} "
                    f"active={row.in_progress_stage or UNKNOWN_LABEL} "
                    f"frame={UNKNOWN_LABEL}"
                ))
        return {
            "pairs": self.timeout_pairs,
            "total_pairs": self.total_pairs,
            "timeout_kind": kinds,
            "handler_registered": handler,
            "signal_sent": signal_sent,
            "signal_start_state": signal_start,
            "dump_observed": dump_observed,
            "sent_but_unobserved": sent_but_unobserved,
            "unavailable_reason": unavailable,
            "artifact_status": artifact,
            "last_completed_stage": last_stage,
            "in_progress_stage": active_stage,
            "in_progress_stage_basis": active_basis,
            "longest_completed_stage": longest_stage,
            "candidate_frames": frames,
            "timeout_hotspots": hotspots,
            "evidence": evidence,
            # 候補 frame は「kill 時点でその thread がいた最内 frame」であって、
            # 原因ではない。出力を読む側が断定しないための注記。
            "candidate_frames_note": (
                "candidate frames are observation points, not a root cause"
            ),
        }


def build_timeout_hotspot_report(roots: Sequence[Path]) -> TimeoutHotspotReport:
    rows: List[TimeoutPairRow] = []
    total = 0
    for root in roots:
        for record in iter_pair_outcomes(Path(root)):
            total += 1
            row = build_timeout_pair_row(record)
            if row is not None:
                rows.append(row)
    rows.sort(key=lambda row: (
        row.sample_identity, row.function_name, row.left_binary_id, row.right_binary_id,
    ))
    return TimeoutHotspotReport(
        roots=tuple(str(root) for root in roots),
        rows=tuple(rows),
        total_pairs=total,
    )


# ---------------------------------------------------------------------------
# 出力
# ---------------------------------------------------------------------------


def format_timeout_hotspot_report(report: TimeoutHotspotReport) -> str:
    section = report.health_section()
    lines = [
        f"Timeout diagnostics: pairs={section['pairs']} of {section['total_pairs']}",
        "  timeout_kind:",
    ]
    if section["timeout_kind"]:
        for kind in TIMEOUT_KIND_ORDER:
            if kind in section["timeout_kind"]:
                lines.append(f"    - {kind}: {section['timeout_kind'][kind]}")
    else:
        lines.append(f"    {NONE_LABEL}")
    for title in (
        "handler_registered", "signal_sent", "signal_start_state", "dump_observed",
        "sent_but_unobserved", "unavailable_reason", "artifact_status",
        "last_completed_stage", "in_progress_stage", "in_progress_stage_basis",
        "longest_completed_stage",
    ):
        lines.append(f"  {title}:")
        values = section[title]
        if not values:
            lines.append(f"    {NONE_LABEL}")
            continue
        for name, count in sorted(values.items(), key=lambda item: (-item[1], item[0])):
            lines.append(f"    - {name}: {count}")
    lines.append("  timeout_hotspots:")
    if section["timeout_hotspots"]:
        for name, count in sorted(
            section["timeout_hotspots"].items(), key=lambda item: (-item[1], item[0])
        ):
            lines.append(f"    - {name}: {count}")
    else:
        lines.append(f"    {NONE_LABEL}")
    lines.append(f"  note: {section['candidate_frames_note']}")
    return "\n".join(lines) + "\n"


def merge_into_health_summary(
    report: TimeoutHotspotReport, *, json_path: Optional[Path], text_path: Optional[Path],
) -> None:
    """gate と同じ手順で `run_health_summary.{json,txt}` に節を足す。"""
    health: Dict[str, Any] = {}
    if json_path is not None and json_path.is_file():
        try:
            loaded = json.loads(json_path.read_text(encoding="utf-8"))
        except ValueError:
            loaded = {}
        if isinstance(loaded, dict):
            health = loaded
    health[HEALTH_KEY] = report.health_section()
    if json_path is not None:
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(
            json.dumps(health, indent=1, sort_keys=True) + "\n", encoding="utf-8"
        )
    if text_path is not None:
        text_path.parent.mkdir(parents=True, exist_ok=True)
        text_path.write_text(
            format_run_health_summary(health) + "\n", encoding="utf-8"
        )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("roots", nargs="+", type=Path, help="result trees to summarize")
    parser.add_argument("--json", type=Path, default=None, help="write the full report")
    parser.add_argument("--health-summary-json", type=Path, default=None,
                        help="run_health_summary.json to merge the section into")
    parser.add_argument("--health-summary-text", type=Path, default=None,
                        help="run_health_summary.txt to rewrite from the merged JSON")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    roots = [root for root in args.roots if root.is_dir()]
    for root in args.roots:
        if not root.is_dir():
            print(f"warning: not a directory: {root}", file=sys.stderr)
    report = build_timeout_hotspot_report(roots)
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(
            json.dumps(report.to_dict(), indent=1, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    if args.health_summary_json is not None or args.health_summary_text is not None:
        merge_into_health_summary(
            report,
            json_path=args.health_summary_json,
            text_path=args.health_summary_text,
        )
    sys.stdout.write(format_timeout_hotspot_report(report))
    return 0


if __name__ == "__main__":
    sys.exit(main())

# -*- coding: utf-8 -*-
"""deadline 前の stack dump 要求と、その dump の永続化（Issue #124 PR-124-C）。

supervisor は deadline まで child の終了を待つ。その待ちの中で、deadline の少し
手前に **一度だけ** child へ `SIGUSR1` を送り、PR-124-B が登録した faulthandler に
全 thread の Python stack を吐かせる。得られた dump は cleanup で消える checkpoint
から run dir 配下の artifact へ退避する。

## この module が守る契約

1. **deadline を延ばさない。** 監視ループ側はこの class の flag を読むだけで、
   worker thread を join しない。journal の読み取り・`os.stat`・dump の polling は
   すべて worker thread の中にある。worker が遅くても失敗してもハングしても、
   kill 開始時刻は `deadline` から `DEADLINE_JITTER_ALLOWANCE_SECONDS` 以内。
2. **readiness を確認できなければ送らない。** 根拠は current execution segment の
   `handler_registered` 行だけ（`faulthandler.register()` が成功した事実）。
   `/proc/<pid>/status` の `SigCgt` は根拠にしない。
3. **送信先は child PID だけ。** process group へは送らない（`killpg` は使わない）。
   送信は同一プロセスへ束縛された pidfd から行い、束縛できない環境では送らない。
4. **「送った」と「取れた」を同一視しない。** `signal_sent` / `dump_observed` /
   `sent_but_unobserved` / `unavailable_reason` を別々に記録する。
5. **取得済み dump は最終 outcome によらず保存する。** deadline 前に正常終了した
   pair の dump も artifact へ退避する。退避の所要時間は kill 開始時刻の検証には
   混ぜない（退避は終了処理が終わってから行う）。

## 記録先を journal にしない理由

journal（`.stage.jsonl`）は child が書く append-only file で、`seq` が 1 から単調
増加し `pair_journal_opened` が 1 本、という性質で execution 境界を判定している
（PR-124-B）。supervisor は別プロセスなので、同じ file へ足すと seq が巻き戻り、
読み手が「複数 execution」と判断してしまう。そこで supervisor 側の観測は
`.runtime-metrics/<pair>.stack-dump.status.json`（schema
``pair-stack-dump-status-v1``）という独立した sidecar に 1 回だけ書く。判定にも
pair-status / receipt schema にも入らない。
"""

from __future__ import annotations

import json
import os
import signal
import stat
import tempfile
import threading
import time
from dataclasses import dataclass
from typing import Any, Dict, Optional

from scripts.function_tracer_pcode.core.stage_journal_reader import (
    JournalRead,
    READINESS_READ_LIMIT_BYTES,
    read_stage_journal,
    select_current_segment,
)

STACK_DUMP_STATUS_SCHEMA = "pair-stack-dump-status-v1"

#: 診断 dump に使う signal。child 側（`cli/pair_diagnostics.py`）と同じもの。
STACK_DUMP_SIGNAL = int(signal.SIGUSR1)

#: 監視ループが 1 回の `wait` で寝る最大時間。
POLL_SLICE_SECONDS = 0.1

#: deadline 到達から kill 開始までに許す scheduler jitter（`POLL_SLICE + 0.4`）。
#: test / AC の上限値で、ここを緩めることは deadline 契約の変更に当たる。
DEADLINE_JITTER_ALLOWANCE_SECONDS = 0.5

#: deadline の何秒前に診断を要求するか。
DEFAULT_STACK_DUMP_LEAD_SECONDS = 2.0

#: worker が dump file の増加を観測する上限（worker 側だけの時間）。
DEFAULT_DUMP_OBSERVE_SECONDS = 1.5

#: dump の増加を見に行く間隔。
DUMP_OBSERVE_SLICE_SECONDS = 0.05

#: 診断 I/O で起こり得る失敗（`except Exception` は使わない）。
_DIAGNOSTIC_ERRORS = (
    AttributeError, LookupError, OSError, RecursionError, TypeError, ValueError,
)

# unavailable の理由（journal 側の語彙は `core/stage_journal_reader.py`）。
UNAVAILABLE_DISABLED = "disabled"
UNAVAILABLE_CANCELLED = "cancelled"
UNAVAILABLE_PROCESS_EXITED = "process_exited"
UNAVAILABLE_IDENTITY_BINDING = "identity_binding_unavailable"
UNAVAILABLE_DUMP_PATH_MISMATCH = "dump_path_mismatch"
UNAVAILABLE_SIGNAL_CONTRACT = "signal_contract_mismatch"
UNAVAILABLE_SIGNAL_FAILED = "signal_failed"

# artifact の退避状態。
ARTIFACT_UNSET = "unset"
ARTIFACT_MISSING = "missing"
ARTIFACT_COPIED = "copied"
ARTIFACT_PARTIAL = "partial"
ARTIFACT_COPY_FAILED = "copy_failed"


@dataclass(frozen=True)
class StackDumpDiagnosticConfig:
    """診断の設定。どれか 1 つでも欠けたら診断は `disabled`。"""

    journal_path: Optional[str] = None
    dump_path_tmp: Optional[str] = None
    dump_artifact_path: Optional[str] = None
    status_output_path: Optional[str] = None
    lead_seconds: float = DEFAULT_STACK_DUMP_LEAD_SECONDS
    observe_seconds: float = DEFAULT_DUMP_OBSERVE_SECONDS

    def disabled_reason(self, *, timeout_seconds: float) -> Optional[str]:
        """診断を行わない理由。`None` なら要求してよい。"""
        if not self.journal_path or not self.dump_path_tmp:
            return UNAVAILABLE_DISABLED
        if not isinstance(self.lead_seconds, (int, float)) or self.lead_seconds <= 0:
            return UNAVAILABLE_DISABLED
        # lead が予算以上だと「deadline より前」が存在しない。
        if float(self.lead_seconds) >= float(timeout_seconds):
            return UNAVAILABLE_DISABLED
        return None


def _absolute(path: Any) -> Optional[str]:
    if not isinstance(path, (str, os.PathLike)):
        return None
    text = os.fspath(path)
    return os.path.abspath(text) if text else None


def _file_size(path: Optional[str]) -> Optional[int]:
    if not path:
        return None
    try:
        status = os.stat(path)
    except _DIAGNOSTIC_ERRORS:
        return None
    if not stat.S_ISREG(status.st_mode):
        return None
    return int(status.st_size)


class StackDumpDiagnostic:
    """deadline 監視ループから見える状態と、その状態を作る daemon worker。

    ループが触ってよいのは `requested` / `request_async()` /
    `cancel_future_requests()` / `disabled_reason` だけ。**join しない。**
    """

    def __init__(
        self,
        config: StackDumpDiagnosticConfig,
        *,
        child_pid: int,
        start_token: Optional[str],
        timeout_seconds: float,
        identity_verifier: Any = None,
    ) -> None:
        self.config = config
        self.child_pid = int(child_pid)
        self.start_token = start_token
        self.timeout_seconds = float(timeout_seconds)
        # 「今なお同じプロセスか」を確かめる呼び出し可能オブジェクト（supervisor の
        # `_same_process` 相当）。診断のためだけに独自定義を作らない。
        self._identity_verifier = identity_verifier
        self._lock = threading.Lock()
        self._cancelled = threading.Event()
        self._thread: Optional[threading.Thread] = None

        self.requested = False
        self.signal_sent = False
        self.dump_observed = False
        self.dump_observed_bytes: Optional[int] = None
        self.dump_baseline_bytes: Optional[int] = None
        # **3 値**。`None` = 「診断 worker が journal を見ていない」（deadline
        # 前に終わった pair など）。`False` = 「見たが readiness を確認できなかった」。
        # 未観測を False に潰すと、集計側で「handler が無かった」と読めてしまう。
        self.handler_registered: Optional[bool] = None
        self.unavailable_reason: Optional[str] = config.disabled_reason(
            timeout_seconds=timeout_seconds
        )
        self.journal_state: Dict[str, Any] = {}
        self.journal_segment_selected = False
        self.artifact_status: str = ARTIFACT_UNSET
        self.artifact_bytes: Optional[int] = None
        self.artifact_path: Optional[str] = _absolute(config.dump_artifact_path)
        self.child_timeout_evidence: Optional[Dict[str, Any]] = None
        self.deadline_monotonic: Optional[float] = None
        self.kill_start_monotonic: Optional[float] = None
        self.requested_monotonic: Optional[float] = None
        self.signal_sent_monotonic: Optional[float] = None

    # -- 監視ループから呼ぶ面 ------------------------------------------------

    @property
    def enabled(self) -> bool:
        return self.config.disabled_reason(timeout_seconds=self.timeout_seconds) is None

    def request_async(self) -> None:
        """診断 worker を起動する。**1 回だけ**、join しない daemon thread。"""
        # lock を取る前に弾く。監視ループを worker の lock 保持で待たせない。
        if self.requested or self._cancelled.is_set() or not self.enabled:
            return
        with self._lock:
            if self.requested or self._cancelled.is_set() or not self.enabled:
                return
            self.requested = True
            self.requested_monotonic = time.monotonic()
            thread = threading.Thread(
                target=self._run_worker,
                name="stack-dump-diagnostic",
                daemon=True,
            )
            self._thread = thread
        # start() は lock の外。worker が即座に lock を取っても詰まらせない。
        thread.start()

    def cancel_future_requests(self) -> None:
        """以後の送信を禁止する（正常終了 / deadline 到達の双方で呼ぶ）。

        Event の確認だけでは「確認後・送信前」の競合を排除できないので、worker は
        送信直前に cancel と pid / start_token を lock の中で再確認する。
        """
        self._cancelled.set()

    def note_deadline(self, deadline_monotonic: float) -> None:
        self.deadline_monotonic = float(deadline_monotonic)

    def note_kill_start(self, kill_start_monotonic: float) -> None:
        self.kill_start_monotonic = float(kill_start_monotonic)

    # -- worker（ここから下はすべて worker thread の中） ----------------------

    def _record_unavailable(self, reason: str) -> None:
        with self._lock:
            if self.unavailable_reason is None:
                self.unavailable_reason = reason

    def _run_worker(self) -> None:
        try:
            self._diagnose()
        except _DIAGNOSTIC_ERRORS as exc:
            self._record_unavailable(f"diagnostic_error:{type(exc).__name__}")

    def _diagnose(self) -> None:
        read = read_stage_journal(
            self.config.journal_path, max_bytes=READINESS_READ_LIMIT_BYTES
        )
        self.journal_state = read.state()
        segment, reason = select_current_segment(
            read, pid=self.child_pid, start_token=self.start_token
        )
        if segment is None:
            # journal は見た（= 観測はした）が current segment を選べなかった。
            self.handler_registered = False
            self._record_unavailable(reason or "journal_unavailable")
            return
        self.journal_segment_selected = True
        handler = segment.handler_row
        if handler is None:
            self.handler_registered = False
            self._record_unavailable("handler_not_registered")
            return
        self.handler_registered = True
        contract_reason = self._readiness_contract_violation(handler.payload)
        if contract_reason is not None:
            self._record_unavailable(contract_reason)
            return
        self.dump_baseline_bytes = _file_size(self.config.dump_path_tmp) or 0
        if not self._send_signal():
            return
        self._observe_dump()

    def _readiness_contract_violation(self, payload: Any) -> Optional[str]:
        """`handler_registered` の payload が current pair の契約と合うか。

        signal 番号・全 thread 出力・dump の書き出し先が現在の設定と一致しない
        journal 行は、current execution のものでも readiness の根拠にしない。
        """
        if not isinstance(payload, dict):
            return UNAVAILABLE_SIGNAL_CONTRACT
        if payload.get("signal_number") != STACK_DUMP_SIGNAL:
            return UNAVAILABLE_SIGNAL_CONTRACT
        if payload.get("all_threads") is not True:
            return UNAVAILABLE_SIGNAL_CONTRACT
        if payload.get("readiness_basis") != "faulthandler_register_returned":
            return UNAVAILABLE_SIGNAL_CONTRACT
        declared_tmp = _absolute(payload.get("dump_path_tmp"))
        if declared_tmp != _absolute(self.config.dump_path_tmp):
            return UNAVAILABLE_DUMP_PATH_MISMATCH
        declared_artifact = payload.get("dump_artifact_path")
        if declared_artifact is not None:
            if _absolute(declared_artifact) != self.artifact_path:
                return UNAVAILABLE_DUMP_PATH_MISMATCH
        return None

    def _identity_is_current(self) -> bool:
        verifier = self._identity_verifier
        if verifier is None:
            return True
        try:
            return bool(verifier())
        except _DIAGNOSTIC_ERRORS:
            return False

    def _send_signal(self) -> bool:
        """pidfd に束縛して 1 回だけ送る。送れなければ理由を残して False。"""
        with self._lock:
            if self._cancelled.is_set():
                self.unavailable_reason = self.unavailable_reason or UNAVAILABLE_CANCELLED
                return False
            if not self._identity_is_current():
                self.unavailable_reason = (
                    self.unavailable_reason or UNAVAILABLE_PROCESS_EXITED
                )
                return False
            pidfd_open = getattr(os, "pidfd_open", None)
            pidfd_send = getattr(signal, "pidfd_send_signal", None)
            if pidfd_open is None or pidfd_send is None:
                # PID 再利用と競合しない送信先を確定できない環境では送らない。
                # SIGUSR1 の既定動作は terminate なので、ここは fail-closed。
                self.unavailable_reason = (
                    self.unavailable_reason or UNAVAILABLE_IDENTITY_BINDING
                )
                return False
            descriptor = None
            try:
                descriptor = pidfd_open(self.child_pid, 0)
                # pidfd を開いたあとにもう一度 identity を確かめる。ここから送信
                # までの間に PID が再利用されても、pidfd は元のプロセスを指す。
                if not self._identity_is_current():
                    self.unavailable_reason = (
                        self.unavailable_reason or UNAVAILABLE_PROCESS_EXITED
                    )
                    return False
                pidfd_send(descriptor, STACK_DUMP_SIGNAL)
            except ProcessLookupError:
                self.unavailable_reason = (
                    self.unavailable_reason or UNAVAILABLE_PROCESS_EXITED
                )
                return False
            except _DIAGNOSTIC_ERRORS as exc:
                self.unavailable_reason = (
                    self.unavailable_reason
                    or f"{UNAVAILABLE_SIGNAL_FAILED}:{type(exc).__name__}"
                )
                return False
            finally:
                if descriptor is not None:
                    try:
                        os.close(descriptor)
                    except OSError:
                        pass
            self.signal_sent = True
            self.signal_sent_monotonic = time.monotonic()
            return True

    def _observe_dump(self) -> None:
        """dump file が増えたかを有限時間だけ見る（worker 側の時間）。"""
        baseline = self.dump_baseline_bytes or 0
        limit = time.monotonic() + max(0.0, float(self.config.observe_seconds))
        while True:
            size = _file_size(self.config.dump_path_tmp)
            if size is not None and size > baseline:
                with self._lock:
                    self.dump_observed = True
                    self.dump_observed_bytes = size
                return
            if time.monotonic() >= limit:
                return
            time.sleep(DUMP_OBSERVE_SLICE_SECONDS)

    # -- 終了処理のあと（監視ループの外）で呼ぶ面 ----------------------------

    @property
    def sent_but_unobserved(self) -> bool:
        """送ったが dump の増加を観測できなかった。**「dump が無い」ではない。**"""
        return bool(self.signal_sent) and not self.dump_observed

    def persist_artifact(self) -> str:
        """checkpoint 配下の dump を run dir 配下の artifact へ退避する。

        **最終 outcome によらず呼ぶ。** deadline 前に正常終了した pair の dump も
        対象で、TIMEOUT だけを保存対象にしない。退避できたかどうかは
        `copied` / `partial` / `missing` / `copy_failed:<errno>` / `unset` で残す。
        「観測しなかった（`sent_but_unobserved`）」と「存在しない（`missing`）」は
        別の事実なので、ここで初めて `missing` を名乗る。
        """
        destination = self.artifact_path
        source = _absolute(self.config.dump_path_tmp)
        if not destination or not source:
            self.artifact_status = ARTIFACT_UNSET
            return self.artifact_status
        size_before = _file_size(source)
        if not size_before:
            # 存在しない、regular file でない、0 byte（handler が書いていない）。
            self.artifact_status = ARTIFACT_MISSING
            self.artifact_bytes = 0 if size_before == 0 else None
            return self.artifact_status
        try:
            os.makedirs(os.path.dirname(destination) or ".", exist_ok=True)
            with open(source, "rb") as reader:
                payload = reader.read()
            descriptor, temporary = tempfile.mkstemp(
                prefix=".stack-dump-", dir=os.path.dirname(destination) or "."
            )
            try:
                with os.fdopen(descriptor, "wb") as writer:
                    writer.write(payload)
                    writer.flush()
                    os.fsync(writer.fileno())
                os.replace(temporary, destination)
            finally:
                if os.path.exists(temporary):
                    os.unlink(temporary)
        except OSError as exc:
            self.artifact_status = f"{ARTIFACT_COPY_FAILED}:{exc.errno}"
            return self.artifact_status
        except _DIAGNOSTIC_ERRORS as exc:
            self.artifact_status = f"{ARTIFACT_COPY_FAILED}:{type(exc).__name__}"
            return self.artifact_status
        self.artifact_bytes = len(payload)
        size_after = _file_size(source)
        # copy の最中に child がまだ書いていた場合、退避したのは途中までの dump。
        self.artifact_status = (
            ARTIFACT_COPIED if size_after == size_before else ARTIFACT_PARTIAL
        )
        return self.artifact_status

    def record_child_timeout_evidence(self, evidence: Optional[Dict[str, Any]]) -> None:
        """cleanup 前に検証した「子の terminal timeout 証拠」を保持する。

        この値は分類（`timeout_kind`）の S 側の根拠**参照**で、判定には使わない。
        検証に失敗した場合も `validated: false` として残し、欠落と区別する。
        """
        self.child_timeout_evidence = evidence

    def status_payload(self) -> Dict[str, Any]:
        deadline = self.deadline_monotonic
        kill_start = self.kill_start_monotonic
        return {
            "schema": STACK_DUMP_STATUS_SCHEMA,
            "child_pid": self.child_pid,
            "child_start_token": self.start_token,
            "enabled": self.enabled,
            "requested": self.requested,
            "handler_registered": self.handler_registered,
            "signal": "SIGUSR1",
            "signal_number": STACK_DUMP_SIGNAL,
            "signal_sent": self.signal_sent,
            "dump_observed": self.dump_observed,
            "dump_observed_bytes": self.dump_observed_bytes,
            "dump_baseline_bytes": self.dump_baseline_bytes,
            "sent_but_unobserved": self.sent_but_unobserved,
            "unavailable_reason": self.unavailable_reason,
            "journal": self.journal_state,
            "journal_current_segment_selected": self.journal_segment_selected,
            "dump_path_tmp": _absolute(self.config.dump_path_tmp),
            "dump_artifact_path": self.artifact_path,
            "artifact_status": self.artifact_status,
            "artifact_bytes": self.artifact_bytes,
            "timeout_seconds": self.timeout_seconds,
            "lead_seconds": float(self.config.lead_seconds),
            "deadline_monotonic": deadline,
            "kill_start_monotonic": kill_start,
            "kill_start_offset_seconds": (
                None if deadline is None or kill_start is None
                else round(kill_start - deadline, 6)
            ),
            "signal_sent_offset_seconds": (
                None if deadline is None or self.signal_sent_monotonic is None
                else round(self.signal_sent_monotonic - deadline, 6)
            ),
            "child_timeout_evidence": self.child_timeout_evidence,
        }

    def write_status(self) -> Optional[str]:
        """sidecar を 1 回だけ書く。失敗しても例外を出さない。"""
        path = _absolute(self.config.status_output_path)
        if not path:
            return None
        payload = self.status_payload()
        try:
            os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
            descriptor, temporary = tempfile.mkstemp(
                prefix=".stack-dump-status-", dir=os.path.dirname(path) or "."
            )
            try:
                with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
                    json.dump(payload, handle, sort_keys=True, separators=(",", ":"))
                    handle.write("\n")
                    handle.flush()
                    os.fsync(handle.fileno())
                os.replace(temporary, path)
            finally:
                if os.path.exists(temporary):
                    os.unlink(temporary)
        except _DIAGNOSTIC_ERRORS:
            return None
        return path


def read_stack_dump_status(path: Any) -> Optional[Dict[str, Any]]:
    """sidecar を読み戻す。無い / 壊れている場合は `None`（0 件ではない）。"""
    resolved = _absolute(path)
    if not resolved:
        return None
    try:
        with open(resolved, "r", encoding="utf-8") as handle:
            payload = json.loads(handle.read())
    except _DIAGNOSTIC_ERRORS:
        return None
    if not isinstance(payload, dict):
        return None
    if payload.get("schema") != STACK_DUMP_STATUS_SCHEMA:
        return None
    return payload


__all__ = [
    "ARTIFACT_COPIED",
    "ARTIFACT_COPY_FAILED",
    "ARTIFACT_MISSING",
    "ARTIFACT_PARTIAL",
    "ARTIFACT_UNSET",
    "DEADLINE_JITTER_ALLOWANCE_SECONDS",
    "DEFAULT_DUMP_OBSERVE_SECONDS",
    "DEFAULT_STACK_DUMP_LEAD_SECONDS",
    "POLL_SLICE_SECONDS",
    "STACK_DUMP_SIGNAL",
    "STACK_DUMP_STATUS_SCHEMA",
    "StackDumpDiagnostic",
    "StackDumpDiagnosticConfig",
    "UNAVAILABLE_DISABLED",
    "UNAVAILABLE_IDENTITY_BINDING",
    "UNAVAILABLE_PROCESS_EXITED",
    "JournalRead",
    "read_stack_dump_status",
]

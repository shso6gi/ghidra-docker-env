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
   `/proc/<pid>/status` の `SigCgt` は根拠にしない。登録は child の一生を覆わない:
   CPython は interpreter の終了処理で faulthandler を外し、登録前の disposition へ戻す。
   だから payload が「外れた後は無視」（``disposition_after_unregister``）と宣言していない
   child には送らない（Issue #204: 既定の terminate のままだと、結果を出し終えて終了処理
   の途中にいる child を殺し、結果を無効にする）。
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

#: worker thread の起動そのものが失敗し得る型。`threading.Thread.start()` は
#: スレッドを作れないと `RuntimeError` を投げる。**この失敗で deadline 監視を
#: 止めないため**、`request_async()` は自分で握り潰して理由だけ残す。
_DIAGNOSTIC_START_ERRORS = (
    AttributeError, MemoryError, OSError, RuntimeError, TypeError, ValueError,
)

#: worker 本体と送信で起こり得る失敗。thread が例外で落ちると Python が stderr へ
#: traceback を出し、それが pair log に混ざるので、ここで受けて理由に変える。
#: 起動側（`_DIAGNOSTIC_START_ERRORS`）と同じ境界にそろえてあり、違いは
#: 起動側だけが `threading` 由来の失敗を名前で区別する点だけ:
#:
#: - `OSError`: pidfd / stat / open（`PermissionError` / `ProcessLookupError` を含む）
#: - `RuntimeError`: interpreter 資源の枯渇、signal API の状態エラー
#: - `MemoryError`: 20 並列で 1 GB 級のプロセスを扱うので現実に起こり得る
#: - `AttributeError` / `TypeError` / `ValueError` / `LookupError`: payload の形が
#:   想定外だったとき（journal は他プロセスが書く file なので信用しない）
#: - `RecursionError`: 自己参照する payload
_WORKER_ERRORS = _DIAGNOSTIC_ERRORS + (MemoryError, RuntimeError)

# unavailable の理由（journal 側の語彙は `core/stage_journal_reader.py`）。
UNAVAILABLE_DISABLED = "disabled"
UNAVAILABLE_CANCELLED = "cancelled"
UNAVAILABLE_PROCESS_EXITED = "process_exited"
UNAVAILABLE_IDENTITY_BINDING = "identity_binding_unavailable"
UNAVAILABLE_DUMP_PATH_MISMATCH = "dump_path_mismatch"
UNAVAILABLE_SIGNAL_CONTRACT = "signal_contract_mismatch"
#: Issue #204: handler が外れた後の disposition が無視だと宣言されていない（signal が child を殺し得る）
UNAVAILABLE_UNREGISTER_TERMINATES = "signal_terminates_after_unregister"
#: child（`cli.pair_diagnostics`）が readiness の payload に載せる「外れた後は無視」の値（唯一の定義）
DISPOSITION_AFTER_UNREGISTER_IGNORE = "ignore"
UNAVAILABLE_SIGNAL_FAILED = "signal_failed"
UNAVAILABLE_START_FAILED = "diagnostic_start_failed"

# 送信開始がどこまで進んだか（`signal_sent` の bool では潰れてしまう区別）。
SIGNAL_START_SENT = "sent"
SIGNAL_START_CLAIMED_NOT_SENT = "claimed_not_sent"
SIGNAL_START_REFUSED_CANCELLED = "refused_cancelled"
SIGNAL_START_NOT_REQUESTED = "not_requested"
SIGNAL_START_NOT_CLAIMED = "not_claimed"

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
        # **送信開始権（一度きり）。cancel と送信開始の linearization point。**
        #
        # worker も cancel も `acquire(blocking=False)` でしか触らないので、
        # **どちらも待たない**。先に取れた側が勝ち、負けた側は即座に戻る:
        #
        # * cancel が取れた -> worker は以後 `acquire` に失敗し、送信を開始できない
        # * worker が取れた -> 送信は「開始済み」。cancel は取得に失敗して即 return し、
        #   syscall の完了は**待たない**（待つと監視ループが worker に引きずられる）
        #
        # 「送信開始の順序づけ」と「syscall の完了」を分けているのが要点。
        # 監視ループが待ってよいものは何一つ無い。
        self._send_permit = threading.Lock()
        #: cancel が送信権を取った（= これ以降 worker は送信を開始できない）。
        #: 書き手は監視スレッドの `cancel_future_requests()` だけ。
        self._send_blocked_by_cancel = False
        self._cancel_linearized_monotonic: Optional[float] = None
        #: 送信権を取った時刻（`send_claimed` が True になった瞬間）。
        self.send_claimed_monotonic: Optional[float] = None
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
        # deadline に到達して termination path へ入った時刻。**まだ signal は
        # 送っていない**（`_terminate_exact_process_group` が終了確認と identity
        # 検証を先に行う）。
        self.deadline_finalization_monotonic: Optional[float] = None
        # 実際に最初の termination signal（SIGTERM）を発した時刻。send が成功した
        # ときだけ入る。deadline 後・signal 前に child が終了した pair では
        # `None` のままで、「kill を開始した」とは記録しない。
        self.kill_signal: Optional[str] = None
        self.kill_signal_monotonic: Optional[float] = None
        self.requested_monotonic: Optional[float] = None
        self.signal_sent_monotonic: Optional[float] = None
        # journal の行は `t_epoch` を持つので、送信した瞬間を epoch でも残す。
        # 集計側はこれで「dump を撮った時点で開いていた region」を切り出す。
        self.signal_sent_epoch: Optional[float] = None

    # -- 監視ループから呼ぶ面 ------------------------------------------------

    @property
    def enabled(self) -> bool:
        return self.config.disabled_reason(timeout_seconds=self.timeout_seconds) is None

    def request_async(self) -> None:
        """診断 worker を起動する。**1 回だけ**、join しない daemon thread。

        **この関数は例外を出さない。** 監視ループはこれを deadline の手前で呼ぶ
        ので、thread を作れない（`RuntimeError: can't start new thread` など）
        場合でもループを抜けさせてはならない。失敗は `unavailable_reason` に
        fail-closed で残し、送信は行わない。
        """
        # lock を取る前に弾く。監視ループを worker の lock 保持で待たせない。
        if self.requested or self._cancelled.is_set() or not self.enabled:
            return
        with self._lock:
            if self.requested or self._cancelled.is_set() or not self.enabled:
                return
            # 起動の成否によらず `requested` を立てる。失敗を毎 poll slice で
            # 再試行すると、そのぶん監視ループが仕事を増やすことになる。
            self.requested = True
            self.requested_monotonic = time.monotonic()
            try:
                thread = threading.Thread(
                    target=self._run_worker,
                    name="stack-dump-diagnostic",
                    daemon=True,
                )
            except _DIAGNOSTIC_START_ERRORS as exc:
                self.unavailable_reason = self.unavailable_reason or (
                    f"{UNAVAILABLE_START_FAILED}:{type(exc).__name__}"
                )
                return
            self._thread = thread
        # start() は lock の外。worker が即座に lock を取っても詰まらせない。
        try:
            thread.start()
        except _DIAGNOSTIC_START_ERRORS as exc:
            self._record_unavailable(
                f"{UNAVAILABLE_START_FAILED}:{type(exc).__name__}"
            )

    def cancel_future_requests(self) -> None:
        """以後の**送信開始**を禁止する（正常終了 / deadline 到達の双方で呼ぶ）。

        **監視ループから呼ばれるので、何も待たない。** 送信権を
        `acquire(blocking=False)` で取りに行くだけで、取れなければ即座に戻る。

        * 取れた場合: cancel が先に linearize した。worker は以後この権利を
          取れないので、**新しい SIGUSR1 の送信を開始できない**。
        * 取れなかった場合: worker がすでに送信を開始している。その事実は
          取り消さない（`signal_sent` / `send_claimed` はそのまま）。
          **進行中の syscall の完了は待たない** —— 待つと、診断 worker が
          syscall で止まっているあいだ監視ループの kill 開始が遅れてしまう。

        つまり「送信開始の順序づけ」だけをここで確定し、「syscall の完了」とは
        分離している。どちらが先だったかは `send_claimed_offset_seconds` と
        `cancel_linearized_offset_seconds` の順序で読める。
        """
        self._cancelled.set()
        if self._send_blocked_by_cancel:
            return
        # blocking=False。**ここが監視ループから見た唯一の同期操作**で、待ちは無い。
        if self._send_permit.acquire(blocking=False):
            self._send_blocked_by_cancel = True
            self._cancel_linearized_monotonic = time.monotonic()

    def note_deadline(self, deadline_monotonic: float) -> None:
        self.deadline_monotonic = float(deadline_monotonic)

    def note_deadline_finalization_start(self, monotonic_time: float) -> None:
        """deadline 到達で termination path へ入った時刻（signal はまだ）。"""
        self.deadline_finalization_monotonic = float(monotonic_time)

    def note_kill_signal(self, name: str, monotonic_time: float) -> None:
        """最初の termination signal を**実際に送れた**時刻。

        `_terminate_exact_process_group` が `os.killpg` の成功後に呼ぶ。属性の
        代入だけで I/O も lock も持たないので、kill 経路を遅らせない。
        """
        self.kill_signal = str(name)
        self.kill_signal_monotonic = float(monotonic_time)

    # -- worker（ここから下はすべて worker thread の中） ----------------------

    def _record_unavailable(self, reason: str) -> None:
        with self._lock:
            if self.unavailable_reason is None:
                self.unavailable_reason = reason

    def _run_worker(self) -> None:
        try:
            self._diagnose()
        except _WORKER_ERRORS as exc:
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
        if payload.get("disposition_after_unregister") != DISPOSITION_AFTER_UNREGISTER_IGNORE:
            return UNAVAILABLE_UNREGISTER_TERMINATES
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
                # ここまでは **gate の外**（遅い処理で監視ループを待たせない）。
                if not self._identity_is_current():
                    self.unavailable_reason = (
                        self.unavailable_reason or UNAVAILABLE_PROCESS_EXITED
                    )
                    return False
                # ここが送信開始の linearization point。**権利を取るだけ**で、
                # syscall はこのあと（権利の外側の話として）行う。取れなければ
                # cancel が先に linearize しているので、送信を開始しない。
                if not self._send_permit.acquire(blocking=False):
                    self.unavailable_reason = (
                        self.unavailable_reason or UNAVAILABLE_CANCELLED
                    )
                    return False
                # 権利を取れた時点で `send_claimed` は True（下の property が
                # 所有から導くので、別 flag への代入を待つ必要が無い）。
                # 以後 cancel は「送信は開始済み」と見なし、**待たずに**戻る。
                self.send_claimed_monotonic = time.monotonic()
                pidfd_send(descriptor, STACK_DUMP_SIGNAL)
                # 観測者が `signal_sent` を見たときに時刻も見えているよう、
                # 時刻を先に書いてから flag を立てる。
                self.signal_sent_monotonic = time.monotonic()
                self.signal_sent_epoch = time.time()
                self.signal_sent = True
            except ProcessLookupError:
                self.unavailable_reason = (
                    self.unavailable_reason or UNAVAILABLE_PROCESS_EXITED
                )
                return False
            except _WORKER_ERRORS as exc:
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
    def send_claimed(self) -> bool:
        """worker が送信権を取った（= 送信開始が linearize した）。

        **permit の所有そのものから導く。** 別 flag を acquire の直後に代入する
        形だと、「acquire 成功 -> 代入」の間に status を snapshot されたときに、
        権利を持っているのに `False` に見える window が残る。

        permit が locked でも cancel が取った場合は worker のものではないので、
        `_send_blocked_by_cancel` で除く。cancel 側にも「acquire 成功 -> flag 代入」
        の window はあるが、`cancel_future_requests()` も `status_payload()` も
        **監視スレッドが呼ぶ**ので、その thread が自分の中間状態を観測することは
        ない（worker はこの property を読まない）。
        """
        return self._send_permit.locked() and not self._send_blocked_by_cancel

    @property
    def signal_start_state(self) -> str:
        """送信開始がどこまで進んだか（`signal_sent` の bool だけでは足りない）。

        * ``sent`` —— 送信の syscall が戻り、送信成功を確認した
        * ``claimed_not_sent`` —— **送信権は取ったが、送信成功をまだ確認できて
          いない**。syscall が失敗した場合だけでなく、まだ実行中（in-flight）・
          ハングしている・worker がその途中で失敗した場合も含む。明示的な失敗は
          `unavailable_reason` が `signal_failed:<例外型>` /
          `process_exited` として持つので、区別はそちらで行う
        * ``refused_cancelled`` —— cancel が先に権利を取ったので開始しなかった
        * ``not_requested`` —— 診断そのものを要求していない（deadline 前に終了）
        * ``not_claimed`` —— 要求はしたが readiness などで権利取得まで進まなかった

        `signal_sent=False` の中身をこの 5 つに分ける（潰さない）のが目的。
        """
        if self.signal_sent:
            return SIGNAL_START_SENT
        if self.send_claimed:
            return SIGNAL_START_CLAIMED_NOT_SENT
        if not self.requested:
            return SIGNAL_START_NOT_REQUESTED
        if self._send_blocked_by_cancel:
            return SIGNAL_START_REFUSED_CANCELLED
        return SIGNAL_START_NOT_CLAIMED

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
        except _WORKER_ERRORS as exc:
            # dump 全体を読むので `MemoryError` も現実に起こり得る。ここで
            # typed に受けて状態へ変える（上位の guard 任せにすると
            # `copy_failed` が残らない）。
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
        kill_signal_start = self.kill_signal_monotonic
        finalization_start = self.deadline_finalization_monotonic

        def _offset(value: Optional[float]) -> Optional[float]:
            if deadline is None or value is None:
                return None
            return round(value - deadline, 6)

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
            # 送信開始の linearization（syscall の成否とは別）。
            "send_claimed": self.send_claimed,
            "send_claimed_offset_seconds": _offset(self.send_claimed_monotonic),
            "signal_start_state": self.signal_start_state,
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
            # deadline 到達 -> termination path へ入った時刻（signal の前）。
            "deadline_finalization_monotonic": finalization_start,
            "deadline_finalization_offset_seconds": _offset(finalization_start),
            # 実際に最初の termination signal を送れた時刻。送っていなければ null
            # （deadline 後・signal 前に child が終了した pair はここが null）。
            "kill_signal": self.kill_signal,
            "kill_signal_monotonic": kill_signal_start,
            # **actual signal start に対応する offset**。以前は termination path
            # へ入った時刻を指していたので、意味を signal 側へそろえた。
            "kill_start_offset_seconds": _offset(kill_signal_start),
            "signal_sent_epoch": self.signal_sent_epoch,
            "signal_sent_offset_seconds": _offset(self.signal_sent_monotonic),
            # cancel が send gate を通った時刻。`signal_sent_offset_seconds` との
            # 前後で「cancel と送信のどちらが先に linearize したか」が読める。
            "cancel_linearized_offset_seconds": _offset(
                self._cancel_linearized_monotonic
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
        except _WORKER_ERRORS:
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

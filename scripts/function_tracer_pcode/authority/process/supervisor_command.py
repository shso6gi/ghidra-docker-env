"""Canonical OS-process supervisor for UNKNOWN-taxonomy v2 workers."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
from typing import Any, Mapping, Optional, Sequence

from scripts.function_tracer_pcode.authority.contracts import authority_digest, canonical_value
from scripts.function_tracer_pcode.authority.process import terminal_evidence
from scripts.function_tracer_pcode.authority.process.supervisor import (
    DurableCheckpointStore,
    ProcessSupervisorAuthorityFactory,
)
from scripts.function_tracer_pcode.authority.process.terminal_driver import (
    DriveResult,
    drive,
)
from scripts.function_tracer_pcode.authority.process.terminal_recovery import ExitMode
from scripts.function_tracer_pcode.authority.process.terminal_transaction import (
    TerminalAuthority,
)
from scripts.function_tracer_pcode.authority.decision.canonical_result import (
    BUNDLE_KIND,
    RESULT_ENVELOPE_FILE,
    validate_durable_child_returncode_observation,
    validate_canonical_result_finalization_bundle,
)
from scripts.function_tracer_pcode.authority.process.stack_dump_diagnostic import (
    DEFAULT_STACK_DUMP_LEAD_SECONDS,
    POLL_SLICE_SECONDS,
    StackDumpDiagnostic,
    StackDumpDiagnosticConfig,
)


COMMAND_SCHEMA = "unknown-taxonomy-v2-process-supervisor-command-v1"
CHILD_ENV_ROOT = "UNKNOWN_TAXONOMY_V2_SUPERVISOR_ROOT"
CHILD_ENV_NONCE = "UNKNOWN_TAXONOMY_V2_EXECUTION_NONCE"
CHILD_ENV_LAUNCH = "UNKNOWN_TAXONOMY_V2_LAUNCH_PATH"
CHILD_ENV_SUPERVISOR_KEY_ID = "UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_ID"
CHILD_ENV_SUPERVISOR_KEY_FILE = "UNKNOWN_TAXONOMY_V2_SUPERVISOR_KEY_FILE"
CHILD_ENV_WORKER_KEY_ID = "UNKNOWN_TAXONOMY_V2_WORKER_KEY_ID"
CHILD_ENV_WORKER_KEY_FILE = "UNKNOWN_TAXONOMY_V2_WORKER_KEY_FILE"

#: Issue #124 PR-124-C: 診断（journal 読取 / bundle 検証 / dump 退避 / sidecar）の
#: 失敗が supervisor の終了状態・exit code・projection を変えないための型付き guard。
#: `except Exception` は使わない（Issue #125 PR-125-B の baseline は delete-only）。
_DIAGNOSTIC_GUARD_ERRORS = (
    ArithmeticError, AttributeError, ImportError, LookupError, MemoryError,
    OSError, RecursionError, RuntimeError, TypeError, ValueError,
)


def _exact_string(name: str, value: Any) -> str:
    if type(value) is not str or not value:
        raise TypeError(f"{name} must be a non-empty exact string")
    return value


def read_process_start_token(pid: int, *, proc_root: Path = Path("/proc")) -> str:
    if type(pid) is not int or pid <= 0:
        raise TypeError("process PID is invalid")
    try:
        stat = (proc_root / str(pid) / "stat").read_text(encoding="utf-8")
        closing = stat.rfind(")")
        fields_after_comm = stat[closing + 2:].split()
        start_time = fields_after_comm[19]
    except Exception as exc:
        raise ValueError("process start token is unavailable") from exc
    if not start_time.isascii() or not start_time.isdecimal():
        raise ValueError("process start token is not canonical")
    return f"linux-proc-starttime-{start_time}"


def process_is_alive(pid: int, start_token: str) -> Optional[bool]:
    """PID + start token の process がいま動いているか（zombie は終了扱い）。

    Issue #165: 終端判断の入力（E と生存の矛盾 / D だけの restart の診断）。
    start token が読めない・一致しないなら、その process はもう居ない。
    ``/proc`` 自体が読めないときだけ None（分からない）。
    """
    try:
        if read_process_start_token(pid) != start_token:
            return False
        stat = (Path("/proc") / str(pid) / "stat").read_text(encoding="utf-8")
    except ValueError:
        return False
    except OSError:
        return None
    return stat[stat.rfind(")") + 2:stat.rfind(")") + 3] not in {"Z", "X"}


def _read_key(path: Path) -> bytes:
    try:
        key = Path(path).read_bytes()
    except Exception as exc:
        raise ValueError("deployment signing key is unavailable") from exc
    if len(key) < 32:
        raise ValueError("deployment signing key is shorter than 32 bytes")
    return key


@dataclass(frozen=True)
class SupervisorCommandConfig:
    checkpoint_root: Path
    authority_output: Path
    working_directory: Path
    execution_nonce: str
    result_occurrence_id: str
    source_snapshot_fingerprint: str
    stream_id: str
    deadline_policy_digest: str
    supervisor_signing_key_id: str
    supervisor_signing_key_file: Path
    worker_signing_key_id: str
    worker_signing_key_file: Path
    # Issue #165: D / E / A（supervisor が観測した終了事実）の署名鍵。
    # supervisor と分類器だけが持ち、worker child の環境には渡さない。
    terminal_evidence_signing_key_id: str
    terminal_evidence_signing_key_file: Path
    timeout_seconds: float
    kill_grace_seconds: float
    child_command: tuple[str, ...]
    allow_child_exit_resolution: bool = False
    # Issue #124 PR-124-C: deadline 手前の stack dump 診断（判定に一切関与しない）。
    # 未指定なら診断は `disabled` で、待ち方の構造だけが従来と同じまま残る。
    # `manifest_entry_preimage_digest` はこれらを含まない（下の property を参照）:
    # 診断の有無で pair の実行 identity を変えてはならない。
    stage_journal_path: Optional[Path] = None
    stack_dump_file: Optional[Path] = None
    stack_dump_artifact: Optional[Path] = None
    diagnostic_status_output: Optional[Path] = None
    stack_dump_lead_seconds: float = DEFAULT_STACK_DUMP_LEAD_SECONDS

    def __post_init__(self) -> None:
        for name in (
            "execution_nonce", "result_occurrence_id",
            "source_snapshot_fingerprint", "stream_id",
            "deadline_policy_digest", "supervisor_signing_key_id",
            "worker_signing_key_id", "terminal_evidence_signing_key_id",
        ):
            _exact_string(name, getattr(self, name))
        if (
            type(self.timeout_seconds) not in {int, float}
            or self.timeout_seconds <= 0
            or type(self.kill_grace_seconds) not in {int, float}
            or self.kill_grace_seconds < 0
        ):
            raise TypeError("process deadline/grace is invalid")
        if type(self.allow_child_exit_resolution) is not bool:
            raise TypeError("child exit resolution mode must be exact bool")
        if (
            type(self.child_command) is not tuple
            or not self.child_command
            or not all(type(item) is str and item for item in self.child_command)
        ):
            raise TypeError("child command must be a non-empty exact tuple")
        if len({
            self.supervisor_signing_key_id, self.worker_signing_key_id,
            self.terminal_evidence_signing_key_id,
        }) != 3:
            raise ValueError("worker, supervisor and terminal evidence key IDs must differ")
        for name in (
            "stage_journal_path", "stack_dump_file", "stack_dump_artifact",
            "diagnostic_status_output",
        ):
            value = getattr(self, name)
            if value is not None and not isinstance(value, (str, os.PathLike)):
                raise TypeError(f"{name} must be a path or None")
        if (
            type(self.stack_dump_lead_seconds) not in {int, float}
            or self.stack_dump_lead_seconds < 0
        ):
            raise TypeError("stack dump lead is invalid")

    @property
    def manifest_entry_preimage_digest(self) -> str:
        return authority_digest({
            "schema": COMMAND_SCHEMA,
            "result_occurrence_id": self.result_occurrence_id,
            "source_snapshot_fingerprint": self.source_snapshot_fingerprint,
            "stream_id": self.stream_id,
            "execution_nonce": self.execution_nonce,
            "deadline_policy_digest": self.deadline_policy_digest,
            "allow_child_exit_resolution": self.allow_child_exit_resolution,
            "working_directory": str(self.working_directory.resolve()),
            "child_command": canonical_value(self.child_command),
        })


class ProcessSupervisorCommand:
    def __init__(self, config: SupervisorCommandConfig) -> None:
        if type(config) is not SupervisorCommandConfig:
            raise TypeError("process supervisor requires exact command config")
        self.config = config
        worker_key = _read_key(config.worker_signing_key_file)
        from scripts.function_tracer_pcode.authority.lifecycle.execution_authority import (
            activate_process_worker_execution_authority_deployment,
        )

        self.execution_authority_startup_receipt = (
            activate_process_worker_execution_authority_deployment(
                key_id=config.worker_signing_key_id,
                key=worker_key,
                key_source_id=str(config.worker_signing_key_file.resolve()),
            )
        )
        self.factory = ProcessSupervisorAuthorityFactory(
            supervisor_signing_key_id=config.supervisor_signing_key_id,
            supervisor_signing_key=_read_key(config.supervisor_signing_key_file),
            worker_signing_key_id=config.worker_signing_key_id,
            worker_signing_key=worker_key,
            terminal_evidence_signing_key_id=config.terminal_evidence_signing_key_id,
            terminal_evidence_signing_key=_read_key(
                config.terminal_evidence_signing_key_file
            ),
        )
        self.store = DurableCheckpointStore(
            config.checkpoint_root, self.factory, config.execution_nonce
        )
        # 自然終了をどう終端へ写すか（runner は検証済み canonical 結果だけを採る）。
        self.exit_mode = (
            ExitMode.CANONICAL_RESULT_REQUIRED
            if config.allow_child_exit_resolution
            else ExitMode.SUPERVISOR_ONLY
        )

    def _durable_terminal_projection(
        self, launch: Any, bundle: Any, *, status: str,
        child_returncode: Any,
    ) -> dict[str, Any]:
        from scripts.function_tracer_pcode.authority.contracts import Outcome

        outcome = Outcome.TIMEOUT if status == "TIMEOUT" else Outcome.ERROR
        error_kind = bundle.error_kind if outcome is Outcome.ERROR else None
        validated = self.factory._validate_supervisor_canonical_bundle(
            bundle.canonical_result_bundle,
            launch=launch,
            outcome=outcome,
            error_kind=error_kind,
        )
        canonical = bundle.canonical_result_bundle
        occurrence = canonical["result_entry_occurrence_receipt"]
        identity = validated["execution_identity"]
        observation_kind = (
            "LIVE_PROCESS_WAIT" if child_returncode is not None
            else "DURABLE_RESTART_NO_CHILD_STATUS"
        )
        validate_durable_child_returncode_observation(
            child_exit_disposition=bundle.child_exit_disposition,
            child_returncode=child_returncode,
            observation_kind=observation_kind,
        )
        return {
            "status": status,
            "authority_kind": type(bundle).__name__,
            "supervisor_authority_kind": type(bundle).__name__,
            "supervisor_final_authority_digest": bundle.bundle_digest,
            "launch_receipt_digest": launch.receipt_digest,
            "finalization_bundle_digest": bundle.bundle_digest,
            "event_stream_authority_digest": (
                bundle.composite_stream_authority_digest
            ),
            "canonical_outcome": validated["outcome"],
            "decision_receipt_digest": validated["decision_receipt_digest"],
            "result_occurrence_id": identity["result_occurrence_id"],
            "result_entry_occurrence_receipt_digest": occurrence[
                "receipt_digest"
            ],
            "execution_identity_digest": identity[
                "execution_identity_digest"
            ],
            "stream_id": identity["stream_id"],
            "source_snapshot_fingerprint": identity[
                "source_snapshot_fingerprint"
            ],
            "canonical_result_bundle_digest": validated["bundle_digest"],
            "canonical_result_bundle_kind": "CanonicalResultFinalizationBundle",
            "canonical_result_payload_preimage_digest": validated[
                "payload_preimage_digest"
            ],
            "semantic_projection_digest": validated[
                "semantic_projection_digest"
            ],
            "error_kind": error_kind,
            "child_exit_disposition": bundle.child_exit_disposition,
            "child_returncode_observation_kind": observation_kind,
            "child_returncode": child_returncode,
            "classification_valid": True,
        }

    def _child_environment(self) -> dict[str, str]:
        environment = dict(os.environ)
        environment.update({
            CHILD_ENV_ROOT: str(self.config.checkpoint_root.resolve()),
            CHILD_ENV_NONCE: self.config.execution_nonce,
            CHILD_ENV_LAUNCH: str((self.store.directory / "launch.json").resolve()),
            CHILD_ENV_SUPERVISOR_KEY_ID: self.config.supervisor_signing_key_id,
            CHILD_ENV_SUPERVISOR_KEY_FILE: str(
                self.config.supervisor_signing_key_file.resolve()
            ),
            CHILD_ENV_WORKER_KEY_ID: self.config.worker_signing_key_id,
            CHILD_ENV_WORKER_KEY_FILE: str(
                self.config.worker_signing_key_file.resolve()
            ),
        })
        return environment

    @staticmethod
    def _barrier_command(read_fd: int, child_command: Sequence[str]) -> tuple[str, ...]:
        return (
            sys.executable, "-m",
            "scripts.function_tracer_pcode.authority.process.supervisor_command",
            "_barrier", str(read_fd), "--", *child_command,
        )

    def _write_projection(self, ownership: Any, payload: Mapping[str, Any]) -> None:
        """projection を公開する（owner の supervisor だけが書く）。

        Issue #165: projection は durable な終端 authority から毎回作り直す出力で、
        入力としては読まない。既存の projection（改ざんを含む）を優先しない。
        """
        if not ownership.held:
            raise RuntimeError("projection write requires supervisor ownership")
        body = dict(payload)
        body["projection_schema"] = COMMAND_SCHEMA
        body["projection_digest"] = authority_digest(body)
        path = self.config.authority_output
        path.parent.mkdir(parents=True, exist_ok=True)
        fd, temporary = tempfile.mkstemp(prefix=".supervisor-", dir=str(path.parent))
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as handle:
                json.dump(body, handle, sort_keys=True, separators=(",", ":"))
                handle.write("\n")
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, path)
            directory_fd = os.open(path.parent, os.O_RDONLY)
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
        finally:
            if os.path.exists(temporary):
                os.unlink(temporary)

    def _resolved_projection(self, authority: TerminalAuthority) -> dict[str, Any]:
        """検証済み canonical 結果 + E の実測 rc の CLI join（canonical RESOLVED）。"""
        envelope = authority.envelope
        receipt = authority.canonical_receipt
        validated = envelope.validated
        identity = validated["execution_identity"]
        occurrence = envelope.bundle.get("result_entry_occurrence_receipt") or {}
        semantic = envelope.bundle["canonical_semantic_result_projection"]
        return {
            "status": "RESOLVED",
            "authority_kind": type(receipt).__name__,
            "supervisor_authority_kind": type(receipt).__name__,
            "supervisor_final_authority_digest": receipt.receipt_digest,
            "launch_receipt_digest": authority.launch.receipt_digest,
            "canonical_outcome": envelope.outcome.value,
            "decision_receipt_digest": validated["decision_receipt_digest"],
            "result_occurrence_id": identity["result_occurrence_id"],
            "result_entry_occurrence_receipt_digest": occurrence.get("receipt_digest"),
            "execution_identity_digest": identity["execution_identity_digest"],
            "stream_id": identity["stream_id"],
            "source_snapshot_fingerprint": identity["source_snapshot_fingerprint"],
            "canonical_result_bundle_digest": validated["bundle_digest"],
            "canonical_result_bundle_kind": BUNDLE_KIND,
            "canonical_result_payload_preimage_digest": validated[
                "payload_preimage_digest"
            ],
            "semantic_projection_digest": validated["semantic_projection_digest"],
            "error_kind": semantic["payload"].get("error_kind"),
            "child_returncode": receipt.child_returncode,
            "classification_valid": True,
        }

    def _same_process(self, process: subprocess.Popen[Any], start_token: str) -> bool:
        try:
            return read_process_start_token(process.pid) == start_token
        except ValueError:
            return process.poll() is not None

    # -- Issue #124 PR-124-C: 非ブロッキングな deadline 監視と診断 --------------
    #
    # deadline の総予算・起点・kill 手順・disposition 文字列・`child_returncode`
    # 検証・`deadline_policy_digest` は**変えない**。変えるのは「待ち方の構造」
    # （1 回待ち -> poll ループ）と、そのループから **join しない** daemon worker
    # に stack dump を要求することだけ。

    def _build_stack_dump_diagnostic(
        self, process: subprocess.Popen[Any], start_token: str,
    ) -> StackDumpDiagnostic:
        """診断 object を組む。**組めなくても例外を出さない。**

        ここで失敗すると `run()` の `except Exception` に落ちて `_resume()` へ
        移ってしまう。診断の都合で outcome / exit code を変えないため、失敗時は
        無効化した診断（`enabled` が False で、送信も退避も行わない）を返す。
        """
        try:
            return self._stack_dump_diagnostic(process, start_token)
        except _DIAGNOSTIC_GUARD_ERRORS:
            return StackDumpDiagnostic(
                StackDumpDiagnosticConfig(),
                child_pid=process.pid,
                start_token=None,
                timeout_seconds=float(self.config.timeout_seconds),
            )

    def _stack_dump_diagnostic(
        self, process: subprocess.Popen[Any], start_token: str,
    ) -> StackDumpDiagnostic:
        config = StackDumpDiagnosticConfig(
            journal_path=(
                None if self.config.stage_journal_path is None
                else str(self.config.stage_journal_path)
            ),
            dump_path_tmp=(
                None if self.config.stack_dump_file is None
                else str(self.config.stack_dump_file)
            ),
            dump_artifact_path=(
                None if self.config.stack_dump_artifact is None
                else str(self.config.stack_dump_artifact)
            ),
            status_output_path=(
                None if self.config.diagnostic_status_output is None
                else str(self.config.diagnostic_status_output)
            ),
            lead_seconds=float(self.config.stack_dump_lead_seconds),
        )
        return StackDumpDiagnostic(
            config,
            child_pid=process.pid,
            start_token=start_token,
            timeout_seconds=float(self.config.timeout_seconds),
            # 送信直前の同一性確認。**`Popen` に触らない**のが要点で、
            # `process.poll()` / `_same_process` は `Popen._waitpid_lock` を取り
            # `waitpid` を呼ぶため、worker thread から呼ぶと監視ループの終了検出と
            # 競合する。identity は `/proc/<pid>/stat` の start token だけで足りる
            # （取れなければ `read_process_start_token` が ValueError を投げ、
            # worker 側が False として扱う）。「すでに終了した」ことは監視ループが
            # `cancel_future_requests()` で伝える。
            identity_verifier=lambda: (
                read_process_start_token(process.pid) == start_token
            ),
        )

    def _wait_for_child_until_deadline(
        self, process: subprocess.Popen[Any], diagnostic: Any, deadline: float,
    ) -> Optional[int]:
        """``deadline``（絶対時刻）まで child を待つ。

        ``None`` を返したら deadline 到達（既存の kill 経路へ）。
        **`deadline` は呼び出し側が 1 回だけ決めてここへ渡す。**この関数は
        deadline を作り直さないし、延ばさない。

        ループの中には同期的な journal 読み取り・`stat`・dump の polling を
        **置かない**。診断の完了 / 失敗 / dump 観測を待つこともしない。診断の
        要求そのものが失敗しても、ループは deadline 監視を続ける。
        """
        diagnostic.note_deadline(deadline)
        lead = float(self.config.stack_dump_lead_seconds)
        # 診断を要求したかはループ側で持つ。診断 object の状態に依存させない
        # （要求が失敗した場合に毎 poll slice で作り直そうとしないため）。
        requested = False
        while True:
            # 最優先は child の終了確認。
            return_code = process.poll()
            if return_code is not None:
                diagnostic.cancel_future_requests()
                return return_code
            now = time.monotonic()
            if now >= deadline:
                diagnostic.cancel_future_requests()
                return None
            if not requested and now >= deadline - lead:
                requested = True
                # daemon worker を起こすだけ。join もしないし戻り値も見ない。
                # 起動が失敗しても理由は診断側に残り、ここは監視を続ける
                # （診断は diagnostic-only で、deadline を動かさない）。
                try:
                    diagnostic.request_async()
                except _DIAGNOSTIC_GUARD_ERRORS:
                    pass
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                continue
            try:
                return_code = process.wait(timeout=min(POLL_SLICE_SECONDS, remaining))
            except subprocess.TimeoutExpired:
                continue
            diagnostic.cancel_future_requests()
            return return_code

    def _child_terminal_timeout_evidence(self) -> Optional[dict[str, Any]]:
        """子が残した canonical 結果から terminal timeout の証拠を**検証して**拾う。

        cleanup で消える checkpoint の中を、消える前に 1 回だけ読む。
        これは `timeout_kind` の S 側の根拠**参照**であって、判定には使わない
        （分類そのものは `reporting/timeout_hotspot_summary` が run 終了後に行う）。
        検証に失敗した場合も `validated: false` として残し、証拠の欠落と区別する。
        """
        path = self.store.directory / RESULT_ENVELOPE_FILE
        try:
            if not path.is_file():
                return None
            envelope = json.loads(path.read_text(encoding="utf-8"))
            payload = envelope["canonical_result_payload"]
            bundle = payload["canonical_result_finalization_bundle"]
        except _DIAGNOSTIC_GUARD_ERRORS as exc:
            return {
                "observed": True,
                "validated": False,
                "validation_error": type(exc).__name__,
            }
        record: dict[str, Any] = {
            "observed": True,
            "validated": False,
            "validation_error": None,
            "source": "checkpoint_result_envelope",
        }
        try:
            preimage = {
                key: value for key, value in payload.items()
                if key != "canonical_result_finalization_bundle"
            }
            validated = validate_canonical_result_finalization_bundle(
                bundle,
                result_payload_preimage=preimage,
                bundle_verification_key_id=self.config.supervisor_signing_key_id,
                bundle_verification_key=_read_key(
                    self.config.supervisor_signing_key_file
                ),
            )
        except _DIAGNOSTIC_GUARD_ERRORS as exc:
            record["validation_error"] = type(exc).__name__
            return record
        identity = validated["execution_identity"]
        selection = bundle.get("terminal_timeout_candidate_selection_receipt")
        selection = selection if isinstance(selection, dict) else {}
        record.update({
            "validated": True,
            "canonical_outcome": validated["outcome"],
            "bundle_digest": validated["bundle_digest"],
            "result_occurrence_id": identity["result_occurrence_id"],
            "stream_id": identity["stream_id"],
            "source_snapshot_fingerprint": identity["source_snapshot_fingerprint"],
            # 受領書は codec で {"object_type", "payload"} に包まれている。
            "terminal_timeout_requirement_ids": sorted({
                str((item.get("payload") if isinstance(item.get("payload"), dict)
                     else item).get("proof_requirement_id"))
                for item in bundle.get("terminal_timeout_receipts") or ()
                if isinstance(item, dict)
                and (item.get("payload") if isinstance(item.get("payload"), dict)
                     else item).get("proof_requirement_id")
            }),
            "terminal_timeout_solver_invocation_id": selection.get(
                "solver_invocation_id"
            ),
            "terminal_timeout_query_digest": selection.get("query_digest"),
        })
        return record

    def _finalize_stack_dump_diagnostic(
        self, diagnostic: Optional[StackDumpDiagnostic],
    ) -> None:
        """終了処理のあと・supervisor 終了の前に、dump を退避して状態を書く。

        **最終 outcome によらず**呼ぶ（deadline 前に正常終了した pair も対象）。
        退避と sidecar 書き出しはここでだけ行い、deadline 監視ループには入れない
        ので、この所要時間は kill 開始時刻の jitter には混ざらない。
        """
        if diagnostic is None:
            return
        diagnostic.cancel_future_requests()
        try:
            diagnostic.record_child_timeout_evidence(
                self._child_terminal_timeout_evidence()
            )
            diagnostic.persist_artifact()
            diagnostic.write_status()
        except _DIAGNOSTIC_GUARD_ERRORS:
            # ここは `run()` の finally の中。診断の失敗で exit code や
            # projection を変えてはいけないので、握り潰して抜ける。
            return

    @staticmethod
    def _invalid_projection(
        launch: Any, error_code: str, *, detail: Optional[str] = None,
        child_returncode: Optional[int] = None,
        diagnostics: Optional[Mapping[str, Any]] = None,
    ) -> dict[str, Any]:
        """INVALID（終端 authority ではない）。どの証拠が足りない / 矛盾するかを残す。"""
        return {
            "status": "INVALID",
            "authority_kind": "InvalidSupervisorCommandProjection",
            "launch_receipt_digest": launch.receipt_digest,
            "error_code": error_code,
            "error_detail": detail,
            "diagnostics": None if diagnostics is None else dict(diagnostics),
            "child_returncode": child_returncode,
        }

    def _terminate_exact_process_group(
        self, process: subprocess.Popen[Any], start_token: str,
        *, on_first_signal: Any = None, signals: Optional[list] = None,
    ) -> str:
        """SIGTERM -> grace -> SIGKILL。**手順と disposition 文字列は不変。**

        ``on_first_signal`` は診断の観測点で、最初の SIGTERM を**実際に送れた**
        ときだけ `(name, monotonic)` で呼ばれる。属性代入だけの軽い callback を
        渡すこと（kill 経路に I/O も lock も足さない）。終了確認や identity 検証
        で signal を送らずに戻る枝では呼ばれないので、送っていない kill を
        「開始した」と記録することはない。

        Issue #165: ``signals`` には ``killpg`` を呼んだ結果だけを順に足す
        （送って戻った / 対象が居なかった）。受信や終了は rc が表すので、ここから
        signal 死を推定しない。
        """
        actions = [] if signals is None else signals
        if process.poll() is not None:
            return f"EXITED_{process.returncode}"
        if not self._same_process(process, start_token):
            raise ValueError("child PID/start-token identity changed before kill")
        if process.poll() is not None:
            return f"EXITED_{process.returncode}"
        first_signal_monotonic = time.monotonic()
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            actions.append(terminal_evidence.SignalAction(
                "SIGTERM", terminal_evidence.SIGNAL_PROCESS_ABSENT,
            ))
            return_code = process.poll()
            if return_code is not None:
                return f"EXITED_{return_code}_BEFORE_SIGTERM"
            raise
        actions.append(terminal_evidence.SignalAction(
            "SIGTERM", terminal_evidence.SIGNAL_SENT,
        ))
        if on_first_signal is not None:
            # 診断の観測点が kill 経路を壊さないようにする。ここは supervisor で
            # 最も安全側に倒すべき経路なので、callback の失敗で disposition や
            # 終了手順が変わることを許さない。
            try:
                on_first_signal("SIGTERM", first_signal_monotonic)
            except _DIAGNOSTIC_GUARD_ERRORS:
                pass
        try:
            process.wait(timeout=self.config.kill_grace_seconds)
            return (
                "SIGTERM_AFTER_DEADLINE"
                if process.returncode == -signal.SIGTERM
                else f"EXITED_{process.returncode}_AFTER_SIGTERM"
            )
        except subprocess.TimeoutExpired:
            if not self._same_process(process, start_token):
                raise ValueError("child PID/start-token identity changed before SIGKILL")
            if process.poll() is not None:
                return f"EXITED_{process.returncode}_BEFORE_SIGKILL"
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                actions.append(terminal_evidence.SignalAction(
                    "SIGKILL", terminal_evidence.SIGNAL_PROCESS_ABSENT,
                ))
                return_code = process.poll()
                if return_code is not None:
                    return f"EXITED_{return_code}_BEFORE_SIGKILL"
                raise
            actions.append(terminal_evidence.SignalAction(
                "SIGKILL", terminal_evidence.SIGNAL_SENT,
            ))
            process.wait()
            return (
                "SIGKILL_AFTER_DEADLINE"
                if process.returncode == -signal.SIGKILL
                else f"EXITED_{process.returncode}_AFTER_SIGKILL"
            )

    def _cleanup_exact_process_group(
        self, process: subprocess.Popen[Any], start_token: Optional[str],
    ) -> str:
        """Best-effort cleanup that never signals an unverified/reused PID."""
        return_code = process.poll()
        if return_code is not None:
            return f"EXITED_{return_code}"
        if start_token is None or not self._same_process(process, start_token):
            return "SKIPPED_UNVERIFIED_PROCESS_IDENTITY"
        return_code = process.poll()
        if return_code is not None:
            return f"EXITED_{return_code}_BEFORE_CLEANUP_SIGKILL"
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            return_code = process.poll()
            return (
                f"EXITED_{return_code}_BEFORE_CLEANUP_SIGKILL"
                if return_code is not None
                else "PROCESS_LOOKUP_RACE_DURING_CLEANUP"
            )
        process.wait()
        return "SIGKILL_DURING_EXCEPTION_CLEANUP"

    def _load_durable_launch(self) -> Any:
        launch = self.factory.decode(json.loads(
            (self.store.directory / "launch.json").read_text(encoding="utf-8")
        ))
        if (
            launch.payload["result_occurrence_id"]
            != self.config.result_occurrence_id
            or launch.payload["manifest_entry_preimage_digest"]
            != self.config.manifest_entry_preimage_digest
            or launch.payload["execution_nonce"] != self.config.execution_nonce
            or launch.payload["stream_id"] != self.config.stream_id
            or launch.payload["source_snapshot_fingerprint"]
            != self.config.source_snapshot_fingerprint
            or launch.payload["deadline_policy_digest"]
            != self.config.deadline_policy_digest
        ):
            raise ValueError("durable launch differs from supervisor command config")
        return launch

    # -- Issue #165: 終了の観測（D / E）と終端 ----------------------------------

    def _record_deadline(
        self, ownership: Any, launch: Any, *, detected_offset_seconds: float,
    ) -> None:
        """deadline に達した事実を、signal を送る前に durable にする（D）。"""
        payload = terminal_evidence.deadline_payload(
            launch,
            configured_timeout_seconds=float(self.config.timeout_seconds),
            deadline_detected_offset_seconds=max(0.0, detected_offset_seconds),
        )
        receipt = self.factory.issue_terminal_evidence(
            terminal_evidence.DEADLINE_RECEIPT_KIND, payload,
        )
        self.store.persist_deadline(ownership, receipt)

    def _record_child_exit(
        self, ownership: Any, *, returncode: int, disposition: str,
        signals: tuple,
    ) -> None:
        """wait で取った child の終了を durable にする（E）。値は観測そのもの。"""

        def build(*, launch: Any, deadline: Any, anchor: Any, envelope: Any) -> Any:
            payload = terminal_evidence.child_exit_payload(
                launch, deadline=deadline, child_returncode=returncode,
                child_exit_disposition=disposition, signal_actions=signals,
                envelope=envelope, anchor=anchor,
            )
            return self.factory.issue_terminal_evidence(
                terminal_evidence.CHILD_EXIT_RECEIPT_KIND, payload,
            )

        self.store.record_child_exit(ownership, build)

    def _project(self, launch: Any, result: DriveResult) -> tuple[int, dict[str, Any]]:
        """drive の結果を projection と supervisor の exit code にする。"""
        authority = result.authority
        if authority is None:
            return 2, self._invalid_projection(
                launch, result.invalid_code, detail=result.detail,
                child_returncode=result.child_returncode,
                diagnostics=result.diagnostics,
            )
        if authority.status == "RESOLVED":
            return 0, self._resolved_projection(authority)
        returncode = authority.child_exit.payload["child_returncode"]
        projection = self._durable_terminal_projection(
            launch, authority.bundle, status=authority.status,
            child_returncode=returncode,
        )
        if authority.status == "TIMEOUT":
            return 124, projection
        return (returncode if returncode else 2), projection

    def _resume(self, ownership: Any, launch: Any = None) -> int:
        """durable な evidence だけから終端を決め直す（run と同じ ``drive``）。"""
        launch = self._load_durable_launch() if launch is None else launch
        try:
            exit_code, projection = self._project(launch, drive(
                self.store, ownership, mode=self.exit_mode,
                process_alive=process_is_alive,
            ))
        except Exception as exc:
            projection = self._invalid_projection(
                launch, "DURABLE_RESTART_AUTHORITY_INVALID",
                detail=f"{type(exc).__name__}: {exc}"[:500],
            )
            exit_code = 2
        self._write_projection(ownership, projection)
        return exit_code

    def run(self) -> int:
        # Issue #165: 起動から projection の公開まで、この store の owner は
        # この supervisor 1 つ（restart の重複起動は先の終了を待つ）。
        with self.store.supervisor_ownership() as ownership:
            if (self.store.directory / "launch.json").exists():
                return self._resume(ownership)
            read_fd, write_fd = os.pipe()
            process: Optional[subprocess.Popen[Any]] = None
            launch: Any = None
            start_token: Optional[str] = None
            diagnostic: Optional[StackDumpDiagnostic] = None
            try:
                process = subprocess.Popen(
                    self._barrier_command(read_fd, self.config.child_command),
                    cwd=self.config.working_directory,
                    env=self._child_environment(),
                    pass_fds=(read_fd,),
                    start_new_session=True,
                )
                os.close(read_fd)
                read_fd = -1
                start_token = read_process_start_token(process.pid)
                launch = self.factory.issue_launch(
                    result_occurrence_id=self.config.result_occurrence_id,
                    manifest_entry_preimage_digest=(
                        self.config.manifest_entry_preimage_digest
                    ),
                    execution_nonce=self.config.execution_nonce,
                    child_pid=process.pid,
                    child_start_token=start_token,
                    stream_id=self.config.stream_id,
                    source_snapshot_fingerprint=(
                        self.config.source_snapshot_fingerprint
                    ),
                    deadline_policy_digest=self.config.deadline_policy_digest,
                )
                self.store.persist_launch(launch)
                os.write(write_fd, b"1")
                os.close(write_fd)
                write_fd = -1
                # Issue #124 PR-124-C: deadline の起点は、この PR の前に
                # `process.wait(timeout=self.config.timeout_seconds)` を呼んでいた
                # のと**同じ位置**（barrier 解放の直後）で 1 回だけ固定する。診断
                # object の生成はそのあとなので、生成時間が予算の外へ逃げない。
                deadline = time.monotonic() + float(self.config.timeout_seconds)
                diagnostic = self._build_stack_dump_diagnostic(process, start_token)
                return_code = self._wait_for_child_until_deadline(
                    process, diagnostic, deadline
                )
                signals: list = []
                if return_code is None:
                    # deadline 到達。ここはまだ signal を送っていないので「termination
                    # path へ入った時刻」として記録し、実際の SIGTERM は
                    # `on_first_signal` で測る。Issue #165: deadline の事実（D）を
                    # signal より前に durable にし、child の終了（E）は wait で
                    # 取った rc と実際に送った signal だけから作る。
                    detected = time.monotonic()
                    diagnostic.note_deadline_finalization_start(detected)
                    self._record_deadline(
                        ownership, launch,
                        detected_offset_seconds=(
                            detected - (deadline - float(self.config.timeout_seconds))
                        ),
                    )
                    disposition = self._terminate_exact_process_group(
                        process, start_token,
                        on_first_signal=diagnostic.note_kill_signal, signals=signals,
                    )
                    return_code = process.returncode
                else:
                    disposition = terminal_evidence.natural_exit_disposition(return_code)
                self._record_child_exit(
                    ownership, returncode=return_code, disposition=disposition,
                    signals=tuple(signals),
                )
                return self._resume(ownership, launch)
            except Exception:
                # 観測か永続化の途中で失敗した。E が durable でなければ drive が
                # INVALID にする（rc も signal 死も推定しない）。
                if launch is not None:
                    return self._resume(ownership, launch)
                raise
            finally:
                for descriptor in (read_fd, write_fd):
                    if descriptor >= 0:
                        os.close(descriptor)
                if process is not None and process.poll() is None:
                    self._cleanup_exact_process_group(process, start_token)
                # 取得できた dump は最終 outcome によらず run dir へ退避する。
                # runner の `process_authority_cleanup` はこのプロセスが終わってから
                # 走るので、ここが「cleanup 前」の最後の機会になる。
                self._finalize_stack_dump_diagnostic(diagnostic)


def _barrier_main(arguments: Sequence[str]) -> int:
    if len(arguments) < 3 or arguments[1] != "--":
        raise ValueError("worker barrier arguments are invalid")
    descriptor = int(arguments[0])
    token = os.read(descriptor, 1)
    os.close(descriptor)
    if token != b"1":
        raise ValueError("worker barrier release authority is invalid")
    os.execvpe(arguments[2], tuple(arguments[2:]), os.environ)
    raise AssertionError("exec returned unexpectedly")


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkpoint-root", required=True)
    parser.add_argument("--authority-output", required=True)
    parser.add_argument("--working-directory", required=True)
    parser.add_argument("--execution-nonce", required=True)
    parser.add_argument("--result-occurrence-id", required=True)
    parser.add_argument("--source-snapshot-fingerprint", required=True)
    parser.add_argument("--stream-id", required=True)
    parser.add_argument("--deadline-policy-digest", required=True)
    parser.add_argument("--supervisor-signing-key-id", required=True)
    parser.add_argument("--supervisor-signing-key-file", required=True)
    parser.add_argument("--worker-signing-key-id", required=True)
    parser.add_argument("--worker-signing-key-file", required=True)
    parser.add_argument("--terminal-evidence-signing-key-id", required=True)
    parser.add_argument("--terminal-evidence-signing-key-file", required=True)
    parser.add_argument("--timeout-seconds", required=True, type=float)
    parser.add_argument("--kill-grace-seconds", type=float, default=30.0)
    parser.add_argument("--allow-child-exit-resolution", action="store_true")
    # Issue #124 PR-124-C: 診断だけの引数。省略すると診断は disabled になり、
    # 待ち方の構造・kill 手順・判定はすべて従来どおり。
    parser.add_argument("--stage-journal", default=None,
                        help="child が書く pair-stage-journal-v1 (readiness の根拠)")
    parser.add_argument("--stack-dump-file", default=None,
                        help="child の faulthandler が書く checkpoint 配下の dump")
    parser.add_argument("--stack-dump-artifact", default=None,
                        help="cleanup 後も残る dump の退避先 (.runtime-metrics)")
    parser.add_argument("--diagnostic-status-output", default=None,
                        help="診断状態 (pair-stack-dump-status-v1) の書き出し先")
    parser.add_argument("--stack-dump-lead-seconds", type=float,
                        default=DEFAULT_STACK_DUMP_LEAD_SECONDS,
                        help="deadline の何秒前に dump を要求するか")
    parser.add_argument("child_command", nargs=argparse.REMAINDER)
    return parser


def main(arguments: Optional[Sequence[str]] = None) -> int:
    values = tuple(sys.argv[1:] if arguments is None else arguments)
    if values and values[0] == "_barrier":
        return _barrier_main(values[1:])
    args = _parser().parse_args(values)
    child_command = tuple(args.child_command)
    if child_command and child_command[0] == "--":
        child_command = child_command[1:]
    config = SupervisorCommandConfig(
        checkpoint_root=Path(args.checkpoint_root),
        authority_output=Path(args.authority_output),
        working_directory=Path(args.working_directory),
        execution_nonce=args.execution_nonce,
        result_occurrence_id=args.result_occurrence_id,
        source_snapshot_fingerprint=args.source_snapshot_fingerprint,
        stream_id=args.stream_id,
        deadline_policy_digest=args.deadline_policy_digest,
        supervisor_signing_key_id=args.supervisor_signing_key_id,
        supervisor_signing_key_file=Path(args.supervisor_signing_key_file),
        worker_signing_key_id=args.worker_signing_key_id,
        worker_signing_key_file=Path(args.worker_signing_key_file),
        terminal_evidence_signing_key_id=args.terminal_evidence_signing_key_id,
        terminal_evidence_signing_key_file=Path(
            args.terminal_evidence_signing_key_file
        ),
        timeout_seconds=args.timeout_seconds,
        kill_grace_seconds=args.kill_grace_seconds,
        allow_child_exit_resolution=args.allow_child_exit_resolution,
        child_command=child_command,
        stage_journal_path=(
            None if args.stage_journal is None else Path(args.stage_journal)
        ),
        stack_dump_file=(
            None if args.stack_dump_file is None else Path(args.stack_dump_file)
        ),
        stack_dump_artifact=(
            None if args.stack_dump_artifact is None
            else Path(args.stack_dump_artifact)
        ),
        diagnostic_status_output=(
            None if args.diagnostic_status_output is None
            else Path(args.diagnostic_status_output)
        ),
        stack_dump_lead_seconds=args.stack_dump_lead_seconds,
    )
    return ProcessSupervisorCommand(config).run()


if __name__ == "__main__":
    raise SystemExit(main())

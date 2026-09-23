# -*- coding: utf-8 -*-
"""Issue #163: supervisor の invocation（起動・再起動）と後始末（test 専用）。

寿命が違う 2 つを分ける。

* ``SupervisorCase``（``_supervisor_support``）: pair 全体。config・durable
  store・pair log・harness の記録 root を持ち、複数の invocation にまたがる。
* ``SupervisorRun``（本 module）: supervisor の **1 回の invocation だけ**の
  immutable な観測。開始時に確保した ``SupervisorInvocationId`` に束縛され、
  値はすべてその invocation 自身の記録から作る。case で共有している file
  （``authority_output`` など）の「いまの値」から後読みしないので、crash した
  invocation のあとで restart しても前の invocation の観測を引き継がない。

invocation は pytest の process から ``fork`` した process で
``ProcessSupervisorCommand(config).run()`` を実行する。fork 先では production
の外側に観測を入れる（production の中身は変えない）:

* ``subprocess.Popen``（barrier の command だけ）: この invocation が起こした
  worker の PID / start token。
* barrier の pipe への解放 byte（``os.write(b"1")``）: その瞬間に
  ``launch.json`` が durable か（launch-before-exec の parent 側の観測）。
* ``authority_output`` への ``os.replace`` / ``os.rename``: この invocation が
  公開した projection の bytes（公開しなかった invocation の ``projection`` は
  None。正常に戻ったのに捕まえられなかったら harness の失敗にする）。
* fd 1 / 2 と ``sys.stdout`` / ``sys.stderr`` を pair log へ向ける（runner と
  同じく supervisor と worker の出力が pair log に集まり、
  ``classify_pair_status`` はその log の結果 JSON と envelope を突き合わせる）。
  pair log は production の意味で pair 単位（runner は resume の出力も同じ log
  に足す）なので case が持つ。

分類の入力（durable store・pair log・鍵 file）の digest は
``classification_inputs`` の 1 箇所で数える。run は終了時点の値を持ち、分類の
ときに今の値と比べる。

fork の時点で pytest の process に他の thread が残っていても、fork 先が lock
待ちで止まった場合は待ち上限（``timeout + grace + 60s``）で失敗になる。
起動の仕方（fork / exec / 並行起動）を変えるときに触るのはこの module だけ。
"""

from __future__ import annotations

from dataclasses import dataclass, field
import os
from pathlib import Path
import signal
import stat
import subprocess
import sys
import time
import traceback
from typing import TYPE_CHECKING, Any, Mapping, Optional, Sequence

from scripts.function_tracer_pcode.tests.unit._supervisor_faults import (
    ChildStopped,
    Deadline,
    Fault,
    install_deadline_control,
    install_publication_faults,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_records import (
    ChildIdentity,
    InvocationRecords,
    SupervisorInvocationId,
    read_json,
    read_json_lines,
    sha256_of,
    write_bytes,
    write_json,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_store import (
    StoreSnapshot,
    inspect_store,
)

if TYPE_CHECKING:
    from scripts.function_tracer_pcode.tests.unit._supervisor_support import (
        SupervisorCase,
    )

#: fork した supervisor が production の例外で抜けたときの exit code。
_SUPERVISOR_RAISED_EXIT = 70
#: supervisor が終わるまで待つ上限に、config の timeout + grace へ足す余裕。
_WAIT_MARGIN_SECONDS = 60.0


class SupervisorRaised(AssertionError):
    """production の ``run()`` が例外で抜けた（traceback を持つ）。"""


@dataclass(frozen=True)
class SupervisorRun:
    """supervisor の 1 回の invocation だけの観測（別 invocation から継承しない）。"""

    case: "SupervisorCase" = field(repr=False, compare=False)
    #: この invocation の identity（case の中で一意、開始順）。
    invocation: SupervisorInvocationId
    #: supervisor の exit code。停止点で crash した場合は None。
    exit_code: Optional[int]
    #: supervisor が crash 停止点で落ちたか。
    crashed: bool
    #: この invocation が公開した projection（digest 検証済み）。公開しなければ None。
    projection: Optional[Mapping[str, Any]]
    #: invocation が終わった時点の durable store。
    store: StoreSnapshot
    #: invocation が終わった時点の分類の入力（``classification_inputs``）。
    classification_inputs: Mapping[str, str]
    #: この invocation が起こした worker（restart / 起こす前に落ちたなら None）。
    child: Optional[ChildIdentity]
    #: その worker が本処理の前に書いた launch の観測（無ければ None）。
    launch_evidence: Optional[Mapping[str, Any]]
    #: この invocation が barrier を解放した瞬間に ``launch.json`` が durable
    #: だったか（barrier を解放しなかった invocation は None）。
    launch_durable_at_barrier_release: Optional[bool]
    #: worker が止まった瞬間の store。``Deadline.AT_CHILD_STOP`` か
    #: ``ChildStopped`` の停止点を使い、worker が実際に止まった invocation だけが持つ。
    store_at_child_stop: Optional[StoreSnapshot]
    #: この invocation の間に発火した停止点（worker の分、supervisor の分の順）。
    faults_fired: tuple[Mapping[str, Any], ...]
    #: この invocation の記録（分類の対象を決める。test は直接読まない）。
    records: InvocationRecords = field(repr=False, compare=False)


# ---------------------------------------------------------------------------
# worker の生存確認と後始末
# ---------------------------------------------------------------------------


def _process_alive(identity: ChildIdentity) -> bool:
    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        read_process_start_token,
    )

    try:
        if read_process_start_token(identity.pid) != identity.start_token:
            return False
        fields = Path(f"/proc/{identity.pid}/stat").read_text(encoding="utf-8")
    except (OSError, ValueError):
        return False
    return fields[fields.rfind(")") + 2] not in {"Z", "X"}


def worker_alive(run: SupervisorRun) -> bool:
    """``run`` が起こした worker（PID + start token）がまだ動いているか。"""

    return run.child is not None and _process_alive(run.child)


def terminate_leftover_workers(case: "SupervisorCase") -> None:
    """case のどの invocation が起こした worker も、同一性を確かめてから止める。

    worker の identity は harness 自身の記録（起こした invocation が Popen の
    直後に書いたもの）から取る。durable store の ``launch.json`` は test が
    書き換えうるので使わない。
    """

    for records in case.records.invocations():
        identity = records.child()
        if identity is None:
            continue
        if not _process_alive(identity):
            _reap_if_our_child(identity.pid)
            continue
        try:
            os.killpg(identity.pid, signal.SIGKILL)
        except ProcessLookupError:
            continue
        deadline = time.monotonic() + 10.0
        while _process_alive(identity) and time.monotonic() < deadline:
            _reap_if_our_child(identity.pid)
            time.sleep(0.01)
        if _process_alive(identity):
            raise AssertionError(f"worker {identity.pid} survived SIGKILL")


def _reap_if_our_child(pid: int) -> None:
    """孤児が pytest（container の PID 1 など）に付け替わっていたら回収する。"""

    try:
        os.waitpid(pid, os.WNOHANG)
    except ChildProcessError:
        pass


# ---------------------------------------------------------------------------
# invocation
# ---------------------------------------------------------------------------


def run_supervisor(
    case: "SupervisorCase", *, deadline: str = Deadline.TIMER,
    faults: Sequence[Fault] = (),
) -> SupervisorRun:
    """case の最初の invocation（worker を起こす）。"""

    if case.records.invocations():
        raise AssertionError("run_supervisor starts a pair; use restart_supervisor")
    return _SupervisorInvocation.start(case, deadline=deadline, faults=faults).wait()


def restart_supervisor(
    case: "SupervisorCase", *, faults: Sequence[Fault] = (),
) -> SupervisorRun:
    """同じ config の supervisor をもう一度起こす（production の resume 経路）。"""

    if not case.records.invocations():
        raise AssertionError("restart_supervisor needs an earlier invocation")
    if any(isinstance(fault.at, ChildStopped) for fault in faults):
        raise ValueError("a restart starts no worker child to stop")
    return _SupervisorInvocation.start(case, deadline=Deadline.TIMER, faults=faults).wait()


def _pair_log_size(case: "SupervisorCase") -> int:
    return case.pair_log.stat().st_size if case.pair_log.exists() else 0


def classification_inputs(case: "SupervisorCase") -> Mapping[str, str]:
    """production の分類器が読む case 側の入力の digest（projection 以外）。"""

    config = case.config
    inputs = {
        "pair-log": sha256_of(case.pair_log),
        "supervisor-key": sha256_of(Path(config.supervisor_signing_key_file)),
        "worker-key": sha256_of(Path(config.worker_signing_key_file)),
    }
    inputs.update({
        f"store/{name}": digest
        for name, digest in inspect_store(case.store_directory).digests.items()
    })
    return inputs


class _SupervisorInvocation:
    """fork した supervisor 1 つ。identity は ``start`` の時点で消費される。"""

    def __init__(
        self, case: "SupervisorCase", records: InvocationRecords, pid: int,
        log_start: int, limit: float,
    ) -> None:
        self.case = case
        self.records = records
        self.pid = pid
        self.log_start = log_start
        self.limit = limit

    @classmethod
    def start(
        cls, case: "SupervisorCase", *, deadline: str, faults: Sequence[Fault],
    ) -> "_SupervisorInvocation":
        for fault in faults:
            if fault.action != "crash":
                raise ValueError("a supervisor fault can only crash the supervisor")
        records = case.records.allocate_invocation()
        log_start = _pair_log_size(case)
        sys.stdout.flush()
        sys.stderr.flush()
        pid = os.fork()
        if pid == 0:  # pragma: no cover - runs in the forked supervisor
            _supervise_in_fork(case, records, deadline, faults)
        limit = (
            time.monotonic() + float(case.config.timeout_seconds)
            + float(case.config.kill_grace_seconds) + _WAIT_MARGIN_SECONDS
        )
        return cls(case, records, pid, log_start, limit)

    def wait(self) -> SupervisorRun:
        process_status = self._reap()
        return self._observe(process_status)

    def _reap(self) -> int:
        reaped = False
        try:
            while True:
                waited, status = os.waitpid(self.pid, os.WNOHANG)
                if waited == self.pid:
                    reaped = True
                    return os.waitstatus_to_exitcode(status)
                if time.monotonic() > self.limit:
                    raise AssertionError("supervisor did not finish within its budget")
                time.sleep(0.01)
        finally:
            if not reaped:
                # 待ち上限超過や KeyboardInterrupt。まだ回収していない自分の子だけを
                # 止める（回収済みの PID は再利用されうるので触らない）。
                os.kill(self.pid, signal.SIGKILL)
                os.waitpid(self.pid, 0)

    def _observe(self, process_status: int) -> SupervisorRun:
        case, records = self.case, self.records
        status = read_json(records.status)
        supervisor_faults = read_json_lines(records.faults)
        crashed = status is None and any(
            entry["action"] == "crash" for entry in supervisor_faults
        )
        if status is None and not crashed:
            raise AssertionError(
                f"{records.invocation} ended with {process_status} without a status "
                "record; pair log appended while it ran (other processes included):\n"
                f"{_read_span(case, self.log_start, _pair_log_size(case))}"
            )
        if status is not None and "exception" in status:
            raise SupervisorRaised(status["exception"])
        projection = _read_projection(records.projection)
        if status is not None and projection is None:
            # run() も _resume() も戻る前に projection を書く。捕まえられなかった
            # なら production の書き方が変わっている（黙って None にしない）。
            raise AssertionError(
                f"{records.invocation} returned but its projection was not captured"
            )
        child = records.child()
        child_records = None if child is None else case.records.child(child)
        evidence = None if child_records is None else read_json(child_records.launch_evidence)
        at_stop = read_json(records.store_at_child_stop)
        release = read_json(records.barrier_release)
        return SupervisorRun(
            case=case,
            invocation=records.invocation,
            exit_code=None if status is None else status["exit_code"],
            crashed=crashed,
            projection=projection,
            store=inspect_store(case.store_directory),
            classification_inputs=classification_inputs(case),
            child=child,
            launch_evidence=evidence,
            launch_durable_at_barrier_release=(
                None if release is None else release["launch_durable"]
            ),
            store_at_child_stop=(
                None if at_stop is None else StoreSnapshot.from_json(at_stop)
            ),
            faults_fired=(
                () if child_records is None else read_json_lines(child_records.faults)
            ) + supervisor_faults,
            records=records,
        )


# ---------------------------------------------------------------------------
# fork 先（supervisor process）
# ---------------------------------------------------------------------------


def _supervise_in_fork(  # pragma: no cover - runs in the forked supervisor
    case: "SupervisorCase", records: InvocationRecords, deadline: str,
    faults: Sequence[Fault],
) -> None:
    code = _SUPERVISOR_RAISED_EXIT
    try:
        log = os.open(case.pair_log, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o644)
        os.dup2(log, 1)
        os.dup2(log, 2)
        # pytest の capture が持っている Python 側の stdout / stderr も fd へ戻す。
        sys.stdout = open(1, "w", buffering=1, closefd=False)
        sys.stderr = open(2, "w", buffering=1, closefd=False)
        _record_started_child(records)
        _observe_barrier_release(case.store_directory, records)
        _capture_projection(case.config.authority_output, records)
        # 停止点は観測の外側に入れる（projection を公開する前に落ちたら、
        # この invocation は projection を公開していない）。
        install_publication_faults(
            faults, role="supervisor", store_directory=case.store_directory,
            projection=case.config.authority_output, sink=records.faults,
        )
        install_deadline_control(
            deadline=deadline, faults=faults, invocation=records,
            harness=case.records, store_directory=case.store_directory,
        )
        from scripts.function_tracer_pcode.authority.process.supervisor_command import (
            ProcessSupervisorCommand,
        )

        code = ProcessSupervisorCommand(case.config).run()
        write_json(records.status, {"exit_code": code})
    except BaseException:  # fork 先は報告して終わる。pytest の中へ巻き戻さない
        write_json(records.status, {"exception": traceback.format_exc()})
        code = _SUPERVISOR_RAISED_EXIT
    finally:
        os._exit(code)


def _record_started_child(records: InvocationRecords) -> None:
    """この invocation が起こした worker（barrier の process）を Popen の直後に記録する。"""

    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        read_process_start_token,
    )

    class RecordingPopen(subprocess.Popen):
        def __init__(self, args: Any, *rest: Any, **kwargs: Any) -> None:
            super().__init__(args, *rest, **kwargs)
            is_barrier = not isinstance(args, (str, bytes)) and "_barrier" in tuple(args)
            if is_barrier and not records.started_child.exists():
                write_json(records.started_child, {
                    "pid": self.pid, "start_token": read_process_start_token(self.pid),
                })

    subprocess.Popen = RecordingPopen


def _observe_barrier_release(store_directory: Path, records: InvocationRecords) -> None:
    """barrier の pipe への解放 byte を書く直前に、launch が durable かを記録する。"""

    original = os.write
    launch = Path(store_directory) / "launch.json"

    def write(descriptor: int, data: Any) -> int:
        if bytes(data) == b"1" and stat.S_ISFIFO(os.fstat(descriptor).st_mode):
            write_json(records.barrier_release, {"launch_durable": launch.is_file()})
        return original(descriptor, data)

    os.write = write


def _capture_projection(authority_output: Path, records: InvocationRecords) -> None:
    """この invocation が ``authority_output`` へ公開した bytes をそのまま残す。"""

    target = Path(authority_output).resolve()

    def _wrap(original: Any) -> Any:
        def publish(source: Any, destination: Any, *args: Any, **kwargs: Any) -> Any:
            if Path(os.fspath(destination)).resolve() != target:
                return original(source, destination, *args, **kwargs)
            data = Path(os.fspath(source)).read_bytes()
            result = original(source, destination, *args, **kwargs)
            write_bytes(records.projection, data)
            return result
        return publish

    os.replace = _wrap(os.replace)
    os.rename = _wrap(os.rename)


# ---------------------------------------------------------------------------
# 読み出し
# ---------------------------------------------------------------------------


def _read_projection(path: Path) -> Optional[Mapping[str, Any]]:
    from scripts.function_tracer_pcode.authority.contracts import authority_digest

    payload = read_json(path)
    if payload is None:
        return None
    body = {key: value for key, value in payload.items() if key != "projection_digest"}
    if authority_digest(body) != payload.get("projection_digest"):
        raise AssertionError("supervisor projection digest does not seal its body")
    return payload


def _read_span(case: "SupervisorCase", start: int, end: int) -> str:
    if not case.pair_log.exists():
        return "<no pair log>"
    with case.pair_log.open("rb") as handle:
        handle.seek(start)
        return handle.read(max(0, end - start)).decode("utf-8", "replace")[-4000:]

# -*- coding: utf-8 -*-
"""Issue #163: supervisor process の起動・再起動・後始末（test 専用）。

supervisor は pytest の process から ``fork`` した process で
``ProcessSupervisorCommand(config).run()`` を実行する。

* fd 1 / 2 を pair log へ向けてから起動するので、runner と同じく worker の
  出力が pair log に集まる（``classify_pair_status`` はその log の結果 JSON と
  envelope を突き合わせる）。
* supervisor 側の crash（``os._exit``）を pytest の process を壊さずに起こせる。
* test が ``monkeypatch`` した production の属性はそのまま fork 先に効く。
* barrier を解放する瞬間（supervisor が barrier の pipe へ ``b"1"`` を書く
  瞬間）に ``launch.json`` が durable かを記録する（launch-before-exec の
  parent 側の観測）。

fork の時点で pytest の process に他の thread が残っていても、fork 先が
lock 待ちで止まった場合は待ち上限（``timeout + grace + 60s``）で失敗になる
（黙って待ち続けない）。

起動の仕方（fork / exec）を変えるときに触るのはこの module だけ。
"""

from __future__ import annotations

from dataclasses import dataclass
import json
import os
from pathlib import Path
import signal
import stat
import sys
import time
import traceback
from typing import TYPE_CHECKING, Any, Mapping, Optional, Sequence

from scripts.function_tracer_pcode.tests.unit._supervisor_child import (
    launch_evidence_path,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_faults import (
    ChildStopped,
    Deadline,
    Fault,
    fired_faults,
    install_deadline_control,
    install_file_faults,
    store_at_child_stop_path,
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


# ---------------------------------------------------------------------------
# worker の生存確認と後始末
# ---------------------------------------------------------------------------


def _process_alive(pid: int, start_token: str) -> bool:
    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        read_process_start_token,
    )

    try:
        if read_process_start_token(pid) != start_token:
            return False
        fields = Path(f"/proc/{pid}/stat").read_text(encoding="utf-8")
    except (OSError, ValueError):
        return False
    return fields[fields.rfind(")") + 2] not in {"Z", "X"}


def worker_alive(case: SupervisorCase) -> bool:
    """``launch.json`` が名指す worker（PID + start token）がまだ動いているか。"""

    launch = _launch_payload(case)
    return launch is not None and _process_alive(
        launch["child_pid"], launch["child_start_token"]
    )


def terminate_leftover_workers(case: SupervisorCase) -> None:
    """launch が名指す worker の process group を、同一性を確かめてから止める。"""

    for launch_path in sorted(case.config.checkpoint_root.glob("*/launch.json")):
        payload = json.loads(launch_path.read_text(encoding="utf-8"))["payload"]
        pid, token = payload["child_pid"], payload["child_start_token"]
        if not _process_alive(pid, token):
            continue
        try:
            os.killpg(pid, signal.SIGKILL)
        except ProcessLookupError:
            continue
        deadline = time.monotonic() + 10.0
        while _process_alive(pid, token) and time.monotonic() < deadline:
            try:
                os.waitpid(pid, os.WNOHANG)  # 孤児が pytest に付け替わった場合
            except ChildProcessError:
                pass
            time.sleep(0.01)
        if _process_alive(pid, token):
            raise AssertionError(f"worker {pid} survived SIGKILL")


def _launch_payload(case: SupervisorCase) -> Optional[Mapping[str, Any]]:
    path = case.store_directory / "launch.json"
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))["payload"]


# ---------------------------------------------------------------------------
# supervisor の起動・再起動
# ---------------------------------------------------------------------------


class SupervisorRaised(AssertionError):
    """production の ``run()`` が例外で抜けた（traceback を持つ）。"""


@dataclass(frozen=True)
class SupervisorRun:
    #: supervisor の exit code。停止点で crash した場合は None。
    exit_code: Optional[int]
    #: supervisor が crash 停止点で落ちたか。
    crashed: bool
    #: ``authority_output`` の projection（digest 検証済み）。書かれなければ None。
    projection: Optional[Mapping[str, Any]]
    #: run 後の durable store。
    store: StoreSnapshot
    #: worker child が止まった瞬間の store。``Deadline.AT_CHILD_STOP`` か
    #: ``ChildStopped`` の停止点を使い、child が実際に止まった run だけが持つ。
    store_at_child_stop: Optional[StoreSnapshot]
    #: worker child が本処理の前に書いた launch の観測（起動しなければ / restart なら None）。
    launch_evidence: Optional[Mapping[str, Any]]
    #: この run の間に発火した停止点。
    faults_fired: tuple[Mapping[str, Any], ...]
    #: barrier を解放した瞬間に ``launch.json`` が durable だったか
    #: （barrier を解放しなかった run / restart は None）。
    launch_durable_at_barrier_release: Optional[bool]


def run_supervisor(
    case: SupervisorCase, *, deadline: str = Deadline.TIMER,
    faults: Sequence[Fault] = (),
) -> SupervisorRun:
    """初回の supervisor（``launch.json`` が無い状態から worker を起こす）。"""

    if (case.store_directory / "launch.json").exists():
        raise AssertionError("run_supervisor starts a pair; use restart_supervisor")
    return _supervise(case, deadline=deadline, faults=faults, starts_child=True)


def restart_supervisor(
    case: SupervisorCase, *, faults: Sequence[Fault] = (),
) -> SupervisorRun:
    """同じ config の supervisor をもう一度走らせる（production の resume 経路）。"""

    if not (case.store_directory / "launch.json").exists():
        raise AssertionError("restart_supervisor needs a durable launch")
    if any(isinstance(fault.at, ChildStopped) for fault in faults):
        raise ValueError("a restart starts no worker child to stop")
    return _supervise(case, deadline=Deadline.TIMER, faults=faults, starts_child=False)


def _supervise(
    case: SupervisorCase, *, deadline: str, faults: Sequence[Fault],
    starts_child: bool,
) -> SupervisorRun:
    fired_before = len(fired_faults(case.records))
    index = len(tuple(case.records.glob("supervisor-run-*.json")))
    status_path = case.records / f"supervisor-run-{index}.json"
    release_path = case.records / f"barrier-release-{index}.json"
    process_status = _fork_supervisor(
        case, deadline, faults, status_path, release_path,
    )
    fired = fired_faults(case.records)[fired_before:]
    status = (
        json.loads(status_path.read_text(encoding="utf-8"))
        if status_path.exists() else None
    )
    crashed = status is None and any(
        entry["role"] == "supervisor" and entry["action"] == "crash"
        for entry in fired
    )
    if status is None and not crashed:
        raise AssertionError(
            f"supervisor ended with {process_status} without a status record; "
            f"log:\n{_tail(case.pair_log)}"
        )
    if status is not None and "exception" in status:
        raise SupervisorRaised(status["exception"])
    # restart は worker を起こさないので、child 側の観測はこの run のものではない。
    launch = _launch_payload(case) if starts_child else None
    evidence = at_stop = None
    if launch is not None:
        path = launch_evidence_path(case.records, launch["child_pid"])
        if path.exists():
            evidence = json.loads(path.read_text(encoding="utf-8"))
        path = store_at_child_stop_path(case.records, launch["child_pid"])
        if path.exists():
            at_stop = StoreSnapshot.from_json(
                json.loads(path.read_text(encoding="utf-8"))
            )
    return SupervisorRun(
        exit_code=None if status is None else status["exit_code"],
        crashed=crashed,
        projection=_read_projection(case.config.authority_output),
        store=inspect_store(case.store_directory),
        store_at_child_stop=at_stop,
        launch_evidence=evidence,
        faults_fired=fired,
        launch_durable_at_barrier_release=(
            json.loads(release_path.read_text(encoding="utf-8"))["launch_durable"]
            if release_path.exists() else None
        ),
    )


def _observe_barrier_release(store_directory: Path, record: Path) -> None:
    """barrier の pipe への解放 byte を書く直前に、launch が durable かを記録する。"""

    original = os.write
    launch = Path(store_directory) / "launch.json"

    def write(descriptor: int, data: Any) -> int:
        if bytes(data) == b"1" and stat.S_ISFIFO(os.fstat(descriptor).st_mode):
            _write_status(record, {"launch_durable": launch.is_file()})
        return original(descriptor, data)

    os.write = write


def _fork_supervisor(
    case: SupervisorCase, deadline: str, faults: Sequence[Fault],
    status_path: Path, release_path: Path,
) -> int:
    for fault in faults:
        if fault.action != "crash":
            raise ValueError("a supervisor fault can only crash the supervisor")
    sys.stdout.flush()
    sys.stderr.flush()
    pid = os.fork()
    if pid == 0:  # pragma: no cover - runs in the forked supervisor
        code = _SUPERVISOR_RAISED_EXIT
        try:
            log = os.open(case.pair_log, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o644)
            os.dup2(log, 1)
            os.dup2(log, 2)
            _observe_barrier_release(case.store_directory, release_path)
            install_file_faults(
                faults, role="supervisor", store_directory=case.store_directory,
                records=case.records,
            )
            install_deadline_control(
                deadline=deadline, faults=faults, records=case.records,
                store_directory=case.store_directory,
            )
            from scripts.function_tracer_pcode.authority.process.supervisor_command import (
                ProcessSupervisorCommand,
            )

            code = ProcessSupervisorCommand(case.config).run()
            _write_status(status_path, {"exit_code": code})
        except BaseException:  # fork 先は報告して終わる。pytest の中へ巻き戻さない
            _write_status(status_path, {"exception": traceback.format_exc()})
            code = _SUPERVISOR_RAISED_EXIT
        finally:
            os._exit(code)
    limit = (
        time.monotonic() + float(case.config.timeout_seconds)
        + float(case.config.kill_grace_seconds) + _WAIT_MARGIN_SECONDS
    )
    reaped = False
    try:
        while True:
            waited, status = os.waitpid(pid, os.WNOHANG)
            if waited == pid:
                reaped = True
                return os.waitstatus_to_exitcode(status)
            if time.monotonic() > limit:
                raise AssertionError("supervisor did not finish within its budget")
            time.sleep(0.01)
    finally:
        if not reaped:
            # 待ち上限超過や KeyboardInterrupt。まだ回収していない自分の子だけを
            # 止める（回収済みの PID は再利用されうるので触らない）。
            os.kill(pid, signal.SIGKILL)
            os.waitpid(pid, 0)


def _write_status(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp")
    temporary.write_text(json.dumps(dict(payload)), encoding="utf-8")
    temporary.replace(path)


def _read_projection(path: Path) -> Optional[Mapping[str, Any]]:
    from scripts.function_tracer_pcode.authority.contracts import authority_digest

    if not path.exists():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    body = {key: value for key, value in payload.items() if key != "projection_digest"}
    if authority_digest(body) != payload.get("projection_digest"):
        raise AssertionError("supervisor projection digest does not seal its body")
    return payload


def _tail(path: Path, lines: int = 40) -> str:
    if not path.exists():
        return "<no pair log>"
    return "\n".join(path.read_text(encoding="utf-8", errors="replace").splitlines()[-lines:])

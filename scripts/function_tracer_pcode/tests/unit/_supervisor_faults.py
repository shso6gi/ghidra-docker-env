# -*- coding: utf-8 -*-
"""Issue #163: supervisor / worker process に注入する決定的な停止点（test 専用）。

production には何も足さない。停止点は production の 2 つの契約だけに依存する。

* **durable file の公開**: checkpoint store の file（envelope を含む）と
  supervisor の projection は、一時 file を書いてから ``os.replace``（または
  ``os.rename``）で公開される。
  * ``FileBoundary("continuation.json", side="after")`` は「store directory
    直下の ``continuation.json`` が公開された直後」を指す。
  * history への移動は ``FileBoundary("checkpoint-history/*/state.json")``
    のように store からの相対 path で名指す（同名 file を取り違えない）。
  * ``ProjectionWrite(side="before")`` は「supervisor が projection を公開する
    直前」を指す。
  内部 method 名を知らないので、store の実装が変わっても「どの file が durable
  になったか」という観測点は変わらない。
* **deadline 監視の入口**: ``ProcessSupervisorCommand._wait_for_child_until_deadline``
  （``deadline`` を引数で受け取る）。child が停止点へ着いた瞬間に deadline を
  到達させる（``Deadline.AT_CHILD_STOP``）ためだけに包む。依存する private
  名はこの 1 つで、この module の ``install_deadline_control`` だけが触る。

停止点へ着いた process がすること（``Fault.action``）:

* ``crash``: 記録を残して ``os._exit``。finally も cleanup も走らない。
* ``pause``（supervisor だけ。Issue #165）: 「止まった」ことを記録し、test が
  invocation の release FIFO に書くまでその場で待つ。durable な公開の直後
  （例: ``deadline.json`` の公開直後 = D は durable で signal はまだ）に
  supervisor を決定的に止める。同期は FIFO と記録だけで、sleep を合否の根拠に
  しない。止まっている間も supervisor は持っている lock（owner lock、公開が
  store の transaction の中なら store の flock も）を持ったまま。
* ``stop``（worker child だけ）: 「止まった」ことを記録して、signal で終了
  させられるまで待つ。supervisor の deadline はこの記録を見て到達させる
  （sleep 競争を作らない）。store の transaction の中（flock を持ったまま）で
  止まることがある。その間に同じ store を触る supervisor を別に起こすと
  lock 待ちになる。

発火の記録は、install した側が渡した場所（その invocation / その child の
記録）にだけ書く。``occurrence`` は install した process の中での公開回数
（process をまたいで数えない）。pytest の process には install しない。
"""

from __future__ import annotations

from dataclasses import dataclass
from fnmatch import fnmatchcase
import os
from pathlib import Path, PurePosixPath
import signal
import threading
import time
from typing import Any, Mapping, Optional, Sequence, Union

from scripts.function_tracer_pcode.tests.unit._supervisor_records import (
    ChildIdentity,
    ChildRecords,
    HarnessRecords,
    InvocationRecords,
    append_json_line,
    write_json,
)
from scripts.function_tracer_pcode.tests.unit._supervisor_store import inspect_store

#: harness が予約する exit code（CLI の 0-4 / supervisor の 124 と衝突しない）。
FAULT_CRASH_EXIT = 86

_POLL_SECONDS = 0.01


def _check_side(side: str, occurrence: int) -> None:
    if type(occurrence) is not int or occurrence < 1:
        raise ValueError("publication occurrence starts at 1")
    if side not in {"before", "after"}:
        raise ValueError("publication side is before or after")


@dataclass(frozen=True)
class FileBoundary:
    """store からの相対 ``path`` に一致する公開の、``occurrence`` 回目の前後。

    ``path`` の各 component は glob（``*``）を使える。深さは一致させる
    （``state.json`` は store 直下だけで、history の ``state.json`` は含まない）。
    """

    path: str
    occurrence: int = 1
    side: str = "after"

    def __post_init__(self) -> None:
        parts = PurePosixPath(self.path).parts
        if not parts or PurePosixPath(self.path).is_absolute() or ".." in parts:
            raise ValueError("file boundary is a relative path inside the store")
        _check_side(self.side, self.occurrence)

    def matches(self, relative: PurePosixPath) -> bool:
        pattern = PurePosixPath(self.path).parts
        return len(pattern) == len(relative.parts) and all(
            fnmatchcase(part, glob) for part, glob in zip(relative.parts, pattern)
        )

    def describe(self) -> str:
        return f"{self.side}:{self.path}#{self.occurrence}"


@dataclass(frozen=True)
class ProjectionWrite:
    """supervisor が projection（``authority_output``）を公開する前後。"""

    occurrence: int = 1
    side: str = "before"

    def __post_init__(self) -> None:
        _check_side(self.side, self.occurrence)

    def describe(self) -> str:
        return f"{self.side}:projection#{self.occurrence}"


@dataclass(frozen=True)
class ChildStopped:
    """supervisor 側だけの停止点: worker child が ``stop`` した瞬間。"""

    def describe(self) -> str:
        return "child-stopped"


Point = Union[FileBoundary, ProjectionWrite, ChildStopped]


@dataclass(frozen=True)
class Fault:
    at: Point
    action: str
    exit_code: int = FAULT_CRASH_EXIT
    ignore_sigterm: bool = False

    def __post_init__(self) -> None:
        if self.action not in {"crash", "stop", "pause"}:
            raise ValueError("fault action is crash, stop or pause")
        if self.action == "stop" and not isinstance(self.at, FileBoundary):
            raise ValueError("only a worker child stops, and only at a store file")
        if self.action == "pause" and isinstance(self.at, ChildStopped):
            raise ValueError("a supervisor pauses at a durable publication")

    def to_json(self) -> dict[str, Any]:
        if not isinstance(self.at, FileBoundary) or self.action == "pause":
            raise ValueError("only store file crash / stop points reach the worker child")
        return {
            "path": self.at.path, "occurrence": self.at.occurrence,
            "side": self.at.side, "action": self.action,
            "exit_code": self.exit_code, "ignore_sigterm": self.ignore_sigterm,
        }

    @classmethod
    def from_json(cls, value: Mapping[str, Any]) -> "Fault":
        return cls(
            FileBoundary(value["path"], value["occurrence"], value["side"]),
            value["action"], value["exit_code"], value["ignore_sigterm"],
        )


def crash_at(point: Point) -> Fault:
    return Fault(point, "crash")


def stop_at(point: FileBoundary) -> Fault:
    return Fault(point, "stop")


def pause_at(point: Union[FileBoundary, ProjectionWrite]) -> Fault:
    """supervisor をその公開の前後で止め、test の ``release`` まで待たせる。"""

    return Fault(point, "pause")


class Deadline:
    """supervisor の deadline をいつ到達させるか。"""

    #: production の timer のまま（``timeout_seconds`` 経過で到達）。
    TIMER = "timer"
    #: worker child が ``stop`` した瞬間に到達させる。child が止まらないまま
    #: ``timeout_seconds`` が過ぎるか child が終わったら production の経路が
    #: そのまま進むが、その invocation は ``SupervisorPathMismatch`` になる
    #: （黙って別の経路を試験したことにしない）。
    AT_CHILD_STOP = "at-child-stop"


# ---------------------------------------------------------------------------
# 発火と停止
# ---------------------------------------------------------------------------


def _fire(
    fault: Fault, *, role: str, sink: Path, child: Optional[ChildRecords],
    release: Optional[Path] = None,
) -> None:
    append_json_line(sink, {
        "role": role, "pid": os.getpid(), "point": fault.at.describe(),
        "action": fault.action,
    })
    if fault.action == "crash":
        os._exit(fault.exit_code)
    if fault.action == "pause":
        if release is None:
            raise AssertionError("only a supervisor invocation can pause")
        # 書き手（test の ``release``）が開いて書き、閉じるまで戻らない。
        with open(release, "rb") as fifo:
            message = fifo.read()
        if message.startswith(WORKER_EXIT_RELEASE):
            _wait_until_worker_exit_is_observable(
                int(message[len(WORKER_EXIT_RELEASE):]), sink=sink,
            )
        return
    if child is None:
        raise AssertionError("only a worker child can stop")
    stop_here(child, point=fault.at.describe(), ignore_sigterm=fault.ignore_sigterm)


#: 解放の合図のうち「worker の終了が supervisor から観測できるまで待ってから続ける」（Issue #226）。
#: 後ろに worker の PID を付ける
WORKER_EXIT_RELEASE = b"worker-exit:"
#: 終了が観測できるまで待つ上限。超えたら観測できなかったと記録して続ける（test がその記録で落ちる）
WORKER_EXIT_OBSERVE_LIMIT_SECONDS = 30.0
#: 終了の観測の記録の ``point``
WORKER_EXIT_OBSERVATION = "worker-exit-observable"


def _wait_until_worker_exit_is_observable(pid: int, *, sink: Path) -> None:
    """supervisor の process の中で、worker（この process の子）の終了が ``waitid`` で見えるまで待つ。

    Issue #226: race A の前提「signal の前に worker が終了した」は、**親である supervisor が終了を
    観測できる** ことで確立する。``/proc/<pid>/stat`` の ``Z`` は thread group leader の状態で、
    ほかの thread の後片付けが残っていれば親の ``waitpid`` はまだ終了を報告しない。

    ``WNOWAIT`` なので回収しない（production の ``poll()`` が自分で回収する経路をそのまま試験する）。
    待つのは条件そのもの（blocking な ``waitid``）で、上限は観測できなかったときの失敗の記録のため。
    """

    observed: list = []

    def _observe() -> None:
        observed.append(os.waitid(os.P_PID, pid, os.WEXITED | os.WNOWAIT))

    waiter = threading.Thread(target=_observe, daemon=True)
    waiter.start()
    waiter.join(WORKER_EXIT_OBSERVE_LIMIT_SECONDS)
    info = observed[0] if observed else None
    append_json_line(sink, {
        "role": "supervisor", "pid": os.getpid(), "point": WORKER_EXIT_OBSERVATION,
        "action": "observe", "worker_pid": pid, "observable": info is not None,
        "code": None if info is None else info.si_code,
        "status": None if info is None else info.si_status,
    })


def _exit_leader_first(child: ChildRecords, code: int) -> None:
    """leader thread だけを先に終わらせ、別の thread が ``finish`` の合図の後で process を終える。"""

    import ctypes

    def _finish() -> None:
        with open(child.finish, "rb") as fifo:
            fifo.read(1)
        os._exit(code)

    threading.Thread(target=_finish, daemon=True).start()
    ctypes.CDLL(None).pthread_exit(None)


def stop_here(
    child: ChildRecords, *, point: str, ignore_sigterm: bool = False,
    exit_on_sigterm: Optional[int] = None, exit_on_sigusr1: Optional[int] = None,
    leader_exits_first: bool = False,
) -> None:
    """止まったことを記録し、signal で終了させられるまで戻らない。

    Issue #165: ``exit_on_sigterm`` は SIGTERM を受けて自分で ``exit_code`` で
    終わる child（signal 後の通常終了、race B）、``exit_on_sigusr1`` は test の
    合図で通常終了する child（signal 前の通常終了、race A）。

    Issue #226: ``leader_exits_first`` は ``exit_on_sigusr1`` の終わり方を 2 段にする。SIGUSR1 で
    leader thread だけが先に終わり（``/proc`` では ``Z`` に見える）、別の thread が ``finish`` の
    FIFO に test が書くまで process を生かし、書かれたら ``exit_on_sigusr1`` で終える。「leader は
    ``Z`` なのに親からはまだ終了が観測できない」状態を、時間でなく test の合図で作るため。
    """

    if leader_exits_first and exit_on_sigusr1 is None:
        raise ValueError("leader_exits_first finishes the exit that SIGUSR1 starts")

    if ignore_sigterm:
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
    if exit_on_sigterm is not None:
        signal.signal(signal.SIGTERM, lambda *_: os._exit(exit_on_sigterm))
    if leader_exits_first:
        os.mkfifo(child.finish)
        signal.signal(signal.SIGUSR1, lambda *_: _exit_leader_first(child, exit_on_sigusr1))
    elif exit_on_sigusr1 is not None:
        signal.signal(signal.SIGUSR1, lambda *_: os._exit(exit_on_sigusr1))
    write_json(child.stopped, {
        "pid": os.getpid(), "point": point, "ignore_sigterm": ignore_sigterm,
    })
    while True:
        signal.pause()


# ---------------------------------------------------------------------------
# file 公開境界
# ---------------------------------------------------------------------------


def install_publication_faults(
    faults: Sequence[Fault], *, role: str, store_directory: Path,
    projection: Optional[Path], sink: Path, child: Optional[ChildRecords] = None,
    release: Optional[Path] = None,
) -> None:
    """この process の ``os.replace`` / ``os.rename`` を停止点つきで包む。

    その時点の ``os.replace`` / ``os.rename`` を包む（先に入った観測を壊さない）。
    process 終了まで有効で、元に戻さない（fork / exec した test 専用 process
    にしか install しない）。
    """

    points = [
        fault for fault in faults
        if isinstance(fault.at, (FileBoundary, ProjectionWrite))
    ]
    if not points:
        return
    store = Path(store_directory).resolve()
    projection_path = None if projection is None else Path(projection).resolve()
    seen = [0] * len(points)

    def _hits(destination: Any) -> list[int]:
        path = Path(os.fspath(destination)).resolve()
        relative = (
            PurePosixPath(path.relative_to(store).as_posix())
            if store in path.parents else None
        )
        hits = []
        for index, fault in enumerate(points):
            at = fault.at
            if isinstance(at, ProjectionWrite):
                if path == projection_path:
                    hits.append(index)
            elif relative is not None and at.matches(relative):
                hits.append(index)
        return hits

    def _fire_side(hits: list[int], side: str) -> None:
        for index in hits:
            fault = points[index]
            if fault.at.side == side and fault.at.occurrence == seen[index]:
                _fire(fault, role=role, sink=sink, child=child, release=release)

    def _wrap(original: Any) -> Any:
        def publish(source: Any, destination: Any, *args: Any, **kwargs: Any) -> Any:
            hits = _hits(destination)
            for index in hits:
                seen[index] += 1
            _fire_side(hits, "before")
            result = original(source, destination, *args, **kwargs)
            _fire_side(hits, "after")
            return result
        return publish

    os.replace = _wrap(os.replace)
    os.rename = _wrap(os.rename)


# ---------------------------------------------------------------------------
# supervisor の deadline 監視
# ---------------------------------------------------------------------------


#: `_wait_for_stop_or_end` の結果: worker が止まった / worker が終わった / 本物の timer が来た
WORKER_STOPPED = "worker-stop"
WORKER_ENDED = "worker-exit"
REAL_TIMER = "timer"


def _wait_for_stop_or_end(process: Any, marker: Path, real_deadline: float) -> str:
    """worker が止まる（``marker``）か、終わるか、本物の timer が来るまで待つ。"""

    while not marker.exists():
        if process.poll() is not None:
            return WORKER_ENDED
        if time.monotonic() >= real_deadline:
            return REAL_TIMER
        time.sleep(_POLL_SECONDS)
    return WORKER_STOPPED


def install_runner_deadline_at_worker_stop(harness: HarnessRecords, *, sink: Path) -> None:
    """runner が起こした production の supervisor の deadline を、worker の ``stop`` に結ぶ（Issue #226）。

    supervisor 単体の harness の ``Deadline.AT_CHILD_STOP`` と同じ: 止まった worker の pair は
    止まった瞬間に deadline へ進み、止まらずに終わる worker の pair は deadline に当たらない。
    pair が deadline に当たるかを host の速さ（runner の timer）で決めない。本物の timer は
    hang の上限としてだけ残し、どの経路を通ったかを pair ごとに ``sink`` へ記録する（test は
    timer に当たった pair が無いことを確かめる）。
    """

    from scripts.function_tracer_pcode.authority.process.process_identity import (
        read_process_start_token,
    )
    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        ProcessSupervisorCommand,
    )

    original = ProcessSupervisorCommand._wait_for_child_until_deadline

    def controlled(self: Any, process: Any, diagnostic: Any, real_deadline: float) -> Any:
        identity = ChildIdentity(process.pid, read_process_start_token(process.pid))
        path = _wait_for_stop_or_end(process, harness.child(identity).stopped, real_deadline)
        arguments = list(getattr(process, "args", ()) or ())
        function = arguments[arguments.index("-f") + 1] if "-f" in arguments else None
        append_json_line(sink, {"worker_pid": process.pid, "function": function, "deadline": path})
        effective = time.monotonic() if path == WORKER_STOPPED else real_deadline
        return original(self, process, diagnostic, effective)

    ProcessSupervisorCommand._wait_for_child_until_deadline = controlled


def install_deadline_control(
    *, deadline: str, faults: Sequence[Fault], invocation: InvocationRecords,
    harness: HarnessRecords, store_directory: Path,
) -> None:
    """child の ``stop`` を deadline（または supervisor の crash）へ結ぶ。

    何も要求されていなければ何も包まない（production の監視そのまま）。
    child が止まった瞬間の store は、この invocation の記録にだけ書く。
    """

    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        ProcessSupervisorCommand,
    )

    crash = next((f for f in faults if isinstance(f.at, ChildStopped)), None)
    if deadline == Deadline.TIMER and crash is None:
        return
    original = ProcessSupervisorCommand._wait_for_child_until_deadline

    def controlled(self: Any, process: Any, diagnostic: Any, real_deadline: float) -> Any:
        started = invocation.child()
        if started is None or started.pid != process.pid:
            # production の run() の中なので、例外にすると _resume() に飲まれて
            # 別の原因に見える。この invocation の status に書いて落ちる。
            write_json(invocation.status, {
                "exception": f"{invocation.invocation} did not record the worker it started",
            })
            os._exit(70)
        marker = harness.child(started).stopped
        if _wait_for_stop_or_end(process, marker, real_deadline) != WORKER_STOPPED:
            return original(self, process, diagnostic, real_deadline)
        write_json(invocation.store_at_child_stop, inspect_store(store_directory).to_json())
        if crash is not None:
            _fire(crash, role="supervisor", sink=invocation.faults, child=None)
        effective = (
            time.monotonic() if deadline == Deadline.AT_CHILD_STOP else real_deadline
        )
        return original(self, process, diagnostic, effective)

    ProcessSupervisorCommand._wait_for_child_until_deadline = controlled

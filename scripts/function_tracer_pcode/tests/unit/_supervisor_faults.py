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
import time
from typing import Any, Mapping, Optional, Sequence, Union

from scripts.function_tracer_pcode.tests.unit._supervisor_records import (
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
        if self.action not in {"crash", "stop"}:
            raise ValueError("fault action is crash or stop")
        if self.action == "stop" and not isinstance(self.at, FileBoundary):
            raise ValueError("only a worker child stops, and only at a store file")

    def to_json(self) -> dict[str, Any]:
        if not isinstance(self.at, FileBoundary):
            raise ValueError("only store file boundaries reach the worker child")
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


def _fire(fault: Fault, *, role: str, sink: Path, child: Optional[ChildRecords]) -> None:
    append_json_line(sink, {
        "role": role, "pid": os.getpid(), "point": fault.at.describe(),
        "action": fault.action,
    })
    if fault.action == "crash":
        os._exit(fault.exit_code)
    if child is None:
        raise AssertionError("only a worker child can stop")
    stop_here(child, point=fault.at.describe(), ignore_sigterm=fault.ignore_sigterm)


def stop_here(child: ChildRecords, *, point: str, ignore_sigterm: bool = False) -> None:
    """止まったことを記録し、signal で終了させられるまで戻らない。"""

    if ignore_sigterm:
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
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
                _fire(fault, role=role, sink=sink, child=child)

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
        while not marker.exists():
            if process.poll() is not None or time.monotonic() >= real_deadline:
                return original(self, process, diagnostic, real_deadline)
            time.sleep(_POLL_SECONDS)
        write_json(invocation.store_at_child_stop, inspect_store(store_directory).to_json())
        if crash is not None:
            _fire(crash, role="supervisor", sink=invocation.faults, child=None)
        effective = (
            time.monotonic() if deadline == Deadline.AT_CHILD_STOP else real_deadline
        )
        return original(self, process, diagnostic, effective)

    ProcessSupervisorCommand._wait_for_child_until_deadline = controlled

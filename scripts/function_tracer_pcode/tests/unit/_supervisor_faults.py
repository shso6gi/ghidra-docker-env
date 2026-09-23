# -*- coding: utf-8 -*-
"""Issue #163: supervisor / worker process に注入する決定的な停止点（test 専用）。

production には何も足さない。停止点は production の 2 つの契約だけに依存する。

* **durable file の公開**: checkpoint store の file（envelope を含む）は、一時
  file を書いてから ``os.replace``（または ``os.rename``）で公開される。
  ``FileBoundary("continuation.json", side="after")`` は「store directory
  直下の ``continuation.json`` が公開された直後」を指す。history への移動は
  ``FileBoundary("checkpoint-history/*/state.json")`` のように store からの
  相対 path で名指す（同名 file を取り違えない）。内部 method 名を知らない
  ので、store の実装が変わっても「どの file が durable になったか」という
  観測点は変わらない。
* **deadline 監視の入口**: ``ProcessSupervisorCommand._wait_for_child_until_deadline``
  （``deadline`` を引数で受け取る）。child が停止点へ着いた瞬間に deadline を
  到達させる（``Deadline.AT_CHILD_STOP``）ためだけに包む。依存する private
  名はこの 1 つで、この module の ``install_deadline_control`` だけが触る。

停止点へ着いた process がすること（``Fault.action``）:

* ``crash``: 記録を残して ``os._exit``。finally も cleanup も走らない。
* ``stop``: 「止まった」ことを記録して、signal で終了させられるまで待つ。
  supervisor の deadline はこの記録を見て到達させる（sleep 競争を作らない）。
  store の transaction の中（flock を持ったまま）で止まることがある。その間に
  同じ store を触る supervisor を別に起こすと lock 待ちになる。

``occurrence`` は install した process の中での公開回数（process をまたいで
数えない）。

どの process でも使える（worker child は spec から、fork した supervisor は
引数から install する）。pytest の process には install しない。
"""

from __future__ import annotations

from dataclasses import dataclass
from fnmatch import fnmatchcase
import json
import os
from pathlib import Path, PurePosixPath
import signal
import time
from typing import Any, Mapping, Optional, Sequence, Union

from scripts.function_tracer_pcode.tests.unit._supervisor_store import inspect_store

#: harness が予約する exit code（CLI の 0-4 / supervisor の 124 と衝突しない）。
FAULT_CRASH_EXIT = 86

_POLL_SECONDS = 0.01
_ORIGINAL_REPLACE = os.replace
_ORIGINAL_RENAME = os.rename


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
        if type(self.occurrence) is not int or self.occurrence < 1:
            raise ValueError("file boundary occurrence starts at 1")
        if self.side not in {"before", "after"}:
            raise ValueError("file boundary side is before or after")

    def matches(self, relative: PurePosixPath) -> bool:
        pattern = PurePosixPath(self.path).parts
        return len(pattern) == len(relative.parts) and all(
            fnmatchcase(part, glob) for part, glob in zip(relative.parts, pattern)
        )

    def describe(self) -> str:
        return f"{self.side}:{self.path}#{self.occurrence}"


@dataclass(frozen=True)
class ChildStopped:
    """supervisor 側だけの停止点: worker child が ``stop`` した瞬間。"""

    def describe(self) -> str:
        return "child-stopped"


Point = Union[FileBoundary, ChildStopped]


@dataclass(frozen=True)
class Fault:
    at: Point
    action: str
    exit_code: int = FAULT_CRASH_EXIT
    ignore_sigterm: bool = False

    def __post_init__(self) -> None:
        if self.action not in {"crash", "stop"}:
            raise ValueError("fault action is crash or stop")

    def to_json(self) -> dict[str, Any]:
        if not isinstance(self.at, FileBoundary):
            raise ValueError("only file boundaries cross the process boundary")
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
    #: worker child が ``stop`` した瞬間に到達させる。child が着く前に
    #: ``timeout_seconds`` が過ぎたら production の timer がそのまま働き、
    #: ``SupervisorRun.store_at_child_stop`` が ``None`` になる（黙って別の
    #: 経路を試験したことにならない）。
    AT_CHILD_STOP = "at-child-stop"


# ---------------------------------------------------------------------------
# 記録（harness の records directory。production は読まない）
# ---------------------------------------------------------------------------


def _append_record(records: Path, filename: str, payload: Mapping[str, Any]) -> None:
    records.mkdir(parents=True, exist_ok=True)
    with (records / filename).open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(dict(payload), sort_keys=True) + "\n")
        handle.flush()
        os.fsync(handle.fileno())


def _write_record(records: Path, filename: str, payload: Mapping[str, Any]) -> None:
    records.mkdir(parents=True, exist_ok=True)
    temporary = records / f".{filename}.{os.getpid()}.tmp"
    temporary.write_text(json.dumps(dict(payload), sort_keys=True), encoding="utf-8")
    _ORIGINAL_REPLACE(temporary, records / filename)


def fired_faults(records: Path) -> tuple[dict[str, Any], ...]:
    path = records / "faults-fired.jsonl"
    if not path.exists():
        return ()
    return tuple(
        json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    )


def child_stop_marker(records: Path, pid: int) -> Path:
    return records / f"child-stopped-{pid}.json"


def store_at_child_stop_path(records: Path, pid: int) -> Path:
    return records / f"store-at-child-stop-{pid}.json"


def _fire(fault: Fault, *, role: str, records: Path) -> None:
    _append_record(records, "faults-fired.jsonl", {
        "role": role, "pid": os.getpid(), "point": fault.at.describe(),
        "action": fault.action,
    })
    if fault.action == "crash":
        os._exit(fault.exit_code)
    stop_here(records, point=fault.at.describe(), ignore_sigterm=fault.ignore_sigterm)


def stop_here(records: Path, *, point: str, ignore_sigterm: bool = False) -> None:
    """止まったことを記録し、signal で終了させられるまで戻らない。"""

    if ignore_sigterm:
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
    _write_record(records, child_stop_marker(records, os.getpid()).name, {
        "pid": os.getpid(), "point": point, "ignore_sigterm": ignore_sigterm,
    })
    while True:
        signal.pause()


# ---------------------------------------------------------------------------
# file 公開境界
# ---------------------------------------------------------------------------


def install_file_faults(
    faults: Sequence[Fault], *, role: str, store_directory: Path, records: Path,
) -> None:
    """この process の ``os.replace`` / ``os.rename`` を停止点つきで包む。

    ``store_directory`` の下へ公開される file だけを、fault ごとに数える。
    process 終了まで有効で、元に戻さない（fork / exec した test 専用 process
    にしか install しない）。
    """

    file_faults = [fault for fault in faults if isinstance(fault.at, FileBoundary)]
    if not file_faults:
        return
    store = Path(store_directory).resolve()
    seen = [0] * len(file_faults)

    def _relative(destination: Any) -> Optional[PurePosixPath]:
        path = Path(os.fspath(destination)).resolve()
        if store not in path.parents:
            return None
        return PurePosixPath(path.relative_to(store).as_posix())

    def _wrap(original: Any) -> Any:
        def publish(source: Any, destination: Any, *args: Any, **kwargs: Any) -> Any:
            relative = _relative(destination)
            hits = [] if relative is None else [
                index for index, fault in enumerate(file_faults)
                if fault.at.matches(relative)
            ]
            for index in hits:
                seen[index] += 1
            for index in hits:
                fault = file_faults[index]
                if fault.at.side == "before" and fault.at.occurrence == seen[index]:
                    _fire(fault, role=role, records=records)
            result = original(source, destination, *args, **kwargs)
            for index in hits:
                fault = file_faults[index]
                if fault.at.side == "after" and fault.at.occurrence == seen[index]:
                    _fire(fault, role=role, records=records)
            return result
        return publish

    os.replace = _wrap(_ORIGINAL_REPLACE)
    os.rename = _wrap(_ORIGINAL_RENAME)


# ---------------------------------------------------------------------------
# supervisor の deadline 監視
# ---------------------------------------------------------------------------


def install_deadline_control(
    *, deadline: str, faults: Sequence[Fault], records: Path,
    store_directory: Path,
) -> None:
    """child の ``stop`` を deadline（または supervisor の crash）へ結ぶ。

    何も要求されていなければ何も包まない（production の監視そのまま）。
    """

    from scripts.function_tracer_pcode.authority.process.supervisor_command import (
        ProcessSupervisorCommand,
    )

    crash = next((f for f in faults if isinstance(f.at, ChildStopped)), None)
    if deadline == Deadline.TIMER and crash is None:
        return
    if deadline not in {Deadline.TIMER, Deadline.AT_CHILD_STOP}:
        raise ValueError(f"unknown deadline mode {deadline!r}")
    original = ProcessSupervisorCommand._wait_for_child_until_deadline

    def controlled(self: Any, process: Any, diagnostic: Any, real_deadline: float) -> Any:
        marker = child_stop_marker(records, process.pid)
        while not marker.exists():
            if process.poll() is not None or time.monotonic() >= real_deadline:
                return original(self, process, diagnostic, real_deadline)
            time.sleep(_POLL_SECONDS)
        _write_record(
            records, store_at_child_stop_path(records, process.pid).name,
            inspect_store(store_directory).to_json(),
        )
        if crash is not None:
            _fire(crash, role="supervisor", records=records)
        effective = (
            time.monotonic() if deadline == Deadline.AT_CHILD_STOP else real_deadline
        )
        return original(self, process, diagnostic, effective)

    ProcessSupervisorCommand._wait_for_child_until_deadline = controlled

# -*- coding: utf-8 -*-
"""Issue #163: harness の記録の置き場所と run identity（唯一の定義）。

記録は production が読まない harness 専用の file で、所有者ごとに分ける。

* **invocation**（supervisor の 1 回の起動）: 開始時に parent が
  ``allocate_invocation`` で directory を排他的に作って identity を確保する。
  成功・crash・例外のどれで終わっても identity は消費済みで、次の起動は必ず
  別の identity になる。その起動が観測したもの（status、barrier 解放、起動した
  child、公開した projection、発火した停止点、child が止まった瞬間の store）は
  すべてこの directory にだけ書く。別の起動の記録を後から読み違えることがない。
* **child**（worker process 1 つ）: child 自身が書く観測（launch の検査結果、
  止まった記録、発火した停止点）。child は起動した invocation を知らない
  （child の command は config の一部で、restart でも変えられない）ので、
  process の identity（PID + start token）で置く。読む側は、invocation が
  Popen の直後に記録した identity でこの directory を引く（PID が再利用されても
  別 process の記録を読まない）。

file 名はこの module の外に出さない。test は ``SupervisorRun`` の field を読む。
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping, Optional

#: 停止点が ``os.replace`` を包んでも、記録の書き込みはそれを通らない。
_ORIGINAL_REPLACE = os.replace


def write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(dict(payload), sort_keys=True), encoding="utf-8")
    _ORIGINAL_REPLACE(temporary, path)


def write_bytes(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_bytes(data)
    _ORIGINAL_REPLACE(temporary, path)


def append_json_line(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(dict(payload), sort_keys=True) + "\n")
        handle.flush()
        os.fsync(handle.fileno())


def sha256_of(path: Path) -> str:
    """file の sha256（無ければ空の bytes の sha256）。"""

    return hashlib.sha256(path.read_bytes() if path.exists() else b"").hexdigest()


def read_json(path: Path) -> Optional[dict[str, Any]]:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def read_json_lines(path: Path) -> tuple[dict[str, Any], ...]:
    if not path.exists():
        return ()
    return tuple(
        json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    )


@dataclass(frozen=True, order=True)
class SupervisorInvocationId:
    """case の中で一意な、supervisor の 1 回の起動の identity（開始順）。"""

    ordinal: int

    def __str__(self) -> str:
        return f"invocation-{self.ordinal:04d}"


@dataclass(frozen=True)
class ChildIdentity:
    pid: int
    start_token: str

    @property
    def key(self) -> str:
        return f"{self.pid}-{self.start_token.rsplit('-', 1)[-1]}"


@dataclass(frozen=True)
class InvocationRecords:
    invocation: SupervisorInvocationId
    directory: Path

    @property
    def status(self) -> Path:
        return self.directory / "status.json"

    @property
    def started_child(self) -> Path:
        return self.directory / "started-child.json"

    @property
    def barrier_release(self) -> Path:
        return self.directory / "barrier-release.json"

    @property
    def projection(self) -> Path:
        return self.directory / "projection.json"

    @property
    def faults(self) -> Path:
        return self.directory / "faults-fired.jsonl"

    @property
    def store_at_child_stop(self) -> Path:
        return self.directory / "store-at-child-stop.json"

    def child(self) -> Optional[ChildIdentity]:
        payload = read_json(self.started_child)
        return None if payload is None else ChildIdentity(**payload)


@dataclass(frozen=True)
class ChildRecords:
    identity: ChildIdentity
    directory: Path

    @property
    def launch_evidence(self) -> Path:
        return self.directory / "launch-evidence.json"

    @property
    def identity_record(self) -> Path:
        return self.directory / "identity.json"

    @property
    def stopped(self) -> Path:
        return self.directory / "stopped.json"

    @property
    def faults(self) -> Path:
        return self.directory / "faults-fired.jsonl"


@dataclass(frozen=True)
class HarnessRecords:
    root: Path

    def allocate_invocation(self) -> InvocationRecords:
        """次の identity を排他的に確保する（``mkdir`` が成功した番号）。"""

        base = self.root / "invocations"
        base.mkdir(parents=True, exist_ok=True)
        ordinal = len(tuple(base.iterdir()))
        while True:
            identity = SupervisorInvocationId(ordinal)
            directory = base / str(identity)
            try:
                directory.mkdir()
            except FileExistsError:
                ordinal += 1
                continue
            return InvocationRecords(identity, directory)

    def invocations(self) -> tuple[InvocationRecords, ...]:
        base = self.root / "invocations"
        if not base.is_dir():
            return ()
        return tuple(
            InvocationRecords(SupervisorInvocationId(int(path.name.rsplit("-", 1)[1])), path)
            for path in sorted(base.iterdir())
        )

    def child(self, identity: ChildIdentity) -> ChildRecords:
        return ChildRecords(identity, self.root / "children" / identity.key)

    def children_with_pid(self, pid: int) -> tuple[ChildRecords, ...]:
        """PID が同じ child の記録すべて（identity を知らない呼び出し側向け）。"""

        base = self.root / "children"
        found = []
        for path in sorted(base.glob(f"{pid}-*")) if base.is_dir() else ():
            payload = read_json(path / "identity.json")
            if payload is not None:
                found.append(ChildRecords(ChildIdentity(**payload), path))
        return tuple(found)

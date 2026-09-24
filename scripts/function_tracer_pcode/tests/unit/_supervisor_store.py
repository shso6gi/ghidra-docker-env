# -*- coding: utf-8 -*-
"""Issue #163: supervisor の durable store を観測する（読むだけ・判定しない）。

store の中身の**意味**の検証は production（``classify_pair_status`` や
``DurableCheckpointStore`` の rematerialize）の責務で、ここでは再実装しない。
ここが返すのは「どの file が durable にあるか」「その bytes」「state.json が
名乗る state」という観測だけ。crash 境界や restart の前後比較（#165）は
この snapshot 同士を比べる。
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Optional


@dataclass(frozen=True)
class StoreSnapshot:
    directory: Path
    #: store directory からの相対 path（``checkpoint-history/...`` を含む）→ sha256。
    #: lock file と書きかけの一時 file（``.`` 始まり）は数えない。
    digests: Mapping[str, str]
    #: ``state.json`` が名乗る checkpoint state（無い・読めなければ None）。
    #: 署名は見ない。
    state: Optional[str]

    @property
    def files(self) -> frozenset[str]:
        return frozenset(self.digests)

    def has(self, name: str) -> bool:
        return name in self.digests

    def to_json(self) -> dict[str, Any]:
        return {
            "directory": str(self.directory),
            "digests": dict(self.digests),
            "state": self.state,
        }

    @classmethod
    def from_json(cls, value: Mapping[str, Any]) -> "StoreSnapshot":
        return cls(Path(value["directory"]), dict(value["digests"]), value["state"])


def inspect_store(directory: Path) -> StoreSnapshot:
    directory = Path(directory)
    digests: dict[str, str] = {}
    if directory.is_dir():
        for path in sorted(directory.rglob("*")):
            relative = path.relative_to(directory)
            if path.is_file() and not any(part.startswith(".") for part in relative.parts):
                digests[relative.as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    state = None
    state_path = directory / "state.json"
    if state_path.is_file():
        # 改ざん・書きかけの store も観測できるように、読めなければ None にする
        # （file があること自体は ``digests`` に残る）。
        try:
            state = json.loads(state_path.read_text(encoding="utf-8"))["payload"]["state"]
        except (ValueError, KeyError, TypeError):
            state = None
    return StoreSnapshot(directory, digests, state)

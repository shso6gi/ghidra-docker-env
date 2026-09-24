"""Issue #165: 閉じた checkpoint chain を history へ移す archive transaction。

この module が持つもの:

* **chain の member 集合**（``CHAIN_MEMBERS``）: 1 つの閉じた（RESOLVED の）
  checkpoint chain を構成する file と役割、必須か任意か。worker の ACTIVE
  commit が前の chain を退避するとき、ACTIVE の rollback、ERROR 前の A archive
  のどれもこの 1 つの表を使う（file を 1 つ足すときに触るのはここだけ）。
* **A（署名済み archive manifest）に対する live / history の union 検証**
  （``inspect_union``）: 各 member が live と history のどちらか（または両方）に
  あり、A が固定した size / digest と一致すること。両側欠落・bytes の不一致・
  history 側の余分な file は拒否する。
* **移動**（``move_remaining``）: member ごとに ``os.replace`` と移動元・移動先の
  directory fsync。``state.json`` を最後に移す。別 filesystem を前提にした
  copy / delete はしない（``os.replace`` が失敗すればそのまま例外）。

持たないもの: 署名（``terminal_evidence`` と factory）、chain の意味検証
（store の ``validate_resolved_chain_members``。ここへは reader を渡して呼ぶ）、
いつ archive するかの判断（``terminal_recovery``）。
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import os
from pathlib import Path
from typing import Callable, Mapping, Optional

from scripts.function_tracer_pcode.authority.process import store_layout as layout



@dataclass(frozen=True)
class ChainMemberSpec:
    name: str
    role: str
    required: bool


#: 閉じた chain の member（移動順。``state.json`` は必ず最後）。
CHAIN_MEMBERS: tuple[ChainMemberSpec, ...] = (
    ChainMemberSpec(layout.PREFIX_STREAM, "prefix_stream", True),
    ChainMemberSpec(layout.CHECKPOINT, "checkpoint", True),
    ChainMemberSpec(layout.CONTINUATION_STREAM, "continuation_stream", True),
    ChainMemberSpec(layout.CONTINUATION, "continuation", True),
    ChainMemberSpec(layout.READY, "ready", True),
    # supervisor が worker の continuation から chain を閉じたときだけある。
    ChainMemberSpec(layout.RECOVERY_RESOLUTION, "recovery_resolution", False),
    ChainMemberSpec(layout.STATE, "state", True),
)
CHAIN_MEMBER_NAMES = tuple(spec.name for spec in CHAIN_MEMBERS)
_SPEC_BY_NAME: Mapping[str, ChainMemberSpec] = {spec.name: spec for spec in CHAIN_MEMBERS}


class ArchiveConflict(ValueError):
    """union が A と合わない（欠落・bytes 不一致・余分な file・anchor 外の chain）。"""


def history_destination(resolved_state_receipt_digest: str) -> str:
    """閉じた chain の退避先（store からの相対 path）。既存の退避と同じ規則。"""

    if (
        type(resolved_state_receipt_digest) is not str
        or not resolved_state_receipt_digest
        or not all(ch.isalnum() for ch in resolved_state_receipt_digest)
    ):
        raise ArchiveConflict("history destination digest is not a safe identity")
    return f"{layout.HISTORY_DIRECTORY}/{resolved_state_receipt_digest}"


def history_directory(directory: Path, resolved_state_receipt_digest: str) -> Path:
    """閉じた chain の退避先の絶対 path。"""

    return Path(directory) / history_destination(resolved_state_receipt_digest)


def validate_member_set(
    members: tuple, *, destination: str, resolved_state_receipt_digest: str,
) -> None:
    """A の member 集合が ``CHAIN_MEMBERS`` の閉じた chain であること。"""

    names = [member.name for member in members]
    if len(set(names)) != len(names):
        raise ArchiveConflict("archive manifest names a member twice")
    if destination != history_destination(resolved_state_receipt_digest):
        raise ArchiveConflict("archive destination does not name the resolved chain")
    for member in members:
        spec = _SPEC_BY_NAME.get(member.name)
        if spec is None or spec.role != member.role:
            raise ArchiveConflict(f"archive member {member.name!r} is not a chain member")
    missing = {spec.name for spec in CHAIN_MEMBERS if spec.required} - set(names)
    if missing:
        raise ArchiveConflict(f"archive manifest lacks required members {sorted(missing)}")
    expected_order = [name for name in CHAIN_MEMBER_NAMES if name in set(names)]
    if names != expected_order:
        raise ArchiveConflict("archive members are not in chain move order")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def live_chain_members(directory: Path) -> tuple[str, ...]:
    """store 直下に今ある chain member の名前（移動順）。"""

    return tuple(name for name in CHAIN_MEMBER_NAMES if (Path(directory) / name).exists())


# ---------------------------------------------------------------------------
# A に対する union の検証
# ---------------------------------------------------------------------------

LOCATION_LIVE = "live"
LOCATION_HISTORY = "history"
LOCATION_BOTH = "both"


@dataclass(frozen=True)
class UnionInspection:
    """A の各 member がいまどこにあるか（検証済み）。"""

    locations: Mapping[str, str]

    @property
    def remaining(self) -> tuple[str, ...]:
        """まだ live に残っている member（移動順）。"""

        return tuple(
            name for name, where in self.locations.items()
            if where in {LOCATION_LIVE, LOCATION_BOTH}
        )

    @property
    def complete(self) -> bool:
        return not self.remaining


def inspect_union(
    directory: Path, members: tuple, destination: str,
) -> UnionInspection:
    """A の member を live / history の union で照合する（書き込まない）。

    * 各 member は少なくとも一方にあり、ある側の bytes はすべて A の size /
      sha256 と一致する。
    * history の退避先に A に無い file があれば拒否する（余分な authority）。
    """

    directory = Path(directory)
    history = directory / destination
    locations: dict[str, str] = {}
    for member in members:
        live_path = directory / member.name
        history_path = history / member.name
        present = []
        for where, path in ((LOCATION_LIVE, live_path), (LOCATION_HISTORY, history_path)):
            if not path.exists():
                continue
            data = path.read_bytes()
            if len(data) != member.size or sha256_bytes(data) != member.sha256:
                raise ArchiveConflict(
                    f"archive member {member.name} differs from the manifest in {where}"
                )
            present.append(where)
        if not present:
            raise ArchiveConflict(f"archive member {member.name} is missing on both sides")
        locations[member.name] = present[0] if len(present) == 1 else LOCATION_BOTH
    if history.exists():
        extra = sorted(
            path.name for path in history.iterdir()
            if not path.name.startswith(".")
            and path.name not in {member.name for member in members}
        )
        if extra:
            raise ArchiveConflict(f"archive destination holds unexpected files {extra}")
    return UnionInspection(locations)


def union_reader(
    directory: Path, destination: str, inspection: UnionInspection,
) -> Callable[[str], bytes]:
    """検証済み union から member の bytes を読む（意味検証の adapter 用）。"""

    directory = Path(directory)

    def read(name: str) -> bytes:
        where = inspection.locations.get(name)
        if where is None:
            raise ArchiveConflict(f"chain member {name} is not in the archive manifest")
        path = directory / name if where == LOCATION_LIVE else directory / destination / name
        return path.read_bytes()

    return read


def directory_reader(directory: Path) -> Callable[[str], bytes]:
    directory = Path(directory)

    def read(name: str) -> bytes:
        return (directory / name).read_bytes()

    return read


# ---------------------------------------------------------------------------
# 移動
# ---------------------------------------------------------------------------


def fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def ensure_history_directory(directory: Path, destination: str) -> Path:
    """退避先を作り、作った階層の親を fsync する（名前の永続化）。"""

    directory = Path(directory)
    history_root = directory / layout.HISTORY_DIRECTORY
    target = directory / destination
    created_root = not history_root.exists()
    history_root.mkdir(exist_ok=True)
    if created_root:
        fsync_directory(directory)
    if not target.exists():
        target.mkdir()
        fsync_directory(history_root)
    return target


def move_member(directory: Path, destination: str, name: str) -> None:
    """1 member を ``os.replace`` で移し、移動先・移動元の directory を fsync する。"""

    directory = Path(directory)
    target = ensure_history_directory(directory, destination)
    os.replace(directory / name, target / name)
    fsync_directory(target)
    fsync_directory(directory)


def move_remaining(
    directory: Path, destination: str, inspection: UnionInspection,
    *, on_moved: Optional[Callable[[str], None]] = None,
) -> None:
    """live に残る member を移動順に移す（``state.json`` は最後）。"""

    for name in inspection.remaining:
        move_member(directory, destination, name)
        if on_moved is not None:
            on_moved(name)

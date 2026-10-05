# -*- coding: utf-8 -*-
"""kill されても残る逐次 stage journal（Issue #124 PR-124-B）。

`StageClock`（`core/stage_journal.py` の隣、`core/stage_clock.py`）は結果 JSON に
**まとめて**載る計測で、結果 JSON が出ない pair（TIMEOUT / SIGKILL）には何も
残らない。この module はその同じ計測を、**1 行ずつ書いて毎回 flush する
append-only JSONL** としても出す。プロセスが SIGKILL されても、すでに書いた行は
残る。

* schema: ``pair-stage-journal-v1``。1 行 = 1 event の JSON object。
* 行の key: ``schema`` / ``seq`` / ``event`` / ``stage`` / ``seconds`` /
  ``t_monotonic`` / ``t_epoch`` / ``pid`` / ``payload``。``schema`` を全行に
  持たせるのは、途中で切れた file でも 1 行だけで解釈できるようにするため。
* ``event`` は ``handler_registered`` / ``stage_start`` / ``stage_end`` /
  ``counter`` / ``note`` / ``journal_end`` の 6 種類だけ。

**行の会計（Issue #106 PR-106-B review 4）。** 読み手が「書かれた行がすべて残っている」ことを
確かめられるように、書き手は次を守る:

* ``seq`` は **書こうとした** 行ごとに 1 つ進む（1 から始まり、書けなかった行も番号を消費する）。
  だから途中の書き込み失敗は、後の行が書ければ ``seq`` の欠番として file に残る。
* 最後の行より後の失敗は欠番にならない。それを見えるようにするのが `StageJournal.seal()` の
  ``journal_end`` 行で、``last_seq``（それまでに書こうとした最後の番号）と ``write_failures`` を
  持つ。``journal_end`` があり、欠番が無く、``write_failures`` が 0 の journal だけが「終わりまで
  全部書けた」と言える。kill された child は ``journal_end`` を書かない（終わりは証明されない）。
* seal / close の後に来た event は書かず、番号も消費しない（journal は seal までの記録）。

**計測の定義はここに作らない。** journal は `StageClock` の region / stage を
そのまま観測する surface で、`stage_end` の ``seconds`` は clock が
``seconds_inclusive`` に足すのと同じ実測値である。同名 region の再入は clock
と同じく最外の区間だけを start / end とし、再入は ``counter`` 1 行で数える
（journal 側で二重計上しない）。

**判定には一切関与しない。** journal は結果 JSON の外にあり、authority /
proof の入力にはならない。file を開けない・書けない場合も呼び出し側へ例外を
出さず、失敗件数だけを自分で数える（`write_failures`）。

dependency rule: 標準ライブラリ以外を import しない（`core` は最下層で、
`smt` の solver worker thread からも `authority` の finalize 区間からも同じ
関数を呼ぶため）。
"""

from __future__ import annotations

import json
import os
import threading
import time
from typing import Any, Dict, Mapping, Optional, Sequence, Tuple

STAGE_JOURNAL_SCHEMA = "pair-stage-journal-v1"

#: handler 登録が成功した事実（`faulthandler.register()` が例外なく返った）。
EVENT_HANDLER_REGISTERED = "handler_registered"
EVENT_STAGE_START = "stage_start"
EVENT_STAGE_END = "stage_end"
EVENT_COUNTER = "counter"
EVENT_NOTE = "note"
#: `StageJournal.seal()` が書く最後の行（payload は ``last_seq`` / ``write_failures``）。
EVENT_JOURNAL_END = "journal_end"

JOURNAL_EVENTS = frozenset({
    EVENT_HANDLER_REGISTERED,
    EVENT_STAGE_START,
    EVENT_STAGE_END,
    EVENT_COUNTER,
    EVENT_NOTE,
    EVENT_JOURNAL_END,
})

#: 逐次記録する region 名。`condition_simplify` のように 1 pair で 10^5 回
#: 開かれる region まで 1 行ずつ書くと journal が本体より重くなるので、
#: 「kill された瞬間に何をしていたか」を復元するのに要る region だけを挙げる。
#: ここに無い region も `StageClock` は従来どおり集計する（計測は変わらない）。
JOURNALED_REGIONS = frozenset({
    "check",
    "branch_plan_orchestration",
    "obligation_build",
    "decompile",
    "analysis_regions",
})

#: `analysis_regions` の**直下**は side（`function1` / `function2`）なので、
#: 名前を列挙せずに親で判定する。side 自身も start / end を記録し、その内側の
#: `decompile` は `payload.side` に side を持つ。
SIDE_PARENT_REGION = "analysis_regions"

#: journal の書き込みで起こり得る失敗。診断は判定を壊さないので握り潰すが、
#: `except Exception` は使わない（Issue #125 PR-125-B の baseline は delete-only）。
#: - `OSError`: open / write / flush（`io.UnsupportedOperation` を含む）
#: - `TypeError` / `ValueError`: payload が JSON にならない・file が閉じている
#: - `RecursionError`: payload が自己参照している
_JOURNAL_ERRORS = (OSError, RecursionError, TypeError, ValueError)


def _coerce_seconds(seconds: Any) -> Optional[float]:
    if seconds is None:
        return None
    try:
        return round(max(0.0, float(seconds)), 6)
    except (TypeError, ValueError):
        return None


def _unserializable(value: Any) -> str:
    """JSON にならない値は型名で置き換える（journal を落とさないため）。"""
    return f"<{type(value).__name__}>"


class StageJournal:
    """1 pair 分の append-only JSONL journal。

    `append()` は 1 行書いて必ず `flush()` する。flush まで済んでいれば、
    プロセスが SIGKILL されても（OS が持っているので）その行は file に残る。
    """

    __slots__ = ("path", "pid", "_lock", "_seq", "_handle", "write_failures", "last_error")

    def __init__(self, path: Any, *, pid: Optional[int] = None) -> None:
        self.path = str(path)
        self.pid = os.getpid() if pid is None else int(pid)
        self._lock = threading.Lock()
        self._seq = 0
        self._handle: Any = None
        self.write_failures = 0
        self.last_error: Optional[str] = None
        self._open()

    def _open(self) -> None:
        try:
            directory = os.path.dirname(self.path)
            if directory:
                os.makedirs(directory, exist_ok=True)
            self._handle = open(self.path, "a", encoding="utf-8", errors="replace")
        except _JOURNAL_ERRORS as exc:
            self._handle = None
            self.write_failures += 1
            self.last_error = f"{type(exc).__name__}: {exc}"[:200]

    @property
    def is_open(self) -> bool:
        return self._handle is not None

    @property
    def sequence(self) -> int:
        return self._seq

    def append(
        self,
        event: str,
        *,
        stage: Optional[str] = None,
        seconds: Any = None,
        payload: Optional[Mapping[str, Any]] = None,
    ) -> Optional[int]:
        """1 event を書いて flush する。書けた場合だけ ``seq`` を返す。

        書けなかった行も ``seq`` を 1 つ消費する（欠番が失敗の痕跡になる。module docstring）。
        """
        if self._handle is None:
            return None
        with self._lock:
            return self._append_locked(event, stage=stage, seconds=seconds, payload=payload)

    def _append_locked(
        self,
        event: str,
        *,
        stage: Optional[str] = None,
        seconds: Any = None,
        payload: Optional[Mapping[str, Any]] = None,
    ) -> Optional[int]:
        handle = self._handle
        if handle is None:
            return None
        self._seq += 1
        sequence = self._seq
        try:
            row = {
                "schema": STAGE_JOURNAL_SCHEMA,
                "seq": sequence,
                "event": str(event),
                "stage": None if stage is None else str(stage),
                "seconds": _coerce_seconds(seconds),
                "t_monotonic": round(time.monotonic(), 6),
                "t_epoch": round(time.time(), 6),
                "pid": self.pid,
                "payload": dict(payload) if payload else {},
            }
            handle.write(json.dumps(
                row, ensure_ascii=False, sort_keys=True, default=_unserializable,
            ) + "\n")
            handle.flush()
        except _JOURNAL_ERRORS as exc:
            self.write_failures += 1
            self.last_error = f"{type(exc).__name__}: {exc}"[:200]
            return None
        return sequence

    def seal(self) -> Optional[int]:
        """``journal_end`` を書いて閉じる。書けた場合だけその ``seq`` を返す。

        ``last_seq`` と ``write_failures`` は同じ lock の中で読むので、他の thread の行と
        食い違わない。``journal_end`` 自身が書けなければ終わりは証明されない（読み手が判断する）。
        """
        if self._handle is None:
            return None
        with self._lock:
            sequence = self._append_locked(EVENT_JOURNAL_END, payload={
                "last_seq": self._seq,
                "write_failures": self.write_failures,
            })
            handle, self._handle = self._handle, None
        self._close_handle(handle)
        return sequence

    def close(self) -> None:
        """``journal_end`` を書かずに閉じる（終わりは証明されない。child の終了では `seal` を使う）。"""
        handle, self._handle = self._handle, None
        self._close_handle(handle)

    def _close_handle(self, handle: Any) -> None:
        if handle is None:
            return
        try:
            handle.flush()
            handle.close()
        except _JOURNAL_ERRORS as exc:
            self.write_failures += 1
            self.last_error = f"{type(exc).__name__}: {exc}"[:200]


# ---------------------------------------------------------------------------
# process 単位の active journal
# ---------------------------------------------------------------------------
#
# `StageClock` の scope は `contextvars` だが、journal は solver の worker
# thread（空 context で始まる）からも書くので **module global** に置く。
# 1 プロセス = 1 pair なので、同時に 2 つの journal は開かない。

_ACTIVE_JOURNAL: Optional[StageJournal] = None


def set_active_stage_journal(journal: Optional[StageJournal]) -> Optional[StageJournal]:
    """このプロセスの active journal を差し替え、直前の journal を返す。"""
    global _ACTIVE_JOURNAL
    previous = _ACTIVE_JOURNAL
    _ACTIVE_JOURNAL = journal
    return previous


def active_stage_journal() -> Optional[StageJournal]:
    return _ACTIVE_JOURNAL


def close_active_stage_journal() -> None:
    global _ACTIVE_JOURNAL
    journal, _ACTIVE_JOURNAL = _ACTIVE_JOURNAL, None
    if journal is not None:
        journal.close()


def seal_active_stage_journal() -> None:
    """active journal を外し、``journal_end`` を書いて閉じる（child の終了時に 1 回）。"""
    global _ACTIVE_JOURNAL
    journal, _ACTIVE_JOURNAL = _ACTIVE_JOURNAL, None
    if journal is not None:
        journal.seal()


def journal_event(
    event: str,
    *,
    stage: Optional[str] = None,
    seconds: Any = None,
    payload: Optional[Mapping[str, Any]] = None,
) -> Optional[int]:
    """active journal があれば 1 event 書く。無ければ no-op（None）。"""
    journal = _ACTIVE_JOURNAL
    if journal is None:
        return None
    return journal.append(event, stage=stage, seconds=seconds, payload=payload)


def journal_stage_start(
    stage: str, payload: Optional[Mapping[str, Any]] = None
) -> Optional[int]:
    return journal_event(EVENT_STAGE_START, stage=stage, payload=payload)


def journal_stage_end(
    stage: str, seconds: Any = None, payload: Optional[Mapping[str, Any]] = None
) -> Optional[int]:
    return journal_event(EVENT_STAGE_END, stage=stage, seconds=seconds, payload=payload)


def journal_counter(
    stage: str, payload: Optional[Mapping[str, Any]] = None, *, seconds: Any = None
) -> Optional[int]:
    return journal_event(EVENT_COUNTER, stage=stage, seconds=seconds, payload=payload)


def journal_note(
    note: str, payload: Optional[Mapping[str, Any]] = None
) -> Optional[int]:
    body: Dict[str, Any] = {"note": str(note)}
    if payload:
        for key, value in payload.items():
            if key != "note":
                body[key] = value
    return journal_event(EVENT_NOTE, payload=body)


# ---------------------------------------------------------------------------
# region の観測（`core/stage_clock.py` から呼ばれる）
# ---------------------------------------------------------------------------


def region_side(path: Sequence[str]) -> Optional[str]:
    """region path のうち `analysis_regions` の直下にある名前（= side）。"""
    for index in range(len(path) - 1):
        if path[index] == SIDE_PARENT_REGION:
            return str(path[index + 1])
    return None


def is_journaled_region(name: str, path: Sequence[str]) -> bool:
    """この region を 1 行ずつ記録するか。

    allowlist に載っている名前と、`analysis_regions` の直下（side）だけ。
    side は名前が固定でないので、名前ではなく親で判定する。
    """
    if name in JOURNALED_REGIONS:
        return True
    return len(path) >= 2 and path[-2] == SIDE_PARENT_REGION


def _region_payload(path: Sequence[str]) -> Dict[str, Any]:
    payload: Dict[str, Any] = {"kind": "region", "path": [str(item) for item in path]}
    side = region_side(path)
    if side is not None:
        payload["side"] = side
    return payload


def journal_region_start(name: str, path: Sequence[str]) -> None:
    if not is_journaled_region(name, path):
        return
    journal_event(EVENT_STAGE_START, stage=name, payload=_region_payload(path))


def journal_region_end(name: str, path: Sequence[str], seconds: Any) -> None:
    if not is_journaled_region(name, path):
        return
    journal_event(
        EVENT_STAGE_END, stage=name, seconds=seconds, payload=_region_payload(path)
    )


def journal_region_reentry(name: str, path: Sequence[str]) -> None:
    """同名 region への再入。

    時間は最外の区間が持っているので `stage_start` / `stage_end` は書かない
    （書くと journal 上で二重計上になる）。回数だけを `counter` で残す。
    ``path`` は再入時点の active path で、その中の**最も内側の同名 node**が
    この再入の時間を持っている（`StageClock._record_reentry` と同じ規則）。
    """
    owner: Tuple[str, ...] = tuple(path) + (str(name),)
    for index in range(len(path) - 1, -1, -1):
        if path[index] == name:
            owner = tuple(path[: index + 1])
            break
    if not is_journaled_region(name, owner):
        return
    payload = _region_payload(owner)
    payload["kind"] = "region_reentry"
    journal_event(EVENT_COUNTER, stage=name, payload=payload)

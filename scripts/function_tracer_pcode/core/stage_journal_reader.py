# -*- coding: utf-8 -*-
"""`pair-stage-journal-v1` を **fail-closed に**読み戻す（Issue #124 PR-124-C）。

PR-124-B は書き手を作った（`core/stage_journal.py`）。この module は読み手で、
supervisor の診断 worker（送信可否の判定）と `reporting/timeout_hotspot_summary`
（stage / hotspot の集計）の両方から使う。

## なぜ「1 file = 1 execution」を前提にできないか

runner は pair を新しく実行すると決めたあと、child を起こす前に既存 journal を
捨てる（PR-124-B）。そこまでは 1 file = 1 execution である。しかし **supervisor
recovery が child をもう一度起こす経路**（launch 永続化の前後で落ちた場合）では、
`.log` と同じく同一 journal に 2 つ目の execution が追記され得る。その場合、

* `seq` が 1..N -> 1..M と巻き戻る
* `pair_journal_opened` の note が 2 本以上になる
* `handler_registered` の `pid` / `start_token` が現在の child と違う

の 3 つが混在の検出条件になる（Issue #124 の 2026-09-14 handoff comment）。

この module は行を **execution segment** に切り、current child に一意に結び付く
segment だけを返す。一意に選べなければ `None` と理由を返す。**前の execution の
readiness / stage / dump を current に流用しない。複数 segment を合算しない。**

## 契約

* 判定には一切関与しない（journal は結果 JSON の外の診断）。
* 読めない・壊れている・曖昧な場合は例外を投げず、`unavailable_reason` を返す。
* regular file 以外は読まない（FIFO を開いて固まらないため）。読む量にも上限を置く。

dependency rule: 標準ライブラリ以外を import しない（`core` は最下層）。
"""

from __future__ import annotations

import json
import os
import stat
from dataclasses import dataclass, field
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core.stage_journal import (
    EVENT_HANDLER_REGISTERED,
    EVENT_NOTE,
    EVENT_STAGE_END,
    EVENT_STAGE_START,
    STAGE_JOURNAL_SCHEMA,
)

#: journal を読む上限。診断のために先頭だけ見れば足りる（readiness 行は先頭側）。
#: hotspot 集計は別の上限を使うので、呼び出し側が明示的に渡す。
READINESS_READ_LIMIT_BYTES = 64 * 1024

#: hotspot 集計の上限。1 pair 55 KB 前後（PR-124-B 実測）なので余裕を持たせる。
SUMMARY_READ_LIMIT_BYTES = 8 * 1024 * 1024

#: `open_pair_journal` が 1 execution の先頭に書く note。
JOURNAL_OPENED_NOTE = "pair_journal_opened"

#: 読み取りで起こり得る失敗（`except Exception` を使わない: PR-125-B の baseline）。
_READ_ERRORS = (OSError, RecursionError, TypeError, ValueError)

# unavailable の理由（送信側 / 集計側で同じ語彙を使う）。
UNAVAILABLE_NO_PATH = "journal_not_configured"
UNAVAILABLE_NOT_REGULAR_FILE = "journal_not_regular_file"
UNAVAILABLE_UNREADABLE = "journal_unreadable"
UNAVAILABLE_EMPTY = "journal_empty"
UNAVAILABLE_NO_HANDLER = "handler_not_registered"
UNAVAILABLE_IDENTITY_CHANGED = "process_identity_changed"
UNAVAILABLE_AMBIGUOUS = "ambiguous_multi_execution"


@dataclass(frozen=True)
class JournalRow:
    """1 行。`payload` は素の dict のまま持つ（解釈は呼び出し側）。"""

    line_number: int
    seq: Optional[int]
    event: str
    stage: Optional[str]
    seconds: Optional[float]
    t_monotonic: Optional[float]
    t_epoch: Optional[float]
    pid: Optional[int]
    payload: Mapping[str, Any]

    @property
    def region_path(self) -> Tuple[str, ...]:
        path = self.payload.get("path")
        if isinstance(path, (list, tuple)):
            return tuple(str(item) for item in path)
        return ()


@dataclass(frozen=True)
class JournalSegment:
    """1 child execution 分の行。`rows` は file 上の順序のまま。"""

    index: int
    rows: Tuple[JournalRow, ...]
    #: この segment の `handler_registered` 行（複数あれば最後のもの）。
    handler_row: Optional[JournalRow] = None

    @property
    def pids(self) -> Tuple[int, ...]:
        return tuple(sorted({row.pid for row in self.rows if row.pid is not None}))

    @property
    def start_token(self) -> Optional[str]:
        if self.handler_row is None:
            return None
        token = self.handler_row.payload.get("start_token")
        return token if isinstance(token, str) and token else None

    @property
    def handler_pid(self) -> Optional[int]:
        if self.handler_row is None:
            return None
        pid = self.handler_row.payload.get("pid")
        return pid if isinstance(pid, int) else None


@dataclass(frozen=True)
class JournalRead:
    """1 file の読み取り結果。"""

    path: Optional[str]
    rows: Tuple[JournalRow, ...] = ()
    segments: Tuple[JournalSegment, ...] = ()
    malformed_lines: int = 0
    partial_final_line: bool = False
    truncated: bool = False
    seq_rollbacks: int = 0
    opened_notes: int = 0
    unavailable_reason: Optional[str] = None

    @property
    def multi_execution(self) -> bool:
        """複数 child execution が混ざっている可能性があるか。

        3 つの検出条件（seq 巻き戻り / 開始 note 2 本以上 / segment 2 本以上）の
        どれかが立てば真。**「検出できるからそのまま全行を読んでよい」ではない**:
        真なら current segment を一意に選べるときだけ使う。
        """
        return (
            len(self.segments) > 1
            or self.seq_rollbacks > 0
            or self.opened_notes > 1
        )

    def state(self) -> Dict[str, Any]:
        """診断 artifact / summary に載せる観測状態（判定には使わない）。"""
        return {
            "path": self.path,
            "rows": len(self.rows),
            "segments": len(self.segments),
            "malformed_lines": self.malformed_lines,
            "partial_final_line": self.partial_final_line,
            "truncated": self.truncated,
            "seq_rollbacks": self.seq_rollbacks,
            "opened_notes": self.opened_notes,
            "multi_execution": self.multi_execution,
            "unavailable_reason": self.unavailable_reason,
        }


@dataclass
class _Builder:
    rows: List[JournalRow] = field(default_factory=list)
    malformed: int = 0
    partial_final_line: bool = False
    truncated: bool = False


def _coerce_int(value: Any) -> Optional[int]:
    return value if isinstance(value, int) and not isinstance(value, bool) else None


def _coerce_float(value: Any) -> Optional[float]:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    return float(value)


def _parse_line(text: str, line_number: int) -> Optional[JournalRow]:
    try:
        row = json.loads(text)
    except ValueError:
        return None
    if not isinstance(row, dict) or row.get("schema") != STAGE_JOURNAL_SCHEMA:
        return None
    event = row.get("event")
    if not isinstance(event, str) or not event:
        return None
    payload = row.get("payload")
    stage = row.get("stage")
    return JournalRow(
        line_number=line_number,
        seq=_coerce_int(row.get("seq")),
        event=event,
        stage=stage if isinstance(stage, str) else None,
        seconds=_coerce_float(row.get("seconds")),
        t_monotonic=_coerce_float(row.get("t_monotonic")),
        t_epoch=_coerce_float(row.get("t_epoch")),
        pid=_coerce_int(row.get("pid")),
        payload=payload if isinstance(payload, dict) else {},
    )


def _read_rows(path: str, *, max_bytes: int) -> _Builder:
    builder = _Builder()
    with open(path, "r", encoding="utf-8", errors="replace") as handle:
        blob = handle.read(max_bytes + 1)
    if len(blob) > max_bytes:
        builder.truncated = True
        blob = blob[:max_bytes]
    if not blob:
        return builder
    lines = blob.split("\n")
    # 末尾に改行が無い = 最後の行は書きかけ（kill された journal で普通に起きる）。
    # 切れた行は「壊れた行」ではなく `partial_final_line` として別に数える。
    trailing = lines.pop()
    if trailing:
        builder.partial_final_line = True
    for index, text in enumerate(lines, start=1):
        if not text.strip():
            continue
        row = _parse_line(text, index)
        if row is None:
            builder.malformed += 1
            continue
        builder.rows.append(row)
    return builder


def _split_segments(rows: Sequence[JournalRow]) -> Tuple[Tuple[JournalSegment, ...], int, int]:
    """行を execution segment に切る。

    新しい segment が始まるのは **file の先頭** / `pair_journal_opened` note /
    `seq` の巻き戻り（直前の行の seq 以下）の 3 か所。戻り値は
    ``(segments, seq_rollbacks, opened_notes)``。
    """
    segments: List[List[JournalRow]] = []
    current: List[JournalRow] = []
    previous_seq: Optional[int] = None
    rollbacks = 0
    opened = 0
    for row in rows:
        is_opened_note = (
            row.event == EVENT_NOTE
            and row.payload.get("note") == JOURNAL_OPENED_NOTE
        )
        rolled_back = (
            row.seq is not None and previous_seq is not None and row.seq <= previous_seq
        )
        if rolled_back:
            rollbacks += 1
        if is_opened_note:
            opened += 1
        if current and (is_opened_note or rolled_back):
            segments.append(current)
            current = []
        current.append(row)
        if row.seq is not None:
            previous_seq = row.seq
    if current:
        segments.append(current)
    built: List[JournalSegment] = []
    for index, group in enumerate(segments):
        handler = None
        for row in group:
            if row.event == EVENT_HANDLER_REGISTERED:
                handler = row
        built.append(JournalSegment(index=index, rows=tuple(group), handler_row=handler))
    return tuple(built), rollbacks, opened


def read_stage_journal(
    path: Any, *, max_bytes: int = READINESS_READ_LIMIT_BYTES,
) -> JournalRead:
    """journal を読んで segment に切る。例外は投げない。

    regular file 以外（FIFO / device / directory / symlink 先が無い）は読まない:
    診断のための読み取りで supervisor が固まってはならない。
    """
    if not isinstance(path, (str, os.PathLike)):
        return JournalRead(path=None, unavailable_reason=UNAVAILABLE_NO_PATH)
    resolved = os.fspath(path)
    if not resolved:
        return JournalRead(path=None, unavailable_reason=UNAVAILABLE_NO_PATH)
    try:
        status = os.stat(resolved)
    except _READ_ERRORS:
        return JournalRead(path=resolved, unavailable_reason=UNAVAILABLE_NOT_REGULAR_FILE)
    if not stat.S_ISREG(status.st_mode):
        return JournalRead(path=resolved, unavailable_reason=UNAVAILABLE_NOT_REGULAR_FILE)
    try:
        builder = _read_rows(resolved, max_bytes=max_bytes)
    except _READ_ERRORS:
        return JournalRead(path=resolved, unavailable_reason=UNAVAILABLE_UNREADABLE)
    if not builder.rows:
        return JournalRead(
            path=resolved,
            malformed_lines=builder.malformed,
            partial_final_line=builder.partial_final_line,
            truncated=builder.truncated,
            unavailable_reason=UNAVAILABLE_EMPTY,
        )
    segments, rollbacks, opened = _split_segments(builder.rows)
    return JournalRead(
        path=resolved,
        rows=tuple(builder.rows),
        segments=segments,
        malformed_lines=builder.malformed,
        partial_final_line=builder.partial_final_line,
        truncated=builder.truncated,
        seq_rollbacks=rollbacks,
        opened_notes=opened,
    )


def select_current_segment(
    read: JournalRead, *, pid: Optional[int] = None, start_token: Optional[str] = None,
) -> Tuple[Optional[JournalSegment], Optional[str]]:
    """current child execution の segment を一意に選ぶ。

    * ``pid`` / ``start_token`` を渡した場合（supervisor 側）: その 2 つに一致する
      `handler_registered` を持つ segment が **ちょうど 1 本**のときだけ返す。
      0 本なら `handler_not_registered`（handler 行が 1 つも無い）または
      `process_identity_changed`（別 execution の handler 行しか無い）。
      2 本以上なら `ambiguous_multi_execution`。
    * 渡さない場合（run 終了後の集計側。launch receipt はもう残っていない）:
      混在の兆候が無く segment が 1 本のときだけ返す。混在していれば
      `ambiguous_multi_execution`。

    **前の execution の segment を current として返すことはない。**
    """
    if read.unavailable_reason is not None:
        return None, read.unavailable_reason
    if not read.segments:
        return None, UNAVAILABLE_EMPTY
    if pid is None and start_token is None:
        if read.multi_execution:
            return None, UNAVAILABLE_AMBIGUOUS
        return read.segments[0], None
    matched = [
        segment for segment in read.segments
        if segment.handler_row is not None
        and (pid is None or segment.handler_pid == pid)
        and (start_token is None or segment.start_token == start_token)
    ]
    if len(matched) == 1:
        return matched[0], None
    if len(matched) > 1:
        return None, UNAVAILABLE_AMBIGUOUS
    if all(segment.handler_row is None for segment in read.segments):
        return None, UNAVAILABLE_NO_HANDLER
    return None, UNAVAILABLE_IDENTITY_CHANGED


@dataclass(frozen=True)
class SegmentStages:
    """1 segment の stage 進行（hotspot 用）。合算は segment を跨がない。"""

    last_completed_stage: Optional[str] = None
    last_completed_path: Tuple[str, ...] = ()
    last_completed_seconds: Optional[float] = None
    in_progress_stage: Optional[str] = None
    in_progress_path: Tuple[str, ...] = ()
    in_progress_since: Optional[float] = None
    #: 完了した区間のうち最も長かったもの。「最後に完了した stage」は kill 後の
    #: teardown（`close_programs` など）になり得るので、時間の所在はこちらで見る。
    longest_completed_stage: Optional[str] = None
    longest_completed_seconds: Optional[float] = None
    started: int = 0
    completed: int = 0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "last_completed_stage": self.last_completed_stage,
            "last_completed_path": list(self.last_completed_path),
            "last_completed_seconds": self.last_completed_seconds,
            "in_progress_stage": self.in_progress_stage,
            "in_progress_path": list(self.in_progress_path),
            "in_progress_since": self.in_progress_since,
            "longest_completed_stage": self.longest_completed_stage,
            "longest_completed_seconds": self.longest_completed_seconds,
            "stage_starts": self.started,
            "stage_ends": self.completed,
        }


def segment_stages(
    segment: JournalSegment, *, as_of_epoch: Optional[float] = None,
) -> SegmentStages:
    """最後に完了した stage と、その時点で進行中の stage。

    進行中の stage は「`stage_start` があって対応する `stage_end` が無い区間のうち
    一番内側（最後に開いたもの）」。同名 region の再入は書き手が最外だけを
    start / end にしているので、ここでも path 込みで突き合わせる。

    ``as_of_epoch`` を渡すと、その ``t_epoch`` **以前**の行だけを見る。SIGTERM を
    受けた child は後始末を走らせてから終わるので、journal の末尾まで読むと開いて
    いた region が全部閉じてしまい「進行中の stage」が空になる。stack dump を
    撮った瞬間（deadline の少し前）で切ると、その時点で開いていた region が残る。
    """
    open_stack: List[JournalRow] = []
    last_completed: Optional[JournalRow] = None
    longest: Optional[JournalRow] = None
    started = 0
    completed = 0
    for row in segment.rows:
        if (
            as_of_epoch is not None
            and row.t_epoch is not None
            and row.t_epoch > as_of_epoch
        ):
            break
        if row.event == EVENT_STAGE_START:
            open_stack.append(row)
            started += 1
            continue
        if row.event != EVENT_STAGE_END:
            continue
        completed += 1
        last_completed = row
        if row.seconds is not None and (
            longest is None or longest.seconds is None or row.seconds > longest.seconds
        ):
            longest = row
        for index in range(len(open_stack) - 1, -1, -1):
            candidate = open_stack[index]
            if candidate.stage == row.stage and candidate.region_path == row.region_path:
                del open_stack[index]
                break
    active = open_stack[-1] if open_stack else None
    return SegmentStages(
        last_completed_stage=None if last_completed is None else last_completed.stage,
        last_completed_path=() if last_completed is None else last_completed.region_path,
        last_completed_seconds=None if last_completed is None else last_completed.seconds,
        in_progress_stage=None if active is None else active.stage,
        in_progress_path=() if active is None else active.region_path,
        in_progress_since=None if active is None else active.t_monotonic,
        longest_completed_stage=None if longest is None else longest.stage,
        longest_completed_seconds=None if longest is None else longest.seconds,
        started=started,
        completed=completed,
    )


@dataclass(frozen=True)
class StageInterval:
    """1 つの stage の区間（`stage_start` から対応する `stage_end` まで、monotonic）。

    ``end`` が ``None`` なのは、segment の終わりまで `stage_end` が来なかった区間。
    """

    stage: Optional[str]
    path: Tuple[str, ...]
    start: float
    end: Optional[float]


def stage_intervals(segment: JournalSegment) -> Tuple[StageInterval, ...]:
    """segment の stage の区間（開始順）。突き合わせは `segment_stages` と同じ規則。

    `stage_start` と `stage_end` は stage 名と region path の組で、最も内側（最後に開いた）
    ものから閉じる。時刻の無い行は区間にしない。
    """
    open_stack: List[JournalRow] = []
    closed: List[StageInterval] = []
    for row in segment.rows:
        if row.t_monotonic is None:
            continue
        if row.event == EVENT_STAGE_START:
            open_stack.append(row)
            continue
        if row.event != EVENT_STAGE_END:
            continue
        for index in range(len(open_stack) - 1, -1, -1):
            candidate = open_stack[index]
            if candidate.stage == row.stage and candidate.region_path == row.region_path:
                del open_stack[index]
                closed.append(StageInterval(
                    stage=candidate.stage, path=candidate.region_path,
                    start=float(candidate.t_monotonic), end=float(row.t_monotonic),
                ))
                break
    closed.extend(
        StageInterval(stage=row.stage, path=row.region_path,
                      start=float(row.t_monotonic), end=None)
        for row in open_stack
    )
    return tuple(sorted(closed, key=lambda interval: interval.start))

# -*- coding: utf-8 -*-
"""作業量を受け取らない読み（record の構築・写し）の固定の上限（Issue #22 PR-22-D）。

作業量で数える walker（`core/json_encoding`）の外で、解析の値の列・mapping を辿る関数の唯一の入口。
上限は `core/live_values.SCAN_LIMIT`（live な値の読みと同じ固定の契約）で、長さを組み込みの slot で
O(1) に読んで比べてから辿る（iterator は 1 要素ずつ数える）。

* `elements_within_limit` / `items_within_limit`: 上限の外は **pair terminal な登録済みの限界**
  （`analysis_budget_exceeded`、場所 `SCAN_LIMITATION_SITE`。pair の台帳へ記録してから上げる）。解析の
  値の大きさが読みの契約の外にあるという限界で、内部バグ（`TypeError`）にしない。
* `prefix_within_limit`: 判定に使わない診断の写し。止めずに先頭だけを写し、写さなかった件数を返す。

live な値の読み方そのもの（組み込みの振る舞いの判定・storage の読み）は `core/live_values` が持ち、
この module は上限の超過の意味（限界）を持つ（`live_values` は標準 library だけを import する）。
"""

from __future__ import annotations

from typing import Any, Iterator, NoReturn, Tuple

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.errors import (
    DeadlineExceeded,
    PairStopState,
    raise_limitation,
)

#: 作業量を受け取らない読みが固定の上限を超えたときの限界の場所
SCAN_LIMITATION_SITE = "core.read_limits.scan"


class _SharedScan:
    """入れ子の列を辿る 1 つの読みが共有する上限（辿った数の和を `SCAN_LIMIT` と比べる）。"""

    __slots__ = ("used",)

    def __init__(self) -> None:
        self.used = 0

    def admit(self, count: int) -> bool:
        if self.used + count > live_values.SCAN_LIMIT:
            return False
        self.used += count
        return True


def scan_budget() -> _SharedScan:
    """入れ子の列を辿る 1 つの読みが共有する上限（`elements_within_limit(..., scan)` に渡す）。"""

    return _SharedScan()


def _scan_limit_exceeded(what: str, observed: int) -> NoReturn:
    """作業量を受け取らない読みが固定の上限を超えた: pair terminal な登録済みの限界。"""

    limit = live_values.SCAN_LIMIT
    raise_limitation(
        DeadlineExceeded(
            f"{what} exceeds the fixed read bound ({observed} > {limit})",
            site=SCAN_LIMITATION_SITE,
            target_key=("read_limits_scan", what),
            missing_semantic_fact=("read_limits_scan", what, limit),
            evidence_refs=(f"limit={limit}", f"observed={observed}"),
        ),
        stop=PairStopState.PAIR_TERMINAL_LIMITATION,
    )


def _admitted(count: int, scan: Any) -> bool:
    return count <= live_values.SCAN_LIMIT if scan is None else scan.admit(count)


def elements_within_limit(values: Any, scan: Any = None) -> Iterator[Any]:
    """`live_values.elements_of` と同じ要素を `SCAN_LIMIT` 個まで（大きさの分かる容器は辿る前に O(1) で
    比べ、iterator は 1 要素ずつ数える）。`scan` を渡すと、入れ子の列の和を上限にする。上限の外は登録済みの
    限界。作業量で数える walker は `elements_of` を使う（数えながら止まる）。"""

    if live_values.builtin_sequence(values) or live_values.builtin_set(values):
        count = live_values.size(values)
        if not _admitted(count, scan):
            _scan_limit_exceeded("a sequence read without a work budget", count)
        return live_values.elements_of(values)
    return _counted(live_values.elements_of(values), scan)


def items_within_limit(mapping: Any) -> Iterator[Tuple[Any, Any]]:
    """`live_values.items_of` と同じ (key, 値) を `SCAN_LIMIT` 組まで（辿る前に O(1) で比べる。外は登録済みの限界）。"""

    count = live_values.size(mapping)
    if not _admitted(count, None):
        _scan_limit_exceeded("a mapping read without a work budget", count)
    return live_values.items_of(mapping)


def _counted(iterator: Iterator[Any], scan: Any = None) -> Iterator[Any]:
    count = 0
    for value in iterator:
        count += 1
        if not (count <= live_values.SCAN_LIMIT if scan is None else scan.admit(1)):
            _scan_limit_exceeded("an iterator read without a work budget", count)
        yield value


def prefix_within_limit(values: Any) -> tuple:
    """診断の写し: `elements_of` と同じ要素の先頭 `SCAN_LIMIT` 個（止めない。上限 + 1 個目を引き出したところで止める）。

    写さなかった件数は `omitted_beyond_limit`（大きさの分かる容器・mapping の長さから O(1) で）。
    """

    scan = _SharedScan()
    head = []
    for value in live_values.elements_of(values):
        if not scan.admit(1):
            break
        head.append(value)
    return tuple(head)


def omitted_beyond_limit(values: Any) -> int:
    """`prefix_within_limit` が写さない件数（大きさの分かる容器・mapping の長さ。それ以外は `TypeError`）。"""

    return max(0, live_values.size(values) - live_values.SCAN_LIMIT)


__all__ = [
    "SCAN_LIMITATION_SITE",
    "elements_within_limit",
    "items_within_limit",
    "omitted_beyond_limit",
    "prefix_within_limit",
    "scan_budget",
]

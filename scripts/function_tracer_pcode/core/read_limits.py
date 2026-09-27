# -*- coding: utf-8 -*-
"""作業量を受け取らない読みの「量が多すぎる」ときの意味の owner（Issue #22 PR-22-D）。

作業量で数える owner（walker・直列化の scope・fingerprint・予算つきの凍結）の外で、解析の値の列・
mapping を辿る関数（record の構築・写し）の唯一の入口。責務の境界:

* `core/live_values` は「安全に読めるか」の owner（値の code を実行せずに storage を読めるか）。量の
  意味は決めない: 固定の上限（`SCAN_LIMIT`）を超える値の storage の読みは、今の文脈の量の owner へ
  渡す（作業量・呼ぶ側・この module）。「安全でない」（`TypeError` / `None`）とは答えない。
* この module は作業量を受け取らない読みの量の意味の owner。

  - この module の入口は、読む前に基底型の slot で O(1) に数え（`live_values.storage_count`）、上限の
    外は **型つきの登録済みの限界** `FixedReadBoundExceeded` を pair の台帳へ記録してから上げる。上限の
    内側だけ安全の判定（振る舞い・key の hash）を行い、それから辿る。
  - 入口の中の入れ子の量（key の tuple の node・包んだ proxy の段・反復の確かめ）も同じ固定の上限で
    読む（`live_values.fixed_bound_reads`）。量の owner の無い文脈の隠れた読み（key で引く・名前で
    属性を読む）が上限を超えたときも、`live_values` へ登録したこの module が同じ限界にする（どの関数から
    読んだかに依らない: 途中の `except TypeError` / `except Exception` を素通りせず、記録が先）。
  - 入口は作業量の文脈の中で呼ばれても固定の上限で読む（「作業量を受け取らない読み」という API の選択。
    作業量を持つ呼ぶ側は walker を使う）。

* `DeadlineExceeded`（時間・段数の打ち切り）は #106 の owner の型で、ここでは使わない: 読みの量の限界は
  reason id（`analysis_budget_exceeded`、authority の契約と共通）だけを共有し、Python の型・stop state
  （軸 C の既定: `PAIR_TERMINAL_LIMITATION`）・owner（この module の site）・診断の分類（例外の型・
  `target_key` の先頭 `fixed_read_bound`）は別。

判定に使わない診断の写し（`prefix_within_limit`）は止めない: 先頭だけを写し、写さなかった件数を返す。
"""

from __future__ import annotations

from typing import Any, Iterator, NoReturn, Tuple

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.errors import AnalysisLimitation, raise_limitation

#: 作業量を受け取らない読みが固定の上限を超えたときの限界の場所
SCAN_LIMITATION_SITE = "core.read_limits.scan"
#: 限界の reason（authority の analysis limitation domain の登録済みの reason。時間の予算と共通の id）
READ_BOUND_REASON_ID = "analysis_budget_exceeded"
#: 限界の `target_key` の先頭（診断の分類。deadline・式の大きさ・event の契約の限界と別の種類）
READ_BOUND_TARGET = "fixed_read_bound"


class FixedReadBoundExceeded(AnalysisLimitation):
    """作業量を受け取らない読みの量が固定の上限（`SCAN_LIMIT`）を超えた限界（**deadline ではない**）。

    reason id は authority の契約上 `analysis_budget_exceeded` を共有するが、型は `DeadlineExceeded`
    から派生しない（#106 が型で deadline を見分けても、読みの量の限界を deadline と数えない）。
    stop state は軸 C（`core/errors._default_stop_state`）の限界の既定で、作る場所で選ばない。
    """

    REASON_ID = READ_BOUND_REASON_ID

    def __init__(self, what: str, *, observed: int) -> None:
        limit = live_values.SCAN_LIMIT
        super().__init__(
            self.REASON_ID,
            f"{what} exceeds the fixed read bound (at least {observed} > {limit})",
            site=SCAN_LIMITATION_SITE,
            target_key=(READ_BOUND_TARGET, what),
            missing_semantic_fact=(READ_BOUND_TARGET, what, limit),
            evidence_refs=(f"limit={limit}", f"observed={observed}"),
        )
        self.what = what
        self.observed = observed
        self.limit = limit


def raise_read_bound_exceeded(what: str, observed: int) -> NoReturn:
    """読みの量の限界を pair の台帳へ記録してから上げる（この module の唯一の限界の組み立て口）。"""

    raise_limitation(FixedReadBoundExceeded(what, observed=observed))


# 作業量の無い文脈の値の storage の読みの量の意味は、この module が決める（`live_values` は標準
# library だけを import するので、owner の側が自分を登録する）
live_values.register_unmetered_read_owner(raise_read_bound_exceeded)


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


def _admit(count: int, scan: Any, what: str) -> None:
    """読む前の量の判定（上限の外は限界。安全の判定より先）。`scan` が無ければ `count` は読みの全体。"""

    if scan is None:
        if count > live_values.SCAN_LIMIT:
            raise_read_bound_exceeded(what, count)
        return
    if not scan.admit(count):
        raise_read_bound_exceeded(what, scan.used + count)


def elements_within_limit(values: Any, scan: Any = None) -> Iterator[Any]:
    """`live_values.elements_of` と同じ要素を `SCAN_LIMIT` 個まで。`scan` を渡すと、入れ子の列の和を上限にする。

    順序: (1) 組み込みの容器（subclass・`OrderedDict`・`MappingProxyType` を含む）は基底型の slot で
    O(1) に数えて上限と比べる（上限の外は限界）、(2) 上限の内側だけ安全の判定をして辿る。iterator は
    1 要素ずつ数える。量の限界は容器の種類に依らない。作業量で数える walker は `elements_of` を使う。
    """

    count = live_values.storage_count(values)
    if count is not None:
        _admit(count, scan, "a sequence read without a work budget")
    with live_values.fixed_bound_reads():
        iterator = live_values.elements_of(values)
    return iterator if count is not None else _counted(iterator, scan)


def items_within_limit(mapping: Any, scan: Any = None) -> Iterator[Tuple[Any, Any]]:
    """`live_values.items_of` と同じ (key, 値) を `SCAN_LIMIT` 組まで（数えてから安全の判定。外は限界）。"""

    count = live_values.storage_count(mapping)
    if count is not None:
        _admit(count, scan, "a mapping read without a work budget")
    with live_values.fixed_bound_reads():
        return live_values.items_of(mapping)


def copied_within_limit(value: Any, scan: Any = None) -> Any:
    """`live_values.copied_container` と同じ写し（dict / list の subclass も基底型の slot で）を、写す要素の
    数を上限（`scan` を渡せば入れ子の和）と比べてから作る。dict / list でなければ `NOT_PLAIN`。"""

    if not (live_values.is_kind(value, dict) or live_values.is_kind(value, list)):
        return live_values.NOT_PLAIN
    _admit(live_values.storage_count(value), scan, "a container copied without a work budget")
    with live_values.fixed_bound_reads():
        return live_values.copied_container(value)


def _counted(iterator: Iterator[Any], scan: Any = None) -> Iterator[Any]:
    # 引き出しは呼ぶ側の文脈（generator の中で文脈を切り替えると、止まっている間も呼ぶ側に残る）: 要素を
    # 作る package の generator の読みはその generator の owner の規則
    count = 0
    for value in iterator:
        count += 1
        if scan is None:
            _admit(count, None, "an iterator read without a work budget")
        else:
            _admit(1, scan, "an iterator read without a work budget")
        yield value


def prefix_within_limit(values: Any) -> tuple:
    """診断の写し: `elements_of` と同じ要素の先頭 `SCAN_LIMIT` 個（止めない。上限 + 1 個目を引き出したところで止める）。

    写す間の値の storage の読みは限界を記録しない（`signalled_storage_reads`）: 安全の判定が上限の外の
    storage を読めないときは、写せた先頭まで。写さなかった件数は `omitted_beyond_limit(values, kept=len(写し))`。
    """

    return _prefix(live_values.elements_of, values)


def prefix_items_within_limit(mapping: Any) -> tuple:
    """診断の写し: `items_of(mapping)` の先頭 `SCAN_LIMIT` 組（`prefix_within_limit` と同じ規則。止めない）。"""

    return _prefix(live_values.items_of, mapping)


def _prefix(read: Any, values: Any) -> tuple:
    head: list = []
    with live_values.signalled_storage_reads():
        try:
            for value in read(values):
                if len(head) >= live_values.SCAN_LIMIT:
                    break
                head.append(value)
        except live_values.StorageBeyondReadBound:
            # 診断の写しの量の意味（止めない）: 写せた先頭まで
            pass
    return tuple(head)


def omitted_beyond_limit(values: Any, *, kept: int) -> int:
    """`prefix_within_limit` が `kept` 個を写したときに写さなかった件数（組み込みの容器の storage の数から
    O(1) で。数えられない値は `TypeError`）。"""

    count = live_values.storage_count(values)
    if count is None:
        raise TypeError(f"{live_values.type_name(type(values))} has no builtin storage to count")
    return max(0, count - kept)


__all__ = [
    "FixedReadBoundExceeded",
    "READ_BOUND_REASON_ID",
    "READ_BOUND_TARGET",
    "SCAN_LIMITATION_SITE",
    "copied_within_limit",
    "elements_within_limit",
    "items_within_limit",
    "omitted_beyond_limit",
    "prefix_items_within_limit",
    "prefix_within_limit",
    "raise_read_bound_exceeded",
    "scan_budget",
]

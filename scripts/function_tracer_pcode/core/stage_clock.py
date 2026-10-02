# -*- coding: utf-8 -*-
"""ペア 1 件の実行を段階（stage）と region 階層で計測する時計（Issue #14 / #124）。

`checker` から `analysis` / `proof` まで同じ型で計測して checker が pull するため、
下位層から import できる `core` に置く。**標準ライブラリ以外を import しない**
（上位層への依存を作らない）。

用語:

``stage``
    `timed()` / `mark()` で記録する平坦な区間（`jvm_start` / `import_binary1` …）。
    Issue #14 からの既存 surface で、意味も出力先（``seconds``）も変えない。

``region``
    `stage_region()` で囲む**階層付き**の区間（Issue #124）。親子関係を持ち、

    * ``seconds_inclusive`` = region 全体（子 region を含む）
    * ``seconds_exclusive`` = ``seconds_inclusive`` − 直接子の inclusive 合計
    * ``calls`` = region に入った実回数（再入も 1 回と数える）
    * ``reentrant_calls`` = そのうち「同名 region の内側だったので独立区間として
      計測しなかった」回数

    同名 region の再入（`check()` の再帰など）は**最外の区間だけ**を計測するので、
    inclusive が二重計上されることはない。``calls`` は実際の呼び出し回数なので、
    独立区間の本数は ``calls - reentrant_calls``。

伝搬は `contextvars`。`ThreadPoolExecutor` の worker は空 context で始まるため、
worker 内で `stage_region()` を呼んでも親 region には混入しない（no-op になる）。
worker から加算される計測は region では測れないので counter で行う
（`smt/parallel.py` の solver counter）。

診断専用。計測に失敗しても例外を呼び出し側へ出さない。
"""

from __future__ import annotations

import os
import threading
import time
from contextlib import contextmanager
from contextvars import ContextVar
from typing import Any, Dict, Iterable, Iterator, List, Mapping, Optional, Sequence, Tuple

# Issue #124 PR-124-B: 同じ stage / region を kill 耐性のある JSONL としても出す。
# journal は**この計測の観測 surface**であって、別の計測定義ではない
# （`stage_end` の秒数は clock が集計するのと同じ実測値）。
from scripts.function_tracer_pcode.core.stage_journal import (
    journal_region_end,
    journal_region_reentry,
    journal_region_start,
    journal_stage_end,
    journal_stage_start,
)

STAGE_TIMING_SCHEMA = "pair-stage-timing-v1"

#: 平坦な stage（`timed()`）の journal payload。region と区別するための印。
_FLAT_STAGE_PAYLOAD = {"kind": "stage"}

#: 恒等式の許容誤差 = ``max(ABSOLUTE, RELATIVE * 比較する値の大きい方)``。
#: 浮動小数点の丸め（snapshot は 6 桁丸め）と scheduler jitter を吸収するための
#: 値で、厳密な float 一致を恒等式の条件にしない。
REGION_IDENTITY_ABSOLUTE_TOLERANCE = 0.05
REGION_IDENTITY_RELATIVE_TOLERANCE = 0.01

#: 派生ビューが名指しする region 名。計測点（`stage_region("check")` など）は
#: 各 entry point が文字列で開き、ここは「どの名前がどの派生値の基準か」を決める。
#: `CHECK_REGION` は内外分離の親、`OBLIGATION_BUILD_REGION` はその分離対象、
#: `ORCHESTRATION_REGION` は恒等式 A / B の対象。
CHECK_REGION = "check"
OBLIGATION_BUILD_REGION = "obligation_build"
ORCHESTRATION_REGION = "branch_plan_orchestration"

_ACTIVE_CLOCK: ContextVar[Optional["StageClock"]] = ContextVar(
    "active_stage_clock", default=None
)
_ACTIVE_REGION_PATH: ContextVar[Tuple[str, ...]] = ContextVar(
    "active_stage_region_path", default=()
)


def process_age_seconds() -> Optional[float]:
    """このプロセスの起動からの経過秒（Linux の /proc、fail-open で None）。"""
    try:
        with open("/proc/self/stat", "r", encoding="ascii", errors="replace") as handle:
            stat = handle.read()
        fields = stat[stat.rindex(")") + 2:].split()
        start_ticks = int(fields[19])
        with open("/proc/uptime", "r", encoding="ascii") as handle:
            uptime = float(handle.read().split()[0])
        ticks_per_second = os.sysconf("SC_CLK_TCK")
        return max(0.0, uptime - start_ticks / float(ticks_per_second))
    except Exception:
        return None


class _RegionNode:
    """region 木の 1 ノード（1 つの path に対応する集計）。"""

    __slots__ = ("name", "seconds_inclusive", "calls", "reentrant_calls", "children")

    def __init__(self, name: str) -> None:
        self.name = name
        self.seconds_inclusive = 0.0
        self.calls = 0
        self.reentrant_calls = 0
        self.children: Dict[str, "_RegionNode"] = {}


class _NullRegion:
    """clock が無いときの no-op ハンドル（生成しないで使い回す）。"""

    __slots__ = ()

    def start(self) -> "_NullRegion":
        return self

    def close(self) -> None:
        return None

    def __enter__(self) -> "_NullRegion":
        return self

    def __exit__(self, *_exc: Any) -> bool:
        return False


_NO_REGION = _NullRegion()


class _OpenRegion:
    """1 回分の region 区間。``with`` でも ``start()`` / ``close()`` でも使える。"""

    __slots__ = ("_clock", "_name", "_token", "_started", "_path", "_closed")

    def __init__(self, clock: "StageClock", name: str) -> None:
        self._clock = clock
        self._name = name
        self._token = None
        self._started: Optional[float] = None
        self._path: Tuple[str, ...] = ()
        self._closed = False

    def start(self) -> "_OpenRegion":
        if self._closed or self._started is not None:
            return self
        try:
            path = _ACTIVE_REGION_PATH.get()
            if self._name in path:
                # 同名 region への再入。時間は最外の区間が持っているので、
                # ここでは呼び出し回数だけを最外ノードへ足す。
                self._clock._record_reentry(path, self._name)
                self._closed = True
                journal_region_reentry(self._name, path)
                return self
            self._path = path + (self._name,)
            self._token = _ACTIVE_REGION_PATH.set(self._path)
            self._started = time.perf_counter()
        except Exception:
            self._closed = True
        else:
            # journal は計測が成立した後で書く（journal 側の失敗が region の
            # 計測を落とさないよう、既存の except の外に置く）。
            journal_region_start(self._name, self._path)
        return self

    def close(self) -> None:
        if self._closed:
            return
        self._closed = True
        try:
            elapsed = (
                time.perf_counter() - self._started
                if self._started is not None
                else 0.0
            )
            if self._token is not None:
                try:
                    _ACTIVE_REGION_PATH.reset(self._token)
                except ValueError:
                    # context をまたいで閉じられた場合は復元だけ諦める。
                    _ACTIVE_REGION_PATH.set(self._path[:-1])
            if self._started is not None:
                self._clock._record_region(self._path, elapsed)
                journal_region_end(self._name, self._path, elapsed)
        except Exception:
            return

    def __enter__(self) -> "_OpenRegion":
        return self.start()

    def __exit__(self, *_exc: Any) -> bool:
        self.close()
        return False


class StageClock:
    """ペア 1 件の実行を stage（平坦）と region（階層）で計測する。

    ``timed(stage)`` で囲んだ区間の秒数を ``seconds[stage]`` に加算し、同じ
    stage を複数回囲めば合算する。``mark(stage, seconds)`` は外部で測った値の
    登録用。``snapshot()`` は結果 JSON の診断ブロックへそのまま入る dict。
    診断なので計測に失敗しても例外を外へ出さない。

    ``scope()`` の内側では `stage_region()` がこの clock へ記録する。scope は
    ペアの処理全体で 1 回だけ開き、stage plan の外から開始する。
    """

    def __init__(self) -> None:
        self.seconds: Dict[str, float] = {}
        self.order: list = []
        self.notes: Dict[str, Any] = {}
        self._regions: Dict[str, _RegionNode] = {}
        self._region_lock = threading.Lock()
        self._process_age_at_start = process_age_seconds()
        self._started = time.monotonic()

    # -- stage（Issue #14 からの既存 surface。意味を変えない） ---------------

    @contextmanager
    def timed(self, stage: str) -> Iterator[None]:
        started = time.monotonic()
        # Issue #124 PR-124-B: JVM 起動や auto-analyze の途中で kill された pair
        # にも「どの stage にいたか」が残るよう、同じ区間を journal にも出す。
        journal_stage_start(stage, _FLAT_STAGE_PAYLOAD)
        try:
            yield
        finally:
            elapsed = time.monotonic() - started
            self.mark(stage, elapsed)
            journal_stage_end(stage, elapsed, _FLAT_STAGE_PAYLOAD)

    def mark(self, stage: str, seconds: float) -> None:
        try:
            value = max(0.0, float(seconds))
        except (TypeError, ValueError):
            return
        if stage not in self.seconds:
            self.order.append(stage)
            self.seconds[stage] = 0.0
        self.seconds[stage] += value

    def note(self, key: str, value: Any) -> None:
        self.notes[key] = value

    # -- region（Issue #124） ------------------------------------------------

    @contextmanager
    def scope(self) -> Iterator["StageClock"]:
        """この clock を「今の実行文脈で有効な clock」にする。"""
        clock_token = _ACTIVE_CLOCK.set(self)
        path_token = _ACTIVE_REGION_PATH.set(())
        try:
            yield self
        finally:
            try:
                _ACTIVE_REGION_PATH.reset(path_token)
            except ValueError:
                _ACTIVE_REGION_PATH.set(())
            try:
                _ACTIVE_CLOCK.reset(clock_token)
            except ValueError:
                _ACTIVE_CLOCK.set(None)

    def _record_region(self, path: Sequence[str], elapsed: float) -> None:
        try:
            value = max(0.0, float(elapsed))
        except (TypeError, ValueError):
            return
        with self._region_lock:
            node = self._node_for(path)
            if node is None:
                return
            node.calls += 1
            node.seconds_inclusive += value

    def _record_reentry(self, path: Sequence[str], name: str) -> None:
        # path の中で最も内側にある同名ノードが、この再入の時間を持っている。
        for index in range(len(path) - 1, -1, -1):
            if path[index] == name:
                with self._region_lock:
                    node = self._node_for(path[: index + 1])
                    if node is None:
                        return
                    node.calls += 1
                    node.reentrant_calls += 1
                return

    def _node_for(self, path: Sequence[str]) -> Optional[_RegionNode]:
        """path のノードを（無ければ祖先ごと作って）返す。lock 内で呼ぶこと。"""
        if not path:
            return None
        children = self._regions
        node: Optional[_RegionNode] = None
        for name in path:
            node = children.get(name)
            if node is None:
                node = _RegionNode(name)
                children[name] = node
            children = node.children
        return node

    # -- snapshot ------------------------------------------------------------

    def snapshot(self) -> Dict[str, Any]:
        payload: Dict[str, Any] = {
            "schema": STAGE_TIMING_SCHEMA,
            "seconds": {stage: round(self.seconds[stage], 6) for stage in self.order},
            "elapsed_seconds": round(time.monotonic() - self._started, 6),
        }
        if self._process_age_at_start is not None:
            # Python 起動から計測開始までの時間（インタプリタ起動・import 込み）。
            payload["process_age_at_start_seconds"] = round(self._process_age_at_start, 6)
        if self.notes:
            payload["notes"] = dict(self.notes)
        regions = self.region_snapshot()
        if regions:
            payload["regions"] = regions
            payload["region_totals"] = region_totals(regions)
            split = split_region_by_ancestor(
                regions, OBLIGATION_BUILD_REGION, CHECK_REGION
            )
            if split is not None:
                payload[OBLIGATION_BUILD_REGION] = split
        return payload

    def region_snapshot(self) -> Dict[str, Any]:
        """region 木を JSON にそのまま入る dict にする（名前順で安定）。"""
        try:
            with self._region_lock:
                return {
                    name: _snapshot_node(self._regions[name])
                    for name in sorted(self._regions)
                }
        except Exception:
            return {}


def _snapshot_node(node: _RegionNode) -> Dict[str, Any]:
    children = {name: _snapshot_node(node.children[name]) for name in sorted(node.children)}
    child_inclusive = sum(child["seconds_inclusive"] for child in children.values())
    exclusive = node.seconds_inclusive - child_inclusive
    payload: Dict[str, Any] = {
        "seconds_inclusive": round(node.seconds_inclusive, 6),
        "seconds_exclusive": round(max(0.0, exclusive), 6),
        "calls": node.calls,
        "reentrant_calls": node.reentrant_calls,
    }
    if exclusive < -REGION_IDENTITY_ABSOLUTE_TOLERANCE:
        # 親が閉じる前に snapshot を取った場合など。0 に丸めた事実を残す
        # （恒等式の検証がこの丸めを見落とさないようにする）。
        payload["exclusive_clamped_from"] = round(exclusive, 6)
    if children:
        payload["children"] = children
    return payload


def region_totals(regions: Mapping[str, Any]) -> Dict[str, Dict[str, Any]]:
    """同名 region を木全体で合算する（同名の入れ子は起きないので重複しない）。

    `check` のように複数の親の下に現れうる region の「実際の呼び出し回数 /
    合計秒」を 1 箇所で読むための派生値。恒等式の項としては使わない。
    """
    totals: Dict[str, Dict[str, Any]] = {}

    def walk(nodes: Mapping[str, Any]) -> None:
        for name, node in nodes.items():
            row = totals.setdefault(
                name,
                {
                    "seconds_inclusive": 0.0,
                    "seconds_exclusive": 0.0,
                    "calls": 0,
                    "reentrant_calls": 0,
                    "paths": 0,
                },
            )
            row["seconds_inclusive"] = round(
                row["seconds_inclusive"] + float(node.get("seconds_inclusive", 0.0) or 0.0), 6
            )
            row["seconds_exclusive"] = round(
                row["seconds_exclusive"] + float(node.get("seconds_exclusive", 0.0) or 0.0), 6
            )
            row["calls"] += int(node.get("calls", 0) or 0)
            row["reentrant_calls"] += int(node.get("reentrant_calls", 0) or 0)
            row["paths"] += 1
            walk(node.get("children") or {})

    walk(regions)
    return {name: totals[name] for name in sorted(totals)}


def split_region_by_ancestor(
    regions: Mapping[str, Any], region_name: str, ancestor_name: str
) -> Optional[Dict[str, Any]]:
    """`region_name` を「`ancestor_name` の内側 / 外側」に分けて合算する。

    `obligation_build` は check の内側（strategy runtime の準備）でも外側
    （stage runner の branch schedule）でも起きるので、単一の値に潰さずに
    分けて出す。``total_*`` は report 用の合計であって恒等式の項ではない
    （恒等式は各親の直接子だけで閉じる）。

    key は `ancestor_name` から作る（`check` なら `inside_check` /
    `outside_check`）。基準にした region 名と出力の名前をずらさないため。
    """
    inside_key = f"inside_{ancestor_name}"
    outside_key = f"outside_{ancestor_name}"
    inside_seconds = outside_seconds = 0.0
    inside_calls = outside_calls = 0
    found = False

    def walk(nodes: Mapping[str, Any], under_ancestor: bool) -> None:
        nonlocal inside_seconds, outside_seconds, inside_calls, outside_calls, found
        for name, node in nodes.items():
            if name == region_name:
                found = True
                seconds = float(node.get("seconds_inclusive", 0.0) or 0.0)
                calls = int(node.get("calls", 0) or 0)
                if under_ancestor:
                    inside_seconds += seconds
                    inside_calls += calls
                else:
                    outside_seconds += seconds
                    outside_calls += calls
            walk(node.get("children") or {}, under_ancestor or name == ancestor_name)

    walk(regions, False)
    if not found:
        return None
    return {
        inside_key: {"seconds": round(inside_seconds, 6), "calls": inside_calls},
        outside_key: {"seconds": round(outside_seconds, 6), "calls": outside_calls},
        "total_seconds": round(inside_seconds + outside_seconds, 6),
        "total_calls": inside_calls + outside_calls,
        "total_is_report_metric_not_identity_term": True,
    }


# -- 恒等式 ------------------------------------------------------------------


def identity_tolerance(*values: float) -> float:
    """恒等式の許容誤差（絶対 0.05 s と相対 1 % の大きい方）。"""
    magnitude = max((abs(float(value)) for value in values), default=0.0)
    return max(
        REGION_IDENTITY_ABSOLUTE_TOLERANCE,
        REGION_IDENTITY_RELATIVE_TOLERANCE * magnitude,
    )


def _identity_row(identity: str, region: str, left: float, right: float) -> Dict[str, Any]:
    tolerance = identity_tolerance(left, right)
    residual = float(left) - float(right)
    return {
        "identity": identity,
        "region": region,
        "left": round(float(left), 6),
        "right": round(float(right), 6),
        "residual": round(residual, 6),
        "tolerance": round(tolerance, 6),
        "within_tolerance": abs(residual) <= tolerance,
    }


def _find_nodes(regions: Mapping[str, Any], name: str) -> List[Tuple[str, Mapping[str, Any]]]:
    found: List[Tuple[str, Mapping[str, Any]]] = []

    def walk(nodes: Mapping[str, Any], prefix: str) -> None:
        for key, node in nodes.items():
            path = f"{prefix}.{key}" if prefix else key
            if key == name:
                found.append((path, node))
            walk(node.get("children") or {}, path)

    walk(regions, "")
    return found


def _closure_row(identity: str, path: str, node: Mapping[str, Any]) -> Dict[str, Any]:
    children = node.get("children") or {}
    child_inclusive = sum(
        float(child.get("seconds_inclusive", 0.0) or 0.0) for child in children.values()
    )
    row = _identity_row(
        identity,
        path,
        float(node.get("seconds_inclusive", 0.0) or 0.0),
        child_inclusive + float(node.get("seconds_exclusive", 0.0) or 0.0),
    )
    row["children"] = sorted(children)
    return row


def region_identity_rows(
    stages: Optional[Mapping[str, Any]],
    phases: Iterable[Mapping[str, Any]] = (),
) -> List[Dict[str, Any]]:
    """恒等式 A / B / C を実測値で評価した行を返す（診断・検証専用）。

    A: ``Σ phases[].seconds.stage_plan`` = ``branch_plan_orchestration`` の inclusive
       （`phases` を渡したときだけ評価する）
    B: ``branch_plan_orchestration`` の inclusive = 直接子の inclusive 合計 + exclusive
    C: 各 ``check`` の inclusive = 直接子の inclusive 合計 + exclusive

    B / C は「各親の直接子だけで閉じる」形なので、子孫の `obligation_build` を
    親側から二重に引くことはない。
    """
    regions = dict((stages or {}).get("regions") or {})
    rows: List[Dict[str, Any]] = []
    if not regions:
        return rows
    orchestration = _find_nodes(regions, ORCHESTRATION_REGION)
    phase_rows = list(phases or ())
    # A は phase 行が与えられたときだけ評価する（phase 行が無いのは「stage plan を
    # 記録していない呼び出し」であって、恒等式が破れているという観測ではない）。
    if orchestration and phase_rows:
        stage_plan_seconds = 0.0
        for phase in phase_rows:
            try:
                stage_plan_seconds += float(
                    ((phase or {}).get("seconds") or {}).get("stage_plan", 0.0) or 0.0
                )
            except (TypeError, ValueError):
                continue
        orchestration_total = sum(
            float(node.get("seconds_inclusive", 0.0) or 0.0) for _path, node in orchestration
        )
        rows.append(
            _identity_row("A", ORCHESTRATION_REGION, stage_plan_seconds, orchestration_total)
        )
    for path, node in orchestration:
        rows.append(_closure_row("B", path, node))
    for path, node in _find_nodes(regions, CHECK_REGION):
        rows.append(_closure_row("C", path, node))
    return rows


# -- module level API --------------------------------------------------------


def active_region_path() -> Tuple[str, ...]:
    """いま開いている region の path（読み取りのみ。worker thread では空）。"""
    return _ACTIVE_REGION_PATH.get()


def stage_region(name: str):
    """有効な clock があれば region を開く。無ければ no-op。

    ``with stage_region("check"):`` としても、``open_stage_region()`` と同じ
    ハンドルとして ``close()`` してもよい。
    """
    clock = _ACTIVE_CLOCK.get()
    if clock is None:
        return _NO_REGION
    return _OpenRegion(clock, name)


def open_stage_region(name: str):
    """`stage_region()` を開始済みの状態で返す（`try/finally` で閉じる用）。"""
    return stage_region(name).start()

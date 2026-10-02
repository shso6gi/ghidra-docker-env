# -*- coding: utf-8 -*-
"""解析の期限と process の期限の間の余裕（margin）の実測と、採用式（Issue #106 PR-106-B）。

runner の `ANALYSIS_TIMEOUT_MARGIN`（`runner_timeout_policy`）は、期限で打ち切った pair が
process の期限より前（supervisor が stack dump の SIGUSR1 を送る lead window の手前）に
終わるための余裕。その根拠を run の出力から測る。判定にも runner の policy にも入力を渡さない
（報告だけを作る）。

## 時計と端点（すべて supervisor と child が共有する monotonic 時計）

supervisor は barrier を外した瞬間に ``deadline = monotonic + PAIR_PROCESS_TIMEOUT`` を 1 回だけ
決め、診断の sidecar（`<pair>.stack-dump.status.json`）に ``deadline_monotonic`` /
``timeout_seconds`` / ``lead_seconds`` と、child の終了を観測した時刻
（``cancel_linearized_offset_seconds``、deadline からの相対）を残す。Eq / Neq の両方の runner が
書く。GNU time の wall（supervisor の起動と、child の終了後の durable write を含む）は使わない:
process の期限に数えられるのは barrier から child の終了までだけ。

期限で打ち切った pair 1 件を、重ならない連続した区間に分ける:

=================== ==================================================================
区間                端点
=================== ==================================================================
``pre``             process の期限の起点 → 解析の期限の起点（trip 時刻 − trip の経過秒）。CLI の
                    起動・JVM・project open・import・auto analyze
``overrun``         解析の期限 → trip（``elapsed_seconds − budget_seconds``）。checkpoint の
                    無い区間・止まるまで戻らない処理（協調的な solver の停止と join を含む）。
                    負の値は「残りが sub-operation の余裕を切ったので始めなかった」
``post_trip``       trip → journal の最後の event。限界の帰属・組み立て・出力の準備・
                    ``connector.finish``・conditional lane・``close_programs``・結果 JSON
``tail``            journal の最後の event → supervisor が child の終了を観測。JVM の停止・
                    interpreter の終了
=================== ==================================================================

``needed = child の終了 − process の期限の起点 − 解析の期限 = pre + overrun + post_trip + tail``。

``post_trip_parts`` は journal の stage の区間（`core.stage_journal_reader.stage_intervals`）と
trip 後の窓の **交差** を、窓の各瞬間をその時点で最も内側に開いていた stage へ 1 回だけ
割り当てて求める。どの stage にも入らない時間は ``other``。各値は 0 以上で、和は
``post_trip`` に一致する（処理の順序・入れ子・trip より前に始まった stage に依らない）。

## 終了の分類（独自の規則を持たない）

TIMEOUT の pair は `timeout_hotspot_summary`（`timeout_kind` の owner）が同じ証拠から分類する:
``PROCESS_DEADLINE_KINDS``（supervisor の wall clock）は ``process_timeouts``、
``child_solver_timeout``（checker 自身の terminal timeout）は ``solver_timeouts``、
証拠の足りないものは ``timeouts_unclassified``。child の終了より先に SIGUSR1 の送信が
始まった pair は ``entered_lead_window``（margin が足りなかった証拠）。

## 採用式（profile ごと）

``required_margin = max_{P∪L∪F}(pre) + max_{P∪L}(overrun) + max_P(post_trip) + max_P(tail) + max(lead)``

* ``P``（profile の run）: その runner profile の設定（並列度・process の期限・解析の期限）で、
  解析の期限がその profile の値 **以下** の run の、期限で打ち切った全 pair。``post_trip`` と
  ``tail`` は打ち切るまでに解析が作った状態の大きさ（期限の長さ）で伸びるので、profile の
  期限より長い期限の run では測らない。
* ``L``（負荷の pool、``--load-root``）: 期限の機構（`core/deadline.py`・solver の停止・
  checkpoint の配置）が対象の code と同じ code で、この host で観測した期限つきの run すべて
  （profile も負荷も問わない）。``overrun`` は期限の長さではなく、負荷と checkpoint の無い区間の
  長さで決まる。共有 host では runner が負荷を制限しないので、観測した高負荷の値を除かない。
* ``F``（固定費の pool、``--pre-root``）: ``pre`` だけに効く追加の run。``pre``（CLI の起動・JVM・
  import・auto analyze）は期限の code に依らず負荷で決まるので、期限の機構が違う code の run
  でも、この host で観測した値は除かない。
* したがって ``pre`` は ``P∪L∪F``、``overrun`` は ``P∪L`` の最大。
* 最大は区間ごとに別の pair でよい（和は 1 pair の実際の合計より保守的）。どの run を
  ``P`` / ``L`` に入れるかは呼び出し側が先に決め、後から run を除かない。
* ``lead`` は supervisor が SIGUSR1 を送る先行時間。child がその窓の中で終わると #204 の経路に
  入るので、margin の中に取る。SIGTERM の後の grace（kill-after）は process の期限の **後** なので
  margin には使えない（入れない）。
* 止められない worker（能力を宣言しない backend）の join には上限が無い: その pair は
  supervisor の TIMEOUT（fallback）になる。margin には入れない。
* 観測した最大は保証ではない（負荷・入力が変われば越え得る）。
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core.stage_journal_reader import (
    SUMMARY_READ_LIMIT_BYTES,
    JournalSegment,
    read_stage_journal,
    select_current_segment,
    stage_intervals,
)
from scripts.function_tracer_pcode.reporting.pair_outcomes import iter_pair_outcomes
from scripts.function_tracer_pcode.reporting.timeout_hotspot_summary import (
    KIND_CHILD_SOLVER_TIMEOUT,
    PROCESS_DEADLINE_KINDS,
    TIMEOUT_OUTCOME,
    load_pair_evidence,
)

SCHEMA = "deadline-margin-summary-v2"
TRIP_NOTE = "deadline_tripped"
#: margin の和に入る区間（``needed`` は確認用の合計）
MARGIN_INTERVALS = ("pre", "overrun", "post_trip", "tail")
INTERVALS = MARGIN_INTERVALS + ("needed",)
POST_TRIP_STAGES = ("authority_finalize", "conditional_lane", "close_programs", "result_emit")
POST_TRIP_PARTS = POST_TRIP_STAGES + ("other",)
#: p99 を名乗る最小の件数（それ未満は max と median / p90 だけ）
P99_MIN_SAMPLES = 100


@dataclass(frozen=True)
class PairMargin:
    key: str
    outcome: str
    budget_seconds: float
    trip_stage: str
    lead_seconds: float
    pre: float
    overrun: float
    post_trip: float
    tail: float
    needed: float
    post_trip_parts: Dict[str, float] = field(default_factory=dict)


@dataclass
class MarginReport:
    roots: List[str]
    pairs: List[PairMargin]
    #: 期限を持たない run（manifest の analysis_timeout が 0）の pair
    without_deadline: int = 0
    #: 期限はあったが trip しなかった（期限内に終わった）pair
    finished_before_deadline: int = 0
    #: supervisor の process deadline が終端を決めた TIMEOUT（`PROCESS_DEADLINE_KINDS`）
    process_timeouts: List[str] = field(default_factory=list)
    #: checker 自身の terminal timeout（`child_solver_timeout`。process の kill ではない）
    solver_timeouts: List[str] = field(default_factory=list)
    #: TIMEOUT だが `timeout_kind` が process とも solver とも確かめられないもの
    timeouts_unclassified: List[str] = field(default_factory=list)
    #: trip したが、child の終了より先に SIGUSR1 の送信が始まった（lead window に入った）pair
    entered_lead_window: List[str] = field(default_factory=list)
    #: 区間を作れなかった pair（journal / sidecar の欠け）と理由
    unreadable: List[Tuple[str, str]] = field(default_factory=list)


def _percentile(values: Sequence[float], q: float) -> float:
    """nearest-rank の百分位。"""

    ordered = sorted(values)
    rank = max(1, math.ceil(q * len(ordered)))
    return ordered[rank - 1]


def describe(values: Sequence[float]) -> Dict[str, Any]:
    if not values:
        return {"n": 0}
    row: Dict[str, Any] = {
        "n": len(values),
        "median": round(_percentile(values, 0.5), 3),
        "p90": round(_percentile(values, 0.9), 3),
        "max": round(max(values), 3),
    }
    if len(values) >= P99_MIN_SAMPLES:
        row["p99"] = round(_percentile(values, 0.99), 3)
    return row


def _read_key_values(path: Path) -> Dict[str, str]:
    fields: Dict[str, str] = {}
    if not path.is_file():
        return fields
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if "=" in line:
            key, value = line.split("=", 1)
            fields[key.strip()] = value.strip()
    return fields


class _Unmeasurable(ValueError):
    """この pair の区間は作れない（理由を報告する）。"""


def _number(mapping: Mapping[str, Any], key: str) -> float:
    value = mapping.get(key)
    if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value):
        raise _Unmeasurable(f"sidecar has no usable {key}")
    return float(value)


def _tripped(segment: JournalSegment) -> List[Any]:
    return [
        row for row in segment.rows
        if row.event == "note" and row.payload.get("note") == TRIP_NOTE
    ]


def post_trip_parts(
    segment: JournalSegment, start: float, end: float,
) -> Dict[str, float]:
    """``[start, end]`` を stage の区間との交差で分ける（各値 >= 0、和 = end − start）。

    窓の各瞬間は、その時点で開いていた区間のうち最後に開いたもの（最も内側）にだけ
    割り当てる。``POST_TRIP_STAGES`` 以外の stage の中の時間は ``other``。
    """

    parts = {name: 0.0 for name in POST_TRIP_PARTS}
    clipped = []
    for interval in stage_intervals(segment):
        lo = max(interval.start, start)
        hi = min(end if interval.end is None else interval.end, end)
        if hi > lo:
            clipped.append((lo, hi, interval))
    cuts = sorted({start, end, *(lo for lo, _, _ in clipped), *(hi for _, hi, _ in clipped)})
    for lo, hi in zip(cuts, cuts[1:]):
        open_now = [interval for a, b, interval in clipped if a <= lo and hi <= b]
        owner = max(open_now, key=lambda interval: interval.start).stage if open_now else None
        parts[owner if owner in POST_TRIP_STAGES else "other"] += hi - lo
    return parts


def pair_margin(
    key: str, outcome: str, segment: JournalSegment, sidecar: Mapping[str, Any],
) -> Optional[PairMargin]:
    """期限で打ち切った 1 pair の区間（trip の無い pair は ``None``）。測れなければ `_Unmeasurable`。"""

    trips = _tripped(segment)
    if not trips:
        return None
    trip = trips[0]
    try:
        budget = float(trip.payload["budget_seconds"])
        elapsed = float(trip.payload["elapsed_seconds"])
        trip_at = float(trip.t_monotonic)
    except (KeyError, TypeError, ValueError) as exc:
        raise _Unmeasurable(f"deadline_tripped note is incomplete: {exc}") from exc
    deadline = _number(sidecar, "deadline_monotonic")
    process = _number(sidecar, "timeout_seconds")
    lead = _number(sidecar, "lead_seconds")
    if sidecar.get("cancel_linearized_offset_seconds") is None:
        raise _Unmeasurable("the child exit was not observed before the stack-dump send")
    child_exit = deadline + _number(sidecar, "cancel_linearized_offset_seconds")
    last = max(float(row.t_monotonic) for row in segment.rows if row.t_monotonic is not None)
    origin = deadline - process
    analysis_origin = trip_at - elapsed
    parts = post_trip_parts(segment, trip_at, last)
    return PairMargin(
        key=key, outcome=outcome, budget_seconds=budget,
        trip_stage=str(trip.payload.get("stage")), lead_seconds=lead,
        pre=round(analysis_origin - origin, 3),
        overrun=round(elapsed - budget, 3),
        post_trip=round(last - trip_at, 3),
        tail=round(child_exit - last, 3),
        needed=round(child_exit - origin - budget, 3),
        post_trip_parts={name: round(value, 3) for name, value in parts.items()},
    )


def summarize_roots(roots: Iterable[Path]) -> MarginReport:
    root_list = [Path(root) for root in roots]
    report = MarginReport(roots=[str(root) for root in root_list], pairs=[])
    for root in root_list:
        manifest = _read_key_values(root / "run_manifest.txt")
        without_deadline = manifest.get("analysis_timeout") == "0"
        for record in iter_pair_outcomes(root):
            key = str(Path(record.status_path).relative_to(root))[: -len(".pair-status.json")]
            evidence = load_pair_evidence(record.status_path)
            if record.outcome == TIMEOUT_OUTCOME:
                kind = evidence.timeout_kind_report().kind
                if kind in PROCESS_DEADLINE_KINDS:
                    report.process_timeouts.append(key)
                elif kind == KIND_CHILD_SOLVER_TIMEOUT:
                    report.solver_timeouts.append(key)
                else:
                    report.timeouts_unclassified.append(key)
            if without_deadline:
                report.without_deadline += 1
                continue
            sidecar = evidence.sidecar
            segment, reason = select_current_segment(
                read_stage_journal(evidence.paths.journal, max_bytes=SUMMARY_READ_LIMIT_BYTES),
                pid=(sidecar or {}).get("child_pid"),
                start_token=(sidecar or {}).get("child_start_token"),
            )
            if segment is None:
                # a pair with no journal was not measured; a TIMEOUT is already listed above
                if record.outcome != TIMEOUT_OUTCOME:
                    report.unreadable.append((key, f"journal: {reason}"))
                continue
            if not _tripped(segment):
                report.finished_before_deadline += 1
                continue
            if (isinstance(sidecar, Mapping) and sidecar.get("signal_sent") is True
                    and sidecar.get("cancel_linearized_offset_seconds") is None):
                report.entered_lead_window.append(key)
                continue
            try:
                if not isinstance(sidecar, Mapping):
                    raise _Unmeasurable("no stack-dump status sidecar")
                margin = pair_margin(key, record.outcome, segment, sidecar)
            except _Unmeasurable as exc:
                report.unreadable.append((key, str(exc)))
                continue
            if margin is not None:
                report.pairs.append(margin)
    return report


def required_margin(
    intervals: Mapping[str, Mapping[str, Any]], lead: Optional[float],
) -> Optional[float]:
    """採用式（module docstring）。どれかの区間に標本が無ければ ``None``（式を作れない）。"""

    if lead is None or any(intervals[name].get("n", 0) == 0 for name in MARGIN_INTERVALS):
        return None
    return round(sum(intervals[name]["max"] for name in MARGIN_INTERVALS) + lead, 3)




def report_dict(
    report: MarginReport, *, margin_seconds: Optional[float] = None,
    load_report: Optional[MarginReport] = None,
    pre_report: Optional[MarginReport] = None,
) -> Dict[str, Any]:
    """``report`` は profile の run（`P`）、``load_report`` は負荷の pool（`L`）、``pre_report`` は
    固定費の pool（`F`）。後の 2 つは任意。"""

    intervals = {
        name: describe([getattr(pair, name) for pair in report.pairs]) for name in INTERVALS
    }
    load_pairs = list(report.pairs) + list(load_report.pairs if load_report else ())
    pre_pairs = load_pairs + list(pre_report.pairs if pre_report else ())
    load_intervals = {
        "pre": describe([pair.pre for pair in pre_pairs]),
        "overrun": describe([pair.overrun for pair in load_pairs]),
    }
    parts = {
        name: describe([pair.post_trip_parts.get(name, 0.0) for pair in report.pairs])
        for name in POST_TRIP_PARTS
    }
    lead = max((pair.lead_seconds for pair in report.pairs), default=None)
    required = required_margin({**intervals, **load_intervals}, lead)
    payload: Dict[str, Any] = {
        "schema": SCHEMA,
        "roots": report.roots,
        "tripped_pairs": len(report.pairs),
        "finished_before_deadline": report.finished_before_deadline,
        "without_deadline": report.without_deadline,
        "process_timeouts": report.process_timeouts,
        "solver_timeouts": report.solver_timeouts,
        "timeouts_unclassified": report.timeouts_unclassified,
        "entered_lead_window": report.entered_lead_window,
        "unreadable": [list(row) for row in report.unreadable],
        "lead_seconds": lead,
        "intervals": intervals,
        "load_roots": [] if load_report is None else load_report.roots,
        "pre_roots": [] if pre_report is None else pre_report.roots,
        "load_intervals": load_intervals,
        "post_trip_parts": parts,
        "required_margin_seconds": required,
        "pairs": [asdict(pair) for pair in report.pairs],
    }
    if margin_seconds is not None:
        over = [pair.key for pair in report.pairs if pair.needed + pair.lead_seconds > margin_seconds]
        payload["margin_seconds"] = margin_seconds
        payload["pairs_over_margin"] = over
        # The margin holds only if the formula fits and nothing ran into the lead
        # window or the process deadline.  An unmeasurable pair or a missing
        # interval is not a pass.
        payload["margin_holds"] = bool(
            required is not None and required <= margin_seconds and not over
            and not report.entered_lead_window and not report.process_timeouts
            and not report.unreadable
        )
    return payload


def format_report(payload: Mapping[str, Any]) -> str:
    lines = [
        "Deadline margin summary:",
        f"  tripped pairs: {payload['tripped_pairs']}"
        f" (finished before the deadline: {payload['finished_before_deadline']},"
        f" no deadline: {payload['without_deadline']},"
        f" unreadable: {len(payload['unreadable'])})",
        f"  TIMEOUT: process {len(payload['process_timeouts'])},"
        f" solver {len(payload['solver_timeouts'])},"
        f" unclassified {len(payload['timeouts_unclassified'])};"
        f" entered the lead window: {len(payload['entered_lead_window'])}",
        f"  stack dump lead: {payload['lead_seconds']}",
    ]
    for title, table in (("intervals (profile runs)", payload["intervals"]),
                         ("load intervals (pre: P+L+F, overrun: P+L)", payload["load_intervals"]),
                         ("post_trip parts", payload["post_trip_parts"])):
        lines.append(f"  {title}:")
        for name, row in table.items():
            stats = " ".join(f"{key}={value}" for key, value in row.items())
            lines.append(f"    - {name}: {stats}")
    lines.append(
        "  required margin (max pre + max overrun over the load pool, max post_trip + max tail"
        f" over the profile runs, + lead): {payload['required_margin_seconds']}"
    )
    if "margin_seconds" in payload:
        lines.append(
            f"  margin {payload['margin_seconds']}: holds={payload['margin_holds']}"
            f" (pairs over it: {len(payload['pairs_over_margin'])})"
        )
    for name in ("process_timeouts", "entered_lead_window"):
        for key in payload[name]:
            lines.append(f"  {name}: {key}")
    for key, reason in payload["unreadable"]:
        lines.append(f"  unreadable: {key}: {reason}")
    return "\n".join(lines)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("roots", nargs="+", type=Path,
                        help="the profile's run result trees (one per half)")
    parser.add_argument("--load-root", action="append", type=Path, default=[],
                        help="a run of the load pool (pre / overrun only; repeatable)")
    parser.add_argument("--pre-root", action="append", type=Path, default=[],
                        help="a run of the fixed-cost pool (pre only; repeatable)")
    parser.add_argument("--margin", type=float, default=None,
                        help="check this ANALYSIS_TIMEOUT_MARGIN against the measurement")
    parser.add_argument("--json", type=Path, default=None)
    args = parser.parse_args(argv)
    load = summarize_roots(args.load_root) if args.load_root else None
    pre = summarize_roots(args.pre_root) if args.pre_root else None
    payload = report_dict(
        summarize_roots(args.roots), margin_seconds=args.margin, load_report=load, pre_report=pre,
    )
    print(format_report(payload))
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(payload, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())

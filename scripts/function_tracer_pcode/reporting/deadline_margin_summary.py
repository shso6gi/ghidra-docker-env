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
``PROCESS_DEADLINE_KINDS``（supervisor の wall clock）は ``process_timeout``、
``child_solver_timeout``（checker 自身の terminal timeout）は ``solver_timeout``、
証拠の足りないものは ``timeout_unclassified``。canonical outcome の無い pair は
``termination_invalid``。child の終了より先に SIGUSR1 の送信が始まった pair は
``entered_lead_window``（margin が足りなかった証拠）。

## 観測と判定の分担

この module は **観測** だけを作る: run ごとの事実（`RunFacts`: 期限・process の期限・並列度・
commit・sample の母集団）と、pair ごとの終了の分類・期限で打ち切ったか（読めなければ理由）・
区間ごとの値か欠測の理由（`PairObservation`）。区間は 1 つずつ別に求め、ある区間が測れない
ことは他の区間を消さない。どの run をどの pool に入れてよいか・採用式・判定（holds /
violated / undetermined）は `reporting/deadline_margin_acceptance.py` だけが決める（集計の
前に決まる規則で、結果を見て標本を除かない）。

* **値が「ある・変換できる」ことと、証拠が「完全・妥当・整合」であることは別。** journal は
  完全に読めたとき（`JournalRead.incomplete_reasons` が空）だけ「trip が無い = 期限内に終わった」
  と読む。数値は有限で値域に入るときだけ値にする（trip の note は全体として、sidecar は項目ごと、
  ``pre`` / ``tail`` は負にならない）。同じ事実の出所（manifest の期限と各 trip の budget、process の
  期限・lead と各 sidecar）は照合し、食い違えば ``RunFacts.conflicts`` に両方を残す（片方で上書き
  しない）。終了は authority の 5 値の `Outcome` だけ（他の綴りは ``termination_invalid``）。
* 観測した最大は保証ではない（負荷・入力が変われば越え得る）。
* ``lead`` は supervisor が SIGUSR1 を送る先行時間。child がその窓の中で終わると #204 の経路に
  入るので、margin の中に取る。SIGTERM の後の grace（kill-after）は process の期限の **後** なので
  margin には使えない（入れない）。
* 止められない worker（能力を宣言しない backend）の join には上限が無い: その pair は
  supervisor の TIMEOUT（fallback）になる。margin には入れない。
"""


from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.authority.contracts import Outcome
from scripts.function_tracer_pcode.core.deadline import parse_budget_seconds
from scripts.function_tracer_pcode.core.stage_journal_reader import (
    SUMMARY_READ_LIMIT_BYTES,
    JournalRow,
    JournalSegment,
    end_attestation_problem,
    read_stage_journal,
    select_verified_segment,
    stage_intervals,
)
from scripts.function_tracer_pcode.reporting import deadline_margin_acceptance as acceptance
from scripts.function_tracer_pcode.reporting.pair_outcomes import (
    PAIR_STATUS_SUFFIX,
    iter_pair_outcomes,
)
from scripts.function_tracer_pcode.reporting.timeout_hotspot_summary import (
    KIND_CHILD_SOLVER_TIMEOUT,
    PROCESS_DEADLINE_KINDS,
    TIMEOUT_OUTCOME,
    load_pair_evidence,
)

SCHEMA = "deadline-margin-summary-v3"
TRIP_NOTE = "deadline_tripped"
#: margin の和に入る区間（``needed`` は確認用の合計）。採用式の項の表（acceptance）が唯一の一覧
MARGIN_INTERVALS = tuple(acceptance.TERM_POOLS)
INTERVALS = MARGIN_INTERVALS + ("needed",)
POST_TRIP_STAGES = ("authority_finalize", "conditional_lane", "close_programs", "result_emit")
POST_TRIP_PARTS = POST_TRIP_STAGES + ("other",)
#: p99 を名乗る最小の件数（それ未満は max と median / p90 だけ）
P99_MIN_SAMPLES = 100


def _require_finite(owner: str, name: str, value: Optional[float], *, positive: bool = False,
                    nonnegative: bool = False) -> None:
    """record の不変条件: 数値は有限（と値域）。破れていれば観測側の bug なので例外にする。"""

    if value is None:
        return
    if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value):
        raise ValueError(f"{owner}.{name} must be a finite number: {value!r}")
    if positive and value <= 0:
        raise ValueError(f"{owner}.{name} must be positive: {value!r}")
    if nonnegative and value < 0:
        raise ValueError(f"{owner}.{name} must not be negative: {value!r}")


@dataclass(frozen=True)
class RunFacts:
    """1 run（result tree の 1 half）の事実。

    同じ事実を複数の出所が記録する（解析の期限: manifest と各 trip の budget、process の期限:
    manifest と各 sidecar、stack dump の lead: manifest と各 sidecar）。出所どうしが一致する
    ときだけ値を持ち、食い違えば値は ``None`` で ``conflicts`` に両方の値を残す（片方で
    上書きしない）。
    """

    root: str
    #: 解析の期限（秒）。``deadline_off`` なら ``None``
    deadline_seconds: Optional[float]
    deadline_off: bool
    #: 期限の値の出所（または値が無い理由）
    deadline_source: str
    pair_process_timeout_seconds: Optional[float]
    stack_dump_lead_seconds: Optional[float]
    parallel_jobs: Optional[int]
    git_commit: Optional[str]
    git_dirty: Optional[bool]
    samples: frozenset
    #: 出所どうしの食い違い・読めない記録（あれば、この run の事実は確定していない）
    conflicts: Tuple[str, ...] = ()

    def __post_init__(self) -> None:
        _require_finite("RunFacts", "deadline_seconds", self.deadline_seconds, positive=True)
        _require_finite("RunFacts", "pair_process_timeout_seconds",
                        self.pair_process_timeout_seconds, positive=True)
        _require_finite("RunFacts", "stack_dump_lead_seconds", self.stack_dump_lead_seconds,
                        nonnegative=True)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "root": self.root, "deadline_seconds": self.deadline_seconds,
            "deadline_off": self.deadline_off, "deadline_source": self.deadline_source,
            "pair_process_timeout_seconds": self.pair_process_timeout_seconds,
            "stack_dump_lead_seconds": self.stack_dump_lead_seconds,
            "parallel_jobs": self.parallel_jobs, "git_commit": self.git_commit,
            "git_dirty": self.git_dirty, "samples": len(self.samples),
            "conflicts": list(self.conflicts),
        }


@dataclass(frozen=True)
class PairObservation:
    key: str
    outcome: str
    #: `deadline_margin_acceptance.TERMINATION_*`
    termination: str
    timeout_kind: Optional[str]
    #: 期限で打ち切った（``True``）/ 打ち切らずに終わった（``False``）/ 読めない（``None``）。
    #: ``False`` は「完全に読めた journal に trip が無い」ときだけ
    cut: Optional[bool]
    cut_unknown_reason: Optional[str] = None
    #: 測れた区間（``MARGIN_INTERVALS`` の部分集合）と測れなかった区間の理由（打ち切った pair だけ）
    values: Dict[str, float] = field(default_factory=dict)
    missing: Dict[str, str] = field(default_factory=dict)
    lead_seconds: Optional[float] = None
    needed: Optional[float] = None
    entered_lead_window: bool = False
    #: 妥当な trip の note が記録した解析の期限（run の事実の照合に使う）
    budget_seconds: Optional[float] = None
    #: 結果 JSON の ``analysis_deadline`` が記録した解析の期限（run の事実の照合に使う）
    result_budget_seconds: Optional[float] = None
    #: sidecar が記録した process の期限（run の事実の照合に使う）
    process_timeout_seconds: Optional[float] = None
    trip_stage: Optional[str] = None
    post_trip_parts: Dict[str, float] = field(default_factory=dict)

    def __post_init__(self) -> None:
        if self.cut is None and not self.cut_unknown_reason:
            raise ValueError("PairObservation: an unknown cut needs its reason")
        for name, value in self.values.items():
            _require_finite("PairObservation", name, value)
        for name, value in self.post_trip_parts.items():
            _require_finite("PairObservation", f"post_trip_parts[{name}]", value)
        _require_finite("PairObservation", "needed", self.needed)
        _require_finite("PairObservation", "lead_seconds", self.lead_seconds, nonnegative=True)
        _require_finite("PairObservation", "budget_seconds", self.budget_seconds, positive=True)
        _require_finite("PairObservation", "result_budget_seconds", self.result_budget_seconds,
                        positive=True)
        _require_finite("PairObservation", "process_timeout_seconds",
                        self.process_timeout_seconds, positive=True)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "key": self.key, "outcome": self.outcome, "termination": self.termination,
            "timeout_kind": self.timeout_kind, "cut": self.cut,
            "cut_unknown_reason": self.cut_unknown_reason, "values": dict(self.values),
            "missing": dict(self.missing), "lead_seconds": self.lead_seconds,
            "needed": self.needed, "entered_lead_window": self.entered_lead_window,
            "budget_seconds": self.budget_seconds,
            "result_budget_seconds": self.result_budget_seconds,
            "process_timeout_seconds": self.process_timeout_seconds,
            "trip_stage": self.trip_stage, "post_trip_parts": dict(self.post_trip_parts),
        }


@dataclass(frozen=True)
class RunObservation:
    facts: RunFacts
    pairs: Tuple[PairObservation, ...]


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


# ---------------------------------------------------------------------------
# 証拠の検証（値が「ある・変換できる」ことと「完全・妥当・整合」は別）
# ---------------------------------------------------------------------------

def _measured(value: Any, name: str, *, positive: bool = False,
              nonnegative: bool = False) -> Tuple[Optional[float], str]:
    """記録された数値を、有限な double で値域に入るときだけ値にする（入らなければ理由）。

    外部の記録の不正（欠け・型・``NaN`` / ``Infinity``・double を越える整数・値域）は理由付きの
    欠測にする（例外にしない）。record の不変条件（`_require_finite`）は内部の bug の検出に残す。
    """

    if value is None:
        return None, f"{name} is missing"
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None, f"{name} is not a number"
    try:
        number = float(value)
    except OverflowError:
        return None, f"{name} is outside the range of a double"
    if not math.isfinite(number):
        return None, f"{name} is not a finite number"
    if positive and number <= 0:
        return None, f"{name} is not positive"
    if nonnegative and number < 0:
        return None, f"{name} is negative"
    return number, ""


def _derived(value: Optional[float], name: str) -> Tuple[Optional[float], str]:
    """有限な記録どうしの派生値（和・差）を、有限なときだけ値にする。

    個々に有限な記録でも組み合わせると double を越え得る（``1e308 + 1e308``）。それは記録の
    組み合わせが値域に入らない証拠の不正で、理由付きの欠測にする。
    """

    if value is None or math.isfinite(value):
        return value, ""
    return None, f"{name} is not a finite number (the recorded values it is derived from are out of range)"


def _manifest_seconds(text: Optional[str], name: str, *, allow_zero: bool = False,
                      ) -> Tuple[Optional[float], str]:
    """manifest の秒（``480`` / ``480s``）。規則は CLI と共有の `core.deadline.parse_budget_seconds`。"""

    if text is None or text == "":
        return None, ""
    number = text[:-1] if text.endswith("s") else text
    if allow_zero and number in ("0", "0.0"):
        return 0.0, ""
    try:
        return parse_budget_seconds(number), ""
    except ValueError:
        return None, f"run_manifest {name}={text!r} is not a valid number of seconds"


def _manifest_count(text: Optional[str]) -> Optional[int]:
    """manifest の件数（10 進の数字だけ）。読めなければ ``None``（例外にしない）。"""

    if not text or not text.isascii() or not text.isdigit():
        return None
    try:
        return int(text)
    except ValueError:                                     # 桁数の上限を越える
        return None


def _sidecar_number(sidecar: Optional[Mapping[str, Any]], key: str, *, positive: bool = False,
                    nonnegative: bool = False) -> Tuple[Optional[float], str]:
    if not isinstance(sidecar, Mapping):
        return None, "no stack-dump status sidecar"
    return _measured(sidecar.get(key), f"sidecar {key}", positive=positive,
                     nonnegative=nonnegative)


@dataclass(frozen=True)
class _Trip:
    at: float
    budget: float
    elapsed: float
    stage: str


def _trip_note(row: JournalRow) -> Tuple[Optional[_Trip], str]:
    """trip の note を、全体として妥当なときだけ読む（1 つでも欠ければ note 全体を使わない）。

    負の overrun（期限の前に始めるのを断った）の範囲は期限の機構の規則なので、ここでは
    決めない（機構が評価対象と同じ pool だけに `deadline_margin_acceptance` が当てる）。
    """

    if row.t_monotonic is None:
        return None, "deadline_tripped has no finite t_monotonic"
    budget, problem = _measured(row.payload.get("budget_seconds"),
                                "deadline_tripped budget_seconds", positive=True)
    if problem:
        return None, problem
    elapsed, problem = _measured(row.payload.get("elapsed_seconds"),
                                 "deadline_tripped elapsed_seconds", nonnegative=True)
    if problem:
        return None, problem
    stage = row.payload.get("stage")
    if not isinstance(stage, str) or not stage:
        return None, "deadline_tripped stage is missing"
    return _Trip(at=row.t_monotonic, budget=budget, elapsed=elapsed, stage=stage), ""


def _tripped(segment: JournalSegment) -> List[JournalRow]:
    return [
        row for row in segment.rows
        if row.event == "note" and row.payload.get("note") == TRIP_NOTE
    ]


# ---------------------------------------------------------------------------
# 期限で打ち切ったかの 2 つの出所（journal と結果 JSON）
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class JournalView:
    """margin が journal から使ってよいもの: 損失の無い current segment と、終わりの証明。

    ``segment`` が ``None`` なら ``problem`` がその理由（読めない・曖昧・損失がある・trip の行が
    契約に反する）。``end_problem`` が ``None`` なのは ``journal_end`` で終わりまで証明された
    segment だけ（それ以外では「trip の行が無い」から trip が無かったとは言えない）。
    """

    segment: Optional[JournalSegment]
    problem: str = ""
    trips: Tuple[JournalRow, ...] = ()
    end_problem: Optional[str] = "no journal"

    @classmethod
    def read(cls, path: Any, sidecar: Optional[Mapping[str, Any]]) -> "JournalView":
        read = read_stage_journal(path, max_bytes=SUMMARY_READ_LIMIT_BYTES)
        segment, reason = select_verified_segment(
            read,
            pid=(sidecar or {}).get("child_pid"),
            start_token=(sidecar or {}).get("child_start_token"),
        )
        if segment is None:
            text = reason if (reason or "").startswith("journal incomplete") else f"journal: {reason}"
            return cls(segment=None, problem=text)
        trips = tuple(_tripped(segment))
        if len(trips) > 1:
            return cls(segment=None, problem=(
                f"journal records {TRIP_NOTE} {len(trips)} times (the deadline writes it once)"))
        return cls(segment=segment, trips=trips, end_problem=end_attestation_problem(segment))


@dataclass(frozen=True)
class DeadlineRecord:
    """結果 JSON の ``diagnostics.analysis_deadline``（`core.deadline.Deadline.diagnostic`）。

    checker が解析の期限の scope の終わりに書く、期限の持ち主自身の最終記録。scope の外では
    期限は trip しないので、``tripped`` は「この解析で trip したか」の完全な記録になる。
    """

    tripped: bool
    budget_seconds: float


def deadline_record(payload: Optional[Mapping[str, Any]]) -> Tuple[Optional[DeadlineRecord], str]:
    """``(記録, "")`` / ``(None, "")``（記録が無い）/ ``(None, 理由)``（記録が契約に合わない）。"""

    if not isinstance(payload, Mapping):
        return None, ""
    diagnostics = payload.get("diagnostics")
    if not isinstance(diagnostics, Mapping) or "analysis_deadline" not in diagnostics:
        return None, ""
    block = diagnostics["analysis_deadline"]
    if not isinstance(block, Mapping):
        return None, "result analysis_deadline is not an object"
    tripped = block.get("tripped")
    if not isinstance(tripped, bool):
        return None, "result analysis_deadline tripped is not a boolean"
    budget, problem = _measured(block.get("budget_seconds"),
                                "result analysis_deadline budget_seconds", positive=True)
    if problem:
        return None, problem
    stage = block.get("trip_stage")
    if tripped != (isinstance(stage, str) and bool(stage)):
        return None, "result analysis_deadline trip_stage does not match tripped"
    return DeadlineRecord(tripped=tripped, budget_seconds=budget), ""


def deadline_cut(
    journal: JournalView, record: Optional[DeadlineRecord], record_problem: str,
) -> Tuple[Optional[bool], str]:
    """期限で打ち切ったか: ``(True / False / None, 読めない理由)``。

    trip が「無かった」と言えるのは、結果 JSON の記録が ``tripped: false`` のときか、``journal_end``
    で終わりまで証明された journal に trip の行が無いときだけ。2 つの出所が両方あれば照合する
    （食い違えば ``None``）。不完全な証拠から trip の不在を結論しない。
    """

    if record_problem:
        return None, record_problem
    journal_trip = None if journal.segment is None else bool(journal.trips)
    attested = journal.segment is not None and journal.end_problem is None
    if record is not None:
        if journal_trip is True and not record.tripped:
            return None, f"the journal records {TRIP_NOTE} but the result's analysis_deadline does not"
        if journal_trip is False and record.tripped and attested:
            return None, f"the result's analysis_deadline records a trip the attested journal does not"
        return record.tripped, ""
    if journal_trip is None:
        return None, f"{journal.problem}; no result records analysis_deadline"
    if journal_trip:
        return True, ""
    if attested:
        return False, ""
    return None, (f"no {TRIP_NOTE} row, but {journal.end_problem}; "
                  "no result records analysis_deadline")


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


#: 解決済みの終了（authority の 5 値の Outcome のうち TIMEOUT 以外）。これ以外の綴りは終了の証拠ではない
_RESOLVED_OUTCOMES = frozenset(item.value for item in Outcome if item is not Outcome.TIMEOUT)


def termination_of(outcome: str, timeout_kind: Optional[str]) -> str:
    """終了の分類。outcome は authority の `Outcome`、TIMEOUT の種類は `timeout_kind` の owner が決める。

    5 値に無い outcome（欠けた・壊れた・未知の綴り）は ``termination_invalid``（正常終了にしない）。
    """

    if outcome == Outcome.TIMEOUT.value:
        return _timeout_termination(timeout_kind)
    if outcome in _RESOLVED_OUTCOMES:
        return acceptance.TERMINATION_RESOLVED
    return acceptance.TERMINATION_INVALID


def _timeout_termination(timeout_kind: Optional[str]) -> str:
    if timeout_kind in PROCESS_DEADLINE_KINDS:
        return acceptance.TERMINATION_PROCESS_TIMEOUT
    if timeout_kind == KIND_CHILD_SOLVER_TIMEOUT:
        return acceptance.TERMINATION_SOLVER_TIMEOUT
    return acceptance.TERMINATION_TIMEOUT_UNCLASSIFIED


def observe_pair(
    key: str, outcome: str, *, termination: str, timeout_kind: Optional[str],
    journal: JournalView, sidecar: Optional[Mapping[str, Any]],
    result_payload: Optional[Mapping[str, Any]] = None,
) -> PairObservation:
    """1 pair の観測。区間は 1 つずつ別に求め、測れない区間は理由を残す（0 で埋めない）。

    打ち切ったかは `deadline_cut`（journal と結果 JSON の照合）。区間は損失の無い journal の
    trip の行から、``post_trip`` / ``tail`` は終わりが証明された journal からだけ求める。
    記録と派生値は有限で値域に入るときだけ値にする（不正な外部の記録は例外にしない）。
    """

    entered = bool(
        isinstance(sidecar, Mapping) and sidecar.get("signal_sent") is True
        and sidecar.get("cancel_linearized_offset_seconds") is None
    )
    process, process_problem = _sidecar_number(sidecar, "timeout_seconds", positive=True)
    lead, lead_problem = _sidecar_number(sidecar, "lead_seconds", nonnegative=True)
    record, record_problem = deadline_record(result_payload)
    base = dict(key=key, outcome=outcome, termination=termination,
                timeout_kind=timeout_kind, entered_lead_window=entered,
                lead_seconds=lead, process_timeout_seconds=process,
                result_budget_seconds=None if record is None else record.budget_seconds)
    cut, cut_problem = deadline_cut(journal, record, record_problem)
    if cut is None:
        return PairObservation(cut=None, cut_unknown_reason=cut_problem, **base)
    if not cut:
        return PairObservation(cut=False, **base)
    missing: Dict[str, str] = {}
    trip, note_problem = (None, journal.problem or (
        f"the journal has no {TRIP_NOTE} row ({journal.end_problem})"))
    if journal.segment is not None and journal.trips:
        trip, note_problem = _trip_note(journal.trips[0])
    if trip is None:
        for name in acceptance.TERM_POOLS:
            missing[name] = note_problem
        if lead is None:
            missing[acceptance.LEAD] = lead_problem
        return PairObservation(cut=True, missing=missing, **base)
    values: Dict[str, float] = {}

    def put(name: str, value: Optional[float], problem: str) -> Optional[float]:
        value, derived_problem = _derived(value, name)
        if value is None:
            missing[name] = derived_problem or problem
        else:
            values[name] = round(value, 3)
        return value

    end_problem = journal.end_problem
    last = None if end_problem else journal.segment.rows[-1].t_monotonic
    deadline, deadline_problem = _sidecar_number(sidecar, "deadline_monotonic")
    offset, offset_problem = _sidecar_number(sidecar, "cancel_linearized_offset_seconds")
    if entered:
        offset_problem = "the child exit was not observed before the stack-dump send"
    child_exit, exit_problem = _derived(
        None if deadline is None or offset is None or entered else deadline + offset,
        "the child exit (deadline_monotonic + cancel_linearized_offset_seconds)")
    origin, origin_problem = _derived(
        None if deadline is None or process is None else deadline - process,
        "the process deadline's origin (deadline_monotonic - timeout_seconds)")
    pre = None if origin is None else trip.at - trip.elapsed - origin
    if pre is not None and pre < 0:
        put("pre", None, f"the analysis started {-pre:g}s before the process deadline's origin")
    else:
        put("pre", pre, origin_problem or deadline_problem or process_problem)
    put("overrun", trip.elapsed - trip.budget, "")
    put("post_trip", None if last is None else last - trip.at, end_problem or "")
    tail = None if child_exit is None or last is None else child_exit - last
    if tail is not None and tail < 0:
        put("tail", None, f"the child exit was observed {-tail:g}s before the last journal event")
    else:
        put("tail", tail, exit_problem or deadline_problem or offset_problem or end_problem or "")
    for name in acceptance.TERM_POOLS:
        if name not in values and name not in missing:
            missing[name] = "no observer for this interval"
    if lead is None:
        missing[acceptance.LEAD] = lead_problem
    needed = None
    if not missing and child_exit is not None and origin is not None:
        needed, problem = _derived(child_exit - origin - trip.budget, "needed")
        if needed is None:
            missing["needed"] = problem
        else:
            needed = round(needed, 3)
    parts: Dict[str, float] = {}
    if last is not None:
        raw = post_trip_parts(journal.segment, trip.at, last)
        if all(math.isfinite(value) for value in raw.values()):
            parts = {name: round(value, 3) for name, value in raw.items()}
    return PairObservation(
        cut=True, values=values, missing=missing, needed=needed,
        budget_seconds=trip.budget, trip_stage=trip.stage, post_trip_parts=parts, **base,
    )


def _sample_of(key: str) -> str:
    """pair の key（``<sample identity>/<function>/<pair stem>``）の sample identity。"""

    return str(Path(key).parent.parent)


def _fmt(values: Iterable[float]) -> str:
    return ",".join(f"{value:g}" for value in sorted(set(values)))


def _reconcile(fact: str, manifest_key: str, manifest: Tuple[Optional[float], str],
               recorded: Mapping[str, Sequence[float]],
               ) -> Tuple[Optional[float], str, Tuple[str, ...]]:
    """同じ事実の出所を照合する: ``(値, 値の出所, 食い違い)``。

    ``recorded`` は出所の名前 → 記録された値。manifest があれば、記録された値はすべてそれと
    等しくなければならない（同じ double を CLI / supervisor が読んで書く）。manifest が無ければ、
    記録された値がすべての出所で 1 つのときだけ採る。
    """

    value, problem = manifest
    present = {label: set(values) for label, values in recorded.items() if values}
    seen = set().union(*present.values()) if present else set()
    described = ", ".join(f"{label}={_fmt(values)}" for label, values in present.items())
    labels = " / ".join(recorded)
    if problem:
        return None, problem, (problem,)
    if value is not None:
        if seen - {value}:
            return None, f"{fact} disagrees between sources", (
                f"{fact} disagrees between sources (run_manifest {manifest_key}={value:g}, "
                f"{described})",)
        return value, f"run_manifest {manifest_key}", ()
    if len(seen) == 1:
        return next(iter(seen)), f"{described} (the manifest does not record it)", ()
    if len(seen) > 1:
        return None, f"{fact} disagrees between sources", (
            f"{fact} disagrees between sources ({described})",)
    return None, f"neither run_manifest {manifest_key} nor {labels} records it", ()


def observe_run(root: Path) -> RunObservation:
    """result tree（1 half）の観測。pair を 1 件も除かない。

    journal は損失の無い current segment だけを使う（`JournalView`）。打ち切ったかは journal と
    結果 JSON の照合（`deadline_cut`）。run の事実は manifest と pair の記録（trip の budget・結果の
    budget・sidecar）を照合して決める（`_reconcile`）。
    """

    root = Path(root)
    manifest = _read_key_values(root / "run_manifest.txt")
    pairs: List[PairObservation] = []
    for record in iter_pair_outcomes(root):
        key = str(Path(record.status_path).relative_to(root))[: -len(PAIR_STATUS_SUFFIX)]
        evidence = load_pair_evidence(record.status_path)
        kind = evidence.timeout_kind_report().kind if record.outcome == TIMEOUT_OUTCOME else None
        pairs.append(observe_pair(
            key, record.outcome, termination=termination_of(record.outcome, kind),
            timeout_kind=kind, journal=JournalView.read(evidence.paths.journal, evidence.sidecar),
            sidecar=evidence.sidecar, result_payload=evidence.result_payload,
        ))
    budgets = {
        f"{TRIP_NOTE} budget_seconds":
            [pair.budget_seconds for pair in pairs if pair.budget_seconds is not None],
        "result analysis_deadline budget_seconds":
            [pair.result_budget_seconds for pair in pairs if pair.result_budget_seconds is not None],
    }
    manifest_deadline = _manifest_seconds(manifest.get("analysis_timeout"), "analysis_timeout",
                                          allow_zero=True)
    deadline_off = manifest_deadline == (0.0, "")
    conflicts: List[str] = []
    if deadline_off:
        deadline, source = None, "run_manifest analysis_timeout=0 (off)"
        recorded = ", ".join(f"{label}={_fmt(values)}" for label, values in budgets.items() if values)
        if recorded:
            conflicts.append(
                "analysis deadline disagrees between sources (run_manifest analysis_timeout=0 "
                f"(off), {recorded})")
    else:
        deadline, source, found = _reconcile(
            "analysis deadline", "analysis_timeout", manifest_deadline, budgets)
        conflicts.extend(found)
    process, _, found = _reconcile(
        "process timeout", "pair_process_timeout_seconds",
        _manifest_seconds(manifest.get("pair_process_timeout_seconds"),
                          "pair_process_timeout_seconds"),
        {"stack-dump sidecar timeout_seconds": [
            pair.process_timeout_seconds for pair in pairs
            if pair.process_timeout_seconds is not None]})
    conflicts.extend(found)
    lead, _, found = _reconcile(
        "stack-dump lead", "pair_stack_dump_lead",
        _manifest_seconds(manifest.get("pair_stack_dump_lead"), "pair_stack_dump_lead",
                          allow_zero=True),
        {"stack-dump sidecar lead_seconds": [
            pair.lead_seconds for pair in pairs if pair.lead_seconds is not None]})
    conflicts.extend(found)
    dirty = manifest.get("git_dirty")
    facts = RunFacts(
        root=str(root), deadline_seconds=deadline, deadline_off=deadline_off,
        deadline_source=source, pair_process_timeout_seconds=process,
        stack_dump_lead_seconds=lead,
        parallel_jobs=_manifest_count(manifest.get("parallel_jobs")),
        git_commit=manifest.get("git_commit") or None,
        git_dirty=None if dirty not in ("0", "1") else dirty == "1",
        samples=frozenset(_sample_of(pair.key) for pair in pairs),
        conflicts=tuple(conflicts),
    )
    return RunObservation(facts=facts, pairs=tuple(pairs))


def observe_runs(roots: Iterable[Path]) -> List[RunObservation]:
    return [observe_run(Path(root)) for root in roots]


def _pool_summary(runs: Sequence[RunObservation]) -> Dict[str, Any]:
    pairs = [pair for run in runs for pair in run.pairs]
    cut = [pair for pair in pairs if pair.cut]

    def keys(predicate) -> List[str]:
        return [pair.key for pair in pairs if predicate(pair)]

    return {
        "runs": [run.facts.to_dict() for run in runs],
        "pairs": len(pairs),
        "cut_pairs": len(cut),
        "finished_before_deadline": sum(1 for pair in pairs if pair.cut is False),
        "cut_unknown": [[pair.key, pair.cut_unknown_reason] for pair in pairs if pair.cut is None],
        "terminations": {
            name: keys(lambda pair, name=name: pair.termination == name)
            for name in (acceptance.TERMINATION_PROCESS_TIMEOUT,
                         acceptance.TERMINATION_SOLVER_TIMEOUT,
                         acceptance.TERMINATION_TIMEOUT_UNCLASSIFIED,
                         acceptance.TERMINATION_INVALID)
        },
        "entered_lead_window": keys(lambda pair: pair.entered_lead_window),
        "missing_intervals": [
            [pair.key, name, reason] for pair in cut for name, reason in pair.missing.items()
        ],
        "intervals": {
            **{name: describe([pair.values[name] for pair in cut if name in pair.values])
               for name in acceptance.TERM_POOLS},
            "needed": describe([pair.needed for pair in cut if pair.needed is not None]),
        },
    }


def report_dict(
    profile: acceptance.MarginProfile, pools: Mapping[str, Sequence[RunObservation]],
) -> Dict[str, Any]:
    """観測の要約と `deadline_margin_acceptance.evaluate_margin` の判定。"""

    verdict = acceptance.evaluate_margin(profile, pools)
    profile_pairs = [pair for run in pools.get(acceptance.POOL_P, ()) for pair in run.pairs if pair.cut]
    return {
        "schema": SCHEMA,
        "profile": {
            "name": profile.name, "deadline_seconds": profile.deadline_seconds,
            "margin_seconds": profile.margin_seconds,
            "pair_process_timeout_seconds": profile.pair_process_timeout_seconds,
            "population": None if profile.population is None else len(profile.population),
            "machinery_commits": None if profile.machinery_commits is None
            else sorted(profile.machinery_commits),
        },
        "pools": {name: _pool_summary(pools.get(name, ())) for name in acceptance.POOLS},
        "post_trip_parts": {
            name: describe([pair.post_trip_parts.get(name, 0.0) for pair in profile_pairs])
            for name in POST_TRIP_PARTS
        },
        "verdict": verdict.to_dict(),
        "required_margin_seconds": verdict.required_margin_seconds,
        "margin_holds": verdict.holds,
        "profile_pairs": [pair.to_dict() for pair in profile_pairs],
    }


def format_report(payload: Mapping[str, Any]) -> str:
    profile = payload["profile"]
    verdict = payload["verdict"]
    lines = [
        "Deadline margin summary:",
        f"  profile {profile['name']}: deadline {profile['deadline_seconds']}"
        f" margin {profile['margin_seconds']} process {profile['pair_process_timeout_seconds']}",
    ]
    for name, pool in payload["pools"].items():
        terminations = pool["terminations"]
        lines.append(
            f"  pool {name}: runs {len(pool['runs'])}, pairs {pool['pairs']}, cut {pool['cut_pairs']},"
            f" finished {pool['finished_before_deadline']}, cut unknown {len(pool['cut_unknown'])},"
            f" missing intervals {len(pool['missing_intervals'])};"
            f" TIMEOUT process {len(terminations['process_timeout'])}"
            f" solver {len(terminations['solver_timeout'])}"
            f" unclassified {len(terminations['timeout_unclassified'])},"
            f" invalid {len(terminations['termination_invalid'])},"
            f" lead window {len(pool['entered_lead_window'])}"
        )
        for interval, row in pool["intervals"].items():
            stats = " ".join(f"{key}={value}" for key, value in row.items())
            lines.append(f"    - {interval}: {stats}")
    lines.append("  post_trip parts (pool P):")
    for name, row in payload["post_trip_parts"].items():
        lines.append(f"    - {name}: " + " ".join(f"{key}={value}" for key, value in row.items()))
    for term, row in verdict["terms"].items():
        lines.append(f"  term {term}: " + " ".join(f"{key}={value}" for key, value in row.items()))
    lines.append(
        f"  required margin: {verdict['required_margin_seconds']}; verdict: {verdict['status']}"
    )
    for reason in verdict["violations"]:
        lines.append(f"  violated: {reason}")
    for reason in verdict["undetermined"]:
        lines.append(f"  undetermined: {reason}")
    return "\n".join(lines)


def _population(manifest: Optional[Path]) -> Optional[frozenset]:
    """固定 subset の manifest（`eqbench_subset.json`）の source 一覧（Eq と Neq）。"""

    if manifest is None:
        return None
    data = json.loads(manifest.read_text(encoding="utf-8"))
    return frozenset(
        source for half in ("eq", "neq") for source in data.get(half, {}).get("sources", ())
    )


def _seconds_argument(text: str) -> float:
    """CLI の秒（正の有限な数）。規則は `core.deadline.parse_budget_seconds`（runner / pair と共有）。"""

    try:
        return parse_budget_seconds(text)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(
            f"{text!r} is not a positive finite number of seconds") from exc


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("roots", nargs="+", type=Path,
                        help="pool P: the profile's run result trees (one per half)")
    parser.add_argument("--load-root", action="append", type=Path, default=[],
                        help="pool L: a run of the load pool (pre / overrun; repeatable)")
    parser.add_argument("--pre-root", action="append", type=Path, default=[],
                        help="pool F: a run of the fixed-cost pool (pre only; repeatable)")
    parser.add_argument("--margin", type=_seconds_argument, default=None,
                        help="the ANALYSIS_TIMEOUT_MARGIN under evaluation")
    parser.add_argument("--profile", default="unnamed", help="the profile's name")
    parser.add_argument("--profile-deadline", type=_seconds_argument, default=None,
                        help="the profile's ANALYSIS_TIMEOUT (pool P needs a deadline at least this)")
    parser.add_argument("--pair-process-timeout", type=_seconds_argument, default=None,
                        help="the profile's PAIR_PROCESS_TIMEOUT (pool P must match it)")
    parser.add_argument("--population-manifest", type=Path, default=None,
                        help="the fixed subset manifest whose sources are the profile's population")
    parser.add_argument("--machinery-commit", action="append", default=None,
                        help="a commit whose deadline machinery is the one under evaluation "
                             "(pools P and L; repeatable)")
    parser.add_argument("--json", type=Path, default=None)
    args = parser.parse_args(argv)
    profile = acceptance.MarginProfile(
        name=args.profile, deadline_seconds=args.profile_deadline, margin_seconds=args.margin,
        pair_process_timeout_seconds=args.pair_process_timeout,
        population=_population(args.population_manifest),
        machinery_commits=None if args.machinery_commit is None else frozenset(args.machinery_commit),
    )
    pools = {
        acceptance.POOL_P: observe_runs(args.roots),
        acceptance.POOL_L: observe_runs(args.load_root),
        acceptance.POOL_F: observe_runs(args.pre_root),
    }
    payload = report_dict(profile, pools)
    print(format_report(payload))
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(payload, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())

# -*- coding: utf-8 -*-
"""記録済み pair を子 process で 1 回、解析の期限つきで再生する（Issue #106 PR-106-A、E1 / E2）。

production と同じ「1 process 1 pair」の条件で、production の `check_from_binaries`（pilot
connector・worker authority 付き）を記録済み object の上で走らせる。期限は
`DeadlinePolicy.clock` だけで操作する:

* ``--trip-stage none``: 期限は十分に長く、どの stage で何回時計を読んだかを観測する
* ``--trip-stage <S>``: stage ``S`` で最初に時計を読んだ瞬間に時計を期限の先へ進める
  （その境界で期限切れを観測させる。他の仕組みには手を入れない）
* ``--inject z3_error_after_limit``（レビュー 3 巡目）: 最初の `Z3Solver` の実行 1 回だけ、
  期限を「1.0 s 先・実行の窓は 0.5 s」に縮めて始め、z3 の check が窓の後（0.7 s）に独立した
  例外を上げる。実行が返った後は期限を元に戻す（この 1 回の判定だけを切り出す）。
  ``--no-deadline`` と組み合わせると、同じ注入を期限なしで観測する

採点はしない。観測を JSON で返し、親の test が判定する。
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

REPO_ROOT = Path(__file__).resolve().parents[4]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.function_tracer_pcode.core import deadline as deadline_module  # noqa: E402
from scripts.function_tracer_pcode.tests.fixtures.pcode.replay import (  # noqa: E402
    SimplePatcher,
    replay_recorded_pair,
)

FAST_PATH = {"recorded": None, "on": True, "off": False}
#: 観測用の期限（十分に長い）と、trip のときに時計を進める量
LONG_BUDGET = 1.0e6
JUMP = 1.0e7


def _reason_ids(payload: Optional[Dict[str, Any]]) -> List[str]:
    ids = []
    for entry in (payload or {}).get("unknown_reasons") or ():
        value = entry.get("reason_id") if isinstance(entry, dict) else None
        if value:
            ids.append(str(value))
    return sorted(set(ids))


class _FailingSolver:
    """本物の z3 の solver を包み、check だけ ``fail_at``（monotonic）まで待ってから例外を上げる。"""

    def __init__(self, inner: Any, fail_at: float) -> None:
        self._inner = inner
        self._fail_at = fail_at

    def check(self, *args: Any) -> Any:
        time.sleep(max(0.0, self._fail_at - time.monotonic()))
        raise RuntimeError("injected backend failure")

    def __getattr__(self, name: str) -> Any:
        return getattr(self._inner, name)


def _inject_z3_error_after_limit(patcher: Any, observed: Dict[str, Any]) -> None:
    import z3

    from scripts.function_tracer_pcode.smt import parallel as parallel_module
    from scripts.function_tracer_pcode.smt.interface import execution_end
    from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver

    original = parallel_module._execute_within
    real_solver = z3.Solver

    def _wrapped(backend, smt_script, timeout_seconds, bound, token):
        if observed.get("injected") or not isinstance(backend, Z3Solver):
            return original(backend, smt_script, timeout_seconds, bound, token)
        observed["injected"] = True
        deadline = deadline_module.active_deadline()
        now = time.monotonic()
        saved = None
        if deadline is not None:
            saved = deadline.absolute
            deadline.absolute = now + 1.0
            bound = deadline_module.ExecutionBound(not_after=now + 0.5, clock=bound.clock)
        z3.Solver = lambda *a, **k: _FailingSolver(real_solver(*a, **k), now + 0.7)
        try:
            row = original(backend, smt_script, timeout_seconds, bound, token)
        finally:
            z3.Solver = real_solver
            if saved is not None:
                deadline.absolute = saved
        observed.update({
            "row_status": row.status.name,
            "row_end": execution_end(row).value,
            "row_limited": row.deadline_limited,
            "row_error": row.error_message,
        })
        return row

    patcher.setattr(parallel_module, "_execute_within", _wrapped)


def run(
    case_dir: Path, *, case_id: str, trip_stage: str, fast_path: Optional[bool],
    inject: str = "none", no_deadline: bool = False,
) -> Dict[str, Any]:
    left = json.loads((case_dir / "left.json").read_text(encoding="utf-8"))
    right = json.loads((case_dir / "right.json").read_text(encoding="utf-8"))
    offset = [0.0]
    tripped_at: List[str] = []
    patcher = SimplePatcher()
    injected: Dict[str, Any] = {}
    if inject == "z3_error_after_limit":
        _inject_z3_error_after_limit(patcher, injected)

    if trip_stage != "none":
        original_read = deadline_module.Deadline._read

        def _read(self, stage):
            if stage == trip_stage and not tripped_at:
                tripped_at.append(stage)
                offset[0] = JUMP
            return original_read(self, stage)

        patcher.setattr(deadline_module.Deadline, "_read", _read)

    policy = deadline_module.DeadlinePolicy(
        budget_seconds=LONG_BUDGET, clock=lambda: time.monotonic() + offset[0],
    )
    started = time.monotonic()
    outcome = replay_recorded_pair(
        left, right, case_id=case_id + "-deadline-" + trip_stage, monkeypatch=patcher,
        identical_fast_path=fast_path, analysis_deadline=None if no_deadline else policy,
    )
    payload = outcome.payload or {}
    diagnostics = payload.get("diagnostics") or {}
    failures = diagnostics.get("failures") or {}
    limitation = failures.get("analysis_limitation") or {}
    return {
        "case_id": case_id,
        "trip_stage": trip_stage,
        "tripped_at": tripped_at,
        "seconds": time.monotonic() - started,
        "failure": None if outcome.failure is None else f"{type(outcome.failure).__name__}: {outcome.failure}",
        "final_outcome": payload.get("final_outcome"),
        "error_message": payload.get("error_message"),
        "reason_ids": _reason_ids(payload),
        "has_decision_receipt": payload.get("decision_receipt") is not None,
        "has_finalization_bundle": payload.get("canonical_result_finalization_bundle") is not None,
        "limitation_site": limitation.get("site"),
        "limitation_type": limitation.get("exception_type"),
        "limitation_disposition": limitation.get("disposition"),
        "limitation_evidence": limitation.get("evidence_refs") or [],
        "pair_stop_state": failures.get("pair_stop_state"),
        "analysis_deadline": diagnostics.get("analysis_deadline"),
        "conditional_lane": diagnostics.get("conditional_lane"),
        "injected": injected,
    }


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case-dir", required=True)
    parser.add_argument("--case-id", required=True)
    parser.add_argument("--trip-stage", required=True)
    parser.add_argument("--fast-path", choices=sorted(FAST_PATH), default="recorded")
    parser.add_argument("--output", required=True)
    parser.add_argument("--inject", choices=["none", "z3_error_after_limit"], default="none")
    parser.add_argument("--no-deadline", action="store_true")
    args = parser.parse_args(argv)
    report = run(
        Path(args.case_dir), case_id=args.case_id, trip_stage=args.trip_stage,
        fast_path=FAST_PATH[args.fast_path], inject=args.inject, no_deadline=args.no_deadline,
    )
    Path(args.output).write_text(json.dumps(report, ensure_ascii=False, sort_keys=True), encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())

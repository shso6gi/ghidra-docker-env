# -*- coding: utf-8 -*-
"""記録済み pair を子 process で 1 回、解析の期限つきで再生する（Issue #106 PR-106-A、E1 / E2）。

production と同じ「1 process 1 pair」の条件で、production の `check_from_binaries`（pilot
connector・worker authority 付き）を記録済み object の上で走らせる。期限は
`DeadlinePolicy.clock` だけで操作する:

* ``--trip-stage none``: 期限は十分に長く、どの stage で何回時計を読んだかを観測する
* ``--trip-stage <S>``: stage ``S`` で最初に時計を読んだ瞬間に時計を期限の先へ進める
  （その境界で期限切れを観測させる。他の仕組みには手を入れない）

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


def run(case_dir: Path, *, case_id: str, trip_stage: str, fast_path: Optional[bool]) -> Dict[str, Any]:
    left = json.loads((case_dir / "left.json").read_text(encoding="utf-8"))
    right = json.loads((case_dir / "right.json").read_text(encoding="utf-8"))
    offset = [0.0]
    tripped_at: List[str] = []
    patcher = SimplePatcher()

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
        identical_fast_path=fast_path, analysis_deadline=policy,
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
    }


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case-dir", required=True)
    parser.add_argument("--case-id", required=True)
    parser.add_argument("--trip-stage", required=True)
    parser.add_argument("--fast-path", choices=sorted(FAST_PATH), default="recorded")
    parser.add_argument("--output", required=True)
    args = parser.parse_args(argv)
    report = run(
        Path(args.case_dir), case_id=args.case_id, trip_stage=args.trip_stage,
        fast_path=FAST_PATH[args.fast_path],
    )
    Path(args.output).write_text(json.dumps(report, ensure_ascii=False, sort_keys=True), encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())

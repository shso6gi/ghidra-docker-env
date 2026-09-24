# -*- coding: utf-8 -*-
"""Issue #165: supervisor の終端 authority を実 child で観測する probe。

production を変えずに（または変えたあとに）同じ入力で走らせ、
「supervisor が何を projection に書き、production の分類器がそれをどう
扱ったか」を 1 行 1 scenario の JSON で出す。判定はしない（期待は
``README.md`` と test が持つ）。

状態は PR #193 の共有 harness（``tests/unit/_supervisor_support``）だけで作る。
worker child は production の broker / store / canonical 経路を通り、
supervisor は fork した production の ``ProcessSupervisorCommand.run()``。

    python3 -B -m scripts.function_tracer_pcode.tests.fixtures.issue165.probe_terminal_authority

出力の各行:

* ``scenario``: 下の ``SCENARIOS`` の名前
* ``runs``: invocation ごとの ``exit_code`` / ``crashed`` / projection の
  ``status`` / ``authority_kind`` / ``error_code`` / ``child_returncode`` /
  ``child_exit_disposition`` と、分類器の結果（``canonical_outcome`` /
  ``classification_valid``）または拒否（例外の型と message の先頭）
* ``store_state``: 最後の invocation の後の ``state.json`` が名乗る state
"""

from __future__ import annotations

import json
import re
import sys
import tempfile
from pathlib import Path
from typing import Any, Callable, Mapping

from scripts.function_tracer_pcode.tests.unit._supervisor_support import (
    Checkpoint,
    ChildScript,
    Deadline,
    Envelope,
    Exit,
    FileBoundary,
    Stop,
    classify,
    crash_at,
    restart_supervisor,
    run_supervisor,
    stop_at,
    supervisor_case,
)


def _run_record(run: Any) -> dict[str, Any]:
    projection = run.projection or {}
    record: dict[str, Any] = {
        "exit_code": run.exit_code,
        "crashed": run.crashed,
        "status": projection.get("status"),
        "authority_kind": projection.get("authority_kind"),
        "error_code": projection.get("error_code"),
        "child_returncode": projection.get("child_returncode"),
        "child_exit_disposition": projection.get("child_exit_disposition"),
        "canonical_outcome": projection.get("canonical_outcome"),
    }
    if run.projection is None:
        record["classify"] = None
        return record
    try:
        classified = classify(run)
    except (AssertionError, OSError, ValueError, KeyError, TypeError) as exc:
        message = re.sub(r"/[^ ']*/issue165-[^/]+/", "<case>/", str(exc).splitlines()[0])
        record["classify"] = {"rejected": type(exc).__name__, "message": message[:160]}
    else:
        record["classify"] = {
            "canonical_outcome": classified["canonical_outcome"],
            "classification_valid": classified["classification_valid"],
            "supervisor_status": classified["supervisor_status"],
        }
    return record


def _deadline_at(boundary: FileBoundary, *, runner_mode: bool = True) -> Callable[[Path], list]:
    def scenario(directory: Path) -> list:
        script = ChildScript((Checkpoint(), Stop()), faults=(stop_at(boundary),))
        with supervisor_case(
            directory, script, allow_child_exit_resolution=runner_mode,
        ) as case:
            return [run_supervisor(case, deadline=Deadline.AT_CHILD_STOP)]
    return scenario


def _natural(steps: tuple, *, runner_mode: bool, restart: bool = False) -> Callable[[Path], list]:
    def scenario(directory: Path) -> list:
        with supervisor_case(
            directory, ChildScript(steps), allow_child_exit_resolution=runner_mode,
        ) as case:
            runs = [run_supervisor(case)]
            if restart:
                runs.append(restart_supervisor(case))
            return runs
    return scenario


def _crash_then_restart(child_steps: tuple, boundary: FileBoundary, *, deadline: bool) -> Callable[[Path], list]:
    def scenario(directory: Path) -> list:
        with supervisor_case(
            directory, ChildScript(child_steps), allow_child_exit_resolution=True,
        ) as case:
            first = run_supervisor(
                case,
                deadline=Deadline.AT_CHILD_STOP if deadline else Deadline.TIMER,
                faults=(crash_at(boundary),),
            )
            return [first, restart_supervisor(case)]
    return scenario


#: scenario 名 -> 状態の作り方。名前は README の表と対応する。
SCENARIOS: Mapping[str, Callable[[Path], list]] = {
    # deadline が来た瞬間の checkpoint（worker が止まった場所）ごと。
    "deadline_no_checkpoint": lambda d: _deadline_no_checkpoint(d),
    "deadline_active": _deadline_at(FileBoundary("state.json", 1, "after")),
    "deadline_continuation_before_cas": _deadline_at(FileBoundary("continuation.json")),
    "deadline_ready": _deadline_at(FileBoundary("state.json", 2, "after")),
    "deadline_resolved": _deadline_at(FileBoundary("state.json", 3, "after")),
    # 自然終了（envelope 無し）: runner mode / 非 runner mode。
    "exit0_resolved_checkpoint_runner": _natural(
        (Checkpoint(), Exit(0)), runner_mode=True),
    "exit1_resolved_checkpoint_nonrunner": _natural(
        (Checkpoint(), Exit(1)), runner_mode=False),
    "exit3_no_checkpoint_nonrunner": _natural((Exit(3),), runner_mode=False),
    "exit0_no_checkpoint_runner": _natural((Exit(0),), runner_mode=True),
    # 封の壊れた envelope を restart する（#165 issuecomment-5804197897）。
    "corrupt_envelope_then_restart": _natural(
        (Checkpoint(), Envelope("UNKNOWN", corrupt="envelope_digest"), Exit()),
        runner_mode=True, restart=True),
    # canonical 結果の対照（#163 の契約）。
    "canonical_timeout_control": _natural(
        (Checkpoint(), Envelope("TIMEOUT"), Exit()), runner_mode=True),
    "canonical_unknown_control": _natural(
        (Checkpoint(), Envelope("UNKNOWN"), Exit()), runner_mode=True),
    # supervisor が deadline 経路の途中で落ちてから restart する。
    "deadline_crash_after_claimed_then_restart": _crash_then_restart(
        (Stop(),), FileBoundary("claimed.json"), deadline=True),
}


def _deadline_no_checkpoint(directory: Path) -> list:
    with supervisor_case(directory, ChildScript((Stop(),))) as case:
        return [run_supervisor(case, deadline=Deadline.AT_CHILD_STOP)]


def main(arguments: list[str]) -> int:
    selected = arguments or list(SCENARIOS)
    for name in selected:
        with tempfile.TemporaryDirectory(prefix=f"issue165-{name}-") as tmp:
            try:
                runs = SCENARIOS[name](Path(tmp))
            except (AssertionError, OSError, ValueError) as exc:
                line = {"scenario": name, "harness_error": type(exc).__name__,
                        "message": str(exc).splitlines()[0][:200]}
            else:
                line = {
                    "scenario": name,
                    "runs": [_run_record(run) for run in runs],
                    "store_state": runs[-1].store.state,
                    "store_files": sorted(
                        f for f in runs[-1].store.files
                        if not f.startswith("checkpoint-history/")
                    ),
                }
        print(json.dumps(line, sort_keys=True), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

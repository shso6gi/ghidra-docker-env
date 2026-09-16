# -*- coding: utf-8 -*-
"""記録済み pair を **1 process につき 1 回**再生する worker（Issue #109 PR-B）。

production は pair ごとに OS process を分ける（runner の
``authority.process.supervisor_command -- env ... cli.main --equiv``）。record も
1 process 1 pair で行っているので、fixture はその条件下の観測列である。

recorded-pair test は 9 回の再生を 1 つの pytest process で回すので、そのまま
だと production には存在しない条件（同じ process で 2 件目以降の判定を走らせる）
になる。実測でも、同じ fixture を同じ process で 2 回再生すると 1 回目と違う
stage 経路へ入り、記録に無い surface を要求することがある。そこで **各再生を
この worker の子 process で 1 回だけ**走らせ、production と同じ process 条件に
そろえる。

worker は採点しない。観測を JSON にして返すだけで、soundness も regression も
親の test が判定する。
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

from scripts.function_tracer_pcode.tests.fixtures.pcode.replay import (  # noqa: E402
    SimplePatcher,
    replay_recorded_pair,
    replay_report,
)

#: variant 名 → ``identical_fast_path``。``recorded`` は記録時の mode を使う。
FAST_PATH_CHOICES = {"recorded": None, "on": True, "off": False}


def _forbid_solver() -> None:
    """solver が動いたら再生を失敗させる（identity fast path の ON 再生用）。"""

    from scripts.function_tracer_pcode.smt.parallel import ParallelSolverRunner

    def _no_solver(*_args: Any, **_kwargs: Any) -> Any:
        raise AssertionError("a solver ran on the identical fast path")

    for name in ("run_single", "run_parallel", "run_sequential"):
        setattr(ParallelSolverRunner, name, _no_solver)


def run(
    case_dir: Path, *, case_id: str, variant: str, fast_path: Optional[bool],
    forbid_solver: bool,
) -> Dict[str, Any]:
    left = json.loads((case_dir / "left.json").read_text(encoding="utf-8"))
    right = json.loads((case_dir / "right.json").read_text(encoding="utf-8"))
    if forbid_solver:
        _forbid_solver()
    started = time.monotonic()
    outcome = replay_recorded_pair(
        left, right,
        case_id=case_id + "-" + variant,
        monkeypatch=SimplePatcher(),
        identical_fast_path=fast_path,
    )
    seconds = time.monotonic() - started
    return replay_report(
        outcome, case_id=case_id, variant=variant, seconds=seconds,
        solver_forbidden=forbid_solver,
    )


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case-dir", required=True)
    parser.add_argument("--case-id", required=True)
    parser.add_argument("--variant", required=True)
    parser.add_argument(
        "--fast-path", choices=sorted(FAST_PATH_CHOICES), default="recorded",
    )
    parser.add_argument("--forbid-solver", action="store_true")
    parser.add_argument("--output", required=True)
    args = parser.parse_args(argv)

    report = run(
        Path(args.case_dir), case_id=args.case_id, variant=args.variant,
        fast_path=FAST_PATH_CHOICES[args.fast_path],
        forbid_solver=bool(args.forbid_solver),
    )
    # 既定の JSON encoder だけを使う。``default=`` を付けると、serialize でき
    # ない値が黙って文字列になり、親が payload を authority へ通せなくなる。
    Path(args.output).write_text(
        json.dumps(report, ensure_ascii=False, sort_keys=True),
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

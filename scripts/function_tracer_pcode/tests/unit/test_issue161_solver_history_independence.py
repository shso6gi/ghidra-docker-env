# -*- coding: utf-8 -*-
"""Issue #161: pairwise / replay の判定は、同じ process で先に解いた query に依らない。

記録済み pair を **1 つの process の中で** 繰り返し再生し、その間に solver の履歴を
変える（condition oracle を切る / 2 回呼ぶ / 条件の順を逆にする / cache を使わない、
z3 の main context に無関係な式を積む、z3 の random seed を変える）。判定・canonical
reason・backend が返した SAT の witness の列が、すべての run で一致することを固定する。

特定の model の値や特定の outcome は固定しない（契約は「履歴に依らない」こと）。
固定するのは ground truth に反しない（Neq の pair を EQ にしない）ことと、記録済みの
観測面を外れない（再生が記録に無い surface を要求しない）ことだけ。
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

pytestmark = pytest.mark.recorded_replay

REPO_ROOT = Path(__file__).resolve().parents[4]

#: main（Issue #161 の修正前）で、同じ process の反復だけで NOT_EQ ↔ UNKNOWN が揺れた pair。
CASES = ("max_snippet_N_B2_O_B4",)


@pytest.mark.parametrize("case_id", CASES)
def test_the_verdict_and_witnesses_do_not_depend_on_solver_history(case_id, tmp_path):
    output = tmp_path / "runs.json"
    completed = subprocess.run(
        [
            sys.executable, "-B", "-m",
            "scripts.function_tracer_pcode.tests.unit._history_independence_replay_driver",
            case_id, str(output),
        ],
        cwd=REPO_ROOT, capture_output=True, text=True, timeout=600,
    )
    assert completed.returncode == 0, completed.stderr[-2000:]
    runs = json.loads(output.read_text(encoding="utf-8"))

    assert len(runs) >= 9
    assert all(run["failure"] is None for run in runs), runs
    reference = runs[0]
    assert reference["witnesses"], "the replay produced no SAT witness"
    for run in runs[1:]:
        assert (run["outcome"], run["reasons"], run["witnesses"]) == (
            reference["outcome"], reference["reasons"], reference["witnesses"],
        ), run["mode"]
    # ground truth（Neq）に反しない・記録済みの観測面の中で完結する
    assert reference["outcome"] != "EQUIVALENT"
    assert all(run["missing"] == {"left": 0, "right": 0} for run in runs), runs

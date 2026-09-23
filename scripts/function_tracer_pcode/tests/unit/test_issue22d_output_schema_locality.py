# -*- coding: utf-8 -*-
"""M-3: 判定に関わらない診断 field を足すのは出力層の 1 行で閉じる（Issue #22 PR-22-D）。

静的な契約（出力層を意味の経路が import しない）は
`test_architecture_boundaries.py`、ここは **実際の production 経路**で確かめる:
記録済み pair を、診断 field を足した場合と足さない場合で 1 回ずつ（別 process で）
再生し、solver へ渡った SMT script の digest・判定・canonical reason・semantic
projection・c_active_base が一致すること、足した field が JSON にだけ現れることを
固定する。
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

pytestmark = pytest.mark.recorded_replay

REPO_ROOT = Path(__file__).resolve().parents[4]
#: 小さく速い、solver を実際に走らせる記録済み pair。
CASE_ID = "max_snippet_N_B2_O_B4"


def _replay_with_query_log(mode: str, tmp_path: Path) -> dict:
    output = tmp_path / f"{mode}.json"
    completed = subprocess.run(
        [
            sys.executable, "-B", "-m",
            "scripts.function_tracer_pcode.tests.unit._output_locality_replay_driver",
            CASE_ID, mode, str(output),
        ],
        cwd=REPO_ROOT, capture_output=True, text=True, timeout=300,
    )
    assert completed.returncode == 0, completed.stderr[-2000:]
    return json.loads(output.read_text(encoding="utf-8"))


def _decision_surface(report: dict) -> dict:
    payload = report["payload"]
    bundle = payload["canonical_result_finalization_bundle"]
    return {
        "final_outcome": payload["final_outcome"],
        "unknown_reasons": [row["reason_id"] for row in payload["unknown_reasons"]],
        "c_active_base": payload["c_active_base"],
        "q_open_base": payload["q_open_base"],
        "semantic_projection": bundle["canonical_semantic_result_projection"],
        "decision_outcome": payload["decision_receipt"]["outcome"],
    }


def test_m3_a_new_diagnostic_field_leaves_the_semantic_path_unchanged(tmp_path):
    baseline = _replay_with_query_log("baseline", tmp_path)
    extra = _replay_with_query_log("extra", tmp_path)

    assert baseline["failure"] is None and extra["failure"] is None
    # solver へ渡った query は数も内容も同じ（出力層の変更は query を作らない）
    assert baseline["solver_queries"], "the replay ran no solver query"
    assert extra["solver_queries"] == baseline["solver_queries"]
    # 判定・reason・relations・semantic projection も同じ
    assert _decision_surface(extra) == _decision_surface(baseline)
    # 足した field は JSON にだけ現れる
    assert "m3_extra_diagnostic" not in baseline["payload"]
    assert extra["payload"]["m3_extra_diagnostic"] == {"observed": 1}

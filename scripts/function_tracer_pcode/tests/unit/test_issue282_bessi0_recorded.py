"""Issue #282: bessi0 の Neq pair（分岐の閾値だけが違う binary）を、記録した Ghidra の出力で本番の経路に通す。

`bess/bessi0` Neq `N_B14_O_B14`（MIPS64 gcc の new O1 / old O1）。閾値は両側とも `.rodata.cst8+0`（`0x100160`）から
読まれ、中身は new が 1.75・old が 3.75（qemu で x=2.0 の結果が違うことを確かめ済み: 計画 v3 §3.5）。修正前は
左右の memory を 1 つの配列で描き、2 つの閾値が同じ記号になって EQUIVALENT になっていた。

この fixture は corpus（`fixtures/pcode/cases.json`）の外に置く: ground truth の表（`scripts/eqbench/neq_ground_truth.tsv`）
にこの pair の検証済みの関係がまだ無いので、corpus の契約（GT を必須にする）に入れられない（計画 v3 §9.2）。assert は
GT に依らない性質だけ:

* EQUIVALENT にならない（#282 AC 3）。
* 理由つきの UNKNOWN なら、反例の memory の状態が実現できないこと（`memory_state_unrealized:` の族）が理由に含まれる。
* 再生で記録の外の呼び出しが無い（`missing_accesses` が空）。

記録元の commit は fixture の header にあり（`recording_commit`）、再生する HEAD と一致は要求しない。
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.tests.fixtures.pcode.replay import replay_recorded_pair

pytestmark = pytest.mark.recorded_replay

FIXTURE = Path(__file__).resolve().parents[1] / "fixtures" / "pcode_issue282" / "bessi0_snippet_N_B14_O_B14"


def _replay_bessi0(monkeypatch):
    left = json.loads((FIXTURE / "left.json").read_text(encoding="utf-8"))
    right = json.loads((FIXTURE / "right.json").read_text(encoding="utf-8"))
    return left, right, replay_recorded_pair(
        left, right, case_id="bessi0_snippet_N_B14_O_B14", monkeypatch=monkeypatch, identical_fast_path=False
    )


def test_bessi0_threshold_pair_is_not_equivalent(monkeypatch):
    left, _right, outcome = _replay_bessi0(monkeypatch)
    assert outcome.failure is None, repr(outcome.failure)
    assert outcome.left.missing_accesses == [] and outcome.right.missing_accesses == []
    payload = outcome.payload
    assert payload["final_outcome"] in {"UNKNOWN", "NOT_EQ"}, payload["final_outcome"]
    assert payload["final_outcome"] != "EQUIVALENT"
    if payload["final_outcome"] == "UNKNOWN":
        text = json.dumps(payload.get("unknown_reasons"), sort_keys=True)
        assert "counterexample_analysis_safety_unproven" in text
        assert "memory_state_unrealized:" in text
    # 記録元の commit は header に残る（再生する HEAD との一致は要求しない）
    assert left["header"]["recording_dirty"] is False

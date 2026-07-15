"""Opt-in real-binary witnesses for frequent recurrence summaries."""

import os
import json
from pathlib import Path
import shutil
import subprocess
import sys

import pytest


_ROOT = Path(__file__).resolve().parents[4]
_PARITY_SOURCE = _ROOT / "scripts/function_tracer_pcode/tests/fixtures/recurrence_parity.c"
_GUARDED_SOURCE = (
    _ROOT / "scripts/function_tracer_pcode/tests/fixtures/recurrence_guarded_affine.c"
)

pytestmark = pytest.mark.skipif(
    os.environ.get("RUN_PYGHIDRA_REGRESSIONS") != "1",
    reason="real PyGhidra binary regressions are opt-in",
)


@pytest.mark.parametrize(
    ("source", "function_name", "expected_transition_tag"),
    (
        (_PARITY_SOURCE, "recurrence_parity_sum", "affine_counted_loop_v1"),
        (
            _GUARDED_SOURCE,
            "recurrence_guarded_steps",
            "guarded_affine_decreasing_state_v1",
        ),
    ),
)
def test_frequent_recurrence_pattern_is_equivalent_across_real_o0_og_binaries(
    tmp_path, source, function_name, expected_transition_tag
):
    compiler = shutil.which("gcc")
    if compiler is None:
        pytest.skip("gcc is required for real-binary recurrence regressions")
    binaries = []
    for optimization in ("-O0", "-Og"):
        output = tmp_path / f"{source.stem}_{optimization[1:]}.o"
        completed = subprocess.run(
            [compiler, optimization, "-c", str(source), "-o", str(output)],
            capture_output=True,
            text=True,
        )
        assert completed.returncode == 0, completed.stderr
        binaries.append(output)
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.function_tracer_pcode.cli.main",
            "--equiv",
            str(binaries[0]),
            str(binaries[1]),
            "-f",
            function_name,
            "--strategy",
            "pairwise",
            "--normalize-mode",
            "safe",
            "--equiv-timeout",
            "10",
            "--emit-result-json",
        ],
        cwd=_ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )
    output = completed.stdout + completed.stderr
    assert completed.returncode == 0, output
    assert "Result: EQUIVALENT" in output
    assert "ERROR: 0" in output
    begin = "=== EQUIVALENCE_RESULT_JSON_BEGIN ==="
    end = "=== EQUIVALENCE_RESULT_JSON_END ==="
    assert begin in output and end in output
    payload = json.loads(output.split(begin, 1)[1].split(end, 1)[0].strip())
    receipt = payload.get("recurrence_promotion_receipt")
    assert receipt is not None
    assert receipt["state"] == "composed"
    assert receipt["branch_local_authority_issued"] is True
    assert receipt["authority"]["branch_id"]
    assert receipt["authority"]["targeted_blocker_keys"]
    sides = [receipt[name] for name in ("left", "right") if receipt.get(name)]
    proposed = [side for side in sides if side["proposal_generated"]]
    assert proposed
    assert any(
        expected_transition_tag in side["transition_proposition_tags"]
        for side in proposed
    )
    for side in proposed:
        assert side["validated_artifact_id"][0] == "validated_recurrence_artifact_v2"
        assert side["artifact_validation_status"] == "validated"
        assert side["validated_artifact_imported"] is True
        assert side["promoted_successor_surface_fingerprint"]
    assert receipt["final_decision_used_promoted_successor"] is True
    assert receipt["promoted_successor_final_outcome"] == "EQ"

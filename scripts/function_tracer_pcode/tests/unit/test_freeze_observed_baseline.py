# -*- coding: utf-8 -*-

import hashlib
import json
import subprocess
import sys
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.equivalence.unknown_reason import (
    UnknownReasonId,
    make_unknown_reason,
)
from scripts.function_tracer_pcode.validation.freeze_observed_baseline import (
    freeze_observed_baseline,
)
from scripts.function_tracer_pcode.validation.unknown_reason_summary import (
    RESULT_JSON_BEGIN,
    RESULT_JSON_END,
)


def _payload(function_name, is_equivalent, **extra):
    payload = {
        "function1_name": function_name,
        "function2_name": function_name,
        "binary1_name": "sample-B1",
        "binary2_name": "sample-B2",
        "is_equivalent": is_equivalent,
        "error_message": None,
        "unknown_reasons": [],
    }
    payload.update(extra)
    return payload


def _write_log(root: Path, function_name: str, left: str, right: str, payload):
    function_dir = root / function_name
    function_dir.mkdir(parents=True, exist_ok=True)
    path = function_dir / f"{function_name}_{left}_{right}.log"
    path.write_text(
        "\n".join(
            [
                "Result: UNKNOWN" if payload["is_equivalent"] is None else "Result: EQUIVALENT",
                RESULT_JSON_BEGIN,
                json.dumps(payload),
                RESULT_JSON_END,
            ]
        )
    )
    return path


def test_freeze_observed_baseline_writes_manifest_hashes_and_recovered_manifests(tmp_path):
    source_root = tmp_path / "logs" / "function_call_test"
    _write_log(
        source_root,
        "fc_apply_indirect",
        "B2",
        "B1",
        _payload(
            "fc_apply_indirect",
            None,
            unknown_reasons=[
                make_unknown_reason(UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY).to_dict()
            ],
        ),
    )
    _write_log(
        source_root,
        "fc_equiv_direct",
        "B1",
        "B2",
        _payload("fc_equiv_direct", True),
    )

    output_root = tmp_path / "artifacts" / "observed"
    manifest_path = freeze_observed_baseline(
        baseline_id="observed-v0@0a53352",
        git_head="0a53352",
        output_root=output_root,
        source_roots={"function_call": source_root},
        runner_commands=("VALIDATION_BEFORE_DIR=<fixed observed baseline>",),
        workspace_root=Path.cwd(),
    )

    manifest = json.loads(manifest_path.read_text())
    recovered = json.loads(
        (output_root / "raw" / manifest["recovered_manifests"]["function_call"]).read_text()
    )
    copied_log = output_root / "raw" / "logs" / "function_call" / "fc_apply_indirect" / "fc_apply_indirect_B2_B1.log"

    assert manifest["baseline_id"] == "observed-v0@0a53352"
    assert manifest["git_head"].startswith("0a53352")
    assert manifest["dirty_state"]["dirty_snapshot_hash"]
    assert manifest["source_paths"][0]["category"] == "function_call"
    assert copied_log.is_file()
    assert str(copied_log.relative_to(output_root / "raw")) in manifest["file_content_hashes"]
    assert recovered["category"] == "function_call"
    assert [entry["function"] for entry in recovered["functions"]] == [
        "fc_apply_indirect",
        "fc_equiv_direct",
    ]
    assert recovered["functions"][0]["binary_pairs"] == ["B1_B2"]


def test_freeze_observed_baseline_records_untracked_hashes_and_git_policy(tmp_path):
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    subprocess.run(["git", "init"], cwd=workspace, check=True, capture_output=True)
    untracked = workspace / "pyrightconfig.json"
    untracked.write_text('{"typeCheckingMode":"basic"}\n')

    source_root = tmp_path / "logs" / "function_call_test"
    _write_log(source_root, "fc_equiv_direct", "B1", "B2", _payload("fc_equiv_direct", True))
    output_root = tmp_path / "artifacts" / "observed"

    manifest_path = freeze_observed_baseline(
        baseline_id="observed-v0@0a53352",
        git_head="HEAD",
        output_root=output_root,
        source_roots={"function_call": source_root},
        workspace_root=workspace,
    )

    manifest = json.loads(manifest_path.read_text())
    state = manifest["dirty_state"]
    untracked_hashes = json.loads(
        (output_root / "raw" / state["untracked_file_hashes_path"]).read_text()
    )

    assert manifest["artifact_storage"]["raw_evidence_git_policy"] == "external_not_committed"
    assert manifest["artifact_storage"]["raw_evidence_hash_index_path"] == "file_hashes.json"
    assert state["untracked_file_hashes_path"] == "workspace_state/untracked_file_hashes.json"
    assert untracked_hashes == {
        "pyrightconfig.json": hashlib.sha256(untracked.read_bytes()).hexdigest()
    }


def test_freeze_observed_baseline_refuses_to_overwrite_existing_raw_dir(tmp_path):
    source_root = tmp_path / "logs" / "function_call_test"
    _write_log(source_root, "fc_equiv_direct", "B1", "B2", _payload("fc_equiv_direct", True))
    output_root = tmp_path / "artifacts" / "observed"

    freeze_observed_baseline(
        baseline_id="observed-v0@0a53352",
        git_head="0a53352",
        output_root=output_root,
        source_roots={"function_call": source_root},
        workspace_root=Path.cwd(),
    )

    with pytest.raises(FileExistsError):
        freeze_observed_baseline(
            baseline_id="observed-v0@0a53352",
            git_head="0a53352",
            output_root=output_root,
            source_roots={"function_call": source_root},
            workspace_root=Path.cwd(),
        )


def test_freeze_observed_baseline_module_execution(tmp_path):
    source_root = tmp_path / "logs" / "function_call_test"
    _write_log(source_root, "fc_equiv_direct", "B1", "B2", _payload("fc_equiv_direct", True))
    output_root = tmp_path / "artifacts" / "observed"

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.function_tracer_pcode.validation.freeze_observed_baseline",
            "--baseline-id",
            "observed-v0@0a53352",
            "--git-head",
            "0a53352",
            "--output-root",
            str(output_root),
            "--source",
            f"function_call={source_root}",
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    assert "artifact_manifest.json" in result.stdout
    assert (output_root / "raw" / "artifact_manifest.json").is_file()

import json
import hashlib
from pathlib import Path
import subprocess

import pytest

from scripts.function_tracer_pcode.equivalence.v2.pair_status_authority import (
    PAIR_STATUS_PUBLIC_KEY_FILE, generate_pair_status_keypair, seal_pair_status,
)
from scripts.function_tracer_pcode.equivalence.v2.contracts import authority_digest
from scripts.function_tracer_pcode.validation.eqbench_build_receipt import (
    build_receipt, validate_receipt as validate_build_receipt,
)
from scripts.function_tracer_pcode.validation import eqbench_build_receipt
from scripts.function_tracer_pcode.validation.execution_identity import (
    build_pair_execution_target, sha256_file, source_tree_digest,
)
from scripts.function_tracer_pcode.validation.execution_receipt import (
    MATRIX_EXECUTION_RECEIPT_FILE, MATRIX_PUBLICATION_MANIFEST_FILE,
    analysis_config_from_run, build_matrix_publication_manifest, main as receipt_main,
    seal_execution_receipt, validate_execution_receipt,
    validate_matrix_publication_manifest,
)
from scripts.function_tracer_pcode.validation.phase10_publication_allowlist import (
    build_publication_allowlist, validate_publication_allowlist,
    validate_staged_index,
)
from scripts.function_tracer_pcode.validation.phase10_validation_manifest import (
    build_manifest, validate_full_eqbench_scope, validate_manifest,
)


def _run(repo, *args):
    subprocess.run(args, cwd=repo, check=True, stdout=subprocess.PIPE)


def _fixture_repo(tmp_path, *, skipped=False):
    repo = tmp_path / "repo"
    (repo / "scripts/function_tracer_pcode").mkdir(parents=True)
    for path, text in (
        (".gitignore", "targets/\n"),
        ("eqbench_run_all_32jobs.sh", "#!/bin/sh\n"),
        ("requirements-test.txt", "pytest\n"),
        ("scripts/validation_matrix_common.sh", "#!/bin/sh\n"),
        ("scripts/eqbench/compile_all_arm_mips.sh", "#!/bin/sh\n"),
        ("scripts/function_tracer_pcode/module.py", "VALUE = 1\n"),
    ):
        (repo / path).parent.mkdir(parents=True, exist_ok=True)
        (repo / path).write_text(text)
    _run(repo, "git", "init", "-q")
    _run(repo, "git", "config", "user.email", "phase10@example.invalid")
    _run(repo, "git", "config", "user.name", "Phase 10 Test")
    _run(repo, "git", "add", ".")
    _run(repo, "git", "commit", "-qm", "fixture")

    junit = Path("artifacts/unknown_taxonomy_v2/phase10/full-unit.xml")
    (repo / junit).parent.mkdir(parents=True)
    (repo / junit).write_text('<testsuites><testsuite tests="1" failures="0" errors="0" skipped="0" time="0.1" /></testsuites>')
    validation_private = tmp_path / "validation.key"
    validation_public = repo / "artifacts/unknown_taxonomy_v2/phase10/validation-verification-key.json"
    generate_pair_status_keypair(validation_private, validation_public)
    source_digest = source_tree_digest(repo)
    junit_receipt = Path("artifacts/unknown_taxonomy_v2/phase10/full-unit.execution-receipt.json")
    (repo / junit_receipt).write_text(json.dumps(seal_execution_receipt(
        execution_kind="FULL_UNIT_JUNIT", command=["pytest", "-q"],
        source_digest_start=source_digest, source_digest_end=source_digest,
        analysis_config_digest="full-unit", exit_status=0,
        artifacts={junit.as_posix(): sha256_file(repo / junit)},
        private_key_path=validation_private, public_key_path=validation_public,
    )))

    matrix = Path("artifacts/unknown_taxonomy_v2/phase10/matrix")
    root = repo / matrix
    relative = Path("sample/Eq/newV/client/client_B1_B2")
    (root / relative).parent.mkdir(parents=True)
    source = repo / "targets/sample/Eq/newV.c"
    left = repo / "targets/sample/Eq/source/newV-arm64-clang-O0"
    right = repo / "targets/sample/Eq/source/newV-arm64-clang-O1"
    for path, data in ((source, b"int client(void){return 1;}"), (left, b"left"), (right, b"right")):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    analysis_config = {
        "schema": "eqbench-analysis-config-v1",
        "authority_kind": "EqBenchAnalysisConfig",
        "run_scope": "REPRESENTATIVE",
        "build_policy": "REUSE_OR_COMPILE",
        "max_samples": 0,
        "sample_filter": "sample",
        "pair_filter": "B1_B2",
        "debug": False,
        "skip_completed_results": skipped,
        "dry_run": False,
        "parallel_jobs": 1,
        "validation_summary_level": "compact",
        "equiv_timeout_seconds": "10",
        "decompile_timeout_seconds": "60",
        "pairwise_timeout_seconds": "5",
        "pairwise_timeout_hard_seconds": "30",
        "pair_process_timeout_seconds": "600",
        "pair_process_kill_after_seconds": "30",
        "prefilter_source_census_digest": hashlib.sha256(b"sample/Eq/newV.c\n").hexdigest(),
    }
    config_digest = authority_digest(analysis_config)
    target = build_pair_execution_target(
        repo, sample_identity="sample/Eq/newV",
        output_sample_relative_path="sample/Eq/newV", function_name="client",
        left_binary_id="B1", right_binary_id="B2", source_path=source,
        left_binary_path=left, right_binary_path=right,
        analysis_source_digest=source_digest, analysis_config_digest=config_digest,
    )
    prefilter_rows = ["sample/Eq/newV.c"]
    prefilter_digest = hashlib.sha256(b"sample/Eq/newV.c\n").hexdigest()
    run_text = (
        "run_scope=REPRESENTATIVE\nbuild_policy=REUSE_OR_COMPILE\nprefilter_source_count=1\n"
        f"prefilter_source_census_digest={prefilter_digest}\nmax_samples=0\n"
        "target_sources=1\ncompleted_samples=1\nskipped_samples=0\ndry_run=0\n"
        f"total_functions=1\ntotal_pair_jobs=1\ntotal_scheduled_pair_jobs={0 if skipped else 1}\n"
        f"total_skipped_pair_jobs={1 if skipped else 0}\nexpected_pairs_per_function=120\n"
        "expected_binary_count=2\ncompiled_binary_count=2\ncompile_failure_count=0\n"
        "missing_binary_count=0\nfunction_census_failure_count=0\nrun_pair_failures=0\n"
        f"analysis_config_digest={config_digest}\nanalysis_source_digest_start={source_digest}\n"
        f"analysis_source_digest_end={source_digest}\nsample_filter=sample\npair_filter=B1_B2\n"
        f"debug=0\nskip_completed_results={1 if skipped else 0}\nparallel_jobs=1\n"
        "validation_summary_level=compact\nequiv_timeout=10\ndecompile_timeout=60\n"
        "pairwise_timeout=5\npairwise_timeout_hard=30\n"
        "pair_process_timeout_seconds=600\npair_process_kill_after_seconds=30\n"
    )
    (root / "run_manifest.txt").write_text(run_text)
    (root / "prefilter_source_paths.txt").write_text("\n".join(prefilter_rows) + "\n")
    (root / "compile_failure_samples.txt").write_text("")
    (root / "missing_binary_axes.txt").write_text("")
    (root / "function_census_failures.txt").write_text("")
    build = build_receipt(
        repo, sample_identity="sample/Eq/newV", source_path=source,
        compile_script_path=repo / "scripts/eqbench/compile_all_arm_mips.sh",
        binary_root=left.parent, target_binary_root=left.parent,
        binary_ids=("B1", "B2"), provenance_kind="ADOPTED_PREBUILT",
    )
    (root / "used_build_receipts.jsonl").write_text(json.dumps(build) + "\n")
    (root / "overall_summary.txt").write_text("TOTAL: 1\n")
    (root / "run_health_summary.json").write_text(json.dumps({
        "final_result_counts": {"EQ": 1, "NOT_EQ": 0, "UNKNOWN": 0, "TIMEOUT": 0, "ERROR": 0, "INCOMPLETE": 0},
        "total_results": 1, "functions": {"client": {"total": 1}},
        "error_kind_counts": {"<none>": 1}, "child_returncode_counts": {"0": 1},
        "supervisor_status_counts": {"RESOLVED": 1},
    }))
    status_relative = relative.with_suffix(".pair-status.json").as_posix()
    (root / "expected_pair_status_paths.txt").write_text(status_relative + "\n")
    (root / "verified_skipped_pair_status_paths.txt").write_text(status_relative + "\n" if skipped else "")
    (root / relative.with_suffix(".log")).write_text("Result: EQUIVALENT\n")
    private = tmp_path / "pair.key"
    public = root / PAIR_STATUS_PUBLIC_KEY_FILE
    generate_pair_status_keypair(private, public)
    digest = "a" * 64
    body = {
        "authority_kind": "SupervisorCanonicalResultResolvedReceipt", "supervisor_authority_kind": "SupervisorCanonicalResultResolvedReceipt",
        "supervisor_final_authority_digest": digest, "launch_receipt_digest": digest,
        "canonical_outcome": "EQUIVALENT", "decision_receipt_digest": digest,
        "result_occurrence_id": "occurrence", "result_entry_occurrence_receipt_digest": digest,
        "execution_identity_digest": digest, "execution_nonce": "nonce", "stream_id": "stream",
        "source_snapshot_fingerprint": digest, "canonical_result_bundle_digest": digest,
        "canonical_result_bundle_kind": "CanonicalResultFinalizationBundle",
        "canonical_result_payload_preimage_digest": digest, "semantic_projection_digest": digest,
        "error_kind": None, "child_returncode": 0, "supervisor_status": "RESOLVED",
        "supervisor_projection_digest": digest, "classification_valid": True,
        "pair_execution_target": target,
    }
    (root / relative.with_suffix(".pair-status.json")).write_text(json.dumps(seal_pair_status(body, private_key_path=private, public_key_path=public)))
    (root / MATRIX_PUBLICATION_MANIFEST_FILE).write_text(json.dumps(
        build_matrix_publication_manifest(root)
    ))
    artifacts = {name: sha256_file(root / name) for name in (
        MATRIX_PUBLICATION_MANIFEST_FILE, "run_health_summary.json",
    )}
    (root / MATRIX_EXECUTION_RECEIPT_FILE).write_text(json.dumps(seal_execution_receipt(
        execution_kind="EQBENCH_MATRIX", command=["./eqbench_run_all_32jobs.sh"],
        source_digest_start=source_digest, source_digest_end=source_digest,
        analysis_config_digest=config_digest, exit_status=0, artifacts=artifacts,
        private_key_path=private, public_key_path=public,
    )))
    return repo, junit, junit_receipt, matrix


def _build(repo, junit, receipt, matrix):
    return build_manifest(repo, junit_path=junit, junit_receipt_path=receipt, matrix_paths=(matrix,), commands=("pytest -q",))


def test_phase10_manifest_binds_current_source_and_accepts_verified_resume(tmp_path):
    repo, junit, receipt, matrix = _fixture_repo(tmp_path, skipped=True)
    manifest = _build(repo, junit, receipt, matrix)
    validate_manifest(repo, manifest)
    assert manifest["matrices"][0]["completion_counters"]["total_skipped_pair_jobs"] == 1
    assert manifest["completion_eligible"] is False


def test_phase10_completion_rejects_representative_matrix(tmp_path):
    repo, junit, receipt, matrix = _fixture_repo(tmp_path)
    with pytest.raises(ValueError, match="requires FULL_EQBENCH"):
        build_manifest(
            repo, junit_path=junit, junit_receipt_path=receipt,
            matrix_paths=(matrix,), commands=("pytest -q",),
            root_purpose="PHASE10_COMPLETION",
        )


def test_full_scope_rejects_max_samples_or_filters(tmp_path):
    repo, _, _, matrix = _fixture_repo(tmp_path)
    publication = dict(build_matrix_publication_manifest(repo / matrix))
    config = dict(publication["analysis_config"])
    config.update({"run_scope": "FULL_EQBENCH", "max_samples": 1})
    publication.update({"run_scope": "FULL_EQBENCH", "analysis_config": config})
    expectation = {
        "expected_source_count": 1,
        "expected_binary_ids": [f"B{index}" for index in range(1, 17)],
        "expected_pairs_per_function": 120,
        "source_paths": ["sample/Eq/newV.c"],
        "expected_functions": {"sample/Eq/newV.c": ["client"]},
    }
    with pytest.raises(ValueError, match="scope authority is incomplete"):
        validate_full_eqbench_scope(publication, expectation)


def test_analysis_config_accepts_full_neq_scope():
    config = analysis_config_from_run({
        "run_scope": "FULL_NEQ",
        "build_policy": "REUSE_OR_COMPILE",
        "max_samples": "0",
        "sample_filter": "",
        "pair_filter": "",
        "debug": "0",
        "skip_completed_results": "1",
        "dry_run": "0",
        "parallel_jobs": "1",
        "validation_summary_level": "compact",
        "equiv_timeout": "10",
        "decompile_timeout": "60",
        "pairwise_timeout": "5",
        "pairwise_timeout_hard": "30",
        "pair_process_timeout_seconds": "600",
        "pair_process_kill_after_seconds": "30",
        "prefilter_source_census_digest": "a" * 64,
    })
    assert config["run_scope"] == "FULL_NEQ"


def test_phase10_manifest_rejects_pair_status_copy_to_another_target(tmp_path):
    repo, junit, receipt, matrix = _fixture_repo(tmp_path)
    root = repo / matrix
    source = next(root.rglob("*.pair-status.json"))
    copied = source.with_name("client_B1_B3.pair-status.json")
    copied.write_bytes(source.read_bytes())
    with pytest.raises(ValueError, match="signed pair target differs|expected pair identity"):
        _build(repo, junit, receipt, matrix)


def test_phase10_manifest_rejects_source_change_without_execution(tmp_path):
    repo, junit, receipt, matrix = _fixture_repo(tmp_path)
    (repo / "scripts/function_tracer_pcode/module.py").write_text("VALUE = 2\n")
    with pytest.raises(ValueError, match="source digest"):
        _build(repo, junit, receipt, matrix)


def test_phase10_manifest_rejects_publishable_secret_key(tmp_path):
    repo, junit, receipt, matrix = _fixture_repo(tmp_path)
    (repo / "artifacts/unknown_taxonomy_v2/phase10/leaked.key").write_bytes(b"secret")
    with pytest.raises(ValueError, match="contains secret keys"):
        _build(repo, junit, receipt, matrix)


def test_phase10_manifest_remains_valid_after_source_preserving_commit(tmp_path):
    repo, junit, receipt, matrix = _fixture_repo(tmp_path)
    manifest = _build(repo, junit, receipt, matrix)
    # Publishing evidence changes HEAD and removes the dirty/untracked state,
    # but does not change the canonical source tree.
    _run(repo, "git", "add", "artifacts")
    _run(repo, "git", "commit", "-qm", "publish evidence")
    validate_manifest(repo, manifest)


def test_phase10_manifest_does_not_require_diagnostic_txt_or_pair_log(tmp_path):
    repo, junit, receipt, matrix = _fixture_repo(tmp_path)
    manifest = _build(repo, junit, receipt, matrix)
    root = repo / matrix
    for path in (
        root / "run_manifest.txt", root / "overall_summary.txt",
        root / "expected_pair_status_paths.txt",
        root / "verified_skipped_pair_status_paths.txt",
        next(root.rglob("*.log")),
    ):
        path.unlink()
    validate_manifest(repo, manifest)


def test_phase10_manifest_rejects_failed_matrix_execution_receipt(tmp_path):
    repo, junit, receipt, matrix = _fixture_repo(tmp_path)
    root = repo / matrix
    public = root / PAIR_STATUS_PUBLIC_KEY_FILE
    # Fixture private key is outside the repository by construction.
    private = tmp_path / "pair.key"
    artifacts = {name: sha256_file(root / name) for name in (
        MATRIX_PUBLICATION_MANIFEST_FILE, "run_health_summary.json",
    )}
    failed = seal_execution_receipt(
        execution_kind="EQBENCH_MATRIX", command=["./eqbench_run_all_32jobs.sh"],
        source_digest_start=source_tree_digest(repo),
        source_digest_end=source_tree_digest(repo),
        analysis_config_digest="config", exit_status=1, artifacts=artifacts,
        private_key_path=private, public_key_path=public,
    )
    (root / MATRIX_EXECUTION_RECEIPT_FILE).write_text(json.dumps(failed))
    with pytest.raises(ValueError, match="does not join"):
        _build(repo, junit, receipt, matrix)


def test_matrix_receipt_normalizes_command_and_signs_actual_exit(tmp_path):
    repo, _, _, matrix = _fixture_repo(tmp_path)
    root = repo / matrix
    output = root / MATRIX_EXECUTION_RECEIPT_FILE
    assert receipt_main([
        "--repo-root", str(repo), "--private-key", str(tmp_path / "pair.key"),
        "--public-key", str(root / PAIR_STATUS_PUBLIC_KEY_FILE),
        "--output", str(output), "--matrix-root", str(root),
        "--source-digest-start", source_tree_digest(repo),
        "--analysis-config-digest", "config", "--exit-status", "1",
        "--", "env", "PARALLEL_JOBS=2", "./eqbench_run_all_32jobs.sh",
    ]) == 0
    body = validate_execution_receipt(
        json.loads(output.read_text()),
        public_key_path=root / PAIR_STATUS_PUBLIC_KEY_FILE,
    )
    assert body["exit_status"] == 1
    assert body["command"] == [
        "env", "PARALLEL_JOBS=2", "./eqbench_run_all_32jobs.sh",
    ]


def test_compile_failure_is_signed_without_green_health_artifact(tmp_path):
    repo, _, _, matrix = _fixture_repo(tmp_path)
    root = repo / matrix
    manifest_path = root / "run_manifest.txt"
    run = manifest_path.read_text()
    run = run.replace("completed_samples=1", "completed_samples=0")
    run = run.replace("compiled_binary_count=2", "compiled_binary_count=1")
    run = run.replace("compile_failure_count=0", "compile_failure_count=1")
    run = run.replace("missing_binary_count=0", "missing_binary_count=1")
    run = run.replace("run_pair_failures=0", "run_pair_failures=1")
    manifest_path.write_text(run)
    (root / "compile_failure_samples.txt").write_text("sample/Eq/newV\n")
    (root / "missing_binary_axes.txt").write_text("sample/Eq/newV/B16\n")
    (root / "run_health_summary.json").unlink()
    output = root / MATRIX_EXECUTION_RECEIPT_FILE
    assert receipt_main([
        "--repo-root", str(repo), "--private-key", str(tmp_path / "pair.key"),
        "--public-key", str(root / PAIR_STATUS_PUBLIC_KEY_FILE),
        "--output", str(output), "--matrix-root", str(root),
        "--source-digest-start", source_tree_digest(repo),
        "--analysis-config-digest", "config", "--exit-status", "1",
        "--", "env", "EQBENCH_RUN_SCOPE=FULL_EQBENCH",
        "./eqbench_run_all_32jobs.sh",
    ]) == 0
    body = validate_execution_receipt(
        json.loads(output.read_text()), public_key_path=root / PAIR_STATUS_PUBLIC_KEY_FILE,
    )
    assert body["exit_status"] == 1
    assert set(body["artifact_sha256"]) == {MATRIX_PUBLICATION_MANIFEST_FILE}


def test_publication_allowlist_is_exact_and_excludes_internal_diagnostics(tmp_path):
    repo, junit, receipt, matrix = _fixture_repo(tmp_path)
    validation_root = Path("artifacts/unknown_taxonomy_v2/phase10/root.json")
    (repo / validation_root).write_text(json.dumps(_build(repo, junit, receipt, matrix)))
    checkpoint = repo / matrix / ".process-authority/checkpoint.json"
    checkpoint.parent.mkdir()
    checkpoint.write_text("{}")
    allowlist = build_publication_allowlist(
        repo, validation_root_path=validation_root,
        allowlist_path=Path("artifacts/unknown_taxonomy_v2/phase10/allowlist.json"),
    )
    serialized = json.loads(json.dumps(allowlist))
    validate_publication_allowlist(repo, serialized)
    paths = {row["path"] for row in serialized["artifacts"]}
    assert validation_root.as_posix() in paths
    assert any(path.endswith("client_B1_B2.pair-status.json") for path in paths)
    assert any(path.endswith("newV-arm64-clang-O0") for path in paths)
    assert not any(".process-authority" in path for path in paths)
    assert not any(path.endswith((".txt", ".log", ".key")) for path in paths)
    assert set(serialized["force_add_paths"]) == {
        "targets/sample/Eq/newV.c",
        "targets/sample/Eq/source/newV-arm64-clang-O0",
        "targets/sample/Eq/source/newV-arm64-clang-O1",
    }
    assert serialized["self_path"] in serialized["regular_add_paths"]


def test_publication_staged_index_requires_allowlist_self_and_exact_blobs(tmp_path):
    repo, junit, receipt, matrix = _fixture_repo(tmp_path)
    validation_root = Path("artifacts/unknown_taxonomy_v2/phase10/root.json")
    allowlist_path = Path("artifacts/unknown_taxonomy_v2/phase10/allowlist.json")
    (repo / validation_root).write_text(json.dumps(_build(repo, junit, receipt, matrix)))
    payload = build_publication_allowlist(
        repo, validation_root_path=validation_root, allowlist_path=allowlist_path,
    )
    (repo / allowlist_path).write_text(json.dumps(payload, sort_keys=True))
    for path in payload["regular_add_paths"]:
        _run(repo, "git", "add", "--", path)
    for path in payload["force_add_paths"]:
        _run(repo, "git", "add", "-f", "--", path)
    validate_staged_index(repo, payload)
    extra = repo / "artifacts/unknown_taxonomy_v2/phase10/old-attempt.json"
    extra.write_text("{}")
    _run(repo, "git", "add", "--", extra.relative_to(repo).as_posix())
    with pytest.raises(ValueError, match="paths differ"):
        validate_staged_index(repo, payload)


def test_runner_full_scope_and_compile_freshness_contracts_are_explicit():
    runner = Path("eqbench_run_all_32jobs.sh").read_text(encoding="utf-8")
    assert 'EQBENCH_RUN_SCOPE="${EQBENCH_RUN_SCOPE:-REPRESENTATIVE}"' in runner
    assert 'EQBENCH_BUILD_POLICY="${EQBENCH_BUILD_POLICY:-REUSE_OR_COMPILE}"' in runner
    assert 'fresh-builds/$TOTAL_SAMPLES' in runner
    assert 'existing binaries were not moved' in runner
    assert 'EQBENCH_MAX_SAMPLES=$EQBENCH_MAX_SAMPLES' in runner
    assert "stale-binaries" not in runner
    assert 'mv -- "$binary_path"' not in runner


def test_neq_runner_emits_typed_matrix_receipt_inputs():
    runner = Path("neqbench_run_all_32jobs.sh").read_text(encoding="utf-8")
    assert 'default_value NEQ_RUN_SCOPE FULL_NEQ' in runner
    assert 'pair_selected "N_${a}_O_${b}"' in runner
    for field in (
        "max_samples", "sample_filter", "pair_filter", "debug",
        "skip_completed_results", "validation_summary_level", "dry_run",
        "prefilter_source_count", "prefilter_source_census_digest",
        "target_sources", "completed_samples", "total_functions",
        "expected_binary_count", "compiled_binary_count",
        "compile_failure_count", "missing_binary_count",
        "function_census_failure_count", "run_pair_failures",
        "analysis_source_digest_end",
    ):
        assert f"{field}=" in runner
    for artifact in (
        "prefilter_source_paths.txt", "compile_failure_samples.txt",
        "missing_binary_axes.txt", "function_census_failures.txt",
        "used_build_receipts.jsonl", "run_health_summary.json",
        "verified_skipped_pair_status_paths.txt",
    ):
        assert artifact in runner


def test_adopted_prebuilt_receipt_is_hash_bound_but_not_full_authority(tmp_path):
    repo, _, _, matrix = _fixture_repo(tmp_path)
    publication = build_matrix_publication_manifest(repo / matrix)
    receipt = publication["build_receipts"][0]
    validate_build_receipt(
        receipt, repo_root=repo, required_binary_ids=("B1", "B2"),
    )
    with pytest.raises(ValueError, match="body is invalid"):
        validate_build_receipt(
            receipt, repo_root=repo, required_binary_ids=("B1", "B2"),
            require_fresh=True,
        )
    binary = repo / receipt["binary_axes"][0]["binary_path"]
    binary.write_bytes(b"tampered")
    with pytest.raises(ValueError, match="axis drifted"):
        validate_build_receipt(
            receipt, repo_root=repo, required_binary_ids=("B1", "B2"),
        )


def test_analysis_config_digest_rejects_debug_or_resume_tamper(tmp_path):
    repo, _, _, matrix = _fixture_repo(tmp_path)
    publication = dict(build_matrix_publication_manifest(repo / matrix))
    config = dict(publication["analysis_config"])
    config["debug"] = not config["debug"]
    publication["analysis_config"] = config
    body = {key: publication[key] for key in publication if key != "artifact_digest"}
    publication["artifact_digest"] = authority_digest(body)
    with pytest.raises(ValueError, match="body is invalid"):
        validate_matrix_publication_manifest(publication)


def test_fresh_build_receipt_carries_toolchain_and_exact_argv(tmp_path, monkeypatch):
    repo, _, _, matrix = _fixture_repo(tmp_path)
    original = build_matrix_publication_manifest(repo / matrix)["build_receipts"][0]
    monkeypatch.setattr(eqbench_build_receipt, "_toolchain_identity", lambda executable, fresh: {
        "executable_requested": executable,
        "identity_status": "RESOLVED",
        "resolved_path": f"/toolchains/{executable}",
        "executable_sha256": "a" * 64,
        "version_argv": [executable, "--version"],
        "version_stdout_sha256": "b" * 64,
    })
    source = repo / original["source_path"]
    binary_root = (repo / original["binary_axes"][0]["binary_path"]).parent
    fresh = build_receipt(
        repo, sample_identity="sample/Eq/newV", source_path=source,
        compile_script_path=repo / original["compile_script_path"],
        binary_root=binary_root, target_binary_root=binary_root,
        binary_ids=("B1", "B2"), provenance_kind="FRESH_COMPILE",
    )
    validate_build_receipt(
        fresh, repo_root=repo, required_binary_ids=("B1", "B2"),
        require_fresh=True,
    )
    assert fresh["binary_axes"][0]["compiler_argv"] == [
        "clang", "--target=aarch64-linux-gnu", "-march=armv8-a", "-O0",
        "-c", "newV.c", "-o", "newV-arm64-clang-O0",
    ]

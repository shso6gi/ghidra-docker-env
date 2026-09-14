import json
import re
from pathlib import Path

from scripts.eqbench.error_rerun_manifest import (
    collect,
    expected_pair_execution_identity,
    read_manifest,
    sample_filter_regex,
    validate_rerun_pair_outcome,
    validate_rerun_pair_target,
    validate_rerun_publication_contract,
)


def test_error_rerun_manifest_collects_exact_eq_and_neq_targets(tmp_path: Path):
    eq_root = tmp_path / "eq"
    neq_root = tmp_path / "neq"
    eq_log = eq_root / "CLEVER/Add/Eq/newV/foo/foo_B1_B2.log"
    neq_log = neq_root / "REVE/addhorn/Neq/newV-oldV/f/f_N_B5_O_B5.log"
    clean_log = eq_root / "CLEVER/Add/Eq/newV/foo/foo_B1_B3.log"
    for path, outcome in (
        (eq_log, "ERROR"), (neq_log, "ERROR"), (clean_log, "EQUIVALENT")
    ):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"Result: {outcome}\n", encoding="utf-8")

    assert collect(eq_root, "EQ") == {
        ("EQ", "CLEVER/Add/Eq/newV", "foo", "B1_B2")
    }
    assert collect(neq_root, "NEQ") == {
        ("NEQ", "REVE/addhorn/Neq/newV-oldV", "f", "N_B5_O_B5")
    }


def test_error_rerun_manifest_rejects_duplicate_targets(tmp_path: Path):
    manifest = tmp_path / "manifest.tsv"
    row = "EQ\tCLEVER/Add/Eq/newV\tfoo\tB1_B2\n"
    manifest.write_text(row + row, encoding="utf-8")

    try:
        read_manifest(manifest)
    except ValueError as exc:
        assert "duplicate" in str(exc)
    else:
        raise AssertionError("duplicate rerun targets were accepted")


def test_summary_includes_error_before_canonical_result_was_written(tmp_path: Path):
    root = tmp_path / "neq"
    directory = root / "CLEVER/sample/Neq/new-old/foo"
    directory.mkdir(parents=True)
    (directory / "foo_N_B1_O_B2.log").write_text(
        "TypeError: Object of type Receipt is not JSON serializable\n"
    )
    (directory / "foo_N_B2_O_B1.log").write_text("Result: UNKNOWN\n")
    (directory / "results_summary.txt").write_text(
        "--- Results for foo ---\n\n"
        "  ERROR pairs:\n"
        "    - B1 ↔ B2\n\n"
        "  UNKNOWN pairs:\n"
        "    - B2 ↔ B1\n"
    )

    assert collect(root, "NEQ") == {
        ("NEQ", "CLEVER/sample/Neq/new-old", "foo", "N_B1_O_B2")
    }


def test_fatal_error_after_result_is_not_hidden_by_stale_summary(tmp_path: Path):
    root = tmp_path / "neq"
    directory = root / "REVE/limit1/Neq/newV-oldV/f"
    directory.mkdir(parents=True)
    (directory / "f_N_B3_O_B1.log").write_text(
        "Result: UNKNOWN\n"
        "TypeError: Object of type SolverQueryExecutionReceipt is not JSON serializable\n"
    )
    (directory / "results_summary.txt").write_text(
        "--- Results for f ---\n\n  UNKNOWN pairs:\n    - B3 ↔ B1\n"
    )

    assert collect(root, "NEQ") == {
        ("NEQ", "REVE/limit1/Neq/newV-oldV", "f", "N_B3_O_B1")
    }


def test_operational_logs_never_enter_pair_target_parser(tmp_path: Path):
    root = tmp_path / "eq"
    root.mkdir()
    (root / "run_stdout.log").write_text(
        "supervisor projection is not a terminal authority\n",
        encoding="utf-8",
    )
    (root / "compile_all.log").write_text(
        "SAT model does not completely bind declared replay inputs\n",
        encoding="utf-8",
    )

    assert collect(root, "EQ") == set()


def test_stale_summary_does_not_hide_unlisted_canonical_error(tmp_path: Path):
    root = tmp_path / "neq"
    directory = root / "CLEVER/sample/Neq/new-old/foo"
    directory.mkdir(parents=True)
    (directory / "foo_N_B1_O_B2.log").write_text(
        "Result: ERROR\nError kind: NEW_FAILURE_KIND\n",
        encoding="utf-8",
    )
    (directory / "results_summary.txt").write_text(
        "--- Results for foo ---\n\n  UNKNOWN pairs:\n    - B1 ↔ B2\n",
        encoding="utf-8",
    )

    assert collect(root, "NEQ") == {
        ("NEQ", "CLEVER/sample/Neq/new-old", "foo", "N_B1_O_B2")
    }


def test_rerun_publication_requires_current_run_and_exact_scheduled_set():
    rows = [("EQ", "sample", "foo", "B1_B2")]
    publication = {
        "analysis_source_digest_start": "source",
        "analysis_source_digest_end": "source",
        "analysis_config_digest": "config",
        "total_pair_jobs": 1,
        "total_scheduled_pair_jobs": 1,
        "total_skipped_pair_jobs": 0,
        "expected_pair_status_paths": ["sample/foo/foo_B1_B2.pair-status.json"],
        "verified_skipped_pair_status_paths": [],
    }
    execution = {
        "execution_kind": "EQBENCH_MATRIX",
        "exit_status": 0,
        "source_tree_digest_start": "source",
        "source_tree_digest_end": "source",
        "analysis_config_digest": "config",
        "command": [
            "ERROR_RERUN_MANIFEST_SHA256=manifest",
            "ERROR_RERUN_RUN_ID=run-current",
            "SKIP_COMPLETED_RESULTS=0",
        ],
    }

    assert validate_rerun_publication_contract(
        rows=rows, publication=publication, execution=execution,
        manifest_digest="manifest", run_id="run-current",
    ) == ("source", "config")

    stale = {**execution, "command": [
        "ERROR_RERUN_MANIFEST_SHA256=manifest",
        "ERROR_RERUN_RUN_ID=run-old",
        "SKIP_COMPLETED_RESULTS=0",
    ]}
    try:
        validate_rerun_publication_contract(
            rows=rows, publication=publication, execution=stale,
            manifest_digest="manifest", run_id="run-current",
        )
    except ValueError as exc:
        assert "exact scheduled target set" in str(exc)
    else:
        raise AssertionError("a stale rerun receipt was accepted")


def test_error_only_publication_accepts_exact_pair_level_schedule_and_skip_partition():
    rows = [
        ("NEQ", "sample", "foo", "N_B1_O_B1"),
        ("NEQ", "sample", "foo", "N_B1_O_B2"),
    ]
    paths = [
        "sample/foo/foo_N_B1_O_B1.pair-status.json",
        "sample/foo/foo_N_B1_O_B2.pair-status.json",
    ]
    publication = {
        "analysis_source_digest_start": "source",
        "analysis_source_digest_end": "source",
        "analysis_config_digest": "config",
        "total_pair_jobs": 2,
        "total_scheduled_pair_jobs": 1,
        "total_skipped_pair_jobs": 1,
        "expected_pair_status_paths": paths,
        "verified_skipped_pair_status_paths": [paths[0]],
    }
    execution = {
        "execution_kind": "EQBENCH_MATRIX",
        "exit_status": 0,
        "source_tree_digest_start": "source",
        "source_tree_digest_end": "source",
        "analysis_config_digest": "config",
        "command": [
            "ERROR_RERUN_MANIFEST_SHA256=manifest",
            "ERROR_RERUN_RUN_ID=run-current",
            "SKIP_COMPLETED_RESULTS=1",
            "ERROR_ONLY_RERUN=1",
        ],
    }
    assert validate_rerun_publication_contract(
        rows=rows, publication=publication, execution=execution,
        manifest_digest="manifest", run_id="run-current",
    ) == ("source", "config")


def test_sample_filter_translates_manifest_identity_for_each_runner():
    rows = [
        ("EQ", "caldat/flmoon/Eq/newV", "flmoon", "B11_B12"),
        ("NEQ", "REVE/addhorn/Neq/newV-oldV", "addhorn", "N_B5_O_B5"),
    ]

    eq_filter = sample_filter_regex(rows, "EQ")
    assert re.search(
        eq_filter,
        "/workspace/targets/EqBench/benchmarks/caldat/flmoon/Eq/newV.c",
    )
    assert not re.search(eq_filter, "caldat/flmoon/Eq/newV")
    neq_filter = sample_filter_regex(rows, "NEQ")
    assert re.search(neq_filter, "REVE/addhorn/Neq/newV-oldV")
    assert not re.search(neq_filter, "/root/REVE/addhorn/Neq/newV-oldV")


def test_signed_supervisor_timeout_accepts_missing_or_plain_log_projection():
    body = {
        "canonical_outcome": "TIMEOUT",
        "supervisor_status": "TIMEOUT",
    }

    assert validate_rerun_pair_outcome("", body) == "TIMEOUT"
    assert validate_rerun_pair_outcome("Result: TIMEOUT\n", body) == "TIMEOUT"


def test_signed_supervisor_timeout_rejects_contradictory_log_projection():
    body = {
        "canonical_outcome": "TIMEOUT",
        "supervisor_status": "TIMEOUT",
    }

    try:
        validate_rerun_pair_outcome("Result: UNKNOWN\n", body)
    except ValueError as exc:
        assert "outcomes differ" in str(exc)
    else:
        raise AssertionError("signed TIMEOUT accepted a contradictory log result")


def test_resolved_status_cannot_use_noncanonical_plain_log_projection():
    body = {
        "canonical_outcome": "UNKNOWN",
        "supervisor_status": "RESOLVED",
    }

    try:
        validate_rerun_pair_outcome("Result: UNKNOWN\n", body)
    except ValueError as exc:
        assert "INCOMPLETE" in str(exc)
    else:
        raise AssertionError("resolved status accepted a noncanonical log projection")


def test_manifest_row_derives_exact_eq_and_neq_execution_identities():
    assert expected_pair_execution_identity(
        ("EQ", "caldat/flmoon/Eq/newV", "flmoon", "B11_B12")
    ) == {
        "sample_identity": "caldat/flmoon/Eq/newV",
        "output_sample_relative_path": "caldat/flmoon/Eq/newV",
        "function_name": "flmoon",
        "left_binary_id": "B11",
        "right_binary_id": "B12",
    }
    assert expected_pair_execution_identity(
        ("NEQ", "REVE/addhorn/Neq/newV-oldV", "f", "N_B5_O_B5")
    ) == {
        "sample_identity": "REVE/addhorn/Neq/newV-oldV",
        "output_sample_relative_path": "REVE/addhorn/Neq/newV-oldV",
        "function_name": "f",
        "left_binary_id": "N_B5",
        "right_binary_id": "O_B5",
    }


def test_copied_signed_status_cannot_satisfy_another_manifest_row():
    row = ("NEQ", "REVE/addhorn/Neq/newV-oldV", "f", "N_B5_O_B5")
    body = {
        "pair_execution_target": {
            "sample_identity": "REVE/barthe/Neq/newV-oldV",
            "output_sample_relative_path": "REVE/barthe/Neq/newV-oldV",
            "function_name": "f",
            "left_binary_id": "N_B16",
            "right_binary_id": "O_B14",
            "analysis_source_digest": "source",
            "analysis_config_digest": "config",
        },
    }

    try:
        validate_rerun_pair_target(
            row, body, source_digest="source", config_digest="config",
        )
    except ValueError as exc:
        assert "identity differs" in str(exc)
    else:
        raise AssertionError("a copied signed status satisfied another manifest row")


def test_pair_target_joins_manifest_identity_and_run_digests():
    row = ("EQ", "caldat/flmoon/Eq/newV", "flmoon", "B11_B12")
    body = {
        "pair_execution_target": {
            **expected_pair_execution_identity(row),
            "analysis_source_digest": "source",
            "analysis_config_digest": "config",
        },
    }

    validate_rerun_pair_target(
        row, body, source_digest="source", config_digest="config",
    )


# --- Issue #125 PR-125-B: typed failure の ERROR が再実行対象に入ること ---------
#
# PR-125-A が足した 3 つの `failure_status` は、いずれも ERROR 結果として
# 出力される。`error_rerun_manifest` は実装を変えずにこれらを拾うはずなので、
# その振る舞いを consumer 側で固定する（実装が ERROR 判定を狭めたら落ちる）。

ISSUE125_FAILURE_STATUSES = (
    "internal_exception",
    "unregistered_reason",
    "limitation_unattributed",
)

#: PR-125-A 以前から ERROR になっていた `failure_status`（回帰防止）。
LEGACY_FAILURE_STATUSES = ("strategy_exception", "legacy_compatibility_error")


def _error_result_log(path: Path, failure_status: str) -> None:
    payload = {
        "function1_name": path.parent.name,
        "function2_name": path.parent.name,
        "binary1_name": "B1",
        "binary2_name": "B2",
        "is_equivalent": None,
        "error_message": f"{failure_status}: analysis failed",
        "failure_status": failure_status,
        "diagnostics": {
            "schema": "result-diagnostics-v1",
            "failures": {
                "swallowed_exceptions": {"total": 0, "by_site": []},
                "internal_exception": {
                    "exception_type": "RuntimeError",
                    "site": "checker.checker.EquivalenceChecker.check",
                    "stack": ["Traceback (most recent call last):"],
                    "stack_digest": "0" * 64,
                },
            },
        },
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "\n".join(
            (
                "=== EQUIVALENCE_RESULT_JSON_BEGIN ===",
                json.dumps(payload),
                "=== EQUIVALENCE_RESULT_JSON_END ===",
                "Result: ERROR",
            )
        )
        + "\n",
        encoding="utf-8",
    )


def test_issue125_failure_statuses_become_eq_rerun_targets(tmp_path: Path):
    root = tmp_path / "eq"
    directory = root / "CLEVER/Add/Eq/newV/foo"
    expected = set()
    for index, status in enumerate(ISSUE125_FAILURE_STATUSES):
        pair = f"B1_B{index + 2}"
        _error_result_log(directory / f"foo_{pair}.log", status)
        expected.add(("EQ", "CLEVER/Add/Eq/newV", "foo", pair))
    # 判定が出た pair は再実行対象にしない。
    (directory / "foo_B1_B9.log").write_text("Result: UNKNOWN\n", encoding="utf-8")

    assert collect(root, "EQ") == expected


def test_issue125_failure_statuses_become_neq_rerun_targets(tmp_path: Path):
    root = tmp_path / "neq"
    directory = root / "REVE/addhorn/Neq/newV-oldV/f"
    expected = set()
    for index, status in enumerate(ISSUE125_FAILURE_STATUSES):
        pair = f"N_B{index + 1}_O_B{index + 1}"
        _error_result_log(directory / f"f_{pair}.log", status)
        expected.add(("NEQ", "REVE/addhorn/Neq/newV-oldV", "f", pair))

    assert collect(root, "NEQ") == expected


def test_existing_error_statuses_still_rerun_alongside_the_new_ones(tmp_path: Path):
    """既存 ERROR の振る舞いを新 status が壊していないこと。"""

    root = tmp_path / "eq"
    directory = root / "CLEVER/Add/Eq/newV/foo"
    expected = set()
    for index, status in enumerate(LEGACY_FAILURE_STATUSES + ISSUE125_FAILURE_STATUSES):
        pair = f"B1_B{index + 2}"
        _error_result_log(directory / f"foo_{pair}.log", status)
        expected.add(("EQ", "CLEVER/Add/Eq/newV", "foo", pair))
    # 素の `Result: ERROR` 行（payload 無し）と fatal marker も従来どおり拾う。
    (directory / "foo_B7_B8.log").write_text("Result: ERROR\n", encoding="utf-8")
    expected.add(("EQ", "CLEVER/Add/Eq/newV", "foo", "B7_B8"))
    (directory / "foo_B7_B9.log").write_text(
        "Result: UNKNOWN\n"
        "TypeError: Object of type SolverQueryExecutionReceipt is not JSON serializable\n",
        encoding="utf-8",
    )
    expected.add(("EQ", "CLEVER/Add/Eq/newV", "foo", "B7_B9"))
    (directory / "foo_B7_B10.log").write_text("Result: EQUIVALENT\n", encoding="utf-8")

    assert collect(root, "EQ") == expected


def test_issue125_failure_statuses_classify_as_error(tmp_path: Path):
    """`collect` が使う分類器そのものの契約。"""

    from scripts.function_tracer_pcode.reporting.result_summary import classify_log_text

    directory = tmp_path / "eq/CLEVER/Add/Eq/newV/foo"
    for status in ISSUE125_FAILURE_STATUSES:
        log = directory / f"foo_B1_B2_{status}.log"
        _error_result_log(log, status)
        text = log.read_text(encoding="utf-8")
        assert classify_log_text(text, matrix_context=True) == "ERROR"

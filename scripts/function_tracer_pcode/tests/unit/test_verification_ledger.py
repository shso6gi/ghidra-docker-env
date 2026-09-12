# -*- coding: utf-8 -*-
"""Issue #123 / PR-123-B: verification ledger の契約。

固定するのは「言えないことを言わせない」性質:

* `requested_scope`（依頼した範囲）と `completed_scope`（実際に検証できた範囲）を
  別々に持ち、単一の bool へ潰さない。
* `coverage` は publication manifest が期待する pair と実在する pair から出す。
  未実行・再利用・payload 無しを「確認済み」に数えない。
* `code_matches_head` は provenance からのみ決まり、commit 不明 / dirty / 別 commit
  を「HEAD を検証済み」と表示しない。`stale_code` は「現 HEAD の証拠ではない」の意で、
  run が無効という意味ではない。
* 3 軸（正解確認 / 遷移 / gate）は独立した counter で、1 個の PASS に畳まない。

source 文字列の grep ではなく、実際に row を作って表示させて確かめる。
"""

import json
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.reporting import outcome_transition, verification_ledger
from scripts.function_tracer_pcode.reporting.execution_receipt import (
    MATRIX_PUBLICATION_SCHEMA,
)
from scripts.function_tracer_pcode.reporting.execution_identity import (
    GIT_DIRTY_NO,
    GIT_DIRTY_UNKNOWN,
    GIT_DIRTY_YES,
    GIT_STATE_UNAVAILABLE,
)

HEAD = "a" * 40
OTHER_COMMIT = "b" * 40
EQ_SAMPLE = "CLEVER/LoopSub/Eq/new"
NEQ_SAMPLE = "CLEVER/LoopSub/Neq/new-old"


def _head_state(commit=HEAD, dirty=GIT_DIRTY_NO):
    return {"commit": commit, "dirty": dirty, "dirty_files": (), "dirty_files_digest": "d"}


def write_pair(tree: Path, sample: str, function: str, left: str, right: str,
               outcome: str, *, reasons=None, payload: bool = True) -> str:
    """1 pair の status（と、必要なら result payload を含む log）を置く。"""
    directory = tree / sample / function
    directory.mkdir(parents=True, exist_ok=True)
    name = f"{function}_{left}_{right}"
    (directory / f"{name}.pair-status.json").write_text(
        json.dumps({
            "canonical_outcome": outcome,
            "pair_execution_target": {
                "sample_identity": sample, "function_name": function,
                "left_binary_id": left, "right_binary_id": right,
            },
        }),
        encoding="utf-8",
    )
    log = directory / f"{name}.log"
    if payload:
        body = json.dumps({
            "unknown_reasons": [{"reason_id": value} for value in (reasons or ())],
            "diagnostics": {},
        })
        log.write_text(
            "=== EQUIVALENCE_RESULT_JSON_BEGIN ===\n"
            f"{body}\n"
            "=== EQUIVALENCE_RESULT_JSON_END ===\n",
            encoding="utf-8",
        )
    else:
        # 240s wall-clock kill 相当: status は在るが result payload が無い。
        log.write_text("killed before the result was emitted\n", encoding="utf-8")
    return f"{sample}/{function}/{name}.pair-status.json"


def write_publication_manifest(tree: Path, expected, skipped=(), *, schema=None) -> None:
    """完成度判定が読む 3 key（schema と 2 つの census）を持つ manifest。"""
    tree.mkdir(parents=True, exist_ok=True)
    (tree / outcome_transition.PUBLICATION_MANIFEST_FILE).write_text(
        json.dumps({
            "schema": MATRIX_PUBLICATION_SCHEMA if schema is None else schema,
            "expected_pair_status_paths": list(expected),
            "verified_skipped_pair_status_paths": list(skipped),
        }),
        encoding="utf-8",
    )


def write_ground_truth(tree: Path, functions) -> None:
    (tree / "function_diff_manifest.json").write_text(
        json.dumps({
            "schema": "eqbench-function-diff-manifest-v1",
            "samples": {
                sample: {
                    "parse_status": "ok",
                    "functions": {
                        name: {
                            "source_relation": relation,
                            "source_impact": impact,
                            "semantic_ground_truth": truth,
                            "ground_truth_evidence": "reviewed",
                        },
                    },
                }
                for sample, name, relation, impact, truth in functions
            },
        }),
        encoding="utf-8",
    )


def write_run_manifest(tree: Path, **fields) -> None:
    tree.mkdir(parents=True, exist_ok=True)
    (tree / "run_manifest.txt").write_text(
        "".join(f"{key}={value}\n" for key, value in fields.items()), encoding="utf-8",
    )


def write_subset_manifest(run_dir: Path, **fields) -> None:
    run_dir.mkdir(parents=True, exist_ok=True)
    (run_dir / "subset_manifest.txt").write_text(
        "".join(f"{key}={value}\n" for key, value in fields.items()), encoding="utf-8",
    )


@pytest.fixture()
def subset_run(tmp_path):
    """eq/neq 両半分を持つ最小の subset run（すべて期待どおり揃っている）。"""
    def build(name, *, commit=HEAD, dirty=GIT_DIRTY_NO, eq_outcomes=None,
              neq_outcomes=None, reasons=None, skipped=()):
        run_dir = tmp_path / name
        expected = {}
        for half, outcomes, sample in (
            ("eq", eq_outcomes or [("f", "B1", "B2", "EQUIVALENT")], EQ_SAMPLE),
            ("neq", neq_outcomes or [("g", "N_B1", "O_B1", "NOT_EQ")], NEQ_SAMPLE),
        ):
            tree = run_dir / half
            paths = [
                write_pair(
                    tree, sample, function, left, right, outcome,
                    reasons=(reasons or {}).get((half, function, left, right), ()),
                    payload=outcome != "TIMEOUT",
                )
                for function, left, right, outcome in outcomes
            ]
            expected[half] = paths
            write_publication_manifest(tree, paths, skipped.get(half, ()) if isinstance(skipped, dict) else skipped)
            write_run_manifest(
                tree, git_commit=commit, git_dirty=dirty,
                analysis_source_digest_start="s", analysis_source_digest_end="s",
                analysis_config_digest="c",
            )
            write_ground_truth(tree, [
                (NEQ_SAMPLE, "g", "changed", "MAY_AFFECT", "UNKNOWN"),
            ])
        write_subset_manifest(
            run_dir, scope="all", manifest_sha256="m",
            git_commit=commit, git_dirty=dirty, git_dirty_files_digest="d",
            start_time_utc="2026-01-01T00:00:00Z", end_time_utc="2026-01-01T00:10:00Z",
            hostname="host", elapsed_seconds="600", exit_status="0",
        )
        return run_dir
    return build


# ---------------------------------------------------------------------------
# requested_scope / completed_scope / coverage
# ---------------------------------------------------------------------------


def test_ledger_row_has_requested_and_completed_scope_and_coverage(subset_run):
    """依頼した範囲と検証できた範囲を別々に保持し、bool へ縮退させない。"""
    row = verification_ledger.build_row(subset_run("run"), requested_scope="subset")

    assert row["requested_scope"] == "subset"
    assert row["completed_scope"] == outcome_transition.COMPLETENESS_COMPLETE
    assert row["coverage"]["pairs_expected"] == 2
    assert row["coverage"]["pairs_with_status"] == 2
    assert row["coverage"]["pairs_missing"] == 0
    # 単一の bool へ潰していないこと（full/partial を 1 個の flag で表さない）。
    assert "full_evaluation" not in row
    assert not any(isinstance(value, bool) for key, value in row.items()
                   if key in ("requested_scope", "completed_scope"))


def test_requested_scope_full_does_not_make_a_partial_run_complete(subset_run):
    """full を「依頼」しても、実際に取れた範囲が partial なら partial のまま。"""
    run_dir = subset_run("run")
    (run_dir / "eq" / EQ_SAMPLE / "f" / "f_B1_B2.pair-status.json").unlink()

    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")

    assert row["requested_scope"] == "full_eq"
    assert row["completed_scope"] == outcome_transition.COMPLETENESS_PARTIAL
    assert row["coverage"]["pairs_missing"] == 1
    assert row["coverage"]["pairs_with_status"] == 1


def test_manifest_completeness_is_fail_closed_without_a_manifest(subset_run):
    """publication manifest が無い tree は complete ではなく unknown。"""
    run_dir = subset_run("run")
    (run_dir / "neq" / outcome_transition.PUBLICATION_MANIFEST_FILE).unlink()

    row = verification_ledger.build_row(run_dir, requested_scope="subset")

    assert row["completed_scope"] == outcome_transition.COMPLETENESS_UNKNOWN
    assert "matrix-publication-manifest.json" in row["completed_scope_detail"]


def test_reused_pairs_are_not_counted_as_executed_by_this_run(subset_run):
    """verified-skipped は「今回走らせていない」ので complete にしない。"""
    run_dir = subset_run("run", skipped={"eq": [f"{EQ_SAMPLE}/f/f_B1_B2.pair-status.json"], "neq": []})

    row = verification_ledger.build_row(run_dir, requested_scope="subset")

    assert row["completed_scope"] == outcome_transition.COMPLETENESS_PARTIAL
    assert row["coverage"]["pairs_verified_skipped"] == 1
    assert "reused" in row["completed_scope_detail"]


def test_empty_tree_is_never_complete(tmp_path):
    """pair を 1 つも期待しない run を「全部できた」と言わない。"""
    run_dir = tmp_path / "empty"
    for half in ("eq", "neq"):
        write_publication_manifest(run_dir / half, [])
    write_subset_manifest(run_dir, scope="all")

    row = verification_ledger.build_row(run_dir, requested_scope="subset")

    assert row["completed_scope"] == outcome_transition.COMPLETENESS_UNKNOWN
    assert row["coverage"]["pairs_expected"] == 0


def test_pairs_without_a_result_payload_are_counted_as_incomparable(subset_run):
    """payload 無し pair は coverage 上で別建て（「確認済み」に混ぜない）。"""
    run_dir = subset_run(
        "run", eq_outcomes=[("f", "B1", "B2", "TIMEOUT")],
    )

    row = verification_ledger.build_row(run_dir, requested_scope="subset")

    assert row["coverage"]["pairs_incomparable"] == 1
    assert row["coverage"]["pairs_with_status"] == 2


# ---------------------------------------------------------------------------
# code_matches_head / stale_code
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "commit,dirty,head,expected",
    [
        (HEAD, GIT_DIRTY_NO, _head_state(), verification_ledger.HEAD_MATCH_YES),
        (OTHER_COMMIT, GIT_DIRTY_NO, _head_state(), verification_ledger.HEAD_MATCH_NO),
        (HEAD, GIT_DIRTY_YES, _head_state(), verification_ledger.HEAD_MATCH_NO),
        (HEAD, GIT_DIRTY_UNKNOWN, _head_state(), verification_ledger.HEAD_MATCH_UNKNOWN),
        (verification_ledger.UNSET, GIT_DIRTY_NO, _head_state(), verification_ledger.HEAD_MATCH_UNKNOWN),
        (GIT_STATE_UNAVAILABLE, GIT_DIRTY_NO, _head_state(), verification_ledger.HEAD_MATCH_UNKNOWN),
        (HEAD, GIT_DIRTY_NO, _head_state(commit=GIT_STATE_UNAVAILABLE),
         verification_ledger.HEAD_MATCH_UNKNOWN),
        (HEAD, GIT_DIRTY_NO, _head_state(dirty=GIT_DIRTY_YES), verification_ledger.HEAD_MATCH_NO),
    ],
)
def test_code_matches_head_never_claims_head_without_provenance(commit, dirty, head, expected):
    row = {"provenance": {"commit": commit, "dirty": dirty}}
    assert verification_ledger.head_match(row, head)[0] == expected


def test_ledger_list_marks_stale_code_and_never_claims_head_coverage(tmp_path, subset_run):
    """別 commit の full row を「HEAD の全件検証」として表示しない。"""
    ledger = tmp_path / "ledger.jsonl"
    stale_full = verification_ledger.build_row(
        subset_run("full", commit=OTHER_COMMIT), requested_scope="full_eq",
    )
    verification_ledger.append_row(ledger, stale_full)
    verification_ledger.append_row(ledger, verification_ledger.build_row(
        subset_run("later", commit=HEAD), requested_scope="subset",
    ))

    listing = verification_ledger.format_listing(
        verification_ledger.read_rows(ledger), _head_state(), ledger_path=ledger,
    )

    assert "stale_code" in listing
    assert "code_matches_head=no" in listing
    assert "full_eq: NO" in listing and "full_neq: NO" in listing
    assert "Subset verification is not full verification" in listing


def test_ledger_list_reports_a_full_run_at_head_as_evaluated(tmp_path, subset_run):
    """逆向きの固定: 現 HEAD の complete な full row は YES と出る。"""
    ledger = tmp_path / "ledger.jsonl"
    for scope in ("full_eq", "full_neq"):
        verification_ledger.append_row(ledger, verification_ledger.build_row(
            subset_run(f"run_{scope}", commit=HEAD), requested_scope=scope,
        ))

    listing = verification_ledger.format_listing(
        verification_ledger.read_rows(ledger), _head_state(), ledger_path=ledger,
    )

    assert "full_eq: YES" in listing and "full_neq: YES" in listing
    assert "Subset verification is not full verification" not in listing


def test_a_subset_only_ledger_never_prints_full_verified(tmp_path, subset_run):
    ledger = tmp_path / "ledger.jsonl"
    for name in ("a", "b", "c"):
        verification_ledger.append_row(ledger, verification_ledger.build_row(
            subset_run(name, commit=HEAD), requested_scope="subset",
        ))

    listing = verification_ledger.format_listing(
        verification_ledger.read_rows(ledger), _head_state(), ledger_path=ledger,
    )

    assert "full_eq: (none recorded)" in listing
    assert "full_eq: NO" in listing and "full_neq: NO" in listing
    assert "full verified" not in listing.lower()


def test_a_run_without_provenance_is_recorded_without_crashing(tmp_path):
    """PR #150 以前の run（provenance field 無し）でも unknown 側へ倒れる。"""
    run_dir = tmp_path / "old"
    path = write_pair(run_dir / "eq", EQ_SAMPLE, "f", "B1", "B2", "UNKNOWN")
    write_publication_manifest(run_dir / "eq", [path])
    write_subset_manifest(run_dir, scope="eq")

    row = verification_ledger.build_row(run_dir, requested_scope="subset")

    assert row["provenance"]["commit"] == verification_ledger.UNSET
    assert row["provenance"]["dirty"] == verification_ledger.UNSET
    assert verification_ledger.head_match(row, _head_state())[0] == (
        verification_ledger.HEAD_MATCH_UNKNOWN
    )
    listing = verification_ledger.format_listing(
        (row,), _head_state(), ledger_path=tmp_path / "ledger.jsonl",
    )
    assert "stale_code" in listing


def test_an_unrecognised_run_directory_is_recorded_as_unknown(tmp_path):
    """manifest も half も無い directory で crash せず unknown を残す。"""
    run_dir = tmp_path / "bare"
    run_dir.mkdir()

    row = verification_ledger.build_row(run_dir, requested_scope="focused")

    assert row["run_layout"] == verification_ledger.LAYOUT_UNRECOGNISED
    assert row["completed_scope"] == outcome_transition.COMPLETENESS_UNKNOWN


def test_an_unparsable_ledger_line_does_not_hide_the_rest(tmp_path, subset_run):
    ledger = tmp_path / "ledger.jsonl"
    ledger.write_text("not json\n", encoding="utf-8")
    verification_ledger.append_row(ledger, verification_ledger.build_row(
        subset_run("run"), requested_scope="subset",
    ))

    listing = verification_ledger.format_listing(
        verification_ledger.read_rows(ledger), _head_state(), ledger_path=ledger,
    )

    assert "1 unreadable" in listing
    assert "requested_scope=subset" in listing


def test_record_appends_one_line_per_run(tmp_path, subset_run):
    ledger = tmp_path / "ledger.jsonl"
    run_dir = subset_run("run")
    for _ in range(2):
        assert verification_ledger.main([
            "--ledger", str(ledger), "record", "--run-dir", str(run_dir),
            "--requested-scope", "subset",
        ]) == 0
    assert len(ledger.read_text(encoding="utf-8").strip().splitlines()) == 2


def test_record_refuses_a_missing_run_directory(tmp_path):
    assert verification_ledger.main([
        "--ledger", str(tmp_path / "ledger.jsonl"), "record",
        "--run-dir", str(tmp_path / "nope"), "--requested-scope", "subset",
    ]) == 1


# ---------------------------------------------------------------------------
# eqbench_run_subset.sh との結合
#
# 台帳への記録は pair 判定のあと・既存 artifact 生成のあとに走り、失敗しても
# run の exit status を変えない。実 script をそのまま起動して確かめる
# (EQBENCH_ROOT を空にしてあるので runner は即座に失敗し、pair は 1 つも走らない)。
# ---------------------------------------------------------------------------

REPO_ROOT = Path(__file__).resolve().parents[4]
SUBSET_SH = REPO_ROOT / "eqbench_run_subset.sh"


def _run_subset_script(tmp_path, *, ledger, output_name):
    import os
    import subprocess

    output_dir = tmp_path / output_name
    environment = dict(os.environ)
    environment.update({
        "OUTPUT_BASE_DIR": str(output_dir),
        "SUBSET_SCOPE": "eq",
        "VERIFICATION_LEDGER": str(ledger),
        "EQBENCH_ROOT": str(tmp_path / "empty-eqbench-root"),
        "NEQ_ROOT": str(tmp_path / "empty-eqbench-root"),
        "EQBENCH_TMPDIR": str(tmp_path / "runner-tmp"),
        "EQBENCH_BUILD_POLICY": "PREBUILT_ONLY",
        "EQBENCH_RESOURCE_ADMISSION": "0",
        "PARALLEL_JOBS": "1",
    })
    (tmp_path / "empty-eqbench-root").mkdir(exist_ok=True)
    completed = subprocess.run(
        ["bash", str(SUBSET_SH)], cwd=REPO_ROOT, env=environment, timeout=300,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    return completed, output_dir


@pytest.mark.skipif(not SUBSET_SH.is_file(), reason="the subset runner is not present")
def test_ledger_record_failure_does_not_change_exit_status(tmp_path):
    """記録できない台帳でも run の exit status は記録できたときと同じ。"""
    working = tmp_path / "ledger.jsonl"
    ok_run, ok_dir = _run_subset_script(tmp_path, ledger=working, output_name="ok")

    # 親が通常ファイルなので台帳への追記は必ず失敗する。
    blocked_parent = tmp_path / "blocked"
    blocked_parent.write_text("not a directory\n", encoding="utf-8")
    failing_run, failing_dir = _run_subset_script(
        tmp_path, ledger=blocked_parent / "ledger.jsonl", output_name="failing",
    )

    assert failing_run.returncode == ok_run.returncode
    ok_manifest = read_key_value_manifest_text(ok_dir / "subset_manifest.txt")
    failing_manifest = read_key_value_manifest_text(failing_dir / "subset_manifest.txt")
    assert ok_manifest["ledger_record_status"] == "0"
    assert failing_manifest["ledger_record_status"] != "0"
    # 失敗は診断として見える形で残る（黙って消えない）。
    assert "ledger" in failing_run.stderr.decode().lower()
    assert (failing_dir / "verification_ledger_record.txt").is_file()
    # 記録できた側は実際に 1 行増えている。
    assert len(working.read_text(encoding="utf-8").strip().splitlines()) == 1


@pytest.mark.skipif(not SUBSET_SH.is_file(), reason="the subset runner is not present")
def test_ledger_record_runs_after_the_existing_artifacts(tmp_path):
    """既存の soundness / manifest 出力を壊さず、そのあとに記録する。"""
    ledger = tmp_path / "ledger.jsonl"
    _completed, output_dir = _run_subset_script(tmp_path, ledger=ledger, output_name="run")

    manifest = read_key_value_manifest_text(output_dir / "subset_manifest.txt")
    assert (output_dir / "soundness_gate.txt").is_file()
    assert manifest["ledger_path"] == str(ledger)
    # PR-123-A の provenance 行が残っていること。
    for key in ("git_commit", "git_dirty", "start_time_utc", "hostname", "exit_status"):
        assert key in manifest
    row = json.loads(ledger.read_text(encoding="utf-8").strip())
    assert row["requested_scope"] == "subset"
    assert row["run_dir"] == str(output_dir)


def read_key_value_manifest_text(path: Path):
    return verification_ledger.read_key_value_manifest(path)


def test_the_runners_literal_none_is_not_recorded_as_a_reference(tmp_path, subset_run):
    """runner が書く `issue=none` を issue 番号として持ち回らない。"""
    run_dir = subset_run("run")
    manifest = run_dir / "subset_manifest.txt"
    manifest.write_text(
        manifest.read_text(encoding="utf-8") + "issue=none\npr=none\n", encoding="utf-8",
    )

    row = verification_ledger.build_row(run_dir, requested_scope="subset")
    named = verification_ledger.build_row(run_dir, requested_scope="subset", issue="123")

    assert row["issue"] is None and row["pr"] is None
    assert named["issue"] == "123"

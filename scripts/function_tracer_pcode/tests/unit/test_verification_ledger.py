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
import shutil
from pathlib import Path

import pytest

from scripts.function_tracer_pcode.reporting import outcome_transition, verification_ledger
from scripts.function_tracer_pcode.authority.contracts import authority_digest
from scripts.function_tracer_pcode.reporting import execution_receipt
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


def write_publication_manifest(
    tree: Path, expected, skipped=(), *, schema=None, run_scope=None,
) -> None:
    """完成度判定が読む 3 key（schema と 2 つの census）を持つ manifest。

    `run_scope` を渡すと、full scope の裏付けに使う側の field も一緒に書く。
    """
    tree.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema": MATRIX_PUBLICATION_SCHEMA if schema is None else schema,
        "expected_pair_status_paths": list(expected),
        "verified_skipped_pair_status_paths": list(skipped),
    }
    if run_scope is not None:
        payload["run_scope"] = run_scope
        payload["analysis_config"] = {
            "run_scope": run_scope, "sample_filter": "", "pair_filter": "",
            "max_samples": 0,
        }
    (tree / outcome_transition.PUBLICATION_MANIFEST_FILE).write_text(
        json.dumps(payload), encoding="utf-8",
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


def build_formal_publication_manifest(run_dir: Path, expected_paths, *, run_scope,
                                      sample_filter="", pair_filter="",
                                      max_samples="0", commit=HEAD,
                                      dirty=GIT_DIRTY_NO) -> dict:
    """本番の builder で publication artifact を作る（schema を test に複製しない）。

    `execution_receipt.build_matrix_publication_manifest()` は run_manifest.txt と
    census file 群から canonical body を組み立て、`analysis_config_digest` /
    `artifact_digest` まで計算する。fixture がこれを使うことで、正式 schema が
    変わっても test 側が古い形のまま drift しない。
    """
    run_dir.mkdir(parents=True, exist_ok=True)
    prefilter = [f"targets/EqBench/benchmarks/sample{index}.c"
                 for index in range(1, 4)]
    run_manifest = {
        "run_kind": "eqbench_all_eq_matrix_current",
        "run_scope": run_scope,
        "build_policy": "PREBUILT_ONLY",
        "max_samples": max_samples,
        "sample_filter": sample_filter,
        "pair_filter": pair_filter,
        "debug": "0",
        "dry_run": "0",
        "parallel_jobs": "20",
        "validation_summary_level": "compact",
        "equiv_timeout": "10",
        "decompile_timeout": "60",
        "pairwise_timeout": "5",
        "pairwise_timeout_hard": "30",
        "pair_process_timeout_seconds": "240",
        "pair_process_kill_after_seconds": "30",
        "prefilter_source_census_digest": execution_receipt._source_census_digest(prefilter),
        "prefilter_source_count": str(len(prefilter)),
        "target_sources": str(len(prefilter)),
        "completed_samples": str(len(prefilter)),
        "skipped_samples": "0",
        "total_functions": "1",
        "total_pair_jobs": str(len(expected_paths)),
        "total_scheduled_pair_jobs": str(len(expected_paths)),
        "total_skipped_pair_jobs": "0",
        "expected_pairs_per_function": str(len(expected_paths)),
        "expected_binary_count": "16",
        "compiled_binary_count": "16",
        "compile_failure_count": "0",
        "missing_binary_count": "0",
        "function_census_failure_count": "0",
        "run_pair_failures": "0",
        "analysis_source_digest_start": "s" * 8,
        "analysis_source_digest_end": "s" * 8,
        "git_commit": commit,
        "git_dirty": dirty,
        "git_dirty_files_digest": "d" * 8,
        "manifest_sha256": "m" * 8,
        "start_time_utc": "2026-01-01T00:00:00Z",
        "end_time_utc": "2026-01-02T00:00:00Z",
        "hostname": "host",
    }
    config = execution_receipt.analysis_config_from_run(run_manifest)
    run_manifest["analysis_config_digest"] = authority_digest(config)
    (run_dir / "run_manifest.txt").write_text(
        "".join(f"{key}={value}\n" for key, value in run_manifest.items()),
        encoding="utf-8",
    )
    for name, rows in (
        ("prefilter_source_paths.txt", prefilter),
        ("compile_failure_samples.txt", []),
        ("missing_binary_axes.txt", []),
        ("function_census_failures.txt", []),
        ("expected_pair_status_paths.txt", list(expected_paths)),
        ("verified_skipped_pair_status_paths.txt", []),
    ):
        (run_dir / name).write_text(
            "".join(f"{row}\n" for row in rows), encoding="utf-8",
        )
    (run_dir / "used_build_receipts.jsonl").write_text("", encoding="utf-8")
    payload = execution_receipt.build_matrix_publication_manifest(run_dir)
    # fixture が本当に正式 artifact であることを、ここでも実際に確かめる。
    execution_receipt.validate_matrix_publication_manifest(payload)
    (run_dir / outcome_transition.PUBLICATION_MANIFEST_FILE).write_text(
        json.dumps(payload, sort_keys=True), encoding="utf-8",
    )
    return dict(payload)


@pytest.fixture()
def full_run(tmp_path):
    """正式 publication contract を満たす whole-benchmark run。

    subset run とは layout も declared run_scope も filter も違う。full verdict は
    この形の artifact からしか作れないことを、fixture 自身が
    `validate_matrix_publication_manifest()` を通して保証する。
    `mutate` で出来上がった artifact を壊し、fail-closed を behavior で確かめる。
    """
    def build(name, *, scope="full_eq", commit=HEAD, dirty=GIT_DIRTY_NO,
              sample_filter="", pair_filter="", max_samples="0",
              run_scope=None, run_manifest_scope=None, outcomes=None,
              with_publication=True, mutate=None):
        run_dir = tmp_path / name
        declared = run_scope or verification_ledger.RUN_SCOPE_BY_FULL_SCOPE.get(scope, scope)
        sample = EQ_SAMPLE if declared == "FULL_EQBENCH" else NEQ_SAMPLE
        paths = [
            write_pair(run_dir, sample, function, left, right, outcome)
            for function, left, right, outcome in (
                outcomes or [("f", "B1", "B2", "EQUIVALENT")]
            )
        ]
        payload = build_formal_publication_manifest(
            run_dir, paths, run_scope=declared, sample_filter=sample_filter,
            pair_filter=pair_filter, max_samples=max_samples, commit=commit,
            dirty=dirty,
        )
        if run_manifest_scope is not None:
            # run_manifest だけ別の（あるいは欠けた）run_scope にする。
            manifest = run_dir / "run_manifest.txt"
            rows = [
                line for line in manifest.read_text(encoding="utf-8").splitlines()
                if not line.startswith("run_scope=")
            ]
            if run_manifest_scope != "":
                rows.insert(1, f"run_scope={run_manifest_scope}")
            manifest.write_text("".join(f"{row}\n" for row in rows), encoding="utf-8")
        published = run_dir / outcome_transition.PUBLICATION_MANIFEST_FILE
        if not with_publication:
            published.unlink()
        elif mutate is not None:
            broken = mutate(dict(payload))
            if broken is None:
                published.unlink()
            else:
                published.write_text(json.dumps(broken, sort_keys=True), encoding="utf-8")
        write_ground_truth(run_dir, [(NEQ_SAMPLE, "g", "changed", "MAY_AFFECT", "UNKNOWN")])
        return run_dir
    return build


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


def test_a_valid_full_run_backed_by_its_artifacts_is_reported_as_evaluated(
    tmp_path, full_run,
):
    """逆向きの固定: artifact が full scope を裏付ける run だけ YES になる。"""
    ledger = tmp_path / "ledger.jsonl"
    for scope in ("full_eq", "full_neq"):
        verification_ledger.append_row(ledger, verification_ledger.build_row(
            full_run(f"run_{scope}", scope=scope), requested_scope=scope,
        ))

    listing = verification_ledger.format_listing(
        verification_ledger.read_rows(ledger), _head_state(), ledger_path=ledger,
    )

    assert "full_eq: YES" in listing and "full_neq: YES" in listing
    assert "Subset verification is not full verification" not in listing


@pytest.mark.parametrize("scope", ["full_eq", "full_neq"])
def test_a_subset_layout_is_never_full_verification_however_it_is_requested(
    tmp_path, subset_run, scope,
):
    """blocker: subset run に full_eq/full_neq を指定しても full と認めない。"""
    ledger = tmp_path / "ledger.jsonl"
    row = verification_ledger.build_row(
        subset_run("run", commit=HEAD), requested_scope=scope,
    )
    verification_ledger.append_row(ledger, row)

    # requested_scope は保持するが、それ自体は証拠にならない。
    assert row["requested_scope"] == scope
    assert row["completed_scope"] == outcome_transition.COMPLETENESS_COMPLETE
    assert verification_ledger.head_match(row, _head_state())[0] == (
        verification_ledger.HEAD_MATCH_YES
    )
    evidence, reason = verification_ledger.full_scope_evidence(row)
    assert evidence is None and "matrix tree" in reason

    listing = verification_ledger.format_listing(
        verification_ledger.read_rows(ledger), _head_state(), ledger_path=ledger,
    )
    assert f"{scope}: YES" not in listing
    assert "full_eq: NO" in listing and "full_neq: NO" in listing
    assert "Subset verification is not full verification" in listing


def test_requested_scope_alone_never_produces_a_full_verdict(tmp_path, full_run):
    """裏付けの各条件を 1 つずつ壊すと full と認めなくなる。"""
    cases = {
        # filter が掛かっていれば、宣言が FULL でも全件ではない
        "narrowed": dict(sample_filter="CLEVER/"),
        "pair_filtered": dict(pair_filter="B1_B2"),
        "sample_limited": dict(max_samples="8"),
        # runner が記録した scope が違う
        "representative": dict(run_scope="REPRESENTATIVE"),
    }
    for name, override in cases.items():
        row = verification_ledger.build_row(
            full_run(name, scope="full_eq", **override), requested_scope="full_eq",
        )
        evidence, reason = verification_ledger.full_scope_evidence(row)
        assert evidence is None, f"{name} was accepted as whole-benchmark evidence"
        assert reason


def test_a_focused_run_is_not_mistaken_for_a_full_run(tmp_path, full_run):
    """focused 依頼は full verdict の候補にすらならない。"""
    row = verification_ledger.build_row(
        full_run("focused", scope="full_eq"), requested_scope="focused",
    )

    evidence, reason = verification_ledger.full_scope_evidence(row)

    assert evidence is None and reason == "not a full scope request"
    listing = verification_ledger.format_listing(
        (row,), _head_state(), ledger_path=tmp_path / "l.jsonl",
    )
    assert "full_eq: NO" in listing and "full_neq: NO" in listing


def test_a_full_run_with_partial_coverage_is_not_evaluated(tmp_path, full_run):
    """full を依頼しても coverage が partial なら YES にしない。"""
    run_dir = full_run(
        "partial", scope="full_eq",
        outcomes=[("f", "B1", "B2", "EQUIVALENT"), ("f", "B3", "B4", "UNKNOWN")],
    )
    (run_dir / EQ_SAMPLE / "f" / "f_B3_B4.pair-status.json").unlink()

    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    evidence, reason = verification_ledger.full_scope_evidence(row)

    assert row["completed_scope"] == outcome_transition.COMPLETENESS_PARTIAL
    assert evidence is None and "completed_scope" in reason
    listing = verification_ledger.format_listing(
        (row,), _head_state(), ledger_path=tmp_path / "l.jsonl",
    )
    assert "full_eq: NO" in listing


def test_a_full_run_without_a_publication_manifest_is_not_evaluated(tmp_path, full_run):
    """census が無ければ全件走ったことを裏付けられない。"""
    row = verification_ledger.build_row(
        full_run("no_manifest", scope="full_eq", with_publication=False),
        requested_scope="full_eq",
    )

    assert row["completed_scope"] == outcome_transition.COMPLETENESS_UNKNOWN
    assert verification_ledger.full_scope_evidence(row)[0] is None


@pytest.mark.parametrize(
    "commit,dirty,head",
    [
        (OTHER_COMMIT, GIT_DIRTY_NO, _head_state()),
        (HEAD, GIT_DIRTY_YES, _head_state()),
        (verification_ledger.UNSET, GIT_DIRTY_NO, _head_state()),
        (HEAD, GIT_DIRTY_NO, _head_state(dirty=GIT_DIRTY_YES)),
    ],
)
def test_a_valid_full_run_is_not_head_verification_when_the_code_differs(
    tmp_path, full_run, commit, dirty, head,
):
    """artifact 上は完全な full run でも、HEAD の証拠でなければ YES にしない。"""
    row = verification_ledger.build_row(
        full_run("full", scope="full_eq", commit=commit, dirty=dirty),
        requested_scope="full_eq",
    )
    # run 自体は full scope を裏付けている（過去 run としては有効）。
    assert verification_ledger.full_scope_evidence(row)[0] == "full_eq"

    listing = verification_ledger.format_listing(
        (row,), head, ledger_path=tmp_path / "l.jsonl",
    )

    assert "full_eq: YES" not in listing
    assert "full_eq: NO" in listing
    assert "stale_code" in listing


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


# ---------------------------------------------------------------------------
# 欠落した half（修正 2）
#
# `scope=all` が要求する half が directory ごと無いとき、存在する half だけを
# 数えて complete にしない。欠落そのものが集計から消えないことも固定する。
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("absent,present", [("neq", "eq"), ("eq", "neq")])
def test_scope_all_with_a_missing_half_is_never_complete(tmp_path, subset_run, absent, present):
    run_dir = subset_run("run")
    shutil.rmtree(run_dir / absent)

    row = verification_ledger.build_row(run_dir, requested_scope="subset")

    assert row["completed_scope"] == outcome_transition.COMPLETENESS_UNKNOWN
    assert absent in row["completed_scope_detail"]
    # 欠落が集計から消えない: 期待した half と欠落した half の両方が残る。
    assert row["coverage"]["trees_expected"] == ["eq", "neq"]
    assert row["coverage"]["trees_missing"] == [absent]
    assert present in row["coverage"]["trees"]
    listing = verification_ledger.format_listing(
        (row,), _head_state(), ledger_path=tmp_path / "l.jsonl",
    )
    assert f"MISSING TREE(S): {absent}" in listing


@pytest.mark.parametrize("scope,absent", [("eq", "neq"), ("neq", "eq")])
def test_a_single_half_scope_is_complete_without_the_other_half(
    tmp_path, subset_run, scope, absent,
):
    """`scope=eq` は neq を要求していないので、無くても complete。"""
    run_dir = subset_run("run")
    shutil.rmtree(run_dir / absent)
    manifest = run_dir / "subset_manifest.txt"
    manifest.write_text(
        manifest.read_text(encoding="utf-8").replace("scope=all", f"scope={scope}"),
        encoding="utf-8",
    )

    row = verification_ledger.build_row(run_dir, requested_scope="subset")

    assert row["completed_scope"] == outcome_transition.COMPLETENESS_COMPLETE
    assert row["coverage"]["trees_expected"] == [scope]
    assert row["coverage"]["trees_missing"] == []


def test_scope_all_with_both_halves_present_is_complete(subset_run):
    row = verification_ledger.build_row(subset_run("run"), requested_scope="subset")

    assert row["completed_scope"] == outcome_transition.COMPLETENESS_COMPLETE
    assert row["coverage"]["trees_expected"] == ["eq", "neq"]
    assert row["coverage"]["trees_missing"] == []


# ---------------------------------------------------------------------------
# list の表示契約（修正 3）と timing の出所（修正 4）
# ---------------------------------------------------------------------------


def test_list_shows_every_field_needed_to_retrace_a_run(tmp_path, subset_run):
    """v4 §7.B: row から検証条件を追えること。"""
    row = verification_ledger.build_row(
        subset_run("run"), requested_scope="subset", issue="123",
    )

    listing = verification_ledger.format_listing(
        (row,), _head_state(), ledger_path=tmp_path / "l.jsonl",
    )

    for expected in (
        "requested_scope=subset",
        "completed_scope=complete",
        "coverage=",
        "commit=",
        "dirty=",
        "manifest_sha256=",
        "analysis_config_digest=",
        "code_matches_head=",
        "layout=subset_halves",
    ):
        assert expected in listing, f"{expected} missing from the listing"


def test_per_tree_analysis_config_digests_are_kept_when_they_differ(tmp_path, subset_run):
    """eq / neq で正当に異なる digest を単語 1 つに潰さない。"""
    run_dir = subset_run("run")
    for half, digest in (("eq", "digest-eq"), ("neq", "digest-neq")):
        manifest = run_dir / half / "run_manifest.txt"
        manifest.write_text(
            manifest.read_text(encoding="utf-8").replace(
                "analysis_config_digest=c", f"analysis_config_digest={digest}"),
            encoding="utf-8",
        )

    row = verification_ledger.build_row(run_dir, requested_scope="subset")
    listing = verification_ledger.format_listing(
        (row,), _head_state(), ledger_path=tmp_path / "l.jsonl",
    )

    # 「異なる」ことと、それぞれの値の両方が読める。
    assert row["provenance"]["analysis_config_digest"] == verification_ledger.MISMATCH
    assert row["provenance"]["trees"]["eq"]["analysis_config_digest"] == "digest-eq"
    assert row["provenance"]["trees"]["neq"]["analysis_config_digest"] == "digest-neq"
    assert "eq=digest-eq" in listing and "neq=digest-neq" in listing


def test_a_value_no_tree_recorded_is_unknown_not_differs(tmp_path, subset_run):
    """「異なる」と「誰も記録していない」を区別する。"""
    run_dir = subset_run("run")
    for half in ("eq", "neq"):
        manifest = run_dir / half / "run_manifest.txt"
        manifest.write_text(
            "".join(
                line + "\n"
                for line in manifest.read_text(encoding="utf-8").splitlines()
                if not line.startswith("analysis_config_digest=")
            ),
            encoding="utf-8",
        )

    row = verification_ledger.build_row(run_dir, requested_scope="subset")

    assert row["provenance"]["analysis_config_digest"] == verification_ledger.UNSET
    assert row["provenance"]["analysis_config_digest"] != verification_ledger.MISMATCH


def test_whole_run_timing_comes_from_the_subset_manifest(tmp_path, subset_run):
    """subset 全体の start/end は half と一致しないのが正常 -> mismatch にしない。"""
    run_dir = subset_run("run")
    # half は run 全体とは別の時刻を持つ（実際の run と同じ形）。
    for half, start, end in (
        ("eq", "2026-01-01T00:00:10Z", "2026-01-01T00:04:05Z"),
        ("neq", "2026-01-01T00:04:06Z", "2026-01-01T00:09:55Z"),
    ):
        manifest = run_dir / half / "run_manifest.txt"
        manifest.write_text(
            manifest.read_text(encoding="utf-8")
            + f"start_time_utc={start}\nend_time_utc={end}\nhostname=host\n",
            encoding="utf-8",
        )

    row = verification_ledger.build_row(run_dir, requested_scope="subset")
    timing = row["timing"]

    assert timing["source"] == "subset_manifest"
    assert timing["start_time_utc"] == "2026-01-01T00:00:00Z"
    assert timing["end_time_utc"] == "2026-01-01T00:10:00Z"
    assert verification_ledger.MISMATCH not in (
        timing["start_time_utc"], timing["end_time_utc"], timing["hostname"],
    )
    # half の時刻は失われず per-tree に残る。
    assert timing["trees"]["eq"]["start_time_utc"] == "2026-01-01T00:00:10Z"
    assert timing["trees"]["neq"]["end_time_utc"] == "2026-01-01T00:09:55Z"
    listing = verification_ledger.format_listing(
        (row,), _head_state(), ledger_path=tmp_path / "l.jsonl",
    )
    assert "timing=2026-01-01T00:00:00Z -> 2026-01-01T00:10:00Z" in listing


def test_matrix_run_timing_still_comes_from_its_run_manifest(full_run, tmp_path):
    row = verification_ledger.build_row(
        full_run("full", scope="full_eq"), requested_scope="full_eq",
    )

    assert row["timing"]["source"] == "run_manifest"
    assert row["timing"]["start_time_utc"] == "2026-01-01T00:00:00Z"
    assert row["timing"]["end_time_utc"] == "2026-01-02T00:00:00Z"


def test_the_last_full_scope_row_keeps_its_own_detail_block(tmp_path, full_run):
    """full row が最後の 1 行でも、digest / timing を追える詳細が出る。"""
    ledger = tmp_path / "ledger.jsonl"
    verification_ledger.append_row(ledger, verification_ledger.build_row(
        full_run("full", scope="full_eq"), requested_scope="full_eq",
    ))

    listing = verification_ledger.format_listing(
        verification_ledger.read_rows(ledger), _head_state(), ledger_path=ledger,
    )

    assert "manifest_sha256=" in listing
    assert "analysis_config_digest=" in listing
    assert "timing=" in listing
    assert "(none)" not in listing


def test_only_the_most_recent_request_per_scope_is_explained(tmp_path, subset_run):
    """同じ scope の古い依頼まで並べて verdict を埋もれさせない。"""
    ledger = tmp_path / "ledger.jsonl"
    for name in ("a", "b", "c"):
        verification_ledger.append_row(ledger, verification_ledger.build_row(
            subset_run(name, commit=HEAD), requested_scope="full_eq",
        ))

    listing = verification_ledger.format_listing(
        verification_ledger.read_rows(ledger), _head_state(), ledger_path=ledger,
    )

    explained = [
        line for line in listing.splitlines()
        if "requested full_eq but is not whole-benchmark evidence" in line
    ]
    assert len(explained) == 1 and explained[0].strip().startswith(str(tmp_path / "c"))
    assert "full_eq: NO" in listing


# ---------------------------------------------------------------------------
# full evidence は「正式 publication artifact contract を満たした artifact」からのみ
#
# 一部 field を自前で再検証するのではなく、artifact の持ち主である
# `execution_receipt.validate_matrix_publication_manifest()` に判定させる。
# したがってここでの固定は「formal validator が reject する artifact を
# `full_scope_evidence()` が accept しない」という等価性そのもの。
# ---------------------------------------------------------------------------


def _published(run_dir: Path):
    path = run_dir / outcome_transition.PUBLICATION_MANIFEST_FILE
    if not path.is_file():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _formal_validator_accepts(run_dir: Path) -> bool:
    payload = _published(run_dir)
    if payload is None:
        return False
    try:
        execution_receipt.validate_matrix_publication_manifest(payload)
    except (ValueError, TypeError):
        return False
    return True


def test_the_full_run_fixture_is_a_formally_valid_publication_artifact(full_run):
    """fixture 自体が current の正式 contract を満たしていること。"""
    run_dir = full_run("valid", scope="full_eq")

    payload = _published(run_dir)
    # 例外が出れば test は失敗する（= fixture が current schema から drift した合図）。
    # validator が既に digest と schema tag を強制しているので、ここで固定するのは
    # 「この fixture が何を表しているか」＝ whole-benchmark scope だけ。
    execution_receipt.validate_matrix_publication_manifest(payload)

    assert payload["run_scope"] == "FULL_EQBENCH"


@pytest.mark.parametrize("scope", ["full_eq", "full_neq"])
def test_only_a_formally_published_unnarrowed_complete_full_run_is_evidence(
    tmp_path, full_run, scope,
):
    """valid な full run だけが YES になる（両 scope）。"""
    run_dir = full_run(f"valid_{scope}", scope=scope)
    assert _formal_validator_accepts(run_dir)

    row = verification_ledger.build_row(run_dir, requested_scope=scope)

    assert row["completed_scope"] == outcome_transition.COMPLETENESS_COMPLETE
    assert verification_ledger.full_scope_evidence(row) == (scope, "")
    listing = verification_ledger.format_listing(
        (row,), _head_state(), ledger_path=tmp_path / "l.jsonl",
    )
    assert f"{scope}: YES" in listing


def _reseal(payload):
    """壊した body の digest を計算し直す。

    `artifact_digest` は body 全体の SHA-256 なので、resealing しないと
    **どの改変も digest 不一致で弾かれてしまい**、名前のついた条件
    （run_scope 不一致・typed config 不正 等）に一度も到達しない。
    それでは test が「stale hash を見ている」だけになるので、意図した条件で
    reject されることを確かめるために封をし直す。
    """
    payload["analysis_config_digest"] = authority_digest(payload["analysis_config"])
    body = {
        key: payload[key]
        for key in execution_receipt.MATRIX_PUBLICATION_FIELDS - {"artifact_digest"}
        if key in payload
    }
    payload["artifact_digest"] = authority_digest(body)
    return payload


def _drop(key, *, reseal=False):
    def mutate(payload):
        payload.pop(key, None)
        return _reseal(payload) if reseal else payload
    return mutate


def _set(key, value, *, reseal=False):
    def mutate(payload):
        payload[key] = value
        return _reseal(payload) if reseal else payload
    return mutate


def _set_config(key, value, *, reseal=True):
    def mutate(payload):
        payload["analysis_config"] = {**payload["analysis_config"], key: value}
        return _reseal(payload) if reseal else payload
    return mutate


# 各 case は「その名前の条件で reject される」ことを狙う。`reseal=True` は
# digest を直してから改変を残し、validator の当該述語まで到達させるため。
# digest 自体を試す 2 件だけは、当然 reseal しない。
PUBLICATION_REJECTIONS = {
    # 欠落 / 余剰は field 集合の検査で落ちる（digest 以前の段階）。
    "missing_top_level_run_scope": _drop("run_scope"),
    "missing_analysis_config": _drop("analysis_config"),
    "extra_field": _set("unexpected_field", "x"),
    # 値の改変は reseal して、名前の条件そのものに到達させる。
    "run_scope_disagrees_with_analysis_config": _set("run_scope", "FULL_NEQ", reseal=True),
    "run_scope_not_a_known_scope": _set("run_scope", "WHATEVER", reseal=True),
    "unknown_schema": _set("schema", "eqbench-matrix-publication-manifest-v2", reseal=True),
    "census_not_a_list": _set("expected_pair_status_paths", "not-a-list", reseal=True),
    # typed analysis config の検査（validate_analysis_config）に到達させる。
    "malformed_analysis_config": _set(
        "analysis_config", {"schema": "eqbench-analysis-config-v2"}, reseal=True),
    "incomplete_analysis_config": _set_config("sample_filter", None),
    "unreadable_filter_type": _set_config("pair_filter", 7),
    "unknown_config_scope": _set_config("run_scope", "WHATEVER"),
    # digest そのものを壊す 2 件（ここだけ reseal しない）。
    "bad_analysis_config_digest": _set("analysis_config_digest", "0" * 64),
    "bad_artifact_digest": _set("artifact_digest", "0" * 64),
}
# reseal しても reject されること（= stale hash 由来の空振りでないこと）を確かめる case。
RESEALED_REJECTIONS = {
    name for name in PUBLICATION_REJECTIONS
    if name not in {"bad_analysis_config_digest", "bad_artifact_digest"}
}


@pytest.mark.parametrize("name", sorted(PUBLICATION_REJECTIONS))
def test_an_artifact_the_formal_validator_rejects_is_never_full_evidence(
    tmp_path, full_run, name,
):
    """formal validator が拒否する artifact を ledger が accept しない。"""
    run_dir = full_run(name, scope="full_eq", mutate=PUBLICATION_REJECTIONS[name])

    assert not _formal_validator_accepts(run_dir), (
        f"{name}: the formal validator accepted this; the case no longer tests anything"
    )
    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    evidence, reason = verification_ledger.full_scope_evidence(row)

    assert evidence is None, f"{name} was accepted as whole-benchmark evidence"
    assert reason
    listing = verification_ledger.format_listing(
        (row,), _head_state(), ledger_path=tmp_path / "l.jsonl",
    )
    assert "full_eq: YES" not in listing


@pytest.mark.parametrize("name", sorted(RESEALED_REJECTIONS))
def test_each_rejection_is_caused_by_its_own_condition_not_a_stale_digest(
    full_run, name,
):
    """digest を封じ直しても reject されること（test の空振り防止）。

    `artifact_digest` は body 全体の hash なので、封じ直さない改変はすべて
    digest 不一致で落ち、名前のついた条件に到達しない。ここでは digest を
    正しくしたうえで、それでもなお reject されることを確かめる。
    """
    run_dir = full_run(f"resealed_{name}", scope="full_eq",
                       mutate=PUBLICATION_REJECTIONS[name])
    payload = _published(run_dir)
    if payload is not None and "artifact_digest" in payload:
        body = {
            key: payload[key]
            for key in execution_receipt.MATRIX_PUBLICATION_FIELDS - {"artifact_digest"}
            if key in payload
        }
        # 欠落 case では body が揃わないので digest 検査より前に落ちる（それが正）。
        if set(payload) == execution_receipt.MATRIX_PUBLICATION_FIELDS:
            assert payload["artifact_digest"] == authority_digest(body), (
                f"{name}: the mutant was not resealed, so the test would pass on a stale hash"
            )

    assert not _formal_validator_accepts(run_dir)
    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    assert verification_ledger.full_scope_evidence(row)[0] is None


def test_a_resealed_typed_config_violation_reaches_the_typed_validator(full_run):
    """typed analysis config の検査が実際に働いていること。"""
    run_dir = full_run(
        "typed_config", scope="full_eq", mutate=_set_config("sample_filter", None))
    payload = _published(run_dir)

    with pytest.raises(ValueError, match="analysis config"):
        execution_receipt.validate_matrix_publication_manifest(payload)


def test_a_missing_publication_manifest_is_never_full_evidence(tmp_path, full_run):
    run_dir = full_run("no_publication", scope="full_eq", with_publication=False)

    assert not _formal_validator_accepts(run_dir)
    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    evidence, reason = verification_ledger.full_scope_evidence(row)

    assert evidence is None
    assert outcome_transition.PUBLICATION_MANIFEST_FILE in reason


def test_an_unparsable_publication_manifest_is_a_diagnostic_not_a_crash(
    tmp_path, full_run,
):
    """壊れた JSON でも CLI を落とさず、理由付きで full evidence 不成立にする。"""
    run_dir = full_run("broken_json", scope="full_eq")
    (run_dir / outcome_transition.PUBLICATION_MANIFEST_FILE).write_text(
        '{"schema": ', encoding="utf-8",
    )
    ledger = tmp_path / "ledger.jsonl"

    # record も list も成功し、他の row も読める。
    assert verification_ledger.main([
        "--ledger", str(ledger), "record", "--run-dir", str(run_dir),
        "--requested-scope", "full_eq",
    ]) == 0
    assert verification_ledger.main(["--ledger", str(ledger), "list"]) == 0

    row = verification_ledger.read_rows(ledger)[0]
    evidence, reason = verification_ledger.full_scope_evidence(row)
    assert evidence is None and "unreadable" in reason


def test_a_malformed_census_entry_is_reported_not_raised(tmp_path, full_run):
    """validator 自身が TypeError を出す形の壊れ方でも診断として扱う。"""
    run_dir = full_run(
        "unhashable_census", scope="full_eq",
        mutate=_set("expected_pair_status_paths", [{"unhashable": True}]),
    )

    assert not _formal_validator_accepts(run_dir)
    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")

    assert verification_ledger.full_scope_evidence(row)[0] is None


@pytest.mark.parametrize(
    "name,kwargs",
    [
        ("sample_filtered", dict(sample_filter="CLEVER/")),
        ("pair_filtered", dict(pair_filter="B1_B2")),
        ("sample_limited", dict(max_samples="8")),
    ],
)
def test_a_narrowed_run_is_not_full_evidence_even_when_formally_published(
    tmp_path, full_run, name, kwargs,
):
    """filter 付きの run は、artifact として正しくても全件ではない。"""
    run_dir = full_run(name, scope="full_eq", **kwargs)

    # 正式 artifact としては妥当（narrowing は contract 違反ではない）。
    assert _formal_validator_accepts(run_dir)
    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    evidence, reason = verification_ledger.full_scope_evidence(row)

    assert evidence is None and "narrowed" in reason


@pytest.mark.parametrize(
    "name,run_manifest_scope,expected",
    [
        ("run_manifest_scope_missing", "", "records no run_scope"),
        ("run_manifest_scope_differs", "FULL_NEQ", "differs across sources"),
        ("run_manifest_scope_representative", "REPRESENTATIVE", "differs across sources"),
    ],
)
def test_the_run_manifest_scope_must_be_present_and_agree(
    full_run, name, run_manifest_scope, expected,
):
    """run_manifest の run_scope が無い / 食い違うなら full evidence にしない。

    「field が無い source は照合対象から外す」挙動ではなく、欠落そのものを理由にする。
    """
    run_dir = full_run(name, scope="full_eq", run_manifest_scope=run_manifest_scope)

    # publication 側は正式なまま: 落ちる理由は run_manifest 側にある。
    assert _formal_validator_accepts(run_dir)
    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    evidence, reason = verification_ledger.full_scope_evidence(row)

    assert evidence is None and expected in reason


def test_a_published_full_neq_run_does_not_satisfy_a_full_eq_request(full_run):
    run_dir = full_run("neq_run", scope="full_neq")

    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    evidence, reason = verification_ledger.full_scope_evidence(row)

    assert evidence is None and "FULL_EQBENCH" in reason


def test_both_latest_full_scope_rows_keep_their_detail_blocks(tmp_path, subset_run, full_run):
    """latest full_eq と latest full_neq の両方の詳細を list から追える。

    row1 subset / row2 full_eq / row3 subset / row4 full_neq / row5 subset。
    row2 は row4 より古いが、`full_eq` の答えの根拠なので詳細が要る。
    """
    ledger = tmp_path / "ledger.jsonl"
    rows = [
        verification_ledger.build_row(subset_run("s1"), requested_scope="subset"),
        verification_ledger.build_row(
            full_run("f_eq", scope="full_eq"), requested_scope="full_eq"),
        verification_ledger.build_row(subset_run("s2"), requested_scope="subset"),
        verification_ledger.build_row(
            full_run("f_neq", scope="full_neq"), requested_scope="full_neq"),
        verification_ledger.build_row(subset_run("s3"), requested_scope="subset"),
    ]
    for row in rows:
        verification_ledger.append_row(ledger, row)

    listing = verification_ledger.format_listing(
        verification_ledger.read_rows(ledger), _head_state(), ledger_path=ledger,
    )

    def detail_blocks(run_dir):
        """詳細 block の先頭行は "  <recorded_at>  <run_dir>" だけ。"""
        return [
            line for line in listing.splitlines()
            if line.strip().endswith(f"  {run_dir}")
        ]

    # latest full_eq（古い方）と latest full_neq、そのあとの subset が詳細を持つ。
    for name in ("f_eq", "f_neq", "s3"):
        assert len(detail_blocks(tmp_path / name)) == 1, f"{name}: {detail_blocks(tmp_path / name)}"
    # 最新 full row より前の、根拠候補でない run は詳細を繰り返さない。
    for name in ("s1", "s2"):
        assert detail_blocks(tmp_path / name) == []
    # 両 full row の検証条件を追える。
    for row in (rows[1], rows[3]):
        digest = row["provenance"]["analysis_config_digest"]
        assert digest != verification_ledger.UNSET
        assert verification_ledger._short(digest) in listing
        assert row["timing"]["start_time_utc"] in listing
        assert verification_ledger._short(row["provenance"]["manifest_sha256"]) in listing


# ---------------------------------------------------------------------------
# 型付き config が表現しない narrowing（rerun manifest 等）への fail-closed
#
# `eqbench_run_all_32jobs.sh` の `EQBENCH_RERUN_MANIFEST`（neq は
# `NEQ_RERUN_MANIFEST`）は、`expected_pair_status_paths` を rerun 対象だけに
# 絞る一方で `total_functions` / `expected_pairs_per_function` は絞らない。
# analysis config にも run_manifest にも現れないので filter 検査では見えない。
# publication manifest 自身が矛盾する（census が宣言した規模に満たない）ので、
# その矛盾を根拠に full evidence を認めない。
# ---------------------------------------------------------------------------


def test_a_census_smaller_than_the_declared_extent_is_not_full_evidence(full_run):
    """rerun 等で census だけが縮んだ run を全件と認めない。"""
    def shrink_census(payload):
        payload["total_functions"] = 40
        payload["expected_pairs_per_function"] = 120
        return _reseal(payload)

    run_dir = full_run("rerun_narrowed", scope="full_eq", mutate=shrink_census)

    # artifact としては正式（rerun は contract 違反ではない）。
    assert _formal_validator_accepts(run_dir)
    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    evidence, reason = verification_ledger.full_scope_evidence(row)

    assert row["completed_scope"] == outcome_transition.COMPLETENESS_COMPLETE
    assert evidence is None, "a census-narrowed run was accepted as whole-benchmark"
    assert "census covers" in reason and "4800" in reason
    assert row["scope_evidence"]["trees"]["."]["pairs_declared"] == 4800
    assert row["scope_evidence"]["trees"]["."]["pairs_in_census"] == 1


def test_an_unreadable_declared_extent_is_not_full_evidence(full_run):
    """規模を宣言する field が読めなければ「全件」と言えない。"""
    def break_extent(payload):
        payload["total_functions"] = 0
        payload["expected_pairs_per_function"] = 0
        return _reseal(payload)

    run_dir = full_run("no_extent", scope="full_eq", mutate=break_extent)

    assert _formal_validator_accepts(run_dir)
    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")

    assert verification_ledger.full_scope_evidence(row)[0] is None


def test_the_real_full_matrix_artifact_satisfies_the_extent_invariant():
    """実在の full run が不変量を満たすこと（規則が現実と食い違わない確認）。"""
    path = Path(REPO_ROOT) / "logs/EqBench/all_eq_matrix_current/matrix-publication-manifest.json"
    if not path.is_file():
        pytest.skip("the historical full matrix artifact is not in this checkout")
    payload = json.loads(path.read_text(encoding="utf-8"))
    execution_receipt.validate_matrix_publication_manifest(payload)

    declared, census = verification_ledger._declared_and_published_extent(payload)

    assert declared == census == len(payload["expected_pair_status_paths"])


# ---------------------------------------------------------------------------
# run_manifest 側の filter も照合対象から外さない
# ---------------------------------------------------------------------------


def test_run_manifest_filters_must_agree_with_the_published_config(full_run):
    """run_manifest が別の filter を言っているなら full evidence にしない。"""
    run_dir = full_run("filter_disagreement", scope="full_eq")
    manifest = run_dir / "run_manifest.txt"
    manifest.write_text(
        manifest.read_text(encoding="utf-8").replace(
            "sample_filter=\n", "sample_filter=CLEVER/\n"),
        encoding="utf-8",
    )

    # publication 側は正式なまま: 落ちる理由は 2 つの source の食い違い。
    assert _formal_validator_accepts(run_dir)
    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    evidence, reason = verification_ledger.full_scope_evidence(row)

    assert evidence is None and "disagree" in reason


def test_absent_run_manifest_filters_are_a_reason_not_a_dropped_source(full_run):
    """run_manifest に filter 行が無い場合、「無い source は無視」にしない。"""
    run_dir = full_run("filters_absent", scope="full_eq")
    manifest = run_dir / "run_manifest.txt"
    manifest.write_text(
        "".join(
            f"{line}\n" for line in manifest.read_text(encoding="utf-8").splitlines()
            if not line.startswith(("sample_filter=", "pair_filter=", "max_samples="))
        ),
        encoding="utf-8",
    )

    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    evidence, reason = verification_ledger.full_scope_evidence(row)

    assert evidence is None
    assert "absent or disagree" in reason
    assert row["scope_evidence"]["trees"]["."]["narrowing_agrees_with_run_manifest"] is None


# ---------------------------------------------------------------------------
# 診断 payload / verdict と listing の整合
# ---------------------------------------------------------------------------


def test_the_scope_evidence_payload_records_what_was_actually_checked(full_run):
    """人が読む診断 field を固定する。"""
    row = verification_ledger.build_row(
        full_run("valid_payload", scope="full_eq"), requested_scope="full_eq",
    )

    tree = row["scope_evidence"]["trees"]["."]
    assert {key: tree[key] for key in tree if key != "scope_health"} == {
        "whole_benchmark_scope": "FULL_EQBENCH",
        "failure_reason": None,
        "formal_publication": "valid",
        "run_manifest_run_scope": "FULL_EQBENCH",
        "publication_run_scope": "FULL_EQBENCH",
        "analysis_config_run_scope": "FULL_EQBENCH",
        "declared_run_scope": "FULL_EQBENCH",
        "narrowed": False,
        "narrowing_agrees_with_run_manifest": True,
        "pairs_declared": 1,
        "pairs_in_census": 1,
    }
    assert row["scope_evidence"]["whole_benchmark_scope"] == "FULL_EQBENCH"
    # scope health: 4 failure counters at 0 and the accounting that must close.
    health = tree["scope_health"]
    assert health["status"] == verification_ledger.SCOPE_HEALTH_OK
    assert health["failure_reason"] is None
    assert health["failures"] == {
        "function_census_failure_count": 0,
        "compile_failure_count": 0,
        "missing_binary_count": 0,
        "run_pair_failures": 0,
    }
    assert health["accounting"]["target_sources"] == health["accounting"]["completed_samples"]
    assert health["accounting"]["expected_binary_count"] == (
        health["accounting"]["compiled_binary_count"])
    assert health["accounting"]["dry_run"] == 0


def test_a_rejected_tree_records_its_reason_in_the_payload(full_run):
    row = verification_ledger.build_row(
        full_run("no_pub", scope="full_eq", with_publication=False),
        requested_scope="full_eq",
    )

    tree = row["scope_evidence"]["trees"]["."]
    assert tree["whole_benchmark_scope"] is None
    assert outcome_transition.PUBLICATION_MANIFEST_FILE in tree["failure_reason"]
    assert tree["formal_publication"] == tree["failure_reason"]


def test_the_row_a_yes_rests_on_is_always_printed(tmp_path, full_run, subset_run):
    """verdict の根拠 row と、詳細表示される row が食い違わない。

    あとから full_eq を「依頼」しただけの subset row が記録されても、YES の
    根拠である本物の full row の詳細が list から消えないこと。
    """
    ledger = tmp_path / "ledger.jsonl"
    good = verification_ledger.build_row(
        full_run("real_full", scope="full_eq"), requested_scope="full_eq")
    verification_ledger.append_row(ledger, good)
    for name in ("later1", "later2"):
        verification_ledger.append_row(ledger, verification_ledger.build_row(
            subset_run(name, commit=HEAD), requested_scope="full_eq"))

    listing = verification_ledger.format_listing(
        verification_ledger.read_rows(ledger), _head_state(), ledger_path=ledger,
    )

    assert "full_eq: YES" in listing and good["run_dir"] in listing
    # 根拠 row の詳細 block（先頭行が "  <time>  <run_dir>"）が出ている。
    assert [
        line for line in listing.splitlines()
        if line.strip().endswith("  " + good["run_dir"])
    ], "the row the YES rests on has no detail block"


def test_limit_never_drops_the_rows_the_verdict_rests_on(tmp_path, full_run, subset_run):
    ledger = tmp_path / "ledger.jsonl"
    good = verification_ledger.build_row(
        full_run("kept_full", scope="full_eq"), requested_scope="full_eq")
    verification_ledger.append_row(ledger, good)
    for name in ("a", "b", "c", "d"):
        verification_ledger.append_row(ledger, verification_ledger.build_row(
            subset_run(name, commit=HEAD), requested_scope="subset"))

    listing = verification_ledger.format_listing(
        verification_ledger.read_rows(ledger), _head_state(), ledger_path=ledger, limit=1,
    )

    assert "full_eq: YES" in listing
    assert [
        line for line in listing.splitlines()
        if line.strip().endswith("  " + good["run_dir"])
    ], "--limit dropped the evidence row behind the verdict"


# ---------------------------------------------------------------------------
# scope health: benchmark 対象が途中で欠落した run を full と認めない
#
# formal validator を通り、残存 census が complete で、
# `total_pair_jobs == total_functions × expected_pairs_per_function` まで
# 自己整合していても、失敗 counter / accounting が「対象が途中で消えた」ことを
# 示すなら full verification ではない。digest は必ず reseal してから試験する。
# ---------------------------------------------------------------------------


def _healthy_full(full_run, name, scope="full_eq", **kwargs):
    """artifact として正式かつ scope health も ok な full run。"""
    return full_run(name, scope=scope, **kwargs)


def test_A_a_function_census_failure_is_never_full_evidence(tmp_path, full_run):
    """本 blocker の直接固定。

    Eq runner は census 不一致を記録して**処理を続行**する（:1096-1099）ので、
    `total_functions` / `total_pair_jobs` / census はすべて縮小後の関数集合から
    作られ、内部的に自己整合する。それでも 1 関数は評価されていない。
    """
    def census_failure(payload):
        payload["function_census_failure_count"] = 1
        payload["function_census_failures"] = ["CLEVER/LoopSub/Eq/new"]
        return _reseal(payload)

    run_dir = full_run("census_failure", scope="full_eq", mutate=census_failure)

    # formal validator は受理する（contract 違反ではない）。
    assert _formal_validator_accepts(run_dir)
    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    evidence, reason = verification_ledger.full_scope_evidence(row)

    # 残存範囲は complete で、extent 不変量も満たす。
    assert row["completed_scope"] == outcome_transition.COMPLETENESS_COMPLETE
    tree = row["scope_evidence"]["trees"]["."]
    assert tree["pairs_declared"] == tree["pairs_in_census"]
    # それでも full evidence にならず、理由が census failure を明示する。
    assert evidence is None
    assert "function_census_failure_count=1" in reason
    assert "CLEVER/LoopSub/Eq/new" in reason
    assert tree["scope_health"]["status"] == verification_ledger.SCOPE_HEALTH_FAILED

    listing = verification_ledger.format_listing(
        (row,), _head_state(), ledger_path=tmp_path / "l.jsonl",
    )
    assert "full_eq: YES" not in listing
    assert "full_eq: NO" in listing
    assert "function_census_failure_count=1" in listing


def test_B_a_compile_failure_is_never_full_evidence(tmp_path, full_run):
    def compile_failure(payload):
        payload["compile_failure_count"] = 1
        payload["compile_failure_samples"] = ["airy/Sign/Eq/newV"]
        return _reseal(payload)

    run_dir = full_run("compile_failure", scope="full_eq", mutate=compile_failure)

    assert _formal_validator_accepts(run_dir)
    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    evidence, reason = verification_ledger.full_scope_evidence(row)

    assert evidence is None
    assert "compile_failure_count=1" in reason and "airy/Sign/Eq/newV" in reason


def test_C_a_missing_binary_is_never_full_evidence(tmp_path, full_run):
    def missing_binary(payload):
        payload["missing_binary_count"] = 1
        payload["missing_binary_axes"] = ["airy/Sign/Eq/newV/B7"]
        return _reseal(payload)

    run_dir = full_run("missing_binary", scope="full_eq", mutate=missing_binary)

    assert _formal_validator_accepts(run_dir)
    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    evidence, reason = verification_ledger.full_scope_evidence(row)

    assert evidence is None
    assert "missing_binary_count=1" in reason


def test_D_a_healthy_full_artifact_is_still_evidence(tmp_path, full_run):
    """逆向きの固定: 健全な full artifact は引き続き YES。"""
    run_dir = _healthy_full(full_run, "healthy", scope="full_eq")

    assert _formal_validator_accepts(run_dir)
    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")

    assert row["scope_evidence"]["trees"]["."]["scope_health"]["status"] == (
        verification_ledger.SCOPE_HEALTH_OK
    )
    assert verification_ledger.full_scope_evidence(row) == ("full_eq", "")
    listing = verification_ledger.format_listing(
        (row,), _head_state(), ledger_path=tmp_path / "l.jsonl",
    )
    assert "full_eq: YES" in listing
    assert "scope_health=ok" in listing


def test_E_a_benchmark_gate_failure_does_not_remove_the_coverage_fact(tmp_path, full_run):
    """gate 軸（C）の失敗を coverage の喪失に混ぜない。

    benchmark gate の結果は publication manifest の field ではない
    （`benchmark_gate_failures` は run_manifest / gate JSON 側）。全 pair を実行した
    run が gate violation を出しても、「全件を実行した」という事実は残る。
    """
    run_dir = _healthy_full(full_run, "gate_fail", scope="full_eq")
    # gate が violation を報告している状態を作る（coverage とは別 artifact）。
    (run_dir / "benchmark_validation_gate.json").write_text(
        json.dumps({
            "gate": "FAIL", "pairs": 1,
            "hard_violations": {"eq_not_eq": 1},
            "suspicious": {"suspicious_eq_on_source_changed_function": 2},
        }),
        encoding="utf-8",
    )
    manifest = run_dir / "run_manifest.txt"
    manifest.write_text(
        manifest.read_text(encoding="utf-8")
        + "benchmark_gate_status=FAIL\nbenchmark_gate_failures=1\n",
        encoding="utf-8",
    )

    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")

    # C 軸は FAIL を報告する。
    assert row["gate"]["benchmark"]["."]["gate"] == "FAIL"
    assert row["gate"]["benchmark"]["."]["hard_violations"] == 1
    assert row["gate"]["benchmark"]["."]["suspicious"] == 2
    # coverage の事実は失われない。
    assert row["scope_evidence"]["trees"]["."]["scope_health"]["status"] == (
        verification_ledger.SCOPE_HEALTH_OK
    )
    assert verification_ledger.full_scope_evidence(row) == ("full_eq", "")
    # gate の状態は scope 判定に混ざっていない（gate 由来の field 名が現れない）。
    serialized = json.dumps(row["scope_evidence"])
    for gate_field in (
        "benchmark_gate", "hard_violations", "suspicious", "gate",
        "benchmark_gate_failures", "benchmark_gate_status",
    ):
        assert gate_field not in serialized, gate_field


def test_run_pair_failures_block_full_evidence_but_are_not_gate_failures(full_run):
    """`run_pair_failures` は「評価できなかった pair」であり gate 失敗ではない。

    fixed subset は TIMEOUT / ERROR pair を 5 件持ちながら `run_pair_failures=0`
    なので、この counter は outcome の悪さではなく分類不能を表す。
    """
    run_dir = full_run(
        "pair_failures", scope="full_eq",
        mutate=lambda payload: _reseal({**payload, "run_pair_failures": 3}),
    )

    assert _formal_validator_accepts(run_dir)
    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    evidence, reason = verification_ledger.full_scope_evidence(row)

    assert evidence is None and "run_pair_failures=3" in reason


def test_a_dry_run_is_never_full_evidence(full_run):
    run_dir = full_run(
        "dry", scope="full_eq",
        mutate=lambda payload: _reseal({**payload, "dry_run": 1}),
    )

    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    evidence, reason = verification_ledger.full_scope_evidence(row)

    assert evidence is None and "dry run" in reason


@pytest.mark.parametrize(
    "name,mutation,expected",
    [
        ("samples_unaccounted", {"completed_samples": 2}, "do not account for"),
        ("binaries_short", {"compiled_binary_count": 8}, "expected binaries were built"),
        ("no_binaries_expected", {"expected_binary_count": 0, "compiled_binary_count": 0},
         "expected binaries were built"),
        ("pairs_unaccounted", {"total_scheduled_pair_jobs": 0}, "do not account for"),
    ],
)
def test_accounting_that_does_not_close_is_not_full_evidence(
    full_run, name, mutation, expected,
):
    """対象が途中で消えたことを accounting の閉じ方から検出する。"""
    run_dir = full_run(
        name, scope="full_eq",
        mutate=lambda payload: _reseal({**payload, **mutation}),
    )

    assert _formal_validator_accepts(run_dir)
    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")
    evidence, reason = verification_ledger.full_scope_evidence(row)

    assert evidence is None, f"{name} was accepted as whole-benchmark evidence"
    assert expected in reason


@pytest.mark.parametrize("scope", ["full_eq", "full_neq"])
def test_scope_health_applies_to_both_runners(full_run, scope):
    """Eq / Neq どちらの run_scope でも同じ health 条件が働く。

    両 runner の counter 意味と accounting の閉じ方は同型（Eq :1096/:1241/:1239、
    Neq :672/:685/:695 と `record_missing_variant_axes`）なので、判定式も共通。
    """
    healthy = verification_ledger.build_row(
        full_run(f"healthy_{scope}", scope=scope), requested_scope=scope)
    broken = verification_ledger.build_row(
        full_run(f"broken_{scope}", scope=scope,
                 mutate=lambda p: _reseal({**p, "function_census_failure_count": 1,
                                           "function_census_failures": ["s"]})),
        requested_scope=scope)

    assert verification_ledger.full_scope_evidence(healthy) == (scope, "")
    assert verification_ledger.full_scope_evidence(broken)[0] is None


def test_unreadable_scope_health_fields_are_unknown_not_ok(full_run):
    """health を判定できないなら ok ではなく unknown（fail-closed）。"""
    run_dir = full_run("unknown_health", scope="full_eq")
    published = run_dir / outcome_transition.PUBLICATION_MANIFEST_FILE
    payload = json.loads(published.read_text(encoding="utf-8"))
    del payload["run_pair_failures"]
    published.write_text(json.dumps(payload), encoding="utf-8")

    health = verification_ledger.scope_health(payload)

    assert health["status"] == verification_ledger.SCOPE_HEALTH_UNKNOWN
    assert "run_pair_failures" in health["failure_reason"]


def test_the_real_full_matrix_scope_health_is_reported_faithfully():
    """実在の full run に新しい条件を当てた結果を固定する（現実との齟齬防止）。"""
    path = Path(REPO_ROOT) / "logs/EqBench/all_eq_matrix_current/matrix-publication-manifest.json"
    if not path.is_file():
        pytest.skip("the historical full matrix artifact is not in this checkout")
    payload = json.loads(path.read_text(encoding="utf-8"))
    execution_receipt.validate_matrix_publication_manifest(payload)

    health = verification_ledger.scope_health(payload)

    # 対象の欠落は無い（census/compile/missing binary は 0、accounting は閉じる）が、
    # 197 pair が canonical 分類に失敗しているので health は failed。
    assert health["failures"]["function_census_failure_count"] == 0
    assert health["failures"]["compile_failure_count"] == 0
    assert health["failures"]["missing_binary_count"] == 0
    assert health["accounting"]["completed_samples"] == health["accounting"]["target_sources"]
    assert health["accounting"]["compiled_binary_count"] == (
        health["accounting"]["expected_binary_count"])
    if health["failures"]["run_pair_failures"]:
        assert health["status"] == verification_ledger.SCOPE_HEALTH_FAILED
        assert "run_pair_failures" in health["failure_reason"]


def test_matrix_root_run_exit_status_comes_from_the_execution_receipt(full_run):
    """matrix-root でも exit status を診断として残す（scope 条件には使わない）。"""
    run_dir = full_run("with_receipt", scope="full_eq")
    (run_dir / verification_ledger.EXECUTION_RECEIPT_FILE).write_text(
        json.dumps({"schema": "phase10-validation-execution-receipt-v1",
                    "execution_kind": "EQBENCH_MATRIX", "exit_status": 1}),
        encoding="utf-8",
    )

    row = verification_ledger.build_row(run_dir, requested_scope="full_eq")

    assert row["run_exit_status"]["status"] == "1"
    assert row["run_exit_status"]["source"] == verification_ledger.EXECUTION_RECEIPT_FILE
    # exit_status は gate 失敗も含むので、単独で full を落とす条件にはしない。
    assert verification_ledger.full_scope_evidence(row) == ("full_eq", "")


def test_subset_run_exit_status_still_comes_from_its_own_manifest(subset_run):
    row = verification_ledger.build_row(subset_run("run"), requested_scope="subset")

    assert row["run_exit_status"]["status"] == "0"
    assert row["run_exit_status"]["source"] == "subset_manifest.txt"

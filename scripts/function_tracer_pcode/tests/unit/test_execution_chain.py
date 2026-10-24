# -*- coding: utf-8 -*-
"""複数 execution にまたがる完全性の証明と実行条件の記録（評価計画 v2 PR-B）。

FULL 評価は、停止や kill の後に同じ出力先で再開した複数の execution で終わることがある。
最後の execution の publication / receipt は自分の execution しか表さず、kill された execution は
何も公開しない。この file は、tree に残る記録（``.executions/<run_id>/`` の開始の記録・
nonce の発行の記録・封印の複製）だけから、tree が 1 つの identity の 1 回の評価として完全か
（``CLOSED_SAME_IDENTITY``）を判定する契約を固定する。

* fixture は本番の writer（``execution_chain.record_*``）、本番の署名（``seal_pair_status`` /
  ``seal_execution_receipt``）、本番の publication builder だけで作る。schema を test に
  複製しない。
* 改ざん・欠損・混在・古い証拠・重複は、名前付きの理由で OPEN になる（fail-closed）。
* FULL tree の完全性（``tree_completeness``）と ledger の full verdict は、再利用が証明された
  ときだけ complete になる。REPRESENTATIVE の再利用は partial のまま。
* Issue #276: 確定した ERROR を含む FULL tree は、他の条件を満たせば scope_health を通り full
  verdict を得る。未完了を含む tree は得ない（Eq / Neq の両 scope）。
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import shutil

import pytest

from scripts.function_tracer_pcode.authority.contracts import (
    CLI_EXIT_CODE_BY_OUTCOME,
    Outcome,
    authority_digest,
)
from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
    generate_pair_status_keypair,
    seal_pair_status,
)
from scripts.function_tracer_pcode.reporting import (
    execution_chain as chain,
    execution_receipt as er,
    outcome_transition,
    pair_runtime_receipt as prr,
    verification_ledger,
)

SOURCE = "a" * 64
DIGEST = "d" * 64
SCOPES = {"FULL_NEQ": "full_neq", "FULL_EQBENCH": "full_eq"}
RUN_KIND = {
    "FULL_NEQ": "neqbench_all_same_isa_function_closure_current",
    "FULL_EQBENCH": "eqbench_all_eq_matrix_current",
    "REPRESENTATIVE": "eqbench_all_eq_matrix_current",
}
ENVIRONMENT = {
    "environment_fingerprint": "image-sha256-x", "python_version": "3.10.12",
    "ghidra_version": "12.0.1", "java_version": "openjdk 21", "z3_version": "4.16.0",
    "cgroup_memory_max": "118111600640", "cgroup_cpu_max": "max 100000",
}


def _run_id(index: int) -> str:
    return f"{index:032x}"


def _binary(sample: str, binary_id: str) -> tuple[str, str]:
    path = f"bin/{sample}/{binary_id}"
    return path, hashlib.sha256(path.encode()).hexdigest()


class ChainTree:
    """One result tree finished by several executions, written with the production code."""

    def __init__(self, root: Path, *, scope: str = "FULL_NEQ", pairs: int = 4):
        self.root = root
        self.scope = scope
        root.mkdir(parents=True)
        self.private_key = root.parent / f"{root.name}-pair-status.key"
        self.public_key = root / chain.PUBLIC_KEY_FILE
        generate_pair_status_keypair(self.private_key, self.public_key)
        self.pairs = [("S0", "f", "B1", f"B{index + 2}") for index in range(pairs)]
        self.prefilter = ["targets/EqBench/benchmarks/S0.c"]
        self.nonce_counter = 0
        self.config_overrides: dict = {}

    # -- paths and targets -------------------------------------------------
    @staticmethod
    def relative(pair) -> str:
        sample, function, left, right = pair
        return f"{sample}/{function}/{function}_{left}_{right}.pair-status.json"

    def target(self, pair, **changes) -> dict:
        sample, function, left, right = pair
        left_path, left_sha = _binary(sample, left)
        right_path, right_sha = _binary(sample, right)
        target = {
            "schema": "eqbench-pair-execution-target-v1",
            "authority_kind": "PairExecutionTargetReceipt",
            "sample_identity": sample, "output_sample_relative_path": sample,
            "function_name": function, "left_binary_id": left, "right_binary_id": right,
            "source_path": f"{sample}.c", "source_sha256": DIGEST,
            "left_binary_path": left_path, "left_binary_sha256": left_sha,
            "right_binary_path": right_path, "right_binary_sha256": right_sha,
            "analysis_source_digest": SOURCE,
            "analysis_config_digest": self.config_digest(),
        }
        target.update(changes)
        return {**target, "target_digest": authority_digest(target)}

    # -- manifests -----------------------------------------------------------
    def start_fields(self, run_id: str, **overrides) -> dict:
        fields = {
            "run_kind": RUN_KIND[self.scope],
            "run_scope": self.scope,
            "build_policy": "PREBUILT_ONLY",
            "max_samples": "0", "sample_filter": "", "pair_filter": "",
            "debug": "0", "dry_run": "0", "parallel_jobs": "30",
            "validation_summary_level": "compact",
            "equiv_timeout": "10", "decompile_timeout": "60", "pairwise_timeout": "5",
            "pairwise_timeout_hard": "30",
            "pair_process_timeout_seconds": "600", "pair_process_kill_after_seconds": "30",
            "analysis_timeout": "410", "analysis_timeout_margin": "190",
            "analysis_config_schema": er.ANALYSIS_CONFIG_V5_SCHEMA,
            er.MATRIX_PUBLICATION_SCHEMA_KEY: er.MATRIX_PUBLICATION_SCHEMA_V4,
            "identical_fast_path": "1",
            "expander_dedup_case_limit_effective": "64",
            "callee_unbound_reuse": "1", "callee_unbound_reuse_shadow": "0",
            "prefilter_source_census_digest": er._source_census_digest(self.prefilter),
            "prefilter_source_count": str(len(self.prefilter)),
            "target_sources": str(len(self.prefilter)),
            "runner_script_sha256": "r" * 64,
            "start_time_utc": f"2026-10-24T00:00:{int(run_id, 16) % 60:02d}Z",
            "hostname": f"container-{run_id[-4:]}",
            "git_commit": "c" * 40, "git_dirty": "no", "git_dirty_files_digest": "none",
            "analysis_source_digest_start": SOURCE,
            "runtime_run_id": run_id,
            **ENVIRONMENT,
        }
        fields.update(self.config_overrides)
        fields.update(overrides)
        config = er.analysis_config_from_run(fields)
        fields["analysis_config_digest"] = authority_digest(config)
        return fields

    def config_digest(self) -> str:
        return self.start_fields(_run_id(0))["analysis_config_digest"]

    # -- one execution ---------------------------------------------------------
    def start(self, run_id: str, **overrides) -> None:
        text = "".join(f"{k}={v}\n" for k, v in self.start_fields(run_id, **overrides).items())
        manifest = self.root / chain.RUN_MANIFEST_FILE
        manifest.write_text(text, encoding="utf-8")
        chain.record_start(self.root, run_id, manifest)

    def next_nonce(self) -> str:
        self.nonce_counter += 1
        return f"{self.nonce_counter:048x}"

    def issue(self, run_id: str, pair, nonce: str, target: dict | None = None) -> None:
        target_file = self.root.parent / f"target-{nonce}.json"
        target_file.write_text(json.dumps(target or self.target(pair)), encoding="utf-8")
        chain.record_issue(
            self.root, run_id, execution_nonce=nonce,
            pair_status_path=self.root / self.relative(pair), target_file=target_file,
        )

    def sealed_status(self, pair, *, outcome: str, nonce: str, target: dict | None = None,
                      supervisor: str = "RESOLVED") -> dict:
        body = {
            "authority_kind": "SupervisorCanonicalResultResolvedReceipt",
            "supervisor_authority_kind": "SupervisorCanonicalResultResolvedReceipt",
            "supervisor_final_authority_digest": DIGEST, "launch_receipt_digest": DIGEST,
            "canonical_outcome": outcome, "decision_receipt_digest": DIGEST,
            "result_occurrence_id": f"production-pilot-{nonce}",
            "result_entry_occurrence_receipt_digest": DIGEST,
            "execution_identity_digest": DIGEST, "execution_nonce": nonce,
            "stream_id": f"stream-{nonce}", "source_snapshot_fingerprint": DIGEST,
            "canonical_result_bundle_digest": DIGEST,
            "canonical_result_bundle_kind": "CanonicalResultFinalizationBundle",
            "canonical_result_payload_preimage_digest": DIGEST,
            "semantic_projection_digest": DIGEST,
            "error_kind": "checker_error" if outcome == "ERROR" else None,
            "child_returncode": CLI_EXIT_CODE_BY_OUTCOME[Outcome(outcome)],
            "supervisor_status": supervisor, "supervisor_projection_digest": DIGEST,
            "classification_valid": True,
            "pair_execution_target": target or self.target(pair),
        }
        if supervisor != "RESOLVED":
            kind = f"Durable{supervisor.title()}FinalizationBundle"
            body.update({
                "authority_kind": kind, "supervisor_authority_kind": kind,
                "finalization_bundle_digest": DIGEST, "event_stream_authority_digest": DIGEST,
                "child_exit_disposition": "EXITED_143_AFTER_SIGTERM",
                "child_returncode_observation_kind": "LIVE_PROCESS_WAIT",
                "child_returncode": 143,
            })
        return seal_pair_status(
            body, private_key_path=self.private_key, public_key_path=self.public_key,
        )

    def decide(self, run_id: str, pair, *, outcome: str = "UNKNOWN", issue: bool = True,
               supervisor: str = "RESOLVED") -> str:
        """The pair decided by ``run_id``: issue record first, then the signed status."""
        nonce = self.next_nonce()
        if issue:
            self.issue(run_id, pair, nonce)
        path = self.root / self.relative(pair)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(self.sealed_status(
            pair, outcome=outcome, nonce=nonce, supervisor=supervisor)), encoding="utf-8")
        return nonce

    def leave_incomplete(self, run_id: str, pair) -> None:
        """Started (issued) and killed before any status: the next execution re-runs it."""
        self.issue(run_id, pair, self.next_nonce())
        (self.root / self.relative(pair)).unlink(missing_ok=True)

    def finish(self, run_id: str, *, reused, end_overrides=None, seal: bool = True) -> dict:
        """The latest execution ends normally: censuses, end fields, publication, receipt, seal."""
        reused = [self.relative(pair) for pair in reused]
        expected = [self.relative(pair) for pair in self.pairs]
        censuses = {
            "prefilter_source_paths.txt": self.prefilter,
            "compile_failure_samples.txt": [], "missing_binary_axes.txt": [],
            "function_census_failures.txt": [],
            "expected_pair_status_paths.txt": expected,
            "verified_skipped_pair_status_paths.txt": reused,
        }
        for name, rows in censuses.items():
            (self.root / name).write_text("".join(f"{row}\n" for row in rows), encoding="utf-8")
        axes = []
        for pair in self.pairs:
            for binary_id in (pair[2], pair[3]):
                path, sha = _binary(pair[0], binary_id)
                if not any(axis["binary_path"] == path for axis in axes):
                    axes.append({"binary_id": binary_id, "binary_path": path, "binary_sha256": sha})
        (self.root / "used_build_receipts.jsonl").write_text(
            json.dumps({"authority_kind": "EqBenchSourceBinaryBuildReceipt", "binary_axes": axes})
            + "\n", encoding="utf-8")
        end = {
            "completed_samples": "1", "skipped_samples": "0", "total_functions": "1",
            "total_pair_jobs": str(len(expected)),
            "total_scheduled_pair_jobs": str(len(expected) - len(reused)),
            "total_skipped_pair_jobs": str(len(reused)),
            "expected_pairs_per_function": str(len(expected)),
            "expected_binary_count": str(len(axes)), "compiled_binary_count": str(len(axes)),
            "compile_failure_count": "0", "missing_binary_count": "0",
            "function_census_failure_count": "0", "run_pair_failures": "0",
            "decided_error_pair_jobs": "0", "incomplete_pair_jobs": "0",
            "analysis_source_digest_end": SOURCE, "end_time_utc": "2026-10-24T09:00:00Z",
        }
        end.update(end_overrides or {})
        manifest = self.root / chain.RUN_MANIFEST_FILE
        manifest.write_text(
            manifest.read_text(encoding="utf-8") + "".join(f"{k}={v}\n" for k, v in end.items()),
            encoding="utf-8")
        publication = er.build_matrix_publication_manifest(self.root)
        er.validate_matrix_publication_manifest(publication)
        (self.root / chain.PUBLICATION_FILE).write_text(
            json.dumps(publication, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        self.seal_receipt(publication)
        if seal:
            chain.record_seal(self.root, run_id)
        return publication

    def seal_receipt(self, publication) -> None:
        receipt = er.seal_execution_receipt(
            execution_kind="EQBENCH_MATRIX", command=["bash", "runner.sh"],
            source_digest_start=publication["analysis_source_digest_start"],
            source_digest_end=publication["analysis_source_digest_end"],
            analysis_config_digest=publication["analysis_config_digest"], exit_status=0,
            artifacts={er.MATRIX_PUBLICATION_MANIFEST_FILE: er.sha256_file(
                self.root / chain.PUBLICATION_FILE)},
            private_key_path=self.private_key, public_key_path=self.public_key,
        )
        (self.root / chain.RECEIPT_FILE).write_text(
            json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def two_executions(tmp_path, *, scope="FULL_NEQ", name="tree", outcomes=None):
    """E1 decides two pairs and is killed with one pair started; E2 resumes and finishes."""
    tree = ChainTree(tmp_path / name, scope=scope)
    outcomes = outcomes or {}
    e1, e2 = _run_id(1), _run_id(2)
    tree.start(e1)
    for pair in tree.pairs[:2]:
        tree.decide(e1, pair, outcome=outcomes.get(pair, "UNKNOWN"),
                    supervisor="TIMEOUT" if outcomes.get(pair) == "TIMEOUT" else "RESOLVED")
    tree.leave_incomplete(e1, tree.pairs[2])
    tree.start(e2)
    for pair in tree.pairs[2:]:
        tree.decide(e2, pair, outcome=outcomes.get(pair, "NOT_EQ"))
    tree.finish(e2, reused=tree.pairs[:2])
    return tree, e1, e2


def _verify(tree) -> dict:
    return chain.verify_execution_chain(tree.root)


# ---------------------------------------------------------------------------
# 1. 正常: 単一 execution・2 execution・複数回の中断
# ---------------------------------------------------------------------------


def test_a_single_execution_tree_is_closed_and_complete_as_before(tmp_path):
    tree = ChainTree(tmp_path / "tree")
    run = _run_id(7)
    tree.start(run)
    for pair in tree.pairs:
        tree.decide(run, pair)
    tree.finish(run, reused=[])
    report = _verify(tree)
    assert report["verdict"] == chain.VERDICT_CLOSED, report["reasons"]
    assert report["pairs_executed_by_latest"] == 4 and len(report["executions"]) == 1
    part = outcome_transition.tree_completeness(tree.root)
    # 1 execution だけの tree の判定は今と変わらない（検証器は呼ばれない）。
    assert part.status == outcome_transition.COMPLETENESS_COMPLETE
    assert part.execution_chain_verdict is None


@pytest.mark.parametrize("scope", ("FULL_NEQ", "FULL_EQBENCH"))
def test_a_resumed_full_tree_is_closed_and_complete_across_two_executions(tmp_path, scope):
    tree, e1, e2 = two_executions(tmp_path, scope=scope)
    report = _verify(tree)
    assert report["verdict"] == chain.VERDICT_CLOSED, report["reasons"]
    executions = {row["runtime_run_id"]: row for row in report["executions"]}
    # kill された E1 は封印されていない。E1 の確定 2 + E2 の実行 2 が census と一致する。
    assert executions[e1]["sealed"] is False and executions[e2]["sealed"] is True
    assert executions[e1]["decided_pairs_attributed"] == 2
    assert executions[e2]["decided_pairs_attributed"] == 2
    assert report["pairs_reused_proven"] == 2 and report["pairs_expected"] == 4
    part = outcome_transition.tree_completeness(tree.root)
    assert part.status == outcome_transition.COMPLETENESS_COMPLETE
    assert "complete across 2 executions" in part.detail
    assert part.as_dict()["pairs_reused_unproven"] == 0
    row = verification_ledger.build_row(tree.root, requested_scope=SCOPES[scope])
    assert row["completed_scope"] == outcome_transition.COMPLETENESS_COMPLETE
    assert verification_ledger.full_scope_evidence(row) == (SCOPES[scope], "")


def test_three_executions_with_two_kills_close_without_gaps_or_duplicates(tmp_path):
    tree = ChainTree(tmp_path / "tree", pairs=6)
    e1, e2, e3 = _run_id(1), _run_id(2), _run_id(3)
    tree.start(e1)
    tree.decide(e1, tree.pairs[0])
    tree.leave_incomplete(e1, tree.pairs[1])
    tree.start(e2)
    tree.decide(e2, tree.pairs[1])
    tree.decide(e2, tree.pairs[2])
    tree.leave_incomplete(e2, tree.pairs[3])
    tree.start(e3)
    for pair in tree.pairs[3:]:
        tree.decide(e3, pair)
    tree.finish(e3, reused=tree.pairs[:3])
    report = _verify(tree)
    assert report["verdict"] == chain.VERDICT_CLOSED, report["reasons"]
    counts = {row["runtime_run_id"]: row["decided_pairs_attributed"] for row in report["executions"]}
    assert counts == {e1: 1, e2: 2, e3: 3}
    assert sum(counts.values()) == report["pairs_expected"] == 6


def test_the_records_survive_every_execution_and_the_publication_still_rebuilds(tmp_path):
    tree, e1, e2 = two_executions(tmp_path)
    executions = tree.root / chain.EXECUTIONS_DIR
    assert (executions / e1 / chain.START_RECORD).is_file()
    assert not (executions / e1 / chain.RECEIPT_FILE).exists()
    for name, top in ((chain.PUBLICATION_FILE, chain.PUBLICATION_FILE),
                      (chain.RECEIPT_FILE, chain.RECEIPT_FILE),
                      (chain.END_RECORD, chain.RUN_MANIFEST_FILE)):
        assert (executions / e2 / name).read_bytes() == (tree.root / top).read_bytes()
    stored = json.loads((tree.root / chain.PUBLICATION_FILE).read_text())
    assert er.build_matrix_publication_manifest(tree.root) == stored
    assert stored["prior_executions"] == [
        {"runtime_run_id": e1, "start_record_sha256": chain.start_record_sha256(tree.root, e1)}]
    row = verification_ledger.build_row(tree.root, requested_scope="full_neq")
    assert row["scope_evidence"]["trees"]["."]["execution_binding"]["status"] == "ok"
    # 記録は上書きできない。
    again = tmp_path / "again.txt"
    again.write_text("".join(f"{k}={v}\n" for k, v in tree.start_fields(e1).items()))
    with pytest.raises(FileExistsError):
        chain.record_start(tree.root, e1, again)


# ---------------------------------------------------------------------------
# 2. Issue #276: 確定した ERROR は分母に残り、full verdict を妨げない。未完了は妨げる。
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("scope", ("FULL_NEQ", "FULL_EQBENCH"))
def test_a_full_tree_with_decided_error_and_timeout_gets_a_full_verdict(tmp_path, scope):
    pairs = ChainTree(tmp_path / "shape", scope=scope).pairs
    tree, e1, e2 = two_executions(
        tmp_path, scope=scope, name="decided",
        outcomes={pairs[0]: "ERROR", pairs[1]: "TIMEOUT", pairs[3]: "ERROR"},
    )
    publication = json.loads((tree.root / chain.PUBLICATION_FILE).read_text())
    assert publication["run_pair_failures"] == 0
    report = _verify(tree)
    assert report["verdict"] == chain.VERDICT_CLOSED, report["reasons"]
    row = verification_ledger.build_row(tree.root, requested_scope=SCOPES[scope])
    tree_row = row["scope_evidence"]["trees"]["."]
    assert tree_row["scope_health"]["status"] == verification_ledger.SCOPE_HEALTH_OK
    assert verification_ledger.full_scope_evidence(row) == (SCOPES[scope], "")
    # 確定した ERROR は一次結果として分母に残る。
    assert row["counts"]["ERROR"] == 2 and row["counts"]["TIMEOUT"] == 1


@pytest.mark.parametrize("scope", ("FULL_NEQ", "FULL_EQBENCH"))
def test_a_full_tree_with_an_incomplete_pair_gets_no_full_verdict(tmp_path, scope):
    tree = ChainTree(tmp_path / "tree", scope=scope)
    run = _run_id(1)
    tree.start(run)
    for pair in tree.pairs[:3]:
        tree.decide(run, pair)
    # 分類に失敗した pair（署名の無い診断）。runner はこれを未完了として run の失敗に数える。
    tree.issue(run, tree.pairs[3], tree.next_nonce())
    (tree.root / tree.relative(tree.pairs[3])).write_text(json.dumps({
        "classification_valid": False, "error_kind": "PAIR_STATUS_AUTHORITY_INVALID",
        "detail": "classification failed",
    }))
    tree.finish(run, reused=[], end_overrides={"run_pair_failures": "1", "incomplete_pair_jobs": "1"})
    report = _verify(tree)
    assert report["verdict"] == chain.VERDICT_OPEN
    assert set(report["reasons"]) == {chain.R_NOT_DECIDED}
    row = verification_ledger.build_row(tree.root, requested_scope=SCOPES[scope])
    evidence, reason = verification_ledger.full_scope_evidence(row)
    assert evidence is None and "run_pair_failures=1" in reason


# ---------------------------------------------------------------------------
# 3. 改ざん・欠損・混在・古い証拠・重複: 名前付きの理由で OPEN（fail-closed）
# ---------------------------------------------------------------------------


def _resign_publication(tree, mutate):
    publication = json.loads((tree.root / chain.PUBLICATION_FILE).read_text())
    mutate(publication)
    body = {k: v for k, v in publication.items() if k != "artifact_digest"}
    publication["artifact_digest"] = authority_digest(body)
    (tree.root / chain.PUBLICATION_FILE).write_text(json.dumps(publication, indent=2, sort_keys=True) + "\n")
    tree.seal_receipt(publication)


def _replace_status(tree, pair, **target_changes):
    """Re-sign the pair's status with a changed target, keeping its nonce."""
    path = tree.root / tree.relative(pair)
    old = json.loads(path.read_text())
    path.write_text(json.dumps(tree.sealed_status(
        pair, outcome=old["canonical_outcome"], nonce=old["execution_nonce"],
        target=tree.target(pair, **target_changes))))


def t_other_source(tree, e1, e2):
    _replace_status(tree, tree.pairs[0], analysis_source_digest="b" * 64)


def t_other_config(tree, e1, e2):
    _replace_status(tree, tree.pairs[3], analysis_config_digest="c" * 64)


def t_moved_path(tree, e1, e2):
    # pair 0 の status を pair 1 の場所へ置く（中身は pair 0 のまま有効に署名されている）。
    shutil.copy(tree.root / tree.relative(tree.pairs[0]), tree.root / tree.relative(tree.pairs[1]))


def t_binary_sha(tree, e1, e2):
    _replace_status(tree, tree.pairs[2], left_binary_sha256="e" * 64)


def t_status_replaced_after_publication(tree, e1, e2):
    # 再利用した pair を、同じ nonce・同じ target で別の outcome に署名し直す。
    path = tree.root / tree.relative(tree.pairs[0])
    old = json.loads(path.read_text())
    path.write_text(json.dumps(tree.sealed_status(
        tree.pairs[0], outcome="EQUIVALENT", nonce=old["execution_nonce"])))


def t_executed_status_replaced_after_publication(tree, e1, e2):
    path = tree.root / tree.relative(tree.pairs[3])
    old = json.loads(path.read_text())
    path.write_text(json.dumps(tree.sealed_status(
        tree.pairs[3], outcome="EQUIVALENT", nonce=old["execution_nonce"])))


def t_other_environment(tree, e1, e2):
    record = tree.root / chain.EXECUTIONS_DIR / e1 / chain.START_RECORD
    record.chmod(0o644)
    record.write_text(record.read_text().replace(
        "environment_fingerprint=image-sha256-x", "environment_fingerprint=image-sha256-y"))


def t_other_parallelism(tree, e1, e2):
    # parallel_jobs は config identity に入るので、別の P の start record は config digest も違う。
    record = tree.root / chain.EXECUTIONS_DIR / e1 / chain.START_RECORD
    fields = tree.start_fields(e1, parallel_jobs="20")
    record.chmod(0o644)
    record.write_text("".join(f"{k}={v}\n" for k, v in fields.items()))


def t_producer_without_start_record(tree, e1, e2):
    (tree.root / chain.EXECUTIONS_DIR / e1 / chain.START_RECORD).unlink()


def t_unsigned_status(tree, e1, e2):
    (tree.root / tree.relative(tree.pairs[1])).write_text(json.dumps({
        "classification_valid": False, "error_kind": "PAIR_STATUS_AUTHORITY_INVALID",
        "detail": "x"}))


def t_unattributed(tree, e1, e2):
    issued = tree.root / chain.EXECUTIONS_DIR / e1 / chain.ISSUED_DIR
    nonce = json.loads((tree.root / tree.relative(tree.pairs[0])).read_text())["execution_nonce"]
    (issued / f"{nonce}.json").unlink()


def t_duplicate_issue(tree, e1, e2):
    nonce = json.loads((tree.root / tree.relative(tree.pairs[0])).read_text())["execution_nonce"]
    tree.issue(e2, tree.pairs[0], nonce)


def t_reused_evidence_producer(tree, e1, e2):
    def mutate(publication):
        publication["reused_pair_evidence"][0]["producing_run_id"] = e2
    _resign_publication(tree, mutate)


def t_reused_evidence_missing(tree, e1, e2):
    def mutate(publication):
        publication["reused_pair_evidence"] = publication["reused_pair_evidence"][1:]
    _resign_publication(tree, mutate)


def t_executed_by_an_earlier_execution(tree, e1, e2):
    # census は pair 0 を「実行した」と言うが、その status は E1 のもの（再利用の申告漏れ）。
    def mutate(publication):
        publication["verified_skipped_pair_status_paths"] = [tree.relative(tree.pairs[1])]
        publication["reused_pair_evidence"] = publication["reused_pair_evidence"][1:]
    _resign_publication(tree, mutate)


def t_latest_unsealed(tree, e1, e2):
    (tree.root / chain.EXECUTIONS_DIR / e2 / chain.RECEIPT_FILE).unlink()


def t_stale_publication(tree, e1, e2):
    # 新しい execution が始まった（kill された）後に残っている、前の execution の publication。
    tree.start(_run_id(3))


def t_unrecognised_entry(tree, e1, e2):
    (tree.root / chain.EXECUTIONS_DIR / "notes.txt").write_text("x")


def t_v3_publication(tree, e1, e2):
    manifest = tree.root / chain.RUN_MANIFEST_FILE
    manifest.write_text(manifest.read_text().replace(
        f"{er.MATRIX_PUBLICATION_SCHEMA_KEY}={er.MATRIX_PUBLICATION_SCHEMA_V4}\n", ""))
    publication = er.build_matrix_publication_manifest(tree.root)
    (tree.root / chain.PUBLICATION_FILE).write_text(json.dumps(publication, indent=2, sort_keys=True) + "\n")
    tree.seal_receipt(publication)


TAMPERING = {
    # status を差し替えると、全 pair の evidence digest が変わり、publication の再構築も一致しない。
    "other-source": (t_other_source, {chain.R_TARGET, chain.R_BINDING}),
    "other-config": (t_other_config, {chain.R_TARGET, chain.R_BINDING}),
    "moved-path": (t_moved_path, {chain.R_PATH, chain.R_BINDING}),
    "binary-sha": (t_binary_sha, {chain.R_BINARY, chain.R_BINDING}),
    "reused-status-replaced": (t_status_replaced_after_publication,
                               {chain.R_REUSED_EVIDENCE, chain.R_BINDING}),
    "executed-status-replaced": (t_executed_status_replaced_after_publication, {chain.R_BINDING}),
    # start の記録を変えると、publication が封じた記録の digest とも一致しない。
    "other-environment": (t_other_environment, {chain.R_CONDITIONS, chain.R_PRIOR, chain.R_BINDING}),
    "other-parallelism": (t_other_parallelism, {chain.R_CONDITIONS, chain.R_PRIOR, chain.R_BINDING}),
    "producer-without-start": (t_producer_without_start_record, {
        chain.R_START_MISSING, chain.R_PRODUCER_NO_START, chain.R_PRIOR, chain.R_BINDING}),
    "unsigned-status": (t_unsigned_status, {chain.R_NOT_DECIDED, chain.R_BINDING}),
    "unattributed": (t_unattributed, {chain.R_UNATTRIBUTED, chain.R_BINDING}),
    "duplicate-issue": (t_duplicate_issue, {chain.R_DUPLICATE_ISSUE, chain.R_BINDING}),
    # publication を封じ直すと、最新の execution の封印の複製と一致しない。
    "reused-evidence-producer": (t_reused_evidence_producer, {
        chain.R_REUSED_EVIDENCE, chain.R_BINDING, chain.R_LATEST_UNSEALED}),
    "reused-evidence-missing": (t_reused_evidence_missing, {chain.R_NO_PUBLICATION}),
    "executed-by-earlier": (t_executed_by_an_earlier_execution, {
        chain.R_EXECUTED_PRODUCER, chain.R_BINDING, chain.R_LATEST_UNSEALED}),
    "latest-unsealed": (t_latest_unsealed, {chain.R_LATEST_UNSEALED, chain.R_SEALED_INVALID}),
    "stale-publication": (t_stale_publication, {
        chain.R_LATEST_START, chain.R_LATEST_UNSEALED, chain.R_PRIOR, chain.R_BINDING}),
    "unrecognised-entry": (t_unrecognised_entry, {chain.R_UNRECOGNISED, chain.R_BINDING}),
    "v3-publication": (t_v3_publication, {chain.R_NO_CHAIN_FIELDS}),
}


@pytest.mark.parametrize("case", sorted(TAMPERING))
def test_each_tampering_opens_the_chain_with_its_named_reason(tmp_path, case):
    tree, e1, e2 = two_executions(tmp_path)
    assert _verify(tree)["verdict"] == chain.VERDICT_CLOSED
    mutate, expected = TAMPERING[case]
    mutate(tree, e1, e2)
    report = _verify(tree)
    assert report["verdict"] == chain.VERDICT_OPEN
    assert set(report["reasons"]) == expected, report["reasons"]
    part = outcome_transition.tree_completeness(tree.root)
    assert part.status != outcome_transition.COMPLETENESS_COMPLETE


def test_a_representative_tree_with_reuse_stays_partial_even_when_the_chain_closes(tmp_path):
    tree, e1, e2 = two_executions(tmp_path, scope="REPRESENTATIVE")
    assert _verify(tree)["verdict"] == chain.VERDICT_CLOSED
    part = outcome_transition.tree_completeness(tree.root)
    assert part.status == outcome_transition.COMPLETENESS_PARTIAL
    assert part.execution_chain_verdict is None
    assert "reused from an earlier run, not executed here" in part.detail


# ---------------------------------------------------------------------------
# 4. 記録の writer: start が無ければ issue できない・上書きしない・tree の外は拒否
# ---------------------------------------------------------------------------


def test_an_issue_record_needs_the_start_record_and_is_never_replaced(tmp_path):
    tree = ChainTree(tmp_path / "tree")
    run = _run_id(1)
    with pytest.raises(ValueError, match="no start record"):
        tree.issue(run, tree.pairs[0], tree.next_nonce())
    tree.start(run)
    nonce = tree.next_nonce()
    tree.issue(run, tree.pairs[0], nonce)
    with pytest.raises(FileExistsError):
        tree.issue(run, tree.pairs[0], nonce)
    target_file = tmp_path / "t.json"
    target_file.write_text(json.dumps(tree.target(tree.pairs[0])))
    with pytest.raises(ValueError):
        chain.record_issue(tree.root, run, execution_nonce=tree.next_nonce(),
                           pair_status_path=tmp_path / "elsewhere.pair-status.json",
                           target_file=target_file)


def test_the_cli_refuses_and_reports_instead_of_writing(tmp_path):
    tree = ChainTree(tmp_path / "tree")
    code = chain.main(["start", "--root", str(tree.root), "--run-id", "nothex",
                       "--manifest", str(tmp_path / "missing")])
    assert code == 1
    assert not (tree.root / chain.EXECUTIONS_DIR).exists()


# ---------------------------------------------------------------------------
# 5. 実行条件: FT_* は config identity に入る（変えると resume は REFUSE）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("knob", (
    "expander_dedup_case_limit_effective", "callee_unbound_reuse", "callee_unbound_reuse_shadow",
))
def test_an_ft_knob_changes_the_config_digest_and_refuses_a_resume(tmp_path, knob, monkeypatch):
    tree, e1, e2 = two_executions(tmp_path)
    changed = tree.start_fields(_run_id(9), **{knob: "999"})
    assert changed["analysis_config_digest"] != tree.config_digest()
    candidate = tmp_path / "candidate.txt"
    candidate.write_text("".join(f"{k}={v}\n" for k, v in changed.items()))
    monkeypatch.setattr(er, "source_tree_digest", lambda root: SOURCE)
    kind, reason = er.full_scope_output_admission(
        tree.root, candidate_manifest=candidate, repo_root=tmp_path)
    assert kind == er.OUTPUT_ADMISSION_REFUSE and "another analysis config" in reason
    same = tree.start_fields(_run_id(9))
    candidate.write_text("".join(f"{k}={v}\n" for k, v in same.items()))
    assert er.full_scope_output_admission(
        tree.root, candidate_manifest=candidate, repo_root=tmp_path)[0] == (
        er.OUTPUT_ADMISSION_SAME_IDENTITY_RESUME)


def test_a_v5_config_is_never_projected_onto_an_older_schema(tmp_path):
    fields = ChainTree(tmp_path / "tree").start_fields(_run_id(1))
    config = er.analysis_config_from_run(fields)
    assert er.normalize_semantic_analysis_config(config)["schema"] == er.ANALYSIS_CONFIG_V5_SCHEMA
    del fields["callee_unbound_reuse"]
    with pytest.raises(ValueError):
        er.analysis_config_from_run(fields)


# ---------------------------------------------------------------------------
# 6. 時間の chain view: 各 pair の時間は、それを作った execution の receipt から
# ---------------------------------------------------------------------------


def _receipt(tree, pair, run_id, seconds, *, nonce):
    sample, function, left, right = pair
    metrics = tree.root / sample / function / prr.RUNTIME_METRICS_DIR
    payload = prr.build_receipt(
        state=prr.STATE_COMPLETED, function_name=function, left_binary_id=left,
        right_binary_id=right, execution_nonce=nonce, run_id=run_id,
        fields={name: "-" for name in (*prr._NUMBER_FIELDS, *prr._INTEGER_FIELDS, *prr._TEXT_FIELDS)},
        usage_files=[],
    )
    payload = {**payload, "elapsed_seconds": seconds, "measurement_complete": True}
    prr.write_receipt(metrics, f"{function}_{left}_{right}", payload)


def test_the_chain_view_counts_each_execution_and_never_zero_fills(tmp_path):
    tree, e1, e2 = two_executions(tmp_path)
    nonces = {pair: json.loads((tree.root / tree.relative(pair)).read_text())["execution_nonce"]
              for pair in tree.pairs}
    _receipt(tree, tree.pairs[0], e1, 10.0, nonce=nonces[tree.pairs[0]])
    _receipt(tree, tree.pairs[2], e2, 5.0, nonce=nonces[tree.pairs[2]])
    _receipt(tree, tree.pairs[3], e2, 7.0, nonce=nonces[tree.pairs[3]])
    view = prr.load_chain_measurements(tree.root).as_dict()
    assert view["measured_by_execution"] == {e1: 1, e2: 2}
    assert view["pairs_measured"] == 3 and view["pairs_without_measurement"] == 1
    assert view["measured_seconds_total"] == 22.0
    # 最新の run だけの delta の意味は変わらない（E1 の receipt は retained）。
    latest = prr.load_tree_measurements(tree.root)
    assert len(latest.measured) == 2 and len(latest.retained) == 1

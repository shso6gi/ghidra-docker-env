# -*- coding: utf-8 -*-
"""Issue #323 (C4): the concrete-execution evaluation report over synthetic trees.

Each tree is laid out as the runners write it -- ``run_manifest.txt``, the
publication manifest, ``<sample>/<function>/<function>_<pair>.pair-status.json``
and the pair log with the result JSON block -- so the report reads it through
the same readers as a real run.  The counts asserted here fix how each section
counts, including what it does with missing and unreadable records.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, List, Optional

import pytest

from scripts.function_tracer_pcode.proof.concrete_counterexample import _digest
from scripts.function_tracer_pcode.reporting import concrete_evaluation as ce

SHA_A = "a" * 64
SHA_B = "b" * 64
EQ_SAMPLE = "S/Eq/newV"
NEQ_SAMPLE = "S/Neq/newV-oldV"
CORE_EXCLUDED_SAMPLE = "CLEVER/UnchLoop/Neq/newV-oldV"


def _manifest(stages: str, budget: str, **overrides: str) -> Dict[str, str]:
    run = {
        "run_scope": "REPRESENTATIVE", "build_policy": "REUSE_OR_COMPILE", "max_samples": "0",
        "sample_filter": "", "pair_filter": "", "debug": "0", "dry_run": "0",
        "parallel_jobs": "4", "validation_summary_level": "compact", "equiv_timeout": "10",
        "decompile_timeout": "60", "pairwise_timeout": "5", "pairwise_timeout_hard": "30",
        "pair_process_timeout_seconds": "600", "pair_process_kill_after_seconds": "30",
        "prefilter_source_census_digest": "0" * 64, "identical_fast_path": "1",
        "analysis_timeout": "410", "analysis_timeout_margin": "190",
        "expander_dedup_case_limit_effective": "16", "callee_unbound_reuse": "1",
        "callee_unbound_reuse_shadow": "0",
        "analysis_config_schema": "eqbench-analysis-config-v6",
        "concrete_stages_requested": stages, "concrete_budget_requested": "60",
        "concrete_stages": stages, "concrete_budget": budget,
        "concrete_inactive_reason": "active" if stages != "none" else "not_requested",
        "analysis_source_digest_start": "1" * 64, "analysis_source_digest_end": "1" * 64,
        "python_version": "3.10", "ghidra_version": "12.0.1",
    }
    run.update(overrides)
    return run


def _setting(on: bool) -> Dict[str, Any]:
    return {
        "schema": "concrete-execution-setting-v1",
        "stages": ["witness_replay"] if on else [],
        "effective_stages": ["witness_replay"] if on else [],
        "inactive_reason": None if on else "not_requested",
        "budget_seconds": 60.0 if on else None, "run_time_limit_seconds": 20.0 if on else None,
        "step_limit": 300000 if on else None, "analysis_deadline_seconds": 410.0,
    }


def _concrete(confirmed: bool, replays: List[Dict[str, Any]], reasons=None, plan="OK") -> Dict[str, Any]:
    payload = {
        "adapter": "concrete-counterexample-proof-v1",
        "proof_kind": "CONDITIONAL_CONCRETE_COUNTEREXAMPLE" if confirmed else None,
        "assumption_set": [], "plan": plan, "witness_count": len(replays) or 1,
        "replays": replays, "confirmed": 0 if confirmed else None, "programs": [],
        "non_decisive_reasons": [] if confirmed else list(reasons or ["concrete_replay_not_confirmed"]),
    }
    return {"artifact_payload": payload, "artifact_digest": _digest(payload), "premises": [],
            "diagnostics": {"seconds": 0.5, "replayed": len(replays)}}


def _replay(status: str, reason: str, digest: str = "w1") -> Dict[str, Any]:
    return {"schema": "concrete-witness-replay-v1", "status": status, "reason": reason,
            "witness_digest": digest, "results": [{"termination": "RETURNED"}]}


def _row(reason: str, effect: str = "blocks_disequivalence") -> Dict[str, Any]:
    return {"reason_id": reason, "decision_effect": effect, "cause_id": reason, "occurrence_id": reason}


SAT = "counterexample_analysis_safety_unproven"


class TreeBuilder:
    def __init__(self, root: Path, stages: str, budget: str, **manifest: str) -> None:
        self.root = root
        self.on = stages != "none"
        root.mkdir(parents=True)
        self.manifest = _manifest(stages, budget, **manifest)
        self.paths: List[str] = []

    def pair(self, sample: str, function: str, left: str, right: str, *, outcome: str,
             conditional: Optional[str] = None, lane: Optional[Dict[str, Any]] = None,
             rows=(), payload: bool = True, setting: Optional[Dict[str, Any]] = None,
             shas=(SHA_A, SHA_B), payload_conditional: Any = "same", premise_kinds=None,
             ) -> None:
        directory = self.root / sample / function
        directory.mkdir(parents=True, exist_ok=True)
        stem = f"{function}_{left}_{right}"
        status: Dict[str, Any] = {
            "canonical_outcome": outcome, "result_occurrence_id": "occ",
            "pair_execution_target": {
                "sample_identity": sample, "function_name": function,
                "left_binary_id": left, "right_binary_id": right,
                "left_binary_sha256": shas[0], "right_binary_sha256": shas[1],
            },
        }
        if conditional is not None:
            kinds = premise_kinds if premise_kinds is not None else (
                ["CONCRETE_CALLING_CONVENTION"] if lane and lane.get("concrete_replay") else ["X"])
            status["conditional_outcome"] = conditional
            status["conditional_decision_receipt"] = {
                "conditional_outcome": conditional, "result_occurrence_id": "occ",
                "assumption_set": [{"kind": kind} for kind in kinds],
            }
        (directory / f"{stem}.pair-status.json").write_text(json.dumps(status))
        log = "header\n"
        if payload:
            result = {
                "final_outcome": outcome,
                "conditional_outcome": conditional if payload_conditional == "same" else payload_conditional,
                "c_active_base": list(rows),
                "diagnostics": {
                    "concrete_execution_setting": setting if setting is not None else _setting(self.on),
                    "timings": {"boundary_seconds": {"conditional_lane": 0.25}},
                },
            }
            if lane is not None:
                result["diagnostics"]["conditional_lane"] = lane
            log += ("=== EQUIVALENCE_RESULT_JSON_BEGIN ===\n" + json.dumps(result)
                    + "\n=== EQUIVALENCE_RESULT_JSON_END ===\n")
        (directory / f"{stem}.log").write_text(log)
        self.paths.append(f"{sample}/{function}/{stem}.pair-status.json")

    def close(self) -> Path:
        (self.root / "run_manifest.txt").write_text(
            "".join(f"{k}={v}\n" for k, v in self.manifest.items()))
        (self.root / "matrix-publication-manifest.json").write_text(json.dumps({
            "schema": "eqbench-matrix-publication-manifest-v4", "run_scope": "REPRESENTATIVE",
            "expected_pair_status_paths": sorted(self.paths), "verified_skipped_pair_status_paths": [],
        }))
        return self.root


def _lane(concrete=None, **extra) -> Dict[str, Any]:
    lane = {"conditional_lane": "non_decisive", **extra}
    if concrete is not None:
        lane["concrete_replay"] = concrete
    return lane


def _populate(builder: TreeBuilder) -> None:
    """One pair per situation the report has to tell apart."""
    on = builder.on
    confirmed = _concrete(True, [_replay("CONFIRMED", "INT")]) if on else None
    # 1. confirmed, only SAT-safety blocked -> conditional NOT_EQ
    builder.pair(NEQ_SAMPLE, "f", "N_B1", "O_B1", outcome="UNKNOWN",
                 conditional="NOT_EQ" if on else None,
                 lane=_lane(confirmed, conditional_lane="issued") if on else _lane(),
                 rows=[_row(SAT)])
    # 2. confirmed, a recurrence row remains -> held at conditional UNKNOWN
    builder.pair(NEQ_SAMPLE, "f", "N_B2", "O_B2", outcome="UNKNOWN",
                 conditional="UNKNOWN" if on else None,
                 lane=_lane(confirmed, conditional_lane="issued") if on else _lane(),
                 rows=[_row(SAT), _row("recurrence_proposal_validation_unproven", "blocks_decision"),
                       _row("outcome_path_region_completeness_unproven", "blocks_equivalence")])
    # 3. confirmed (other function), two other reasons remain
    builder.pair(NEQ_SAMPLE, "g", "N_B1", "O_B1", outcome="UNKNOWN",
                 conditional="UNKNOWN" if on else None,
                 lane=_lane(confirmed, conditional_lane="issued") if on else _lane(),
                 rows=[_row(SAT), _row("recurrence_proposal_validation_unproven"),
                       _row("pure_call_semantics_unproven")])
    # 4. replayed, no evidence: one hazard and one time limit
    nothing = _concrete(False, [
        _replay("NO_EVIDENCE", "RUN_HAS_HAZARD:side0:UNDEFINED_MEMORY_READ", "w2"),
        _replay("NO_EVIDENCE", "RUN_DID_NOT_RETURN:side1:TIME_LIMIT", "w3"),
    ], reasons=["concrete_replay_not_confirmed", "concrete_replay_budget_exhausted"]) if on else None
    builder.pair(NEQ_SAMPLE, "h", "N_B1", "O_B1", outcome="UNKNOWN", lane=_lane(nothing), rows=[_row(SAT)])
    # 5. no witness
    builder.pair(NEQ_SAMPLE, "h", "N_B2", "O_B2", outcome="UNKNOWN",
                 lane=_lane(_concrete(False, [], reasons=["concrete_replay_no_witness"]) if on else None))
    # 6. input correspondence refused at the plan
    refused = _concrete(False, [], reasons=["concrete_replay_plan_refused"],
                        plan="INPUT_SURFACE:side0:PARAMETER_NOT_IN_REGISTER") if on else None
    builder.pair(NEQ_SAMPLE, "h", "N_B3", "O_B3", outcome="UNKNOWN", lane=_lane(refused))
    # 7. lane not run (counterexample committed)
    builder.pair(NEQ_SAMPLE, "k", "N_B1", "O_B1", outcome="UNKNOWN",
                 lane={"skipped": "counterexample_committed", "pair_stop_state": "x"})
    # 8. main NOT_EQ (not eligible)
    builder.pair(NEQ_SAMPLE, "k", "N_B2", "O_B2", outcome="NOT_EQ")
    # 9. TIMEOUT without a payload
    builder.pair(NEQ_SAMPLE, "k", "N_B3", "O_B3", outcome="TIMEOUT", payload=False)
    # 10. Neq-Core excluded function, confirmed
    builder.pair(CORE_EXCLUDED_SAMPLE, "foo", "N_B1", "O_B1", outcome="UNKNOWN",
                 conditional="NOT_EQ" if on else None,
                 lane=_lane(confirmed, conditional_lane="issued") if on else _lane(),
                 rows=[_row(SAT)])
    # 11/12. Eq pairs: equivalent, and UNKNOWN whose replay found no difference
    builder.pair(EQ_SAMPLE, "e", "B1", "B2", outcome="EQUIVALENT")
    same = _concrete(False, [_replay("NO_EVIDENCE", "NO_DIFFERENCE_OBSERVED", "w4")]) if on else None
    builder.pair(EQ_SAMPLE, "e", "B1", "B3", outcome="UNKNOWN", lane=_lane(same), rows=[_row(SAT)])


@pytest.fixture
def trees(tmp_path):
    off = TreeBuilder(tmp_path / "off", "none", "0")
    on = TreeBuilder(tmp_path / "on", "witness_replay", "60")
    _populate(off)
    _populate(on)
    return off.close(), on.close()


def test_a_matched_pair_of_trees_is_comparable_and_consistent(trees):
    report = ce.build_report(*trees)

    assert report["conditions"]["comparable"], report["conditions"]
    assert report["setting_records"]["baseline"]["ok"]
    assert report["setting_records"]["treatment"]["ok"]
    assert report["setting_records"]["treatment"]["counts"] == {"agrees": 11, "no_result_payload": 1}
    assert report["integrity"]["treatment"]["ok"], report["integrity"]
    assert ce.report_exit_code(report) == ce.EXIT_OK


def test_the_three_tiers_are_counted_apart(trees):
    det = ce.build_report(*trees)["detection"]

    neq = det["treatment"]["neq"]
    assert neq["main_not_eq"] == {"pairs": 1, "function_pairs": 1}
    assert neq["conditional_not_eq"] == {"pairs": 2, "function_pairs": 2}
    assert neq["concrete_difference"] == {"pairs": 4, "function_pairs": 3}
    assert neq["main_or_conditional_not_eq"] == {"pairs": 3, "function_pairs": 3}
    # Neq-Core leaves the UnchLoop foo out
    core = det["treatment"]["neq_core"]
    assert core["pairs"] == neq["pairs"] - 1
    assert core["conditional_not_eq"] == {"pairs": 1, "function_pairs": 1}
    # the baseline (SMT only) has the main column and nothing else
    assert det["baseline"]["neq"]["conditional_not_eq"] == {"pairs": 0, "function_pairs": 0}
    assert det["baseline"]["neq"]["concrete_difference"] == {"pairs": 0, "function_pairs": 0}
    assert det["treatment"]["eq_false_not_eq"] == {
        "main": 0, "conditional": 0, "concrete_difference": 0, "pairs": []}


def test_detection_against_the_smt_only_baseline_keeps_the_columns_apart(trees):
    against = ce.build_report(*trees)["against_baseline"]

    neq = against["neq"]
    assert neq["baseline_main_not_eq"] == {"pairs": 1, "function_pairs": 1}
    assert neq["gained_main"] == {"pairs": 0, "function_pairs": 0}
    assert neq["gained_conditional_only"] == {"pairs": 2, "function_pairs": 2}
    assert neq["lost_main"] == {"pairs": 0, "function_pairs": 0}
    assert neq["difference_only"] == {"pairs": 2, "function_pairs": 2}
    assert against["neq_core"]["gained_conditional_only"] == {"pairs": 1, "function_pairs": 1}
    assert against["eq"]["gained_conditional_only"] == {"pairs": 0, "function_pairs": 0}


def test_confirmed_pairs_held_back_are_broken_down_by_remaining_reason(trees):
    blocked = ce.build_report(*trees)["blocked"]

    assert blocked["pairs"] == 2 and blocked["function_pairs"] == 2
    # blocks_equivalence rows never hold a NOT_EQ back; SAT-safety is discharged
    assert blocked["per_reason"] == {
        "recurrence_proposal_validation_unproven": {
            "pairs": 2, "function_pairs": 2, "sole_remaining_reason_pairs": 1},
        "pure_call_semantics_unproven": {
            "pairs": 1, "function_pairs": 1, "sole_remaining_reason_pairs": 0},
    }
    assert blocked["combinations"] == {
        "recurrence_proposal_validation_unproven": 1,
        "pure_call_semantics_unproven,recurrence_proposal_validation_unproven": 1,
    }
    assert blocked["reconstruction"] == {"agrees": 4, "not_reconstructible": 0}


def test_the_funnel_separates_each_reason_a_pair_left_the_replay(trees):
    funnel = ce.build_report(*trees)["funnel"]

    assert funnel["pairs"] == {
        "confirmed": 4, "not_eligible": 3, "replayed_no_evidence": 2, "no_witness": 1,
        "plan_refused_input": 1, "lane_not_run": 1,
    }
    assert funnel["pair_details"]["replayed_no_evidence"] == {
        "hazard+limit+budget_exhausted": 1, "no_difference": 1}
    assert funnel["pair_details"]["lane_not_run"] == {"counterexample_committed": 1}
    assert funnel["witnesses"] == {"confirmed": 4, "hazard": 1, "limit": 1, "no_difference": 1}


def test_the_baseline_funnel_says_the_stage_was_off(trees):
    baseline = ce.load_tree(trees[0])

    classes = {ce.pair_funnel_class(f)[0] for f in baseline.facts.values() if f.outcome == "UNKNOWN"}
    assert classes == {"stage_off", "lane_not_run"}


def test_differences_count_pairs_function_pairs_and_witnesses(trees):
    diff = ce.build_report(*trees)["concrete_differences"]

    assert (diff["pairs"], diff["function_pairs"], diff["confirmed_witness_replays"]) == (4, 3, 4)
    assert diff["distinct_confirmed_witnesses"] == 1
    assert diff["conditional_of_confirmed"] == {"NOT_EQ": 2, "UNKNOWN": 2}


@pytest.mark.parametrize("override,name", [
    ({"analysis_source_digest_start": "2" * 64, "analysis_source_digest_end": "2" * 64}, "source_digest"),
    ({"parallel_jobs": "8"}, "analysis_config.parallel_jobs"),
    ({"analysis_timeout": "300"}, "analysis_config.analysis_timeout_seconds"),
    ({"ghidra_version": "12.1"}, "environment.ghidra_version"),
    ({"analysis_source_digest_end": "3" * 64}, "source_stable.treatment"),
])
def test_a_difference_in_conditions_is_named_and_blocks_unless_allowed(tmp_path, override, name):
    off = TreeBuilder(tmp_path / "off", "none", "0")
    on = TreeBuilder(tmp_path / "on", "witness_replay", "60", **override)
    _populate(off)
    _populate(on)
    roots = off.close(), on.close()

    report = ce.build_report(*roots)
    names = {c["name"] for c in report["conditions"]["checks"] if c["status"] != "same"}
    assert name in names
    assert ce.report_exit_code(report) == ce.EXIT_NOT_COMPARABLE

    allowed = ce.build_report(*roots, allowed=sorted(names))
    assert allowed["conditions"]["comparable"]
    assert allowed["conditions"]["allowed"] == sorted(names)


def test_different_binaries_or_pairs_block(tmp_path):
    off = TreeBuilder(tmp_path / "off", "none", "0")
    on = TreeBuilder(tmp_path / "on", "witness_replay", "60")
    _populate(off)
    _populate(on)
    on.pair(NEQ_SAMPLE, "z", "N_B1", "O_B1", outcome="UNKNOWN")
    off.pair(NEQ_SAMPLE, "z", "N_B2", "O_B2", outcome="UNKNOWN", shas=(SHA_A, SHA_A))
    on.pair(NEQ_SAMPLE, "z", "N_B2", "O_B2", outcome="UNKNOWN", shas=(SHA_A, SHA_B))
    report = ce.build_report(off.close(), on.close())

    checks = {c["name"]: c for c in report["conditions"]["checks"]}
    assert checks["pair_set"]["status"] == "differs"
    assert checks["pair_set"]["treatment"] == 1
    assert checks["binaries.differing_pairs"]["treatment"] == 1
    assert not report["conditions"]["comparable"]


def test_a_tree_without_the_concrete_identity_is_not_comparable(tmp_path):
    off = TreeBuilder(tmp_path / "off", "none", "0", analysis_config_schema="eqbench-analysis-config-v5")
    on = TreeBuilder(tmp_path / "on", "witness_replay", "60")
    _populate(off)
    _populate(on)
    report = ce.build_report(off.close(), on.close())

    names = {c["name"] for c in report["conditions"]["checks"] if c["status"] != "same"}
    assert "concrete_setting_recorded" in names
    assert not report["conditions"]["comparable"]


def test_a_pair_whose_record_contradicts_its_manifest_is_an_integrity_failure(tmp_path):
    off = TreeBuilder(tmp_path / "off", "none", "0")
    on = TreeBuilder(tmp_path / "on", "witness_replay", "60")
    _populate(off)
    _populate(on)
    off.pair(NEQ_SAMPLE, "z", "N_B1", "O_B1", outcome="UNKNOWN", lane=_lane())
    # the treatment says ON, this pair ran OFF (and so left no replay record)
    on.pair(NEQ_SAMPLE, "z", "N_B1", "O_B1", outcome="UNKNOWN", lane=_lane(), setting=_setting(False))
    report = ce.build_report(off.close(), on.close())

    assert report["setting_records"]["treatment"]["counts"]["disagrees"] == 1
    assert not report["setting_records"]["treatment"]["ok"]
    assert ce.report_exit_code(report) == ce.EXIT_INTEGRITY


def test_a_replay_record_in_an_off_tree_is_an_integrity_failure(tmp_path):
    off = TreeBuilder(tmp_path / "off", "none", "0")
    on = TreeBuilder(tmp_path / "on", "witness_replay", "60")
    _populate(off)
    _populate(on)
    record = _concrete(False, [], reasons=["concrete_replay_no_witness"])
    off.pair(NEQ_SAMPLE, "z", "N_B1", "O_B1", outcome="UNKNOWN", lane=_lane(record))
    on.pair(NEQ_SAMPLE, "z", "N_B1", "O_B1", outcome="UNKNOWN", lane=_lane(record))
    report = ce.build_report(off.close(), on.close())

    assert report["setting_records"]["baseline"]["replay_records_inconsistent_with_setting"] == 1
    assert ce.report_exit_code(report) == ce.EXIT_INTEGRITY


def test_status_and_result_json_disagreeing_is_an_integrity_failure(tmp_path):
    off = TreeBuilder(tmp_path / "off", "none", "0")
    on = TreeBuilder(tmp_path / "on", "witness_replay", "60")
    _populate(off)
    _populate(on)
    off.pair(NEQ_SAMPLE, "z", "N_B1", "O_B1", outcome="UNKNOWN", lane=_lane())
    on.pair(NEQ_SAMPLE, "z", "N_B1", "O_B1", outcome="UNKNOWN", conditional="NOT_EQ",
            payload_conditional="UNKNOWN", lane=_lane())
    report = ce.build_report(off.close(), on.close())

    assert report["integrity"]["treatment"]["failures"] == {"status_conditional_vs_result_json": 1}
    assert ce.report_exit_code(report) == ce.EXIT_INTEGRITY


def test_a_tampered_replay_record_fails_its_digest(tmp_path):
    off = TreeBuilder(tmp_path / "off", "none", "0")
    on = TreeBuilder(tmp_path / "on", "witness_replay", "60")
    _populate(off)
    _populate(on)
    record = _concrete(False, [], reasons=["concrete_replay_no_witness"])
    record["artifact_payload"]["witness_count"] = 99
    off.pair(NEQ_SAMPLE, "z", "N_B1", "O_B1", outcome="UNKNOWN", lane=_lane())
    on.pair(NEQ_SAMPLE, "z", "N_B1", "O_B1", outcome="UNKNOWN", lane=_lane(record))
    report = ce.build_report(off.close(), on.close())

    assert report["integrity"]["treatment"]["failures"] == {"concrete_artifact_digest": 1}


def test_a_reconstruction_that_contradicts_the_verdict_fails(tmp_path):
    off = TreeBuilder(tmp_path / "off", "none", "0")
    on = TreeBuilder(tmp_path / "on", "witness_replay", "60")
    _populate(off)
    _populate(on)
    off.pair(NEQ_SAMPLE, "z", "N_B1", "O_B1", outcome="UNKNOWN", lane=_lane())
    # NOT_EQ issued although a blocking row the concrete proof does not discharge remains
    on.pair(NEQ_SAMPLE, "z", "N_B1", "O_B1", outcome="UNKNOWN", conditional="NOT_EQ",
            lane=_lane(_concrete(True, [_replay("CONFIRMED", "INT")]), conditional_lane="issued"),
            rows=[_row("pure_call_semantics_unproven")])
    report = ce.build_report(off.close(), on.close())

    assert report["blocked"]["reconstruction"]["disagrees"] == 1
    assert ce.report_exit_code(report) == ce.EXIT_INTEGRITY


def test_an_eq_difference_is_reported_as_a_false_not_eq(tmp_path):
    off = TreeBuilder(tmp_path / "off", "none", "0")
    on = TreeBuilder(tmp_path / "on", "witness_replay", "60")
    _populate(off)
    _populate(on)
    off.pair(EQ_SAMPLE, "e", "B2", "B3", outcome="UNKNOWN", lane=_lane())
    on.pair(EQ_SAMPLE, "e", "B2", "B3", outcome="UNKNOWN", conditional="UNKNOWN",
            lane=_lane(_concrete(True, [_replay("CONFIRMED", "INT")]), conditional_lane="issued"),
            rows=[_row(SAT), _row("pure_call_semantics_unproven")])
    det = ce.build_report(off.close(), on.close())["detection"]["treatment"]

    assert det["eq_false_not_eq"]["concrete_difference"] == 1
    assert det["eq_false_not_eq"]["conditional"] == 0
    assert len(det["eq_false_not_eq"]["pairs"]) == 1


def test_the_cli_writes_json_and_tsv_and_returns_the_exit_code(trees, tmp_path, capsys):
    out, tsv = tmp_path / "r.json", tmp_path / "p.tsv"
    code = ce.main(["--baseline", str(trees[0]), "--treatment", str(trees[1]),
                    "--json", str(out), "--pairs", str(tsv)])

    assert code == ce.EXIT_OK
    assert json.loads(out.read_text())["schema"] == ce.REPORT_SCHEMA
    rows = tsv.read_text().splitlines()
    assert len(rows) == 13  # header + 12 pairs
    held = [r for r in rows if r.split("\t")[13] == "pure_call_semantics_unproven,"
            "recurrence_proposal_validation_unproven"]
    assert len(held) == 1
    assert "COMPARABLE" in capsys.readouterr().out

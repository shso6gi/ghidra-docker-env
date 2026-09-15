# -*- coding: utf-8 -*-
"""Issue #15 PR-15-B: the identical-input fast path is part of the analysis identity.

Turning the fast path off changes what a pair's result is evidence *of*, so the
two modes must not share an ``analysis_config_digest``: a resume or a summary
shortcut that reused an ON pair status for an OFF run would quietly destroy the
oracle the OFF run exists to provide.

A manifest opts into the new identity by naming ``analysis_config_schema``.  One
that does not name it keeps reading exactly as before, so every run recorded
before this change still publishes and still compares.
"""
from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.authority.contracts import authority_digest
from scripts.function_tracer_pcode.reporting.execution_receipt import (
    ANALYSIS_CONFIG_V3_FIELDS,
    ANALYSIS_CONFIG_V3_SCHEMA,
    _read_key_values,
    analysis_config_from_run,
    compatible_previous_run_manifest_analysis_identity,
    normalize_semantic_analysis_config,
    validate_analysis_config,
)

BASE_RUN = {
    "run_scope": "REPRESENTATIVE",
    "build_policy": "PREBUILT_ONLY",
    "max_samples": "0",
    "sample_filter": "",
    "pair_filter": "",
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
    "prefilter_source_census_digest": "census-digest",
}


def v3_run(flag: str = "1", **overrides):
    return dict(
        BASE_RUN,
        analysis_config_schema=ANALYSIS_CONFIG_V3_SCHEMA,
        identical_fast_path=flag,
        **overrides,
    )


def test_a_manifest_without_the_schema_key_still_reads_as_v2():
    config = analysis_config_from_run(BASE_RUN)
    assert config["schema"] == "eqbench-analysis-config-v2"
    assert "identical_fast_path" not in config


def test_the_v3_schema_carries_the_flag_as_an_exact_bool():
    on = analysis_config_from_run(v3_run("1"))
    off = analysis_config_from_run(v3_run("0"))

    assert on["schema"] == ANALYSIS_CONFIG_V3_SCHEMA
    assert set(on) == ANALYSIS_CONFIG_V3_FIELDS
    assert on["identical_fast_path"] is True
    assert off["identical_fast_path"] is False


def test_the_two_modes_and_the_legacy_identity_are_three_different_digests():
    digests = {
        authority_digest(analysis_config_from_run(run))
        for run in (BASE_RUN, v3_run("1"), v3_run("0"))
    }
    assert len(digests) == 3


def test_normalizing_a_v3_config_does_not_erase_the_mode():
    on = normalize_semantic_analysis_config(analysis_config_from_run(v3_run("1")))
    off = normalize_semantic_analysis_config(analysis_config_from_run(v3_run("0")))

    assert on["schema"] == ANALYSIS_CONFIG_V3_SCHEMA
    assert on != off
    # ... and a v3 run is not compatible with a v2 one either.
    assert on != normalize_semantic_analysis_config(analysis_config_from_run(BASE_RUN))


@pytest.mark.parametrize("run,match", [
    pytest.param(
        {key: value for key, value in v3_run().items() if key != "identical_fast_path"},
        "lacks typed analysis config", id="missing-flag",
    ),
    pytest.param(v3_run("yes"), "lacks typed analysis config", id="bad-value"),
    pytest.param(v3_run("true"), "lacks typed analysis config", id="word-value"),
    pytest.param(v3_run("2"), "lacks typed analysis config", id="out-of-range"),
    pytest.param(
        dict(BASE_RUN, analysis_config_schema="eqbench-analysis-config-v4",
             identical_fast_path="1"),
        "unknown analysis config schema", id="unknown-schema",
    ),
    pytest.param(
        dict(BASE_RUN, analysis_config_schema="eqbench-analysis-config-v2"),
        "unknown analysis config schema", id="older-schema-named",
    ),
])
def test_a_manifest_that_names_the_schema_must_carry_it(run, match):
    with pytest.raises(ValueError, match=match):
        analysis_config_from_run(run)


@pytest.mark.parametrize("mutate", [
    pytest.param(lambda c: {**c, "identical_fast_path": "1"}, id="string-flag"),
    pytest.param(lambda c: {**c, "identical_fast_path": 1}, id="int-flag"),
    pytest.param(lambda c: {k: v for k, v in c.items() if k != "identical_fast_path"},
                 id="dropped-flag"),
    pytest.param(lambda c: {**c, "extra": "x"}, id="extra-field"),
])
def test_a_v3_config_object_is_validated_field_by_field(mutate):
    config = dict(analysis_config_from_run(v3_run("1")))
    with pytest.raises(ValueError):
        validate_analysis_config(mutate(config))


SOURCE_DIGEST = "b" * 64


def write_run_manifest(path, run):
    """A prior run's manifest, sealed with the digest that run would have taken."""

    fields = dict(
        run,
        analysis_config_digest=authority_digest(analysis_config_from_run(run)),
        analysis_source_digest_start=SOURCE_DIGEST,
        analysis_source_digest_end=SOURCE_DIGEST,
    )
    path.write_text(
        "".join(f"{key}={value}\n" for key, value in fields.items()), encoding="utf-8",
    )
    return path


@pytest.mark.parametrize("previous,current,reusable", [
    pytest.param(v3_run("1"), v3_run("1"), True, id="on-resumes-on"),
    pytest.param(v3_run("0"), v3_run("0"), True, id="off-resumes-off"),
    pytest.param(v3_run("1"), v3_run("0"), False, id="off-never-resumes-on"),
    pytest.param(v3_run("0"), v3_run("1"), False, id="on-never-resumes-off"),
    pytest.param(BASE_RUN, v3_run("1"), False, id="v3-never-resumes-a-legacy-run"),
    pytest.param(v3_run("1"), BASE_RUN, False, id="legacy-never-resumes-v3"),
    pytest.param(BASE_RUN, BASE_RUN, True, id="legacy-resumes-legacy"),
])
def test_a_run_never_reuses_the_other_mode_s_pair_statuses(
    tmp_path, previous, current, reusable,
):
    """The resume check is where an ON pair status could land in an OFF run.

    That would destroy the oracle silently -- the OFF run would report results
    the fast path produced -- so the two modes must not be compatible here.
    """

    manifest = write_run_manifest(tmp_path / "run_manifest.txt", previous)
    identity = compatible_previous_run_manifest_analysis_identity(
        manifest, current_config=analysis_config_from_run(current),
    )
    assert (identity is not None) is reusable


# One real ``run_manifest.txt`` written before this change (the Issue #124-C
# subset run at ``d75c253``), inlined so the check does not depend on a
# git-ignored ``logs/`` tree.  Its sealed digest must stay reproducible.
HISTORICAL_RUN_MANIFEST = r"""
run_kind=eqbench_all_eq_matrix_current
run_scope=REPRESENTATIVE
build_policy=PREBUILT_ONLY
eqbench_root=/workspace/targets/EqBench/benchmarks
output_base_dir=/workspace/logs/EqBench/subset_issue124c_r6/eq
python_bin=python3
parallel_jobs=20
parallel_jobs_requested=20
resource_admission_enabled=0
resource_admission_jobs=28
cpu_tokens=28
pair_cpu_tokens=8
progress_interval_seconds=5
validation_summary_level=compact
pair_process_timeout=240s
pair_process_kill_after=30s
pair_stack_dump_lead=2s
pair_process_timeout_seconds=240
pair_process_kill_after_seconds=30
equiv_timeout=10
decompile_timeout=60
pairwise_timeout=5
pairwise_timeout_hard=30
expander_dedup_case_limit_requested=
expander_dedup_case_limit_effective=16
callee_unbound_reuse=1
callee_unbound_reuse_shadow=0
skip_completed_results=1
error_only_rerun=0
debug=0
eqbench_tmpdir=/workspace/tmp
authority_keyset_id=cda35b812d4ffe8f45047c6078071c49af57ac07337bb4e86821a5d251d35e42
compile_axes=arm64,mips64 x clang,gcc x O0,O1,O2,O3
prefilter_source_count=147
prefilter_source_census_digest=8968e85f2d9cd5b872b3dd0cdbe6978cb9434fab569f183fd89e5ec1c6510201
max_samples=0
target_sources=8
function_policy=all top-level source-defined functions except main
binary_policy=verified build receipt first; isolated fresh build fallback
sample_filter=/(CLEVER/LoopSub/Eq/new|REVE/loop2/Eq/newV|REVE/barthe2big/Eq/new|airy/Sign/Eq/newV|dart/test/Eq/newV|pow/test/Eq/newV|ran/ranzero/Eq/newV|statcalc/addValue/Eq/newV)\.c$
pair_filter=B1_B2,B5_B7,B9_B10,B13_B15,B1_B9,B6_B14,B3_B11,B4_B16
runner_script_sha256=f6efef5297156abeac218a5cc0fa506f65d6c3714e79f2bbcf85d4de56793259
start_time_utc=2026-09-14T23:19:18Z
hostname=8e221abc82fc
git_commit=d75c2533f547f35d116424cab2a353665dcd44eb
git_dirty=0
git_dirty_files_digest=b25729965b2e6177a75487fd3e3df7811986b07da66bb750ca34a6e7001092aa
analysis_source_digest_start=ce23ca6e8632d2e57161e3a2f0ddfc9d46d22b9a2c5754f40b66c9e9a77f6aa1
dry_run=0
analysis_config_digest=5e2c8c3f6a3e882154f711fa07d11b47a6e409850768e866e9585e3085b52130
completed_samples=8
skipped_samples=0
total_functions=8
total_pair_jobs=64
total_scheduled_pair_jobs=64
total_skipped_pair_jobs=0
expected_pairs_per_function=120
expected_binary_count=112
compiled_binary_count=112
compile_failure_count=0
missing_binary_count=0
function_census_failure_count=0
process_authority_cleanup_failure_count=0
run_pair_failures=0
benchmark_gate_status=PASS
benchmark_gate_failures=0
analysis_source_digest_end=ce23ca6e8632d2e57161e3a2f0ddfc9d46d22b9a2c5754f40b66c9e9a77f6aa1
end_time_utc=2026-09-14T23:23:22Z
""".lstrip("\n")


def test_a_run_recorded_before_this_change_still_reads_and_still_matches(tmp_path):
    path = tmp_path / "run_manifest.txt"
    path.write_text(HISTORICAL_RUN_MANIFEST, encoding="utf-8")

    run = _read_key_values(path)
    config = analysis_config_from_run(run)

    assert config["schema"] == "eqbench-analysis-config-v2"
    assert authority_digest(config) == run["analysis_config_digest"]

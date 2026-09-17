# -*- coding: utf-8 -*-
"""Did the CI subset run do what the workflow asked it to, for the scope it asked?

Issue #109 PR-109-C.  ``.github/workflows/eqbench-subset.yml`` runs the fixed
measurement subset (``eqbench_run_subset.sh``) against real binaries.  Deciding
whether that run succeeded is not "did the shell step exit 0": the runner
records its own exit status in ``subset_manifest.txt`` instead of propagating
every diagnostic failure, and the two gates a subset run produces mean
different things.  This module is the single place that decides, so the
workflow has one verdict step and the rules can be unit tested without a
runner.

``verify``
    Read a finished run tree and answer, per check, whether it matches what the
    workflow asked for.  Three things the workflow must not get wrong are
    encoded here rather than in YAML:

    *scope awareness* -- ``eq`` and ``neq`` are separate halves with separate
    result trees and **separate run-manifest keys** for the EqBench tree they
    walked (``eqbench_root`` versus ``neq_root``).  A ``scope=eq`` run has no
    ``neq`` half at all, so requiring the other half's directory, key, gate or
    artifact would fail a perfectly good run.  The other direction is
    fail-closed: a half the scope *does* ask for and that is missing is a
    failure, never a skipped check.

    *gate separation* -- the shared soundness gate (``soundness_gate.json``,
    schema ``soundness-gate-v2``, one verdict for the whole run) and the
    per-half benchmark validation gate (``benchmark_validation_gate.json`` plus
    ``benchmark_gate_status`` in the half's run manifest) are different
    contracts with different owners.  Each check names the file it read, and
    neither gate's verdict is ever read from the other's file.

    *env propagation* -- the values the workflow normalised once
    (``pair_process_timeout``, ``identical_fast_path``, the working root) are
    checked against what each half's run manifest says it actually ran with,
    which is the far end of ``workflow input -> shell env -> container env ->
    eqbench_run_subset.sh -> child runner``.

``collect``
    Copy the evidence of a run into an artifact directory, bounded: everything
    except the per-pair ``.log`` files, plus the logs of the pairs that are
    worth reading (gate violations and ``ERROR`` / ``TIMEOUT`` outcomes), up to
    a cap.  Nothing here judges a run; it only decides what gets kept.

Exit 0 when every check passed, 1 otherwise (or when an input is unreadable --
"I could not look" must not read as "it is fine").
"""

from __future__ import annotations

import argparse
import json
import shutil
import sys
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath
from typing import Dict, List, Mapping, Optional, Sequence, Tuple

VERIFICATION_SCHEMA = "eqbench-ci-subset-verification-v1"

#: Which result halves a scope asks for.  This is the only place the mapping
#: lives; both the runner and this verification read the same three words.
HALVES_BY_SCOPE: Mapping[str, Tuple[str, ...]] = {
    "eq": ("eq",),
    "neq": ("neq",),
    "all": ("eq", "neq"),
}
ALL_HALVES: Tuple[str, ...] = ("eq", "neq")

#: The run-manifest key naming the EqBench tree the half actually walked.  The
#: two runners use different names on purpose (``eqbench_run_all_32jobs.sh``
#: takes ``EQBENCH_ROOT``, ``neqbench_run_all_32jobs.sh`` takes ``NEQ_ROOT``),
#: so a half is verified through its own key and never through the other's.
ROOT_KEY_BY_HALF: Mapping[str, str] = {"eq": "eqbench_root", "neq": "neq_root"}

SUBSET_MANIFEST_FILE = "subset_manifest.txt"
RUN_MANIFEST_FILE = "run_manifest.txt"
SOUNDNESS_GATE_JSON = "soundness_gate.json"
SOUNDNESS_GATE_TEXT = "soundness_gate.txt"
SOUNDNESS_GATE_SCHEMA = "soundness-gate-v2"
BENCHMARK_GATE_JSON = "benchmark_validation_gate.json"
BENCHMARK_GATE_TEXT = "benchmark_validation_gate.txt"
BENCHMARK_GATE_PASS = "PASS"
BINARY_MANIFEST_HEADER = "# eqbench-binary-manifest-v1"
PAIR_STATUS_SUFFIX = ".pair-status.json"

DEFAULT_ANALYSIS_CONFIG_SCHEMA = "eqbench-analysis-config-v3"

#: ``subset_manifest.txt``'s ``pr`` field when ``SUBSET_PR`` was never set.
#: The CI workflow leaves it that way on purpose: that field says which pull
#: request a measurement belongs to, and a GitHub Actions run identifier is not
#: that.  The run id belongs in ``ci_metadata.json`` and in the artifact name,
#: so a run id turning up here is a provenance failure, not a nicety.
SUBSET_PR_UNSET = "none"

#: What each half writes in ``DRY_RUN=1`` mode: the list of sources it would
#: have run, with their absolute paths under the EqBench tree it walked.  That
#: makes it the one artifact that proves the working root reached the child
#: runner without anything being compiled or decompiled.
DRY_RUN_SOURCES_FILE = "dry_run_sources.txt"

#: In dry-run mode ``eqbench_run_all_32jobs.sh`` writes its run manifest before
#: stopping and ``neqbench_run_all_32jobs.sh`` does not -- it exits earlier than
#: its manifest block.  So a dry run cannot read back the Neq half's settings,
#: only the sources it selected.  This allows an ABSENT manifest for that half
#: and nothing else: a manifest that is there is always checked, so the day the
#: two runners are made symmetric this check tightens on its own rather than
#: leaving a stale allowance behind.
DRY_RUN_MANIFEST_OPTIONAL: Tuple[str, ...] = ("neq",)

#: Outcomes whose pair log is worth keeping even when no gate complained.
DIAGNOSTIC_OUTCOMES = ("ERROR", "TIMEOUT")

#: ``verify --profile propagation`` checks only that the settings reached the
#: child runners; it is used after a ``DRY_RUN=1`` pass, which writes the run
#: manifests but no pairs, no gates and no binaries.
PROFILE_FULL = "full"
PROFILE_PROPAGATION = "propagation"
PROFILES = (PROFILE_FULL, PROFILE_PROPAGATION)

#: The gate/contract each check belongs to.  Kept apart in the report so that
#: "the soundness gate passed" can never be read off a benchmark gate row.
GATE_SCOPE = "scope"
GATE_RUN_STATUS = "run_status"
GATE_ENV_PROPAGATION = "env_propagation"
GATE_SHARED_SOUNDNESS = "shared_soundness_gate"
GATE_BENCHMARK_VALIDATION = "benchmark_validation_gate"
GATE_ARTIFACTS = "artifacts"
GATE_ORDER = (
    GATE_SCOPE,
    GATE_RUN_STATUS,
    GATE_ENV_PROPAGATION,
    GATE_SHARED_SOUNDNESS,
    GATE_BENCHMARK_VALIDATION,
    GATE_ARTIFACTS,
)

EXIT_OK = 0
EXIT_FAIL = 1


class SubsetCiError(Exception):
    """An input this module was pointed at cannot be read as what it claims."""


@dataclass
class Check:
    """One yes/no question, and the file the answer was read from."""

    name: str
    gate: str
    passed: bool
    detail: str
    source: str = ""

    def as_dict(self) -> Dict[str, object]:
        return {
            "name": self.name,
            "gate": self.gate,
            "passed": self.passed,
            "detail": self.detail,
            "source": self.source,
        }


@dataclass
class Report:
    profile: str
    scope: str
    halves: Tuple[str, ...]
    expected: Dict[str, object]
    checks: List[Check] = field(default_factory=list)

    @property
    def passed(self) -> bool:
        return all(check.passed for check in self.checks)

    def add(
        self, name: str, gate: str, passed: bool, detail: str, source: str = "",
    ) -> None:
        self.checks.append(Check(name, gate, passed, detail, source))

    def by_gate(self) -> Dict[str, List[Check]]:
        grouped: Dict[str, List[Check]] = {}
        for check in self.checks:
            grouped.setdefault(check.gate, []).append(check)
        return grouped

    def as_dict(self) -> Dict[str, object]:
        grouped = self.by_gate()
        return {
            "schema": VERIFICATION_SCHEMA,
            "profile": self.profile,
            "scope": self.scope,
            "halves": list(self.halves),
            "root_key_by_half": {
                half: ROOT_KEY_BY_HALF[half] for half in self.halves
            },
            "expected": dict(self.expected),
            "passed": self.passed,
            "gates": {
                gate: {
                    "passed": all(check.passed for check in checks),
                    "checks": [check.as_dict() for check in checks],
                }
                for gate, checks in grouped.items()
            },
            "checks": [check.as_dict() for check in self.checks],
        }

    def as_text(self) -> str:
        lines = [
            f"CI subset verification ({self.profile} profile)",
            f"  scope:  {self.scope}",
            f"  halves: {', '.join(self.halves) or '(none)'}",
        ]
        for key, value in sorted(self.expected.items()):
            lines.append(f"  expected {key}: {value}")
        lines.append("")
        grouped = self.by_gate()
        for gate in GATE_ORDER:
            checks = grouped.get(gate)
            if not checks:
                continue
            verdict = "PASS" if all(check.passed for check in checks) else "FAIL"
            lines.append(f"[{gate}] {verdict}")
            for check in checks:
                mark = "ok  " if check.passed else "FAIL"
                source = f"  <- {check.source}" if check.source else ""
                lines.append(f"  {mark} {check.name}: {check.detail}{source}")
            lines.append("")
        lines.append("VERIFICATION: " + ("PASS" if self.passed else "FAIL"))
        return "\n".join(lines) + "\n"


def halves_for_scope(scope: str) -> Tuple[str, ...]:
    try:
        return HALVES_BY_SCOPE[scope]
    except KeyError:
        raise SubsetCiError(
            f"scope must be one of {', '.join(sorted(HALVES_BY_SCOPE))}: {scope!r}"
        )


def read_key_value_manifest(path: Path) -> Dict[str, str]:
    """A ``key=value`` manifest, keeping values that themselves contain ``=``.

    The shell side reads these with the same rule (a later line wins), so a
    manifest that repeats a key means here what it means there.
    """

    values: Dict[str, str] = {}
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise SubsetCiError(f"cannot read {path}: {exc}")
    for line in text.splitlines():
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, _, value = line.partition("=")
        values[key.strip()] = value
    return values


def read_json(path: Path) -> object:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise SubsetCiError(f"cannot read {path}: {exc}")
    except ValueError as exc:
        raise SubsetCiError(f"{path} is not JSON: {exc}")


def _relative(run_dir: Path, path: Path) -> str:
    try:
        return str(path.relative_to(run_dir))
    except ValueError:
        return str(path)


def _check_manifest_value(
    report: Report,
    run_dir: Path,
    name: str,
    gate: str,
    manifest_path: Path,
    manifest: Mapping[str, str],
    key: str,
    expected: str,
) -> None:
    actual = manifest.get(key)
    source = _relative(run_dir, manifest_path)
    if actual is None:
        report.add(name, gate, False, f"{key} is missing", source)
        return
    report.add(
        name,
        gate,
        actual == expected,
        f"{key}={actual!r} (expected {expected!r})",
        source,
    )


def _verify_scope(report: Report, run_dir: Path) -> None:
    """The halves the scope asks for are present; the others are not required.

    An out-of-scope half that exists anyway is a failure, not a bonus: the
    workflow runs into a fresh output directory, so a ``neq`` tree in a
    ``scope=eq`` run means the results are not the ones this run produced.
    """

    for half in report.halves:
        half_dir = run_dir / half
        report.add(
            f"scope.{half}.half_present",
            GATE_SCOPE,
            half_dir.is_dir(),
            f"{half} half directory {'exists' if half_dir.is_dir() else 'is missing'}",
            _relative(run_dir, half_dir),
        )
    for half in ALL_HALVES:
        if half in report.halves:
            continue
        half_dir = run_dir / half
        report.add(
            f"scope.{half}.half_absent",
            GATE_SCOPE,
            not half_dir.exists(),
            (
                f"{half} is outside scope {report.scope!r} and "
                + ("is absent" if not half_dir.exists() else "unexpectedly exists")
            ),
            _relative(run_dir, half_dir),
        )


def _verify_run_status(
    report: Report,
    run_dir: Path,
    runner_exit_status: Optional[int],
    full: bool,
) -> None:
    manifest_path = run_dir / SUBSET_MANIFEST_FILE
    if not manifest_path.is_file():
        report.add(
            "run.subset_manifest",
            GATE_RUN_STATUS,
            False,
            "subset manifest is missing",
            _relative(run_dir, manifest_path),
        )
        return
    manifest = read_key_value_manifest(manifest_path)
    report.add(
        "run.subset_manifest",
        GATE_RUN_STATUS,
        True,
        f"{len(manifest)} recorded settings",
        _relative(run_dir, manifest_path),
    )
    _check_manifest_value(
        report, run_dir, "run.scope", GATE_RUN_STATUS, manifest_path, manifest,
        "scope", report.scope,
    )
    _check_manifest_value(
        report, run_dir, "run.exit_status", GATE_RUN_STATUS, manifest_path, manifest,
        "exit_status", "0",
    )
    if not full:
        return
    if runner_exit_status is not None:
        report.add(
            "run.runner_exit_status",
            GATE_RUN_STATUS,
            runner_exit_status == 0,
            f"the subset runner step exited {runner_exit_status} (expected 0)",
            "workflow step",
        )
    # The dataset provenance field must not have been used to carry a CI
    # identifier.  Only a real run writes this; a dry run has no pairs and no
    # measurement to attribute.
    _check_manifest_value(
        report, run_dir, "run.subset_pr", GATE_RUN_STATUS, manifest_path,
        manifest, "pr", SUBSET_PR_UNSET,
    )


def _verify_dry_run_sources(
    report: Report, run_dir: Path, half: str, working_root: str,
) -> None:
    """The sources this half selected, and the tree it read them from."""

    path = run_dir / half / DRY_RUN_SOURCES_FILE
    source = _relative(run_dir, path)
    if not path.is_file():
        report.add(
            f"env.{half}.dry_run_sources", GATE_ENV_PROPAGATION, False,
            "the half selected no sources (it wrote no dry-run census)", source,
        )
        return
    lines = [line for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
    paths = [
        field for line in lines for field in line.split("\t") if field.startswith("/")
    ]
    prefix = working_root.rstrip("/") + "/"
    outside = sorted({field for field in paths if not field.startswith(prefix)})
    passed = bool(lines) and bool(paths) and not outside
    if passed:
        detail = (
            f"{len(lines)} sources, {len(paths)} paths, all under {working_root}"
        )
    elif outside:
        detail = f"{len(outside)} path(s) outside {working_root}, e.g. {outside[0]}"
    else:
        detail = f"{len(lines)} lines with no absolute source path"
    report.add(f"env.{half}.dry_run_sources", GATE_ENV_PROPAGATION, passed, detail, source)


def _verify_env_propagation(
    report: Report, run_dir: Path, expected: Mapping[str, str], dry_run: bool,
) -> None:
    """What each half recorded it ran with, against what the workflow asked."""

    for half in report.halves:
        if dry_run:
            _verify_dry_run_sources(
                report, run_dir, half, str(expected["working_root"]),
            )
        manifest_path = run_dir / half / RUN_MANIFEST_FILE
        source = _relative(run_dir, manifest_path)
        if not manifest_path.is_file():
            allowed = dry_run and half in DRY_RUN_MANIFEST_OPTIONAL
            report.add(
                f"env.{half}.run_manifest",
                GATE_ENV_PROPAGATION,
                allowed,
                (
                    "this runner writes no run manifest in dry-run mode; the "
                    "half's settings are verified by the full profile, and the "
                    "root it walked by the dry-run census above"
                    if allowed else "run manifest is missing"
                ),
                source,
            )
            continue
        manifest = read_key_value_manifest(manifest_path)
        report.add(
            f"env.{half}.run_manifest",
            GATE_ENV_PROPAGATION,
            True,
            f"{len(manifest)} recorded settings",
            source,
        )
        # The half's own root key -- never the other half's.
        _check_manifest_value(
            report, run_dir, f"env.{half}.working_root", GATE_ENV_PROPAGATION,
            manifest_path, manifest, ROOT_KEY_BY_HALF[half],
            str(expected["working_root"]),
        )
        _check_manifest_value(
            report, run_dir, f"env.{half}.pair_process_timeout",
            GATE_ENV_PROPAGATION, manifest_path, manifest,
            "pair_process_timeout", str(expected["pair_process_timeout"]),
        )
        _check_manifest_value(
            report, run_dir, f"env.{half}.identical_fast_path",
            GATE_ENV_PROPAGATION, manifest_path, manifest,
            "identical_fast_path", str(expected["identical_fast_path"]),
        )
        _check_manifest_value(
            report, run_dir, f"env.{half}.analysis_config_schema",
            GATE_ENV_PROPAGATION, manifest_path, manifest,
            "analysis_config_schema", str(expected["analysis_config_schema"]),
        )


def _verify_shared_soundness_gate(report: Report, run_dir: Path) -> None:
    """The one gate covering the whole run.  Read only from its own file."""

    gate_path = run_dir / SOUNDNESS_GATE_JSON
    source = _relative(run_dir, gate_path)
    if not gate_path.is_file():
        report.add(
            "soundness.report", GATE_SHARED_SOUNDNESS, False,
            "soundness gate report is missing", source,
        )
        return
    try:
        payload = read_json(gate_path)
    except SubsetCiError as exc:
        report.add("soundness.report", GATE_SHARED_SOUNDNESS, False, str(exc), source)
        return
    if not isinstance(payload, dict):
        report.add(
            "soundness.report", GATE_SHARED_SOUNDNESS, False,
            "soundness gate report is not a JSON object", source,
        )
        return
    report.add(
        "soundness.report", GATE_SHARED_SOUNDNESS, True,
        f"{payload.get('pairs')} pairs checked", source,
    )
    schema = payload.get("schema")
    report.add(
        "soundness.schema", GATE_SHARED_SOUNDNESS,
        schema == SOUNDNESS_GATE_SCHEMA,
        f"schema={schema!r} (expected {SOUNDNESS_GATE_SCHEMA!r})", source,
    )
    passed = payload.get("passed")
    # ``is True`` on purpose: a truthy string or a 1 is not this gate saying
    # it passed, it is a report this verification cannot read.
    report.add(
        "soundness.passed", GATE_SHARED_SOUNDNESS, passed is True,
        f"passed={passed!r} (expected True)", source,
    )


def _verify_benchmark_validation_gates(report: Report, run_dir: Path) -> None:
    """The per-half gate.  A different contract from the soundness gate above.

    Both of its sources are checked: the half's run manifest (what the runner
    recorded when the gate ran) and the gate's own report.
    """

    for half in report.halves:
        manifest_path = run_dir / half / RUN_MANIFEST_FILE
        if manifest_path.is_file():
            manifest = read_key_value_manifest(manifest_path)
            _check_manifest_value(
                report, run_dir, f"benchmark.{half}.recorded_status",
                GATE_BENCHMARK_VALIDATION, manifest_path, manifest,
                "benchmark_gate_status", BENCHMARK_GATE_PASS,
            )
        else:
            report.add(
                f"benchmark.{half}.recorded_status", GATE_BENCHMARK_VALIDATION,
                False, "run manifest is missing",
                _relative(run_dir, manifest_path),
            )
        gate_path = run_dir / half / BENCHMARK_GATE_JSON
        source = _relative(run_dir, gate_path)
        if not gate_path.is_file():
            report.add(
                f"benchmark.{half}.report", GATE_BENCHMARK_VALIDATION, False,
                "benchmark validation gate report is missing", source,
            )
            continue
        try:
            payload = read_json(gate_path)
        except SubsetCiError as exc:
            report.add(
                f"benchmark.{half}.report", GATE_BENCHMARK_VALIDATION, False,
                str(exc), source,
            )
            continue
        gate = payload.get("gate") if isinstance(payload, dict) else None
        report.add(
            f"benchmark.{half}.report", GATE_BENCHMARK_VALIDATION,
            gate == BENCHMARK_GATE_PASS,
            f"gate={gate!r} (expected {BENCHMARK_GATE_PASS!r})", source,
        )


def required_artifacts(halves: Sequence[str]) -> List[str]:
    """Run-dir relative files the scope's own evidence cannot do without."""

    names = [SUBSET_MANIFEST_FILE, SOUNDNESS_GATE_JSON, SOUNDNESS_GATE_TEXT]
    for half in halves:
        names.extend(
            [
                f"{half}/{RUN_MANIFEST_FILE}",
                f"{half}/{BENCHMARK_GATE_JSON}",
                f"{half}/{BENCHMARK_GATE_TEXT}",
                f"{half}/function_diff_manifest.json",
                f"{half}/overall_summary.txt",
                f"{half}/run_health_summary.json",
                f"{half}/run_health_summary.txt",
                f"{half}.log",
                f"binary_manifest_{half}.txt",
            ]
        )
    return names


def _verify_artifacts(report: Report, run_dir: Path) -> None:
    for name in required_artifacts(report.halves):
        path = run_dir / name
        present = path.is_file() and path.stat().st_size > 0
        report.add(
            f"artifact.{name}", GATE_ARTIFACTS, present,
            "present and non-empty" if present else "missing or empty", name,
        )
    for half in report.halves:
        path = run_dir / f"binary_manifest_{half}.txt"
        source = f"binary_manifest_{half}.txt"
        if not path.is_file():
            report.add(
                f"binary_manifest.{half}", GATE_ARTIFACTS, False,
                "binary manifest is missing", source,
            )
            continue
        lines = [
            line for line in path.read_text(encoding="utf-8").splitlines() if line
        ]
        header_ok = bool(lines) and lines[0] == BINARY_MANIFEST_HEADER
        # header + column row + at least one binary: a manifest built before the
        # run (or from an empty tree) would stop at the column row, and that is
        # exactly the thing this check exists to catch.
        rows = max(len(lines) - 2, 0)
        report.add(
            f"binary_manifest.{half}", GATE_ARTIFACTS, header_ok and rows > 0,
            (
                f"{rows} binaries, header "
                + ("ok" if header_ok else f"is {lines[0]!r}" if lines else "missing")
            ),
            source,
        )


def verify(
    run_dir: Path,
    scope: str,
    working_root: str,
    pair_process_timeout: str,
    identical_fast_path: str,
    analysis_config_schema: str = DEFAULT_ANALYSIS_CONFIG_SCHEMA,
    profile: str = PROFILE_FULL,
    runner_exit_status: Optional[int] = None,
) -> Report:
    if profile not in PROFILES:
        raise SubsetCiError(f"profile must be one of {', '.join(PROFILES)}: {profile!r}")
    halves = halves_for_scope(scope)
    expected: Dict[str, object] = {
        "working_root": working_root,
        "pair_process_timeout": pair_process_timeout,
        "identical_fast_path": identical_fast_path,
        "analysis_config_schema": analysis_config_schema,
    }
    report = Report(profile=profile, scope=scope, halves=halves, expected=expected)
    if not run_dir.is_dir():
        report.add(
            "run.directory", GATE_RUN_STATUS, False,
            f"run directory is missing: {run_dir}",
        )
        return report
    _verify_scope(report, run_dir)
    _verify_run_status(
        report, run_dir, runner_exit_status, full=profile == PROFILE_FULL,
    )
    _verify_env_propagation(
        report, run_dir, {str(k): str(v) for k, v in expected.items()},
        dry_run=profile == PROFILE_PROPAGATION,
    )
    if profile == PROFILE_FULL:
        _verify_shared_soundness_gate(report, run_dir)
        _verify_benchmark_validation_gates(report, run_dir)
        _verify_artifacts(report, run_dir)
    return report


# --------------------------------------------------------------------------
# collect
# --------------------------------------------------------------------------


def _gate_violation_status_paths(run_dir: Path, halves: Sequence[str]) -> List[str]:
    """Pair-status paths named by the soundness gate's violation rows.

    The gate records absolute paths from inside the container, so the rows are
    resolved back to this tree from the fields that identify the pair rather
    than from the recorded path.
    """

    gate_path = run_dir / SOUNDNESS_GATE_JSON
    if not gate_path.is_file():
        return []
    try:
        payload = read_json(gate_path)
    except SubsetCiError:
        return []
    if not isinstance(payload, dict):
        return []
    rows: List[Mapping[str, object]] = []
    verified = payload.get("verified_ground_truth")
    if isinstance(verified, dict):
        for key in ("unconditional_violations", "conditional_violations"):
            value = verified.get(key)
            if isinstance(value, list):
                rows.extend(row for row in value if isinstance(row, dict))
    identical = payload.get("identical_input")
    if isinstance(identical, dict):
        for key in ("soundness_violations", "fast_path_violations"):
            value = identical.get(key)
            if isinstance(value, list):
                rows.extend(row for row in value if isinstance(row, dict))
    integrity = payload.get("config_integrity")
    if isinstance(integrity, dict):
        value = integrity.get("violations")
        if isinstance(value, list):
            rows.extend(row for row in value if isinstance(row, dict))

    resolved: List[str] = []
    for row in rows:
        scope_path = row.get("scope")
        half = PurePosixPath(str(scope_path)).name if scope_path else ""
        sample = row.get("sample_identity")
        function = row.get("function_name")
        pair_id = row.get("pair_id")
        if half not in halves or not all(
            isinstance(value, str) and value for value in (sample, function, pair_id)
        ):
            continue
        resolved.append(
            f"{half}/{sample}/{function}/{function}_{pair_id}{PAIR_STATUS_SUFFIX}"
        )
    return resolved


def _diagnostic_status_paths(run_dir: Path, halves: Sequence[str]) -> List[str]:
    """Pairs whose own status says the run could not judge them normally."""

    found: List[str] = []
    for half in halves:
        half_dir = run_dir / half
        if not half_dir.is_dir():
            continue
        for path in sorted(half_dir.rglob("*" + PAIR_STATUS_SUFFIX)):
            try:
                payload = read_json(path)
            except SubsetCiError:
                continue
            if not isinstance(payload, dict):
                continue
            if payload.get("canonical_outcome") in DIAGNOSTIC_OUTCOMES:
                found.append(_relative(run_dir, path))
    return found


def select_pair_logs(
    run_dir: Path, halves: Sequence[str], limit: int,
) -> List[str]:
    """Run-dir relative ``.log`` paths worth keeping, gate rows first."""

    ordered: List[str] = []
    seen = set()
    for relative in _gate_violation_status_paths(run_dir, halves) + _diagnostic_status_paths(
        run_dir, halves
    ):
        log_relative = relative[: -len(PAIR_STATUS_SUFFIX)] + ".log"
        if log_relative in seen:
            continue
        seen.add(log_relative)
        if (run_dir / log_relative).is_file():
            ordered.append(log_relative)
        if len(ordered) >= limit:
            break
    return ordered


def collect(
    run_dir: Path, dest: Path, scope: str, max_pair_logs: int = 100,
) -> Dict[str, object]:
    """Copy a run's evidence into ``dest``, without the bulk of the pair logs."""

    halves = halves_for_scope(scope)
    if not run_dir.is_dir():
        raise SubsetCiError(f"run directory is missing: {run_dir}")
    dest.mkdir(parents=True, exist_ok=True)

    copied = 0
    skipped_logs = 0
    for path in sorted(run_dir.rglob("*")):
        if not path.is_file():
            continue
        relative = path.relative_to(run_dir)
        # Top-level <half>.log is the half's console output and is small; the
        # per-pair logs inside a half tree are the 50 MB.
        if path.suffix == ".log" and len(relative.parts) > 1:
            skipped_logs += 1
            continue
        target = dest / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, target)
        copied += 1

    selected = select_pair_logs(run_dir, halves, max_pair_logs)
    for relative in selected:
        target = dest / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(run_dir / relative, target)
    return {
        "run_dir": str(run_dir),
        "dest": str(dest),
        "scope": scope,
        "halves": list(halves),
        "files_copied": copied,
        "pair_logs_skipped": skipped_logs,
        "pair_logs_kept": selected,
        "max_pair_logs": max_pair_logs,
    }


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    commands = parser.add_subparsers(dest="command", required=True)

    verify_command = commands.add_parser(
        "verify", help="decide whether a CI subset run met the workflow's contract",
    )
    verify_command.add_argument("--run-dir", type=Path, required=True)
    verify_command.add_argument("--scope", required=True, choices=sorted(HALVES_BY_SCOPE))
    verify_command.add_argument(
        "--working-root", required=True,
        help="the EqBench working root the halves must have walked, as the run "
             "manifests record it (a container path)",
    )
    verify_command.add_argument("--pair-process-timeout", required=True)
    verify_command.add_argument("--identical-fast-path", required=True)
    verify_command.add_argument(
        "--analysis-config-schema", default=DEFAULT_ANALYSIS_CONFIG_SCHEMA,
    )
    verify_command.add_argument("--profile", default=PROFILE_FULL, choices=PROFILES)
    verify_command.add_argument(
        "--runner-exit-status", type=int, default=None,
        help="exit status observed for the subset runner step (full profile)",
    )
    verify_command.add_argument("--json", type=Path, default=None)
    verify_command.add_argument("--text", type=Path, default=None)

    collect_command = commands.add_parser(
        "collect", help="copy a run's evidence into an artifact directory",
    )
    collect_command.add_argument("--run-dir", type=Path, required=True)
    collect_command.add_argument("--dest", type=Path, required=True)
    collect_command.add_argument("--scope", required=True, choices=sorted(HALVES_BY_SCOPE))
    collect_command.add_argument("--max-pair-logs", type=int, default=100)
    collect_command.add_argument("--json", type=Path, default=None)
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        if args.command == "verify":
            report = verify(
                run_dir=args.run_dir,
                scope=args.scope,
                working_root=args.working_root,
                pair_process_timeout=args.pair_process_timeout,
                identical_fast_path=args.identical_fast_path,
                analysis_config_schema=args.analysis_config_schema,
                profile=args.profile,
                runner_exit_status=args.runner_exit_status,
            )
            text = report.as_text()
            sys.stdout.write(text)
            if args.text is not None:
                args.text.parent.mkdir(parents=True, exist_ok=True)
                args.text.write_text(text, encoding="utf-8")
            if args.json is not None:
                args.json.parent.mkdir(parents=True, exist_ok=True)
                args.json.write_text(
                    json.dumps(report.as_dict(), indent=1, sort_keys=True) + "\n",
                    encoding="utf-8",
                )
            return EXIT_OK if report.passed else EXIT_FAIL
        summary = collect(
            run_dir=args.run_dir,
            dest=args.dest,
            scope=args.scope,
            max_pair_logs=args.max_pair_logs,
        )
        print(
            "collected {files_copied} files into {dest} "
            "({pair_logs_skipped} pair logs skipped, {kept} kept)".format(
                kept=len(summary["pair_logs_kept"]), **summary
            )
        )
        if args.json is not None:
            args.json.parent.mkdir(parents=True, exist_ok=True)
            args.json.write_text(
                json.dumps(summary, indent=1, sort_keys=True) + "\n", encoding="utf-8",
            )
        return EXIT_OK
    except SubsetCiError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return EXIT_FAIL


if __name__ == "__main__":
    sys.exit(main())

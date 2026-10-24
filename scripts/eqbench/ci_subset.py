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
    (``pair_process_timeout``, ``identical_fast_path``, the effective analysis
    deadline and its margin, the working root) are
    checked against what each half's run manifest says it actually ran with,
    which is the far end of ``workflow input -> shell env -> container env ->
    eqbench_run_subset.sh -> child runner``.

    *workload completeness* -- the gates above are about the pairs that were
    judged, so on their own they are happy with a run that judged nothing: a
    subset run whose every pair was killed at its deadline passes the soundness
    gate and both benchmark gates with ``exit_status=0``, because a ``TIMEOUT``
    violates nothing.  So the scope's pairs are also required to be *there and
    attempted*: the expected set comes from the fixed subset definition and the
    run's own publication manifest rather than from a count written here, every
    expected pair status must exist and be readable, none may have been reused
    from an earlier run, and each half must carry at least one outcome the
    analysis actually produced.  A run with some ``TIMEOUT`` pairs is normal
    and passes; a run with nothing but ``TIMEOUT`` / ``ERROR`` does not.

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

DEFAULT_ANALYSIS_CONFIG_SCHEMA = "eqbench-analysis-config-v5"

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
#: leaving a stale allowance behind.  The asymmetry itself is Issue #174.
DRY_RUN_MANIFEST_OPTIONAL: Tuple[str, ...] = ("neq",)

#: Outcomes whose pair log is worth keeping even when no gate complained.
DIAGNOSTIC_OUTCOMES = ("ERROR", "TIMEOUT")

#: The run's own account of the pairs it meant to produce (Issue #104 / #123).
PUBLICATION_MANIFEST_FILE = "matrix-publication-manifest.json"
PUBLICATION_MANIFEST_SCHEMA = "eqbench-matrix-publication-manifest-v4"
#: v3 is what the runners published before the execution chain (eval plan v2
#: PR-B); both carry the same expected-pair census this module reads.
PUBLICATION_MANIFEST_SCHEMAS = (
    "eqbench-matrix-publication-manifest-v3", PUBLICATION_MANIFEST_SCHEMA,
)

#: The fixed subset's definition -- the source of truth for which samples and
#: pair ids the subset is, so the expected pair set is never a number written
#: into this module.
SUBSET_DEFINITION_FILE = (
    Path(__file__).resolve().parents[1]
    / "function_tracer_pcode" / "reporting" / "eqbench_subset.json"
)
SUBSET_DEFINITION_SCHEMA = "eqbench-measurement-subset-v1"

#: Which canonical outcomes mean "the analysis produced a judgement about this
#: pair".  Not a list invented here: the authority layer already says what each
#: outcome means for resuming a batch, and the two outcomes it calls a deadline
#: backlog and an infrastructure failure are exactly the two that say nothing
#: about the pair.  Imported lazily so that a caller who only wants ``collect``
#: does not pay for it.
def semantic_outcomes() -> frozenset:
    """Outcomes that are a result, as the authority layer classifies them."""

    from scripts.function_tracer_pcode.authority.contracts import (
        BATCH_RESUME_DISPOSITION_BY_OUTCOME,
    )

    not_a_result = {"RESUMABLE_DEADLINE_BACKLOG", "FAILED_INFRASTRUCTURE"}
    return frozenset(
        outcome.value
        for outcome, disposition in BATCH_RESUME_DISPOSITION_BY_OUTCOME.items()
        if disposition not in not_a_result
    )

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
GATE_WORKLOAD = "workload"
GATE_SHARED_SOUNDNESS = "shared_soundness_gate"
GATE_BENCHMARK_VALIDATION = "benchmark_validation_gate"
GATE_ARTIFACTS = "artifacts"
GATE_ORDER = (
    GATE_SCOPE,
    GATE_RUN_STATUS,
    GATE_ENV_PROPAGATION,
    GATE_WORKLOAD,
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
    # Not supplied is not "fine": in the full profile this is one of the
    # success conditions, so a caller that omits it gets a failure rather than
    # a check that quietly does not happen.
    report.add(
        "run.runner_exit_status",
        GATE_RUN_STATUS,
        runner_exit_status == 0,
        (
            f"the subset runner step exited {runner_exit_status} (expected 0)"
            if runner_exit_status is not None
            else "no runner exit status was supplied (--runner-exit-status)"
        ),
        "workflow step",
    )
    # The dataset provenance field must not have been used to carry a CI
    # identifier.  Only a real run writes this; a dry run has no pairs and no
    # measurement to attribute.
    _check_manifest_value(
        report, run_dir, "run.subset_pr", GATE_RUN_STATUS, manifest_path,
        manifest, "pr", SUBSET_PR_UNSET,
    )
    # ... and the run does say what it was made for.  Which issue is the
    # workflow's business, so this asks only that the attribution exists: a run
    # recorded as belonging to nothing cannot be found again from the ledger.
    issue = manifest.get("issue")
    report.add(
        "run.subset_issue", GATE_RUN_STATUS,
        bool(issue) and issue != SUBSET_PR_UNSET,
        f"issue={issue!r} (must name what the run was made for)",
        _relative(run_dir, manifest_path),
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
        # Issue #106 PR-106-B: the effective deadline and margin each half
        # recorded, against the values the workflow resolved once with the
        # runners' own rule (`runner_timeout_policy resolve`).
        for key in ("analysis_timeout", "analysis_timeout_margin"):
            _check_manifest_value(
                report, run_dir, f"env.{half}.{key}", GATE_ENV_PROPAGATION,
                manifest_path, manifest, key, str(expected[key]),
            )
        _check_manifest_value(
            report, run_dir, f"env.{half}.analysis_config_schema",
            GATE_ENV_PROPAGATION, manifest_path, manifest,
            "analysis_config_schema", str(expected["analysis_config_schema"]),
        )


def pair_identity_from_status_path(relative_path: str) -> Optional[Tuple[str, str]]:
    """``(sample identity, pair id)`` out of a ``<sample>/<fn>/<fn>_<pair>`` path.

    The runners lay a pair status out that way and the publication manifest
    lists exactly those paths, so this is a read of their layout rather than a
    guess.  ``None`` means "not a pair status path", which the callers treat as
    a manifest they cannot check -- never as one that agrees.
    """

    path = PurePosixPath(relative_path)
    name = path.name
    if not name.endswith(PAIR_STATUS_SUFFIX):
        return None
    parts = path.parts
    if len(parts) < 3:
        return None
    function = parts[-2]
    sample = "/".join(parts[:-2])
    stem = name[: -len(PAIR_STATUS_SUFFIX)]
    prefix = function + "_"
    if not sample or not function or not stem.startswith(prefix):
        return None
    pair_id = stem[len(prefix):]
    return (sample, pair_id) if pair_id else None


def subset_definition_pairs(
    half: str, definition_path: Path,
) -> Tuple[frozenset, int, int]:
    """The ``(sample, pair id)`` set the fixed subset *is*, for one half.

    Read from ``eqbench_subset.json``, which is the subset's definition -- so
    "did this run cover the subset?" is answered against the thing that defines
    the subset, not against a number kept in this file.
    """

    payload = read_json(definition_path)
    if not isinstance(payload, dict):
        raise SubsetCiError(f"{definition_path} is not a JSON object")
    schema = payload.get("schema")
    if schema != SUBSET_DEFINITION_SCHEMA:
        raise SubsetCiError(
            f"{definition_path} has schema {schema!r}, expected "
            f"{SUBSET_DEFINITION_SCHEMA!r}"
        )
    section = payload.get(half)
    if not isinstance(section, dict):
        raise SubsetCiError(f"{definition_path} has no {half!r} section")
    sources = section.get("sources")
    pair_ids = section.get("pair_ids")
    for name, value in (("sources", sources), ("pair_ids", pair_ids)):
        if not isinstance(value, list) or not value or not all(
            isinstance(item, str) and item for item in value
        ):
            raise SubsetCiError(
                f"{definition_path}: {half}.{name} is not a non-empty list of strings"
            )
    return (
        frozenset((source, pair_id) for source in sources for pair_id in pair_ids),
        len(sources),
        len(pair_ids),
    )


def binary_manifest_samples(path: Path) -> frozenset:
    """The ``sample_identity`` column of a binary manifest, as a set.

    The format is ``scripts/eqbench/binary_manifest.py``'s: a header line, a
    column row, then tab-separated rows.  A file that is not one raises rather
    than returning an empty set, because "no samples" and "I could not read
    the samples" must not look the same.
    """

    try:
        lines = [line for line in path.read_text(encoding="utf-8").splitlines() if line]
    except OSError as exc:
        raise SubsetCiError(f"cannot read {path.name}: {exc}")
    if not lines or lines[0] != BINARY_MANIFEST_HEADER:
        raise SubsetCiError(
            f"{path.name} does not start with {BINARY_MANIFEST_HEADER!r}"
        )
    samples = set()
    for line in lines[2:]:
        fields = line.split("\t")
        if len(fields) < 4 or not fields[0]:
            raise SubsetCiError(f"{path.name} has a row with no sample identity")
        samples.add(fields[0])
    if not samples:
        raise SubsetCiError(f"{path.name} names no binaries")
    return frozenset(samples)


def _publication_manifest(run_dir: Path, half: str) -> Mapping[str, object]:
    payload = read_json(run_dir / half / PUBLICATION_MANIFEST_FILE)
    if not isinstance(payload, dict):
        raise SubsetCiError(
            f"{half}/{PUBLICATION_MANIFEST_FILE} is not a JSON object"
        )
    schema = payload.get("schema")
    if schema not in PUBLICATION_MANIFEST_SCHEMAS:
        raise SubsetCiError(
            f"{half}/{PUBLICATION_MANIFEST_FILE} has schema {schema!r}, expected one of "
            f"{PUBLICATION_MANIFEST_SCHEMAS!r}"
        )
    paths = payload.get("expected_pair_status_paths")
    if not isinstance(paths, list) or not paths or not all(
        isinstance(item, str) and item for item in paths
    ):
        raise SubsetCiError(
            f"{half}/{PUBLICATION_MANIFEST_FILE} lists no expected pair statuses"
        )
    # Every comparison below is between SETS, and turning a list into a set
    # loses a repeated entry silently: a manifest listing 64 paths of which two
    # are the same would then agree with a run of 63 pairs.  So the list is
    # checked for repeats first, while it is still a list.
    repeated = sorted(
        {path for path in paths if paths.count(path) > 1}
    )
    if repeated:
        raise SubsetCiError(
            f"{half}/{PUBLICATION_MANIFEST_FILE} lists {len(paths)} expected pair "
            f"statuses but only {len(set(paths))} distinct ones: "
            f"{len(repeated)} path(s) repeat, e.g. {repeated[0]}"
        )
    return payload


def _verify_workload(
    report: Report, run_dir: Path, definition_path: Path,
) -> None:
    """The scope's pairs were there, were run, and produced something.

    Everything here is about whether the run happened, not about whether any
    judgement was right -- that is the two gates' business.  It exists because
    a run that judged nothing at all satisfies both of them.
    """

    for half in report.halves:
        manifest_source = f"{half}/{PUBLICATION_MANIFEST_FILE}"
        try:
            manifest = _publication_manifest(run_dir, half)
        except SubsetCiError as exc:
            # Without the manifest there is no expectation to check the half
            # against, so the rest of its workload checks would be guesses.
            # The verdict is already FAIL, and the run tree is collected whole,
            # so the outcome counts stay recoverable from the artifact.
            report.add(
                f"workload.{half}.publication_manifest", GATE_WORKLOAD, False,
                str(exc), manifest_source,
            )
            continue
        expected_paths = [str(item) for item in manifest["expected_pair_status_paths"]]
        dry_run = manifest.get("dry_run")
        report.add(
            f"workload.{half}.publication_manifest", GATE_WORKLOAD,
            dry_run in (0, False),
            (
                f"{len(expected_paths)} expected pair statuses, dry_run={dry_run!r}"
                if dry_run in (0, False)
                else f"the run recorded dry_run={dry_run!r}; it executed no pairs"
            ),
            manifest_source,
        )

        # (a) does the run's own expectation cover the subset it claims to be?
        try:
            definition, source_count, pair_count = subset_definition_pairs(
                half, definition_path,
            )
        except SubsetCiError as exc:
            report.add(
                f"workload.{half}.subset_coverage", GATE_WORKLOAD, False,
                f"the subset definition is unusable: {exc}", str(definition_path),
            )
            definition = None
        if definition is not None:
            identities = {pair_identity_from_status_path(path) for path in expected_paths}
            unreadable = sum(1 for item in identities if item is None)
            covered = frozenset(item for item in identities if item is not None)
            missing = sorted(definition - covered)
            extra = sorted(covered - definition)
            passed = not unreadable and not missing and not extra
            if passed:
                detail = (
                    f"{len(covered)} (sample, pair) identities = the definition's "
                    f"{source_count} sources x {pair_count} pair ids"
                )
            else:
                detail = (
                    f"{len(missing)} definition pair(s) not expected "
                    f"(e.g. {missing[0] if missing else '-'}), "
                    f"{len(extra)} unexpected (e.g. {extra[0] if extra else '-'}), "
                    f"{unreadable} path(s) not readable as a pair status"
                )
            report.add(
                f"workload.{half}.subset_coverage", GATE_WORKLOAD, passed, detail,
                manifest_source,
            )

        # (b) is every expected pair status actually on disk, and nothing else?
        half_dir = run_dir / half
        on_disk = {
            str(path.relative_to(half_dir)).replace("\\", "/")
            for path in half_dir.rglob("*" + PAIR_STATUS_SUFFIX)
        } if half_dir.is_dir() else set()
        expected_set = set(expected_paths)
        absent = sorted(expected_set - on_disk)
        unexpected = sorted(on_disk - expected_set)
        report.add(
            f"workload.{half}.pair_statuses", GATE_WORKLOAD,
            not absent and not unexpected,
            (
                f"{len(on_disk)} pair statuses, all expected"
                if not absent and not unexpected
                else f"{len(absent)} missing (e.g. {absent[0] if absent else '-'}), "
                     f"{len(unexpected)} unexpected "
                     f"(e.g. {unexpected[0] if unexpected else '-'})"
            ),
            f"{half}/",
        )

        # (c) a CI run executes its pairs; it does not inherit them.  The
        #     runners reuse a completed pair status when one is already there
        #     (SKIP_COMPLETED_RESULTS), and a reused pair is not evidence that
        #     this run can still produce it.
        reused = manifest.get("verified_skipped_pair_status_paths")
        skipped_jobs = manifest.get("total_skipped_pair_jobs")
        reused_count = len(reused) if isinstance(reused, list) else None
        report.add(
            f"workload.{half}.executed_not_reused", GATE_WORKLOAD,
            reused_count == 0 and skipped_jobs == 0,
            f"reused pair statuses={reused_count!r}, skipped pair jobs={skipped_jobs!r} "
            "(both must be 0)",
            manifest_source,
        )
        failures = manifest.get("run_pair_failures")
        report.add(
            f"workload.{half}.run_pair_failures", GATE_WORKLOAD, failures == 0,
            f"run_pair_failures={failures!r} (expected 0)", manifest_source,
        )

        # (d) non-vacuity: at least one pair the analysis actually decided.
        #     Read through the same reader the soundness gate and the transition
        #     report use, so an unreadable status is INVALID here too rather
        #     than silently absent from the counts.
        try:
            from scripts.function_tracer_pcode.reporting.pair_outcomes import (
                OUTCOME_INVALID, OUTCOME_MISSING, iter_pair_outcomes,
            )
            counts: Dict[str, int] = {}
            for row in iter_pair_outcomes(half_dir):
                counts[row.outcome] = counts.get(row.outcome, 0) + 1
        except (ImportError, OSError, ValueError) as exc:
            # Narrow on purpose: the reader turns a malformed pair status into
            # INVALID itself, so what is left here is "the reader is not
            # available" or "the tree cannot be read" -- and an unexpected
            # failure should surface as a traceback, not as a tidy FAIL row.
            report.add(
                f"workload.{half}.readable_outcomes", GATE_WORKLOAD, False,
                f"the pair statuses could not be read: {exc}", f"{half}/",
            )
            continue
        summary = ", ".join(f"{name}={counts[name]}" for name in sorted(counts))
        unusable = counts.get(OUTCOME_INVALID, 0) + counts.get(OUTCOME_MISSING, 0)
        report.add(
            f"workload.{half}.readable_outcomes", GATE_WORKLOAD, unusable == 0,
            (
                f"{sum(counts.values())} pair statuses read ({summary or 'none'})"
                if unusable == 0
                else f"{unusable} pair status(es) carry no usable outcome ({summary})"
            ),
            f"{half}/",
        )
        # (e) the binary manifest is built from this run's pair statuses, so the
        #     samples it names must be the subset's samples for this half.  A
        #     well-formed manifest left over from another run would otherwise
        #     satisfy the artifact check on its own.
        if definition is not None:
            manifest_path = run_dir / f"binary_manifest_{half}.txt"
            wanted = {source for source, _ in definition}
            try:
                named = binary_manifest_samples(manifest_path)
            except SubsetCiError as exc:
                report.add(
                    f"workload.{half}.binary_manifest_samples", GATE_WORKLOAD, False,
                    str(exc), f"binary_manifest_{half}.txt",
                )
            else:
                missing_samples = sorted(wanted - named)
                extra_samples = sorted(named - wanted)
                report.add(
                    f"workload.{half}.binary_manifest_samples", GATE_WORKLOAD,
                    not missing_samples and not extra_samples,
                    (
                        f"{len(named)} samples, exactly the subset's"
                        if not missing_samples and not extra_samples
                        else f"{len(missing_samples)} subset sample(s) absent "
                             f"(e.g. {missing_samples[0] if missing_samples else '-'}), "
                             f"{len(extra_samples)} foreign "
                             f"(e.g. {extra_samples[0] if extra_samples else '-'})"
                    ),
                    f"binary_manifest_{half}.txt",
                )

        decided = sum(counts.get(name, 0) for name in semantic_outcomes())
        report.add(
            f"workload.{half}.semantic_outcomes", GATE_WORKLOAD, decided > 0,
            (
                f"{decided} of {sum(counts.values())} pairs produced a result "
                f"({summary or 'none'})"
                if decided
                else "no pair produced a result: every outcome is a deadline or an "
                     f"infrastructure failure ({summary or 'none'})"
            ),
            f"{half}/",
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
                f"{half}/{PUBLICATION_MANIFEST_FILE}",
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
    analysis_timeout: str,
    analysis_timeout_margin: str,
    analysis_config_schema: str = DEFAULT_ANALYSIS_CONFIG_SCHEMA,
    profile: str = PROFILE_FULL,
    runner_exit_status: Optional[int] = None,
    subset_definition: Path = SUBSET_DEFINITION_FILE,
) -> Report:
    if profile not in PROFILES:
        raise SubsetCiError(f"profile must be one of {', '.join(PROFILES)}: {profile!r}")
    halves = halves_for_scope(scope)
    expected: Dict[str, object] = {
        "working_root": working_root,
        "pair_process_timeout": pair_process_timeout,
        "identical_fast_path": identical_fast_path,
        "analysis_timeout": analysis_timeout,
        "analysis_timeout_margin": analysis_timeout_margin,
        "analysis_config_schema": analysis_config_schema,
        "subset_definition": str(subset_definition),
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
        _verify_workload(report, run_dir, subset_definition)
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
        "--analysis-timeout", required=True,
        help="the effective ANALYSIS_TIMEOUT every half must have recorded "
             "(seconds as `runner_timeout_policy resolve` prints it; 0 = off)",
    )
    verify_command.add_argument(
        "--analysis-timeout-margin", required=True,
        help="the effective ANALYSIS_TIMEOUT_MARGIN every half must have recorded",
    )
    verify_command.add_argument(
        "--analysis-config-schema", default=DEFAULT_ANALYSIS_CONFIG_SCHEMA,
    )
    verify_command.add_argument(
        "--subset-definition", type=Path, default=SUBSET_DEFINITION_FILE,
        help="the fixed subset's definition, which says which samples and pair "
             "ids the run had to cover (full profile)",
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
                analysis_timeout=args.analysis_timeout,
                analysis_timeout_margin=args.analysis_timeout_margin,
                analysis_config_schema=args.analysis_config_schema,
                profile=args.profile,
                runner_exit_status=args.runner_exit_status,
                subset_definition=args.subset_definition,
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

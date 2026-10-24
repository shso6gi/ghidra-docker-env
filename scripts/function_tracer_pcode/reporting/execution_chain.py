"""The execution chain of a matrix result tree (eval plan v2 PR-B).

A FULL evaluation is often finished by several *executions* of the runner on
the same output directory: one is stopped or killed, the next resumes it and
reuses every pair the earlier ones decided.  The top-level artifacts of the tree
(``run_manifest.txt``, the publication, the signed execution receipt) describe
only the latest execution, and a killed execution never writes its end-of-run
artifacts at all.  This module owns the records that survive every execution
and the verifier that decides, from those records alone, whether the tree is
one complete evaluation of a single identity.

Records, under ``<tree>/.executions/<runtime_run_id>/``:

``run_manifest.start.txt``
    The manifest the execution installed at the top level when it started
    (its run kind, scope, analysis config and its digest, source digest,
    runner, inputs and environment).  Written once, right after the manifest is
    installed and before any pair work; never overwritten.
``issued/<execution_nonce>.json``
    Written before a pair's analysis starts: which pair (status path and
    target digest) this execution started under that nonce.  The nonce is in
    the signed pair status, so a decided pair is attributed to the execution
    that issued its nonce -- also when that execution was killed before it
    could publish anything.  A pair whose issue record cannot be written is not
    analysed.
``seal/`` (``run_manifest.end.txt``, the publication, the execution receipt)
    Copies made when the execution sealed (finished normally), committed
    together by one directory rename.  An execution without ``seal/`` was
    killed or failed before its end.

**Commit points.**  Every record is written under a temporary name of the form
``.<final name>.uncommitted-<random>`` in its final directory, made durable,
and only then given its final name (a hard link for a file, a rename for the
``seal/`` directory) -- the single commit point.  So a writer stopped at any
moment leaves either the committed record or *uncommitted debris*, never a
half-written record under a final name.  Debris is never evidence and the
verifier ignores it: no committed record ever exists under a debris name, so
ignoring debris cannot hide one.  An execution directory that holds nothing
but debris is an execution stopped before its start record was committed --
it started no pair (an issue record needs the start record) -- and is ignored
too.  Everything else is judged: a committed record that is missing where the
other records require it, unreadable, malformed or inconsistent opens the
chain, and so does any entry that is neither a record nor debris.  Resuming
the same identity therefore reaches ``CLOSED_SAME_IDENTITY`` after any stop
without deleting anything by hand, while a damaged record is never accepted.

``verify_execution_chain`` returns ``CLOSED_SAME_IDENTITY`` only when every
check in ``CHAIN_CHECKS`` passes; anything absent, unreadable, inconsistent or
ambiguous is ``OPEN`` with named reasons.  Reading these records never changes
an outcome, a pair status or a runner exit code.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import tempfile
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

EXECUTIONS_DIR = ".executions"
START_RECORD = "run_manifest.start.txt"
END_RECORD = "run_manifest.end.txt"
ISSUED_DIR = "issued"
SEAL_DIR = "seal"
UNCOMMITTED_MARK = ".uncommitted-"
ISSUE_SCHEMA = "eqbench-pair-execution-issue-v1"
RUN_MANIFEST_FILE = "run_manifest.txt"
PUBLICATION_FILE = "matrix-publication-manifest.json"
RECEIPT_FILE = "validation-execution-receipt.json"
PUBLIC_KEY_FILE = "pair-status-verification-key.json"
PAIR_STATUS_SUFFIX = ".pair-status.json"
RUN_ID_KEY = "runtime_run_id"
#: start-record keys that legitimately differ between executions of one
#: evaluation.  Every other key -- run kind, scope, analysis config and its
#: digest, source digest, runner script, inputs, paths, environment -- must be
#: equal in every execution of the chain.
PER_EXECUTION_START_KEYS = frozenset({
    RUN_ID_KEY, "start_time_utc", "hostname",
    "git_commit", "git_dirty", "git_dirty_files_digest",
})

VERDICT_CLOSED = "CLOSED_SAME_IDENTITY"
VERDICT_OPEN = "OPEN"

# Named reasons (one per failed check).
R_NO_PUBLICATION = "latest_publication_invalid"
R_NO_CHAIN_FIELDS = "publication_has_no_execution_chain"
R_BINDING = "latest_execution_binding_failed"
R_LATEST_START = "latest_start_record_missing_or_differs"
R_LATEST_UNSEALED = "latest_execution_seal_missing_or_differs"
R_UNRECOGNISED = "unrecognised_execution_record"
R_START_MISSING = "execution_has_no_start_record"
R_CONDITIONS = "execution_conditions_differ"
R_SEALED_INVALID = "sealed_execution_invalid"
R_PRIOR = "prior_executions_differ_from_records"
R_CENSUS = "pair_census_inconsistent"
R_NOT_DECIDED = "pair_status_not_decided"
R_TARGET = "pair_target_identity_differs"
R_PATH = "pair_status_path_differs_from_target"
R_BINARY = "binary_sha_differs_from_build_receipt"
R_UNATTRIBUTED = "pair_status_not_attributed_to_an_execution"
R_DUPLICATE_ISSUE = "execution_nonce_issued_more_than_once"
R_PRODUCER_NO_START = "producing_execution_has_no_start_record"
R_EXECUTED_PRODUCER = "executed_pair_not_produced_by_latest_execution"
R_REUSED_PRODUCER = "reused_pair_produced_by_latest_execution"
R_REUSED_EVIDENCE = "reused_pair_evidence_differs"
R_OBSERVATION = "execution_records_unreadable"
R_DAMAGED = "execution_record_damaged"


# ---------------------------------------------------------------------------
# Writing the records (called by the runners through the CLI below)
# ---------------------------------------------------------------------------


def _execution_dir(root: Path, run_id: str) -> Path:
    if not re.fullmatch(r"[0-9a-f]{32}", run_id):
        raise ValueError(f"runtime_run_id is not 32 hex digits: {run_id!r}")
    return Path(root) / EXECUTIONS_DIR / run_id


def _fsync_directory(path: Path) -> None:
    directory = os.open(path, os.O_RDONLY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def _write_durable(path: Path, data: bytes) -> None:
    with open(path, "xb") as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())


def _write_exclusive(path: Path, data: bytes) -> None:
    """Commit ``path`` with ``data``; an existing record is an error.

    The data is made durable under an uncommitted temporary name first; the
    hard link to the final name is the commit point (``link`` fails if the name
    exists, so a record is never replaced).  The temporary name is removed
    afterwards; a stop in between leaves only debris (see the module docstring).
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    handle, temporary = tempfile.mkstemp(
        prefix=f".{path.name}{UNCOMMITTED_MARK}", dir=path.parent,
    )
    try:
        with os.fdopen(handle, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, path)
    finally:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
    _fsync_directory(path.parent)


def record_start(root: Path, run_id: str, manifest: Path) -> Path:
    """Record the manifest execution ``run_id`` started with (I1)."""
    data = Path(manifest).read_bytes()
    values = _parse_key_values(data.decode("utf-8"))
    if values.get(RUN_ID_KEY) != run_id:
        raise ValueError("the start manifest does not name this runtime_run_id")
    path = _execution_dir(root, run_id) / START_RECORD
    _write_exclusive(path, data)
    return path


def record_issue(
    root: Path, run_id: str, *, execution_nonce: str, pair_status_path: Path,
    target_file: Path,
) -> Path:
    """Record that ``run_id`` starts the pair at ``pair_status_path`` (I2)."""
    root = Path(root)
    execution = _execution_dir(root, run_id)
    if not (execution / START_RECORD).is_file():
        raise ValueError("the execution has no start record")
    if not re.fullmatch(r"[0-9a-f]{16,128}", execution_nonce):
        raise ValueError("execution nonce is malformed")
    relative = _relative_status_path(root, Path(pair_status_path))
    target = json.loads(Path(target_file).read_text(encoding="utf-8"))
    digest = target.get("target_digest") if isinstance(target, Mapping) else None
    if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise ValueError("the pair target has no target digest")
    payload = {
        "schema": ISSUE_SCHEMA, RUN_ID_KEY: run_id, "execution_nonce": execution_nonce,
        "pair_status_path": relative, "target_digest": digest,
    }
    path = execution / ISSUED_DIR / f"{execution_nonce}.json"
    _write_exclusive(path, (json.dumps(payload, sort_keys=True) + "\n").encode("utf-8"))
    return path


SEAL_FILES = ((RUN_MANIFEST_FILE, END_RECORD), (PUBLICATION_FILE, PUBLICATION_FILE),
              (RECEIPT_FILE, RECEIPT_FILE))


def record_seal(root: Path, run_id: str) -> None:
    """Commit the latest execution's end artifacts as its ``seal/`` (I3).

    The three copies are written into an uncommitted staging directory and
    committed together by renaming it to ``seal`` -- there is no partially
    sealed state.
    """
    root = Path(root)
    execution = _execution_dir(root, run_id)
    if not (execution / START_RECORD).is_file():
        raise ValueError("the execution has no start record")
    final = execution / SEAL_DIR
    if final.exists():
        raise FileExistsError(f"the execution is already sealed: {final}")
    staging = Path(tempfile.mkdtemp(prefix=f".{SEAL_DIR}{UNCOMMITTED_MARK}", dir=execution))
    for source, name in SEAL_FILES:
        _write_durable(staging / name, (root / source).read_bytes())
    _fsync_directory(staging)
    os.rename(staging, final)
    _fsync_directory(execution)


def _relative_status_path(root: Path, path: Path) -> str:
    resolved_root = root.resolve()
    resolved = path if path.is_absolute() else Path.cwd() / path
    resolved = Path(os.path.normpath(resolved.resolve().parent)) / resolved.name
    relative = resolved.relative_to(resolved_root).as_posix()
    if not relative.endswith(PAIR_STATUS_SUFFIX) or ".." in Path(relative).parts:
        raise ValueError(f"not a pair-status path inside the tree: {path}")
    return relative


ENVIRONMENT_FINGERPRINT_ENV = "EQBENCH_ENVIRONMENT_FINGERPRINT"
UNAVAILABLE = "unavailable"


def _one_line(value: str) -> str:
    return " ".join(value.split()) or UNAVAILABLE


def _command_version(argv: Sequence[str], pattern: str) -> str:
    try:
        completed = subprocess.run(
            list(argv), capture_output=True, text=True, timeout=60, check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return UNAVAILABLE
    for line in (completed.stdout + "\n" + completed.stderr).splitlines():
        if re.search(pattern, line):
            return _one_line(line)
    return UNAVAILABLE


def _first_line(path: Path) -> str:
    try:
        return _one_line(path.read_text(encoding="utf-8").splitlines()[0])
    except (OSError, UnicodeError, IndexError):
        return UNAVAILABLE


def environment_lines(repo_root: Path) -> List[str]:
    """The environment rows every start record carries (``key=value``).

    Tool versions, the container's resource limits and the fingerprint the
    evaluation wrapper passes in.  None of them is part of the analysis config
    digest; the chain verifier requires them to be equal across the executions
    of one evaluation.  A value that cannot be observed is recorded as
    ``unavailable`` -- recorded, never guessed -- and still has to agree.
    """
    from scripts.function_tracer_pcode.config.settings import discover_runtime_environment

    runtime = discover_runtime_environment(repo_root=Path(repo_root))
    ghidra = UNAVAILABLE
    if runtime.ghidra_install_dir:
        try:
            for line in (
                Path(runtime.ghidra_install_dir) / "Ghidra" / "application.properties"
            ).read_text(encoding="utf-8").splitlines():
                if line.startswith("application.version="):
                    ghidra = _one_line(line.split("=", 1)[1])
        except (OSError, UnicodeError):
            pass
    java = str(Path(runtime.java_home) / "bin" / "java") if runtime.java_home else "java"
    rows = {
        "environment_fingerprint": os.environ.get(ENVIRONMENT_FINGERPRINT_ENV) or "unrecorded",
        "python_version": platform.python_version(),
        "ghidra_version": ghidra,
        "java_version": _command_version([java, "-version"], r'version "'),
        "z3_version": _command_version(["z3", "--version"], r"[Vv]ersion"),
        "cgroup_memory_max": _first_line(Path("/sys/fs/cgroup/memory.max")),
        "cgroup_cpu_max": _first_line(Path("/sys/fs/cgroup/cpu.max")),
    }
    return [f"{key}={value}" for key, value in rows.items()]


# ---------------------------------------------------------------------------
# Reading the records
# ---------------------------------------------------------------------------


def _parse_key_values(text: str) -> Dict[str, str]:
    values: Dict[str, str] = {}
    for line in text.splitlines():
        if not line or "=" not in line:
            raise ValueError("manifest contains a malformed row")
        key, value = line.split("=", 1)
        if not key or key in values:
            raise ValueError("manifest repeats or lacks a key")
        values[key] = value
    return values


_DEBRIS = re.compile(r"\.(?P<name>.+)" + re.escape(UNCOMMITTED_MARK) + r"[A-Za-z0-9_]+")


def _debris_of(name: str) -> Optional[str]:
    """The final name an uncommitted temporary name was for, or ``None``."""
    match = _DEBRIS.fullmatch(name)
    return match.group("name") if match else None


@dataclass
class ExecutionRecords:
    """What one ``.executions/<run_id>/`` directory holds, classified."""

    run_id: str
    start_text: Optional[str] = None
    issued: List[Mapping[str, Any]] = field(default_factory=list)
    sealed: bool = False
    #: Committed records that are damaged or entries that are neither a record
    #: nor debris -- each opens the chain.
    problems: List[str] = field(default_factory=list)
    debris: List[str] = field(default_factory=list)

    @property
    def started(self) -> bool:
        return self.start_text is not None

    @property
    def holds_records(self) -> bool:
        return bool(self.issued or self.sealed or self.problems)


@dataclass
class ChainRecords:
    executions: Dict[str, ExecutionRecords] = field(default_factory=dict)
    #: Directories stopped before their start record was committed (debris only).
    never_started: List[str] = field(default_factory=list)
    unrecognised: List[str] = field(default_factory=list)

    def started(self) -> Dict[str, ExecutionRecords]:
        return {run_id: e for run_id, e in self.executions.items() if e.started}


def _read_execution(directory: Path, run_id: str) -> ExecutionRecords:
    records = ExecutionRecords(run_id)
    for entry in sorted(directory.iterdir()):
        name = entry.name
        debris = _debris_of(name)
        if debris in (START_RECORD, SEAL_DIR):
            records.debris.append(name)
        elif name == START_RECORD and entry.is_file() and not entry.is_symlink():
            try:
                text = entry.read_text(encoding="utf-8")
                if _parse_key_values(text).get(RUN_ID_KEY) != run_id:
                    raise ValueError("it names another runtime_run_id")
                records.start_text = text
            except (OSError, UnicodeError, ValueError) as exc:
                records.problems.append(f"{START_RECORD}: {exc}")
        elif name == ISSUED_DIR and entry.is_dir() and not entry.is_symlink():
            _read_issued(entry, run_id, records)
        elif name == SEAL_DIR and entry.is_dir() and not entry.is_symlink():
            present = sorted(path.name for path in entry.iterdir())
            if present != sorted(final for _source, final in SEAL_FILES):
                records.problems.append(f"{SEAL_DIR}/ holds {present}")
            else:
                records.sealed = True
        else:
            records.problems.append(f"unrecognised entry {name}")
    return records


def _read_issued(directory: Path, run_id: str, records: ExecutionRecords) -> None:
    for path in sorted(directory.iterdir()):
        debris = _debris_of(path.name)
        if debris is not None and re.fullmatch(r"[0-9a-f]{16,128}\.json", debris):
            records.debris.append(f"{ISSUED_DIR}/{path.name}")
            continue
        try:
            if not path.is_file() or path.is_symlink():
                raise ValueError("not a regular file")
            record = json.loads(path.read_text(encoding="utf-8"))
            if (
                not isinstance(record, Mapping)
                or set(record) != {
                    "schema", RUN_ID_KEY, "execution_nonce", "pair_status_path",
                    "target_digest",
                }
                or record.get("schema") != ISSUE_SCHEMA
                or record.get(RUN_ID_KEY) != run_id
                or f"{record.get('execution_nonce')}.json" != path.name
            ):
                raise ValueError("issue record does not describe itself")
        except (OSError, UnicodeError, ValueError) as exc:
            records.problems.append(f"{ISSUED_DIR}/{path.name}: {exc}")
            continue
        records.issued.append(record)


def read_chain_records(root: Path) -> ChainRecords:
    """Every execution directory of ``root``, classified (see the module docstring).

    Raises ``OSError`` only when ``.executions`` itself cannot be listed.
    """
    chain = ChainRecords()
    directory = Path(root) / EXECUTIONS_DIR
    if not directory.exists():
        return chain
    for entry in sorted(directory.iterdir()):
        if not (entry.is_dir() and not entry.is_symlink()
                and re.fullmatch(r"[0-9a-f]{32}", entry.name)):
            chain.unrecognised.append(entry.name)
            continue
        try:
            records = _read_execution(entry, entry.name)
        except OSError as exc:
            records = ExecutionRecords(entry.name, problems=[f"unreadable: {exc}"])
        if not records.started and not records.holds_records:
            chain.never_started.append(entry.name)
            continue
        chain.executions[entry.name] = records
    return chain


def execution_ids(root: Path) -> Tuple[List[str], List[str]]:
    """``(started execution ids, unrecognised entries)`` under ``.executions``."""
    chain = read_chain_records(root)
    return sorted(chain.started()), list(chain.unrecognised)


def start_record_sha256(root: Path, run_id: str) -> str:
    return hashlib.sha256((_execution_dir(root, run_id) / START_RECORD).read_bytes()).hexdigest()


def prior_executions(root: Path, latest_run_id: str) -> List[Mapping[str, str]]:
    """The publication v4 ``prior_executions`` field: every other committed start.

    Never raises on debris or damaged records: the publication records what is
    committed, and the verifier judges the rest (a run must be able to finish
    and publish whatever state an earlier execution left).
    """
    rows = []
    for run_id, records in sorted(read_chain_records(root).started().items()):
        if run_id == latest_run_id:
            continue
        rows.append({
            RUN_ID_KEY: run_id,
            "start_record_sha256": hashlib.sha256(
                records.start_text.encode("utf-8")).hexdigest(),
        })
    return rows


def issued_records(root: Path) -> Tuple[Dict[str, List[Mapping[str, Any]]], List[str]]:
    """``(nonce -> committed issue records of started executions, problems)``."""
    by_nonce: Dict[str, List[Mapping[str, Any]]] = {}
    problems: List[str] = []
    chain = read_chain_records(root)
    for run_id, records in chain.executions.items():
        problems.extend(f"{run_id}/{problem}" for problem in records.problems)
        for record in records.issued:
            by_nonce.setdefault(str(record["execution_nonce"]), []).append(record)
    return by_nonce, problems


def producing_run_id(
    by_nonce: Mapping[str, Sequence[Mapping[str, Any]]], status_payload: Mapping[str, Any],
    relative: str,
) -> Optional[str]:
    """The execution that issued this status's nonce for this path, if exactly one."""
    rows = [
        row for row in by_nonce.get(str(status_payload.get("execution_nonce")), ())
        if row.get("pair_status_path") == relative
        and row.get("target_digest")
        == (status_payload.get("pair_execution_target") or {}).get("target_digest")
    ]
    return str(rows[0][RUN_ID_KEY]) if len(rows) == 1 else None


def pair_status_evidence(
    root: Path, expected: Sequence[str], reused: Sequence[str], latest_run_id: str,
) -> Tuple[str, List[Mapping[str, Any]]]:
    """``(evidence digest over every expected pair, reused-pair evidence rows)``.

    Used by the publication v4 builder.  The digest covers each expected pair's
    signed body digest (or ``MISSING`` / ``UNSIGNED``) and its producing
    execution, so a status replaced after the publication changes a rebuilt
    publication.  The reused rows carry what a verifier needs to check that a
    reused pair is still the one the latest execution reused.
    """
    root = Path(root)
    by_nonce, _problems = issued_records(root)
    lines, rows = [], []
    reused_set = set(reused)
    for relative in sorted(expected):
        path = root / relative
        body_digest, target_digest, producer = "MISSING", None, None
        if path.is_file():
            try:
                payload = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, UnicodeError, ValueError):
                payload = None
            if isinstance(payload, Mapping) and isinstance(payload.get("pair_status_body_digest"), str):
                body_digest = payload["pair_status_body_digest"]
                target_digest = (payload.get("pair_execution_target") or {}).get("target_digest")
                producer = producing_run_id(by_nonce, payload, relative)
            else:
                body_digest = "UNSIGNED"
        lines.append(f"{relative}\t{body_digest}\t{producer or '-'}")
        if relative in reused_set:
            if body_digest in ("MISSING", "UNSIGNED"):
                raise ValueError(f"a reused pair has no signed status: {relative}")
            rows.append({
                "pair_status_path": relative, "pair_status_body_digest": body_digest,
                "target_digest": target_digest, "producing_run_id": producer,
            })
    digest = hashlib.sha256(("\n".join(lines) + "\n").encode("utf-8")).hexdigest()
    return digest, rows


# ---------------------------------------------------------------------------
# Verification
# ---------------------------------------------------------------------------


def expected_status_path(target: Mapping[str, Any]) -> str:
    function = target["function_name"]
    return (
        f"{target['output_sample_relative_path']}/{function}/"
        f"{function}_{target['left_binary_id']}_{target['right_binary_id']}{PAIR_STATUS_SUFFIX}"
    )


def build_receipt_binary_shas(build_receipts: Sequence[Any]) -> Dict[str, Optional[str]]:
    """``binary_path -> sha256`` over the published build receipts (``None`` if ambiguous)."""
    shas: Dict[str, Optional[str]] = {}
    for receipt in build_receipts:
        for axis in (receipt or {}).get("binary_axes") or ():
            path, sha = axis.get("binary_path"), axis.get("binary_sha256")
            if not isinstance(path, str) or not isinstance(sha, str):
                continue
            if path in shas and shas[path] != sha:
                shas[path] = None
            else:
                shas[path] = sha
    return shas


def check_pair_status(
    root: Path, relative: str, *, public_key_path: Path, source_digest: str,
    config_digest: str, binary_shas: Mapping[str, Optional[str]],
) -> Tuple[Optional[Mapping[str, Any]], Optional[str], Optional[str]]:
    """One expected pair: ``(payload, body, None)`` when decided and consistent.

    Otherwise ``(payload or None, None, reason)`` with a named reason.  Shared
    by the chain verifier and the post-run identity audit, so the two never
    disagree about what a valid pair of a tree is.
    """
    from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
        FINALIZATION_DURABLE,
        FINALIZATION_RESOLVED,
        pair_status_finalization,
        validate_signed_pair_status,
    )

    path = Path(root) / relative
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        body = validate_signed_pair_status(payload, public_key_path=public_key_path)
        if pair_status_finalization(payload, public_key_path=public_key_path) not in (
            FINALIZATION_RESOLVED, FINALIZATION_DURABLE,
        ):
            raise ValueError("no regular terminal state")
    except (OSError, UnicodeError, ValueError, TypeError, KeyError):
        return None, None, R_NOT_DECIDED
    target = body["pair_execution_target"]
    if (
        target.get("analysis_source_digest") != source_digest
        or target.get("analysis_config_digest") != config_digest
    ):
        return payload, None, R_TARGET
    if expected_status_path(target) != relative:
        return payload, None, R_PATH
    for side in ("left", "right"):
        recorded = binary_shas.get(target[f"{side}_binary_path"])
        if recorded is None or recorded != target[f"{side}_binary_sha256"]:
            return payload, None, R_BINARY
    return payload, body, None


def _start_conditions(values: Mapping[str, str]) -> Dict[str, str]:
    return {key: value for key, value in values.items() if key not in PER_EXECUTION_START_KEYS}


def verify_execution_chain(root: Path) -> Dict[str, Any]:
    """Whether ``root`` is one evaluation of one identity across its executions.

    See the module docstring and I5 in the PR-B design: ``CLOSED_SAME_IDENTITY``
    only when every check passes; ``OPEN`` with every failed check's reason
    (and a few example paths) otherwise.
    """
    from scripts.function_tracer_pcode.reporting.execution_receipt import (
        build_matrix_publication_manifest,
        matrix_execution_binding_mismatch,
        validate_execution_receipt,
        validate_matrix_publication_manifest,
    )

    root = Path(root)
    reasons: Dict[str, List[str]] = {}

    def fail(reason: str, detail: str = "") -> None:
        reasons.setdefault(reason, [])
        if detail and len(reasons[reason]) < 5:
            reasons[reason].append(detail)

    report: Dict[str, Any] = {
        "root": str(root), "verdict": VERDICT_OPEN, "reasons": reasons,
        "latest_run_id": None, "run_scope": None, "executions": [],
        "pairs_expected": 0, "pairs_executed_by_latest": 0, "pairs_reused": 0,
        "pairs_reused_proven": 0,
    }

    def done() -> Dict[str, Any]:
        report["verdict"] = VERDICT_CLOSED if not reasons else VERDICT_OPEN
        report["reasons"] = {key: value for key, value in sorted(reasons.items())}
        return report

    key_path = root / PUBLIC_KEY_FILE
    try:
        publication_payload = json.loads((root / PUBLICATION_FILE).read_text(encoding="utf-8"))
        publication = validate_matrix_publication_manifest(publication_payload)
        receipt = validate_execution_receipt(
            json.loads((root / RECEIPT_FILE).read_text(encoding="utf-8")),
            public_key_path=key_path,
        )
    except (OSError, UnicodeError, ValueError, TypeError, KeyError) as exc:
        fail(R_NO_PUBLICATION, f"{type(exc).__name__}: {exc}")
        return done()
    report["run_scope"] = publication["run_scope"]
    latest = publication.get(RUN_ID_KEY)
    if not isinstance(latest, str):
        fail(R_NO_CHAIN_FIELDS, f"publication schema {publication.get('schema')}")
        return done()
    report["latest_run_id"] = latest
    mismatch = matrix_execution_binding_mismatch(root / PUBLICATION_FILE, publication, receipt)
    if mismatch is not None:
        fail(R_BINDING, mismatch)
    try:
        rebuilt = build_matrix_publication_manifest(root)
        if dict(rebuilt) != dict(publication_payload):
            fail(R_BINDING, "the current artifacts rebuild a different publication")
    except (OSError, UnicodeError, ValueError, KeyError) as exc:
        fail(R_BINDING, f"publication cannot be rebuilt: {type(exc).__name__}: {exc}")

    # Executions on disk: committed records are judged, uncommitted debris and
    # executions stopped before their start record are not evidence.
    try:
        chain = read_chain_records(root)
    except OSError as exc:
        fail(R_OBSERVATION, str(exc))
        return done()
    for name in chain.unrecognised:
        fail(R_UNRECOGNISED, name)
    report["never_started_executions"] = list(chain.never_started)
    report["uncommitted_debris"] = sum(len(e.debris) for e in chain.executions.values())
    starts: Dict[str, Dict[str, str]] = {}
    start_texts: Dict[str, str] = {}
    sealed: Dict[str, bool] = {}
    for run_id, records in chain.executions.items():
        for problem in records.problems:
            fail(R_SEALED_INVALID if problem.startswith(SEAL_DIR) else R_DAMAGED,
                 f"{run_id}/{problem}")
        if not records.started:
            # Issue records or a seal without the start record that must precede them.
            fail(R_START_MISSING, f"{run_id}: records without a committed start record")
            continue
        start_texts[run_id] = records.start_text
        starts[run_id] = _parse_key_values(records.start_text)
        sealed[run_id] = records.sealed
        if not records.sealed:
            continue
        seal = _execution_dir(root, run_id) / SEAL_DIR
        try:
            copy_payload = json.loads((seal / PUBLICATION_FILE).read_text(encoding="utf-8"))
            copy = validate_matrix_publication_manifest(copy_payload)
            copy_receipt = validate_execution_receipt(
                json.loads((seal / RECEIPT_FILE).read_text(encoding="utf-8")),
                public_key_path=key_path,
            )
            why = matrix_execution_binding_mismatch(seal / PUBLICATION_FILE, copy, copy_receipt)
            if why is not None:
                raise ValueError(why)
            if copy.get(RUN_ID_KEY) != run_id:
                raise ValueError("sealed publication names another execution")
            if not (seal / END_RECORD).read_text(encoding="utf-8").startswith(records.start_text):
                raise ValueError("end manifest does not continue the start record")
        except (OSError, UnicodeError, ValueError, TypeError, KeyError) as exc:
            fail(R_SEALED_INVALID, f"{run_id}: {exc}")

    # The latest execution.
    if latest not in starts:
        fail(R_LATEST_START, f"{latest}: no start record")
    else:
        try:
            top = (root / RUN_MANIFEST_FILE).read_text(encoding="utf-8")
            if not top.startswith(start_texts[latest]):
                fail(R_LATEST_START, "run_manifest.txt does not continue the start record")
        except (OSError, UnicodeError) as exc:
            fail(R_LATEST_START, str(exc))
        if not sealed.get(latest):
            fail(R_LATEST_UNSEALED, latest)
        else:
            seal = _execution_dir(root, latest) / SEAL_DIR
            for source, name in SEAL_FILES:
                try:
                    same = (root / source).read_bytes() == (seal / name).read_bytes()
                except OSError as exc:
                    fail(R_LATEST_UNSEALED, f"{name}: {exc}")
                    continue
                if not same:
                    fail(R_LATEST_UNSEALED, f"{SEAL_DIR}/{name} differs from the top-level {source}")
        reference = _start_conditions(starts[latest])
        for run_id, values in starts.items():
            conditions = _start_conditions(values)
            if conditions != reference:
                keys = sorted(
                    key for key in set(conditions) | set(reference)
                    if conditions.get(key) != reference.get(key)
                )
                fail(R_CONDITIONS, f"{run_id}: {', '.join(keys[:5])}")
        if starts[latest].get("analysis_config_digest") != publication["analysis_config_digest"] or (
            starts[latest].get("analysis_source_digest_start")
            != publication["analysis_source_digest_start"]
        ):
            fail(R_CONDITIONS, "the latest start record differs from the publication")
    recorded_prior = sorted(
        (row[RUN_ID_KEY], row["start_record_sha256"]) for row in publication["prior_executions"]
    )
    on_disk = sorted(
        (run_id, hashlib.sha256(text.encode("utf-8")).hexdigest())
        for run_id, text in start_texts.items() if run_id != latest
    )
    if recorded_prior != on_disk:
        fail(R_PRIOR, (
            f"publication lists {len(recorded_prior)} prior start record(s), the tree holds "
            f"{len(on_disk)}; {len(set(recorded_prior) ^ set(on_disk))} differ by id or digest"
        ))

    # The pair census.
    expected = list(publication["expected_pair_status_paths"])
    reused = list(publication["verified_skipped_pair_status_paths"])
    report["pairs_expected"] = len(expected)
    report["pairs_reused"] = len(reused)
    if not set(reused) <= set(expected):
        fail(R_CENSUS, "a reused pair is not in the expected census")
    evidence = {row["pair_status_path"]: row for row in publication["reused_pair_evidence"]}
    if set(evidence) != set(reused):
        fail(R_REUSED_EVIDENCE, "reused_pair_evidence does not cover exactly the reused pairs")
    # Damaged issue records were reported with their execution above.
    by_nonce, _problems = issued_records(root)
    binary_shas = build_receipt_binary_shas(publication["build_receipts"])
    executed_by: Dict[str, int] = {run_id: 0 for run_id in starts}
    reused_set = set(reused)
    for relative in expected:
        payload, body, reason = check_pair_status(
            root, relative, public_key_path=key_path,
            source_digest=publication["analysis_source_digest_start"],
            config_digest=publication["analysis_config_digest"], binary_shas=binary_shas,
        )
        if reason is not None:
            fail(reason, relative)
            continue
        nonce = body["execution_nonce"]
        if len(by_nonce.get(nonce, ())) > 1:
            fail(R_DUPLICATE_ISSUE, relative)
            continue
        producer = producing_run_id(by_nonce, payload, relative)
        if producer is None:
            fail(R_UNATTRIBUTED, relative)
            continue
        if producer not in starts:
            fail(R_PRODUCER_NO_START, f"{relative} <- {producer}")
            continue
        executed_by[producer] += 1
        if relative in reused_set:
            if producer == latest:
                fail(R_REUSED_PRODUCER, relative)
                continue
            row = evidence.get(relative) or {}
            if (
                row.get("pair_status_body_digest") != payload["pair_status_body_digest"]
                or row.get("target_digest") != body["pair_execution_target"]["target_digest"]
                or row.get("producing_run_id") != producer
            ):
                fail(R_REUSED_EVIDENCE, relative)
                continue
            report["pairs_reused_proven"] += 1
        elif producer != latest:
            fail(R_EXECUTED_PRODUCER, f"{relative} <- {producer}")
    report["pairs_executed_by_latest"] = executed_by.get(latest, 0)
    report["executions"] = [
        {
            RUN_ID_KEY: run_id, "latest": run_id == latest, "sealed": sealed.get(run_id, False),
            "start_time_utc": starts[run_id].get("start_time_utc"),
            "decided_pairs_attributed": executed_by[run_id],
        }
        for run_id in sorted(starts, key=lambda rid: (starts[rid].get("start_time_utc") or "", rid))
    ]
    if sum(executed_by.values()) != len(expected) and not reasons:
        fail(R_CENSUS, "attributed pairs do not account for the census")
    return done()


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    start = sub.add_parser("start", help="record the manifest an execution started with")
    start.add_argument("--root", required=True)
    start.add_argument("--run-id", required=True)
    start.add_argument("--manifest", required=True)
    issue = sub.add_parser("issue", help="record a pair started under an execution nonce")
    issue.add_argument("--root", required=True)
    issue.add_argument("--run-id", required=True)
    issue.add_argument("--execution-nonce", required=True)
    issue.add_argument("--pair-status", required=True)
    issue.add_argument("--target-file", required=True)
    seal = sub.add_parser("seal", help="copy the latest execution's end artifacts")
    seal.add_argument("--root", required=True)
    seal.add_argument("--run-id", required=True)
    verify = sub.add_parser("verify", help="CLOSED_SAME_IDENTITY / OPEN with reasons")
    verify.add_argument("--root", required=True)
    environment = sub.add_parser("environment-lines", help="the start record's environment rows")
    environment.add_argument("--repo-root", required=True)
    args = parser.parse_args(argv)
    try:
        if args.command == "environment-lines":
            print("\n".join(environment_lines(Path(args.repo_root))))
        elif args.command == "start":
            record_start(Path(args.root), args.run_id, Path(args.manifest))
        elif args.command == "issue":
            record_issue(
                Path(args.root), args.run_id, execution_nonce=args.execution_nonce,
                pair_status_path=Path(args.pair_status), target_file=Path(args.target_file),
            )
        elif args.command == "seal":
            record_seal(Path(args.root), args.run_id)
        else:
            report = verify_execution_chain(Path(args.root))
            print(json.dumps(report, indent=2, sort_keys=True))
            return 0 if report["verdict"] == VERDICT_CLOSED else 1
    except (OSError, UnicodeError, ValueError) as exc:
        print(f"execution_chain {args.command}: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

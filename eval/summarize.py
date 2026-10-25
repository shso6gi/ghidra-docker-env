# -*- coding: utf-8 -*-
"""評価 wrapper の読み取り専用の集計（評価計画 v2 PR-D）。

評価の完了・正式性の判定を、ここでは**作らない**。呼ぶだけにする:

* 実行の連鎖の完全性: ``reporting.execution_chain.verify_execution_chain``
* tree の完全性: ``reporting.outcome_transition.tree_completeness``
* 正式な full verdict: ``reporting.verification_ledger.build_row`` +
  ``full_scope_evidence``（ledger の条件はそのまま。ledger file には書かない）
* gate: ``soundness_gate.build_gate_report``（メモリ上）と、runner が書いた
  ``benchmark_validation_gate.json``（読み戻すだけ）
* 時間: ``pair_runtime_receipt.load_chain_measurements``

この module が自分で持つのは、wrapper が記録した条件（fingerprint）と tree の開始の記録の
照合、中断の記録（container の終了・cgroup の ``oom_kill``・未終端の pair）の突き合わせ、
表示だけ。出力先にも wrapper の dir にも書かない（呼び出し側は read-only の mount で動かす）。

使い方（container の中、repo を ``--repo`` に置く）::

    python3 -B eval/summarize.py preflight --repo R --out OUT
    python3 -B eval/summarize.py launch-evidence --repo R --out OUT
    python3 -B eval/summarize.py report --repo R --out OUT --wrapper W --matrix neq [--json]

``report`` の終了コード: 0 = 評価が完了（下の COMPLETE）、1 = 未完了、2 = 判定できない。
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import sys
import time
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

SUMMARY_SCHEMA = "eval-summary-v1"
PREFLIGHT_SCHEMA = "eval-preflight-v1"
LAUNCH_EVIDENCE_SCHEMA = "eval-launch-evidence-v1"

VERDICT_COMPLETE = "COMPLETE"
VERDICT_INCOMPLETE = "INCOMPLETE"
VERDICT_UNVERIFIABLE = "UNVERIFIABLE"
EXIT_BY_VERDICT = {VERDICT_COMPLETE: 0, VERDICT_INCOMPLETE: 1, VERDICT_UNVERIFIABLE: 2}

REQUESTED_SCOPE_BY_MATRIX = {"neq": "full_neq", "eq": "full_eq"}

# Neq-Core の集計の定義（EvalPrep 計画 v2 §7.4「Neq-Core は集計時に UnchLoop の foo を除いて
# 作る」）。解析にも判定にも使わない、表示の view だけの定義。(sample identity の接頭辞, 関数名)。
NEQ_CORE_EXCLUDED = (("CLEVER/UnchLoop/Neq/", "foo"),)

# 中断の突き合わせで、pair の終了時刻と cgroup の観測の間に許す遅れ（秒）。wrapper の
# 観測間隔（10 秒）より長くする。
OOM_MATCH_SLACK_SECONDS = 15.0

INCOMPLETE_STATUS = "INCOMPLETE"
RUNNING_STATE = "RUNNING"


# ---------------------------------------------------------------------------
# 小さな読み取り
# ---------------------------------------------------------------------------


def _read_json(path: Path) -> Optional[Any]:
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, UnicodeError, ValueError):
        return None


def _read_jsonl(path: Path) -> Tuple[List[Mapping[str, Any]], int]:
    """行ごとの JSON object と、読めなかった行の数（読めない行は黙って捨てない）。"""
    rows: List[Mapping[str, Any]] = []
    bad = 0
    try:
        text = Path(path).read_text(encoding="utf-8")
    except FileNotFoundError:
        return rows, 0
    except (OSError, UnicodeError):
        return rows, 1
    for line in text.splitlines():
        if not line.strip():
            continue
        try:
            value = json.loads(line)
        except ValueError:
            bad += 1
            continue
        if isinstance(value, dict):
            rows.append(value)
        else:
            bad += 1
    return rows, bad


def start_record_fingerprints(out: Path) -> Dict[str, Optional[str]]:
    """確定した開始の記録ごとの ``environment_fingerprint``（execution_chain の reader で読む）。"""
    from scripts.function_tracer_pcode.reporting import execution_chain

    chain = execution_chain.read_chain_records(out)
    values: Dict[str, Optional[str]] = {}
    for run_id, records in sorted(chain.executions.items()):
        if not records.started:
            continue
        try:
            fields = execution_chain._parse_key_values(records.start_text)
        except ValueError:
            values[run_id] = None
            continue
        values[run_id] = fields.get("environment_fingerprint")
    return values


def _verify(out: Path) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    from scripts.function_tracer_pcode.reporting.execution_chain import verify_execution_chain

    try:
        return verify_execution_chain(out), None
    except Exception as exc:  # noqa: BLE001 - 判定できないことを結果として返す
        return None, f"{type(exc).__name__}: {exc}"


# ---------------------------------------------------------------------------
# preflight（start の前）
# ---------------------------------------------------------------------------


def preflight(repo: Path, out: Path) -> Dict[str, Any]:
    """start の判断に要る事実だけ: 検証器の判定、開始の記録の fingerprint、今の source digest。"""
    from scripts.function_tracer_pcode.reporting.execution_identity import source_tree_digest

    report: Dict[str, Any] = {"schema": PREFLIGHT_SCHEMA, "output": str(out)}
    report["output_exists"] = out.exists()
    report["output_entries"] = sorted(p.name for p in out.iterdir()) if out.is_dir() else []
    report["current_source_digest"] = source_tree_digest(repo)
    if not out.is_dir():
        report["verify"], report["verify_error"] = None, None
        report["start_fingerprints"] = {}
        report["start_source_digests"] = {}
        return report
    started = time.monotonic()
    report["verify"], report["verify_error"] = _verify(out)
    report["verify_seconds"] = round(time.monotonic() - started, 1)
    try:
        report["start_fingerprints"] = start_record_fingerprints(out)
        report["start_source_digests"] = _start_values(out, "analysis_source_digest_start")
    except OSError as exc:
        report["start_fingerprints"] = None
        report["start_records_error"] = str(exc)
    return report


def _start_values(out: Path, key: str) -> Dict[str, Optional[str]]:
    from scripts.function_tracer_pcode.reporting import execution_chain

    chain = execution_chain.read_chain_records(out)
    values: Dict[str, Optional[str]] = {}
    for run_id, records in sorted(chain.executions.items()):
        if records.started:
            try:
                values[run_id] = execution_chain._parse_key_values(records.start_text).get(key)
            except ValueError:
                values[run_id] = None
    return values


# ---------------------------------------------------------------------------
# launch の証拠（container の終了の直後、次の再開が pair の診断を消す前に写す）
# ---------------------------------------------------------------------------


def unterminated_pairs(out: Path) -> List[Dict[str, Any]]:
    """runner が記録した、終端していない pair（次の execution の境界で消える記録）。

    * ``concluded_incomplete``: runner が INCOMPLETE と結論した pair（child の外部 kill など）。
      runtime receipt の ``status`` と ``child_returncode`` は runner が書いた値（PR-A）。
    * ``interrupted_running``: progress が ``RUNNING`` のまま（execution ごと止まった／kill された）。

    ここは列挙だけで、確定かどうかは判定しない（確定は署名済み status と検証器）。
    """
    rows: List[Dict[str, Any]] = []
    if not out.is_dir():
        return rows
    for path in sorted(out.rglob("*.progress.json")):
        if path.parent.name != ".runtime-metrics":
            continue
        stem = path.name[: -len(".progress.json")]
        progress = _read_json(path)
        runtime = _read_json(path.with_name(stem + ".runtime.json"))
        receipt = runtime if isinstance(runtime, dict) else progress
        if not isinstance(receipt, dict):
            rows.append({"pair": _pair_relative(out, path, stem), "kind": "unreadable_receipt"})
            continue
        if receipt.get("status") == INCOMPLETE_STATUS:
            kind = "concluded_incomplete"
        elif receipt.get("state") == RUNNING_STATE:
            kind = "interrupted_running"
        else:
            continue
        sidecar = _read_json(path.with_name(stem + ".classification-failure.json"))
        rows.append({
            "pair": _pair_relative(out, path, stem),
            "kind": kind,
            "run_id": receipt.get("run_id"),
            "execution_nonce": receipt.get("execution_nonce"),
            "child_returncode": receipt.get("child_returncode"),
            "error_kind": receipt.get("error_kind"),
            "started_at_epoch": receipt.get("started_at_epoch"),
            "finished_at_epoch": receipt.get("finished_at_epoch"),
            "classification_failure": sidecar if isinstance(sidecar, dict) else None,
        })
    return rows


def _pair_relative(out: Path, receipt_path: Path, stem: str) -> str:
    return (receipt_path.parent.parent / (stem + ".pair-status.json")).relative_to(out).as_posix()


def launch_evidence(out: Path) -> Dict[str, Any]:
    started = time.monotonic()
    verify, error = _verify(out) if out.is_dir() else (None, "output directory does not exist")
    return {
        "schema": LAUNCH_EVIDENCE_SCHEMA,
        "captured_at_epoch": time.time(),
        "unterminated_pairs": unterminated_pairs(out),
        "verify": _verify_view(verify),
        "verify_error": error,
        "seconds": round(time.monotonic() - started, 1),
    }


def _verify_view(report: Optional[Mapping[str, Any]]) -> Optional[Dict[str, Any]]:
    if report is None:
        return None
    keys = ("verdict", "reasons", "latest_run_id", "run_scope", "executions", "pairs_expected",
            "pairs_executed_by_latest", "pairs_reused", "pairs_reused_proven",
            "never_started_executions", "uncommitted_debris")
    return {key: report.get(key) for key in keys}


# ---------------------------------------------------------------------------
# report（summary）
# ---------------------------------------------------------------------------


def _isa_of(binary_path: Any) -> str:
    """binary の file 名 ``<variant>-<arch>-<compiler>-<opt>`` の arch（runner の命名）。"""
    if not isinstance(binary_path, str):
        return "unknown"
    parts = Path(binary_path).name.split("-")
    return parts[-3] if len(parts) >= 4 else "unknown"


def _neq_core_excluded(sample: str, function: str) -> bool:
    return any(sample.startswith(prefix) and function == name
               for prefix, name in NEQ_CORE_EXCLUDED)


def observed_statuses(out: Path) -> Dict[str, int]:
    """status file の観測（署名は検証しない。確定の判定は検証器だけが行う）。"""
    from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
        pair_status_operational_diagnostic,
    )

    counts: Counter = Counter()
    logs_with_status = 0
    for path in out.rglob("*.pair-status.json"):
        payload = _read_json(path)
        if not isinstance(payload, dict):
            counts["unreadable"] += 1
        elif pair_status_operational_diagnostic(payload) is not None:
            counts["operational_diagnostic"] += 1
        elif isinstance(payload.get("canonical_outcome"), str):
            counts["with_outcome"] += 1
        else:
            counts["without_outcome"] += 1
        if path.with_name(path.name[: -len(".pair-status.json")] + ".log").is_file():
            logs_with_status += 1
    logs = sum(1 for path in out.rglob("*.log")
               if path.parent.name not in (".runtime-metrics",)
               and not path.name.startswith(("compile_", "run_stdout"))
               and path.parent != out)
    counts["logs_without_status"] = max(logs - logs_with_status, 0)
    counts["status_files"] = sum(counts[k] for k in (
        "unreadable", "operational_diagnostic", "with_outcome", "without_outcome"))
    return dict(counts)


def raw_aggregate(out: Path, matrix: str, soundness: Any) -> Dict[str, Any]:
    """生の全件集計（canonical outcome を status から数える。CLOSED のときだけ確定値）。"""
    from scripts.function_tracer_pcode.authority.decision.pair_status_authority import (
        error_kind_is_environment_dependent,
    )
    from scripts.function_tracer_pcode.reporting.outcome_transition import (
        correctness_axis,
        load_ground_truth,
    )
    from scripts.function_tracer_pcode.reporting.pair_outcomes import iter_pair_outcomes

    manifest, ground_truth = load_ground_truth(out)
    outcomes: Counter = Counter()
    core: Counter = Counter()
    by_isa: Dict[str, Counter] = {}
    errors: Counter = Counter()
    environment_errors: Counter = Counter()
    not_eq: Counter = Counter()
    functions = set()
    core_functions = set()
    for record in iter_pair_outcomes(out):
        outcomes[record.outcome] += 1
        functions.add((record.sample_identity, record.function_name))
        if matrix == "neq" and not _neq_core_excluded(record.sample_identity, record.function_name):
            core[record.outcome] += 1
            core_functions.add((record.sample_identity, record.function_name))
        payload = _read_json(Path(record.status_path)) or {}
        target = payload.get("pair_execution_target") if isinstance(payload, dict) else None
        target = target if isinstance(target, dict) else {}
        left, right = _isa_of(target.get("left_binary_path")), _isa_of(target.get("right_binary_path"))
        isa = left if left == right else f"{left}x{right}"
        by_isa.setdefault(isa, Counter())[record.outcome] += 1
        if record.outcome == "ERROR":
            kind = payload.get("error_kind") if isinstance(payload, dict) else None
            kind = str(kind) if kind is not None else "<none>"
            errors[kind] += 1
            if error_kind_is_environment_dependent(None if kind == "<none>" else kind):
                environment_errors[kind] += 1
        if record.outcome == "NOT_EQ":
            not_eq[correctness_axis(record, manifest)] += 1
    fast_path_eq = None
    if soundness is not None:
        fast_path_eq = sum(
            1 for row in soundness.accumulator.identical_rows
            if isinstance(row.get("disposition"), dict)
            and row["disposition"].get("applied") is True
            and row.get("outcome") == "EQUIVALENT"
        )
    view: Dict[str, Any] = {
        "pairs": sum(outcomes.values()),
        "functions": len(functions),
        "outcomes": dict(sorted(outcomes.items())),
        "identical_fast_path_eq": fast_path_eq,
        "error_by_kind": dict(sorted(errors.items())),
        "environment_dependent_error_by_kind": dict(sorted(environment_errors.items())),
        "by_isa": {isa: dict(sorted(counts.items())) for isa, counts in sorted(by_isa.items())},
        "not_eq_by_ground_truth": dict(sorted(not_eq.items())),
        "ground_truth": ground_truth,
    }
    if matrix == "neq":
        view["neq_core"] = {
            "excluded": [f"{prefix}* {name}" for prefix, name in NEQ_CORE_EXCLUDED],
            "pairs": sum(core.values()), "functions": len(core_functions),
            "outcomes": dict(sorted(core.items())),
        }
    return view


def _soundness(out: Path) -> Tuple[Optional[Any], Dict[str, Any]]:
    from scripts.function_tracer_pcode.reporting import soundness_gate

    try:
        report = soundness_gate.build_gate_report([out])
    except Exception as exc:  # noqa: BLE001 - 判定できないことを結果として表示する
        return None, {"status": "unavailable", "detail": f"{type(exc).__name__}: {exc}"}
    status = "EMPTY" if not report.records else ("PASS" if report.passed else "FAIL")
    acc = report.accumulator
    return report, {
        "status": status,
        "pairs": len(report.records),
        "violations": {
            "verified_ground_truth": len(acc.unconditional_verified_violations),
            "conditional": len(acc.conditional_verified_violations),
            "identical_same_function": len(acc.identical_soundness_violations),
            "fast_path": len(acc.fast_path_violations),
            "config_integrity": len(acc.config_integrity_violations),
        },
    }


def _benchmark_gate(out: Path) -> Dict[str, Any]:
    payload = _read_json(out / "benchmark_validation_gate.json")
    if not isinstance(payload, dict):
        return {"status": "unknown", "detail": "no readable benchmark_validation_gate.json"}
    return {
        "status": payload.get("gate", "unknown"),
        "pairs": payload.get("pairs"),
        "hard_violations": sum((payload.get("hard_violations") or {}).values()),
        "suspicious": sum((payload.get("suspicious") or {}).values()),
        "note": "written by the runner at the end of the latest sealed execution",
    }


def _identity_audit(out: Path) -> Dict[str, Any]:
    from scripts.function_tracer_pcode.reporting.execution_receipt import (
        audit_matrix_pair_identity,
    )

    try:
        audit = audit_matrix_pair_identity(out)
    except Exception as exc:  # noqa: BLE001
        return {"status": "unavailable", "detail": f"{type(exc).__name__}: {exc}"}
    view: Dict[str, Any] = {"status": "PASS" if audit.get("passed") else "FAIL"}
    for key, value in audit.items():
        if key in ("passed", "matrix_root"):
            continue
        view[key] = len(value) if isinstance(value, list) else value
    return view


def _formal(out: Path, matrix: str, repo: Path) -> Dict[str, Any]:
    from scripts.function_tracer_pcode.reporting import verification_ledger as ledger
    from scripts.function_tracer_pcode.reporting.execution_identity import git_state

    requested = REQUESTED_SCOPE_BY_MATRIX[matrix]
    try:
        row = ledger.build_row(out, requested_scope=requested)
    except Exception as exc:  # noqa: BLE001
        return {"full_verdict": None, "reason": f"ledger row: {type(exc).__name__}: {exc}"}
    scope, reason = ledger.full_scope_evidence(row)
    head, head_detail = ledger.head_match(row, git_state(repo))
    return {
        "requested_scope": requested,
        "full_verdict": scope,
        "reason": reason,
        "completed_scope": row.get("completed_scope"),
        "completed_scope_detail": row.get("completed_scope_detail"),
        "code_matches_head": head,
        "code_matches_head_detail": head_detail,
    }


def _launches(wrapper: Path) -> Tuple[List[Dict[str, Any]], List[str]]:
    """wrapper の launch ごとの記録と、欠けている記録（欠損は黙って捨てない）。"""
    launches: List[Dict[str, Any]] = []
    gaps: List[str] = []
    root = wrapper / "launches"
    if not root.is_dir():
        return launches, gaps
    for directory in sorted(root.iterdir(), key=lambda p: (len(p.name), p.name)):
        if not directory.is_dir() or not directory.name.isdigit():
            continue
        entry: Dict[str, Any] = {"launch": int(directory.name)}
        entry["launch_record"] = _read_json(directory / "launch.json")
        for name in ("exit.json", "evidence.json"):
            entry[name.split(".")[0]] = _read_json(directory / name)
        watch, bad = _read_jsonl(directory / "watch.jsonl")
        entry["watch"] = watch
        if bad:
            gaps.append(f"launch {directory.name}: {bad} unreadable watch line(s)")
        if entry["exit"] is None:
            gaps.append(f"launch {directory.name}: no container exit record")
        elif entry["exit"].get("container_started") is False:
            # 起動前に失敗した launch: container も pair も無いので、終了後の証拠は要らない。
            pass
        else:
            if entry["evidence"] is None:
                gaps.append(f"launch {directory.name}: no post-run evidence")
            if not (directory / "runner.log").is_file():
                gaps.append(f"launch {directory.name}: no runner log")
        launches.append(entry)
    return launches, gaps


def _launch_view(entry: Mapping[str, Any]) -> Dict[str, Any]:
    exit_record = entry.get("exit") or {}
    samples = list(entry.get("watch") or [])
    if isinstance(exit_record.get("last_cgroup_sample"), dict):
        samples.append(exit_record["last_cgroup_sample"])
    peaks = [s.get("memory_peak") for s in samples if isinstance(s.get("memory_peak"), int)]
    return {
        "launch": entry.get("launch"),
        "kind": (entry.get("launch_record") or {}).get("kind"),
        "exit_code": exit_record.get("exit_code"),
        "runner_exit_meaning": exit_record.get("runner_exit_meaning"),
        "oom_killed": exit_record.get("oom_killed"),
        "started_at": exit_record.get("started_at"),
        "finished_at": exit_record.get("finished_at"),
        "runtime_run_ids": exit_record.get("runtime_run_ids"),
        "watch_samples": len(entry.get("watch") or []),
        "memory_peak_bytes": max(peaks, default=None),
        "evidence_saved": entry.get("evidence") is not None,
    }


def _oom_windows(watch: Sequence[Mapping[str, Any]]) -> List[Tuple[float, float, int]]:
    """``oom_kill`` が増えた観測の区間 (前回の観測, 今回の観測, 増分)。"""
    windows = []
    previous_at: Optional[float] = None
    for row in watch:
        at = row.get("at_epoch")
        if not isinstance(at, (int, float)):
            continue
        delta = row.get("oom_kill_delta")
        if isinstance(delta, int) and delta > 0:
            windows.append((previous_at if previous_at is not None else at, at, delta))
        previous_at = at
    return windows


def interruptions(launches: Sequence[Mapping[str, Any]]) -> Dict[str, Any]:
    """中断の記録の突き合わせ。SIGKILL だけから OOM と断定しない（計画 §10-3）。

    * ``external_kill``: child が SIGKILL（rc -9）で終わり、runner が未完了とした pair。
    * ``possible_oom``: そのうち、同じ launch の cgroup の ``oom_kill`` が、その pair の実行区間に
      増えていたもの（あるいは container 自体が OOMKilled のもの）。それ以外は OOM と書かない。
    """
    rows = []
    totals: Counter = Counter()
    for entry in launches:
        exit_record = entry.get("exit") or {}
        evidence = entry.get("evidence") or {}
        windows = _oom_windows(entry.get("watch") or [])
        container_oom = exit_record.get("oom_killed") is True
        oom_total = sum(delta for _a, _b, delta in windows)
        totals["oom_kill_events"] += oom_total
        for pair in evidence.get("unterminated_pairs") or []:
            rc = pair.get("child_returncode")
            start = pair.get("started_at_epoch")
            end = pair.get("finished_at_epoch")
            if not isinstance(end, (int, float)):
                end = exit_record.get("finished_at_epoch")
            overlap = any(
                isinstance(start, (int, float)) and isinstance(end, (int, float))
                and lo <= end + OOM_MATCH_SLACK_SECONDS and hi >= start
                for lo, hi, _delta in windows
            )
            if pair.get("kind") == "concluded_incomplete" and rc == -9:
                cause = "external_kill"
            elif pair.get("kind") == "concluded_incomplete":
                cause = "incomplete_other"
            else:
                cause = "execution_stopped"
            possible_oom = container_oom or (cause == "external_kill" and overlap)
            totals[cause] += 1
            if possible_oom:
                totals["possible_oom"] += 1
            rows.append({
                "launch": entry.get("launch"), "pair": pair.get("pair"), "cause": cause,
                "child_returncode": rc, "possible_oom": possible_oom,
                "run_id": pair.get("run_id"),
            })
    return {"totals": dict(sorted(totals.items())), "pairs": rows}


def _container_state(wrapper: Path) -> Optional[Dict[str, Any]]:
    """host 側の wrapper が渡した container と lock の状態（無ければ None）。"""
    import os

    text = os.environ.get("EVAL_HOST_STATE")
    if not text:
        return None
    try:
        value = json.loads(text)
    except ValueError:
        return None
    return value if isinstance(value, dict) else None


def report(repo: Path, out: Path, wrapper: Path, matrix: str) -> Dict[str, Any]:
    reasons: List[str] = []
    unverifiable: List[str] = []
    meta = _read_json(wrapper / "meta.json")
    fingerprint = meta.get("fingerprint") if isinstance(meta, dict) else None
    if fingerprint is None:
        unverifiable.append("wrapper meta.json is missing or unreadable")
    result: Dict[str, Any] = {
        "schema": SUMMARY_SCHEMA, "matrix": matrix, "output": str(out), "wrapper": str(wrapper),
        "fingerprint": fingerprint,
        "freeze_commit": (meta or {}).get("conditions", {}).get("freeze_commit")
        if isinstance(meta, dict) else None,
        "host_state": _container_state(wrapper),
    }
    if not out.is_dir():
        result.update({"verdict": VERDICT_INCOMPLETE if not unverifiable else VERDICT_UNVERIFIABLE,
                       "verdict_reasons": unverifiable or ["the output directory does not exist yet"]})
        return result

    timings: Dict[str, float] = {}

    def timed(name, call, fallback=None):
        """1 つの読み取り。失敗は判定できない理由として残し、成功に数えない。"""
        started = time.monotonic()
        try:
            return call()
        except Exception as exc:  # noqa: BLE001 - 読めないことを結果として表示する
            unverifiable.append(f"{name} failed: {type(exc).__name__}: {exc}")
            return fallback
        finally:
            timings[name] = round(time.monotonic() - started, 1)

    from scripts.function_tracer_pcode.reporting.outcome_transition import tree_completeness
    from scripts.function_tracer_pcode.reporting.pair_runtime_receipt import load_chain_measurements

    verify, verify_error = timed("execution_chain_verify", lambda: _verify(out), (None, None))
    if verify is None and verify_error:
        unverifiable.append(f"execution_chain verify failed: {verify_error}")
    completeness = timed("tree_completeness", lambda: tree_completeness(out).as_dict(), {})
    fingerprints = timed("start_records", lambda: start_record_fingerprints(out), {})
    foreign = sorted(run_id for run_id, value in fingerprints.items() if value != fingerprint)
    soundness_report, soundness = timed("soundness_gate", lambda: _soundness(out), (None, {}))
    if soundness.get("status") == "unavailable":
        unverifiable.append(f"soundness gate failed: {soundness.get('detail')}")
    result["census"] = {
        "execution_chain": _verify_view(verify),
        "tree_completeness": completeness,
        "observed_statuses": timed("observed_statuses", lambda: observed_statuses(out), {}),
        "note": "decided = attributed by the execution chain verifier; observed counts are not verified",
    }
    audit = timed("identity_audit", lambda: _identity_audit(out), {})
    if audit.get("status") == "unavailable" and (verify or {}).get("verdict") == "CLOSED_SAME_IDENTITY":
        # 検証器が受理した tree を audit が読めないのは食い違い（未完了の tree では当然読めない）。
        unverifiable.append(f"identity audit failed on a CLOSED tree: {audit.get('detail')}")
    result["gates"] = {
        "execution_chain": {"verdict": (verify or {}).get("verdict"),
                            "reasons": (verify or {}).get("reasons"), "error": verify_error},
        "identity_audit": audit,
        "soundness": soundness,
        "benchmark": _benchmark_gate(out),
        "start_record_fingerprints": {
            "executions": len(fingerprints), "differing_from_wrapper": foreign,
        },
    }
    result["formal"] = timed("ledger", lambda: _formal(out, matrix, repo), {})
    if result["formal"].get("full_verdict") is None and str(
            result["formal"].get("reason", "")).startswith("ledger row:"):
        unverifiable.append(result["formal"]["reason"])
    result["raw"] = timed("raw_aggregate",
                          lambda: raw_aggregate(out, matrix, soundness_report), {})
    result["time"] = timed("chain_coverage", lambda: load_chain_measurements(out).as_dict(), {})
    result["time"]["note"] = (
        "each pair is timed by the execution that produced it; executions may have run "
        "under different host load; missing measurements are counted, never 0")
    launches, gaps = timed("wrapper_records", lambda: _launches(wrapper), ([], []))
    result["interruptions"] = timed("interruptions", lambda: interruptions(launches),
                                    {"totals": {}, "pairs": []})
    result["launches"] = [_launch_view(entry) for entry in launches]
    result["wrapper_record_gaps"] = gaps
    result["timings_seconds"] = timings

    # 完了の判定は、検証器・完全性・ledger の結論を並べるだけ（自分の規則を足さない）。
    if verify is not None and verify.get("verdict") != "CLOSED_SAME_IDENTITY":
        reasons.append("execution chain is OPEN: " + ", ".join(verify.get("reasons") or {}))
    if foreign:
        reasons.append(f"{len(foreign)} execution(s) did not run under this wrapper's conditions")
    formal = result["formal"]
    if formal.get("full_verdict") != REQUESTED_SCOPE_BY_MATRIX[matrix]:
        reasons.append(f"no full verdict: {formal.get('reason')}")
    if formal.get("code_matches_head") != "yes":
        reasons.append(f"not evidence about the code at HEAD: {formal.get('code_matches_head_detail')}")
    host = result["host_state"] or {}
    if host.get("container") not in (None, "absent"):
        reasons.append(f"an evaluation container is {host.get('container')}")
    if gaps:
        reasons.append("wrapper records have gaps: " + "; ".join(gaps))
    if unverifiable:
        result["verdict"] = VERDICT_UNVERIFIABLE
        result["verdict_reasons"] = unverifiable + reasons
    else:
        result["verdict"] = VERDICT_INCOMPLETE if reasons else VERDICT_COMPLETE
        result["verdict_reasons"] = reasons
    return result


# ---------------------------------------------------------------------------
# 表示
# ---------------------------------------------------------------------------


def _line(key: str, value: Any) -> str:
    if isinstance(value, (dict, list)):
        value = json.dumps(value, sort_keys=True, ensure_ascii=False)
    return f"  {key}: {value}"


def format_report(result: Mapping[str, Any]) -> str:
    lines = [f"Evaluation summary ({result.get('matrix')}): {result.get('output')}",
             _line("freeze_commit", result.get("freeze_commit")),
             _line("fingerprint", result.get("fingerprint")),
             _line("host_state", result.get("host_state"))]
    census = result.get("census")
    if census:
        chain = census.get("execution_chain") or {}
        lines += ["", "1. Census (are all pairs there?)",
                  _line("pairs_expected", chain.get("pairs_expected")),
                  _line("decided_by_execution", [
                      {"run_id": e.get("runtime_run_id"), "sealed": e.get("sealed"),
                       "decided": e.get("decided_pairs_attributed")}
                      for e in chain.get("executions") or []]),
                  _line("pairs_reused / proven", f"{chain.get('pairs_reused')} / {chain.get('pairs_reused_proven')}"),
                  _line("tree_completeness", f"{census['tree_completeness'].get('status')} "
                        f"({census['tree_completeness'].get('detail')}); missing "
                        f"{census['tree_completeness'].get('pairs_missing')}"),
                  _line("observed_statuses (unverified)", census.get("observed_statuses")),
                  _line("never_started_executions", chain.get("never_started_executions")),
                  _line("uncommitted_debris", chain.get("uncommitted_debris"))]
        gates = result["gates"]
        lines += ["", "2. Gates",
                  _line("execution_chain", f"{gates['execution_chain'].get('verdict')} "
                        f"{json.dumps(gates['execution_chain'].get('reasons') or {}, sort_keys=True)}"),
                  _line("identity_audit", gates.get("identity_audit")),
                  _line("soundness_gate", gates.get("soundness")),
                  _line("benchmark_validation_gate", gates.get("benchmark")),
                  _line("start_record_fingerprints", gates.get("start_record_fingerprints"))]
        formal = result["formal"]
        lines += ["", "3. Formal verdict (verification ledger)",
                  _line("full_verdict", formal.get("full_verdict") or "NO"),
                  _line("reason", formal.get("reason") or "-"),
                  _line("completed_scope", f"{formal.get('completed_scope')} ({formal.get('completed_scope_detail')})"),
                  _line("code_matches_head", f"{formal.get('code_matches_head')} ({formal.get('code_matches_head_detail')})")]
        raw = result["raw"]
        lines += ["", "4. Raw totals (canonical outcome of every pair status; final only when the chain is CLOSED)",
                  _line("pairs / functions", f"{raw.get('pairs')} / {raw.get('functions')}"),
                  _line("outcomes", raw.get("outcomes"))]
        if "neq_core" in raw:
            lines.append(_line("neq_core", raw["neq_core"]))
        lines += [_line("identical_fast_path_eq", raw.get("identical_fast_path_eq")),
                  _line("error_by_kind", raw.get("error_by_kind")),
                  _line("environment_dependent_error_by_kind", raw.get("environment_dependent_error_by_kind")),
                  _line("by_isa", raw.get("by_isa")),
                  "", "5. NOT_EQ by ground truth (consistent = confirmed; unconfirmed kept apart)",
                  _line("not_eq", raw.get("not_eq_by_ground_truth")),
                  _line("ground_truth", raw.get("ground_truth")),
                  "", "6. Time (chain coverage)", _line("coverage", result.get("time")),
                  "", "7. Interruptions and OOM",
                  _line("totals", result["interruptions"]["totals"])]
        for row in result["interruptions"]["pairs"][:50]:
            lines.append(_line("pair", row))
        if len(result["interruptions"]["pairs"]) > 50:
            lines.append(f"  ... {len(result['interruptions']['pairs']) - 50} more (see --json)")
        for launch in result.get("launches") or []:
            lines.append(_line("launch", launch))
        lines.append(_line("wrapper_record_gaps", result.get("wrapper_record_gaps")))
        lines.append(_line("timings_seconds", result.get("timings_seconds")))
    lines += ["", f"VERDICT: {result.get('verdict')}"]
    lines += [f"  - {reason}" for reason in result.get("verdict_reasons") or []]
    return "\n".join(lines) + "\n"


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("preflight", "launch-evidence", "report"):
        command = sub.add_parser(name)
        command.add_argument("--repo", required=True, type=Path)
        command.add_argument("--out", required=True, type=Path)
        if name == "report":
            command.add_argument("--wrapper", required=True, type=Path)
            command.add_argument("--matrix", required=True, choices=sorted(REQUESTED_SCOPE_BY_MATRIX))
            command.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    sys.path.insert(0, str(args.repo))
    if args.command == "preflight":
        print(json.dumps(preflight(args.repo, args.out), sort_keys=True))
        return 0
    if args.command == "launch-evidence":
        print(json.dumps(launch_evidence(args.out), sort_keys=True))
        return 0
    result = report(args.repo, args.out, args.wrapper, args.matrix)
    if args.json:
        print(json.dumps(result, indent=1, sort_keys=True, default=str))
    else:
        sys.stdout.write(format_report(result))
    return EXIT_BY_VERDICT[result["verdict"]]


if __name__ == "__main__":
    sys.exit(main())

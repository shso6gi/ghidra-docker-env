# -*- coding: utf-8 -*-
"""評価 wrapper の読み取り専用の判定と集計（評価計画 v2 PR-D）。

**完了の判定はこの module の ``completion`` 1 つだけ**。``summary``（``report``）と ``start``
の「完了済み」はどちらもこれを呼ぶ。条件はそれぞれの owner の判定を並べるだけで、自分の規則を
足さない:

======================  ===============================================================
条件                     owner
======================  ===============================================================
実行の連鎖              ``reporting.execution_chain.verify_execution_chain``（CLOSED）
正式な full verdict      ``verification_ledger.build_row`` + ``full_scope_evidence``
HEAD の一致              ``verification_ledger.head_match``
条件（fingerprint）      wrapper の ``meta.json`` と、各 execution の開始の記録
wrapper の記録           ``eval/records.py``（launch の状態機械・破損・execution との対応）
container の状態         host の wrapper が観測して ``EVAL_HOST_STATE`` で渡す
======================  ===============================================================

理由の code と分類（resumable / blocking / permanent / unverifiable）、``start`` の決定、
応答の形（このファイルが出す JSON の schema と終了コード）は ``eval/protocol.py`` が唯一の owner。
ここは登録表から分類を引き、契約どおりの応答を出すだけ。

中断の集計（``interruptions``）は、launch の証拠の写しを、その receipt の execution を記録した
launch に帰属させてから数える（``interruption_events``）。

使い方（container の中）::

    python3 -B eval/summarize.py completion|verify|launch-evidence|report \
        --repo R --out OUT --wrapper W --matrix neq|eq [--json]

``report`` の終了コード: 0 = 完了、1 = 未完了、2 = 判定できない（集計の欄が作れなかったときも 2。
``protocol.summary_exit_code``）。wrapper はこの終了コードと JSON の両方を照合して受理する。
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import sys
import time
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

if str(Path(__file__).resolve().parent) not in sys.path:
    sys.path.insert(0, str(Path(__file__).resolve().parent))
import records  # noqa: E402  (eval/ の記録の形式と検査)

import protocol  # noqa: E402  (応答の契約と理由の分類の唯一の置き場所)
from protocol import (  # noqa: E402
    BLOCKING, COMPLETION_SCHEMA, EXIT_BY_VERDICT, PERMANENT, RESUMABLE, SUMMARY_SCHEMA,
    UNVERIFIABLE, VERDICT_COMPLETE, VERDICT_INCOMPLETE, VERDICT_UNVERIFIABLE, VERIFY_SCHEMA,
)

LAUNCH_EVIDENCE_SCHEMA = protocol.EVIDENCE_SCHEMA

REQUESTED_SCOPE_BY_MATRIX = {"neq": "full_neq", "eq": "full_eq"}

# Neq-Core の集計の定義（EvalPrep 計画 v2 §7.4「Neq-Core は集計時に UnchLoop の foo を除いて
# 作る」）。解析にも判定にも使わない、表示の view だけの定義。(sample identity の接頭辞, 関数名)。
NEQ_CORE_EXCLUDED = (("CLEVER/UnchLoop/Neq/", "foo"),)

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


def start_record_fingerprints(out: Path) -> Dict[str, Optional[str]]:
    """確定した開始の記録ごとの ``environment_fingerprint``（execution_chain の reader で読む）。"""
    from scripts.function_tracer_pcode.reporting import execution_chain

    return _start_values(out, "environment_fingerprint")


def _verify(out: Path) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    from scripts.function_tracer_pcode.reporting.execution_chain import verify_execution_chain

    try:
        return verify_execution_chain(out), None
    except Exception as exc:  # noqa: BLE001 - 判定できないことを結果として返す
        return None, f"{type(exc).__name__}: {exc}"


def verify_report(out: Path) -> Dict[str, Any]:
    """``status --verify``: 検証器だけ（判定には使わない表示）。"""
    started = time.monotonic()
    verify, error = _verify(out) if out.is_dir() else (None, "the output does not exist")
    return {"schema": VERIFY_SCHEMA, "verify": _verify_view(verify), "verify_error": error,
            "verify_seconds": round(time.monotonic() - started, 1)}


def _start_values(out: Path, key: str) -> Dict[str, Optional[str]]:
    from scripts.function_tracer_pcode.reporting import execution_chain

    chain = execution_chain.read_chain_records(out)
    values: Dict[str, Optional[str]] = {}
    for run_id, entry in sorted(chain.executions.items()):
        if entry.started:
            try:
                values[run_id] = execution_chain._parse_key_values(entry.start_text).get(key)
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


def _launch_view(launch: records.Launch) -> Dict[str, Any]:
    exit_record = launch.exit or {}
    observed = [row for row in launch.watch if row.get("observed") is True]
    peaks = [row.get("memory_peak") for row in observed if type(row.get("memory_peak")) is int]
    return {
        "launch": launch.number,
        "state": launch.state,
        "kind": (launch.launch or {}).get("kind"),
        "exit_kind": exit_record.get("kind"),
        "exit_code": exit_record.get("exit_code"),
        "runner_exit_meaning": exit_record.get("runner_exit_meaning"),
        "oom_killed": exit_record.get("oom_killed"),
        "started_at": exit_record.get("started_at"),
        "finished_at": exit_record.get("finished_at"),
        "runtime_run_ids": exit_record.get("runtime_run_ids"),
        "observations": len(launch.watch),
        "observations_unobserved": len(launch.watch) - len(observed),
        "watch_unreadable_lines": launch.watch_unreadable_lines,
        "watch_write_failures": exit_record.get("watch_write_failures"),
        "memory_peak_bytes": max(peaks, default=None),
        "evidence_recorded": launch.evidence is not None,
    }


def interruption_events(launches: Sequence[records.Launch]) -> Dict[str, Any]:
    """launch の snapshot（``evidence.json``）から、中断の event を作る（集計の前の帰属）。

    snapshot は、その launch が終わった時点の出力先にある **すべての** 未終端の receipt の写しで、
    前の execution が残した receipt も含む。snapshot にあることは、その launch で起きたことを
    意味しない。そこで:

    * event の同一性は ``(execution の run_id, execution_nonce, pair)``。同じ pair でも、別の
      execution や nonce で再び止まったものは別の event（実際の再試行）。同じ組を複数の snapshot
      で見たものは 1 つの event の重複観測で、数えない（何回観測されたかは ``observed_in``）。
    * event は、その run_id を ``exit.json`` の ``runtime_run_ids`` に記録した launch に帰属させる。
      OOM の判定には、その launch の観測と ``OOMKilled`` だけを使う。
    * run_id が無い、またはどの launch も記録していない run_id の receipt は ``unattributed``
      として別に報告し、どの launch の現象にもしない。
    """
    owner: Dict[str, int] = {}
    for launch in launches:
        for run_id in (launch.exit or {}).get("runtime_run_ids") or []:
            owner[run_id] = launch.number
    events: Dict[Tuple[Any, Any, Any], Dict[str, Any]] = {}
    unattributed: Dict[Tuple[Any, Any, Any], Dict[str, Any]] = {}
    for launch in launches:
        for row in (launch.evidence or {}).get("unterminated_pairs") or []:
            key = (row.get("run_id"), row.get("execution_nonce"), row.get("pair"))
            launch_number = owner.get(row.get("run_id")) if isinstance(row.get("run_id"), str) else None
            target = events if launch_number is not None else unattributed
            event = target.setdefault(key, {**row, "launch": launch_number, "observed_in": []})
            event["observed_in"].append(launch.number)
    return {"events": list(events.values()), "unattributed": list(unattributed.values())}


def interruptions(launches: Sequence[records.Launch]) -> Dict[str, Any]:
    """中断の集計。帰属させた event だけを数え、SIGKILL だけから OOM と断定しない（計画 §10-3）。

    * ``external_kill``: child が SIGKILL（rc -9）で終わり、runner が未完了とした pair。
      ``possible_oom`` は ``records.oom_attribution`` に **その event の launch** の観測と
      ``OOMKilled`` を渡して決める（yes / no / unobserved）。
    * ``execution_stopped`` / ``incomplete_other``: OOM の判定の対象外。その launch の container
      自体が OOMKilled のときだけ yes。
    * 帰属できない receipt は ``unattributed`` に数えるだけ（OOM を結び付けない）。
    """
    by_number = {launch.number: launch for launch in launches}
    model = interruption_events(launches)
    rows = []
    totals: Counter = Counter()
    for launch in launches:
        for interval in records.counter_intervals(launch.watch):
            if interval.delta:
                totals["oom_kill_increments"] += interval.delta
            elif interval.delta is None:
                totals["oom_kill_counter_resets"] += 1
    for event in model["events"]:
        launch = by_number[event["launch"]]
        exit_record = launch.exit or {}
        container_oom = exit_record.get("oom_killed")
        rc = event.get("child_returncode")
        if event.get("kind") == "concluded_incomplete" and rc == -9:
            cause = "external_kill"
        elif event.get("kind") == "concluded_incomplete":
            cause = "incomplete_other"
        else:
            cause = "execution_stopped"
        end = event.get("finished_at_epoch")
        if not isinstance(end, (int, float)):
            end = exit_record.get("finished_at_epoch")
        if cause == "external_kill":
            possible = records.oom_attribution(
                launch.watch, start=event.get("started_at_epoch"), end=end,
                container_oom_killed=container_oom)
        else:
            possible = records.OOM_YES if container_oom is True else "not_applicable"
        totals[cause] += 1
        totals[f"possible_oom_{possible}"] += 1
        if len(event["observed_in"]) > 1:
            totals["repeat_observations"] += len(event["observed_in"]) - 1
        rows.append({
            "launch": event["launch"], "pair": event.get("pair"), "cause": cause,
            "child_returncode": rc, "possible_oom": possible, "run_id": event.get("run_id"),
            "execution_nonce": event.get("execution_nonce"), "observed_in": event["observed_in"],
        })
    unattributed = [
        {"pair": row.get("pair"), "kind": row.get("kind"), "run_id": row.get("run_id"),
         "execution_nonce": row.get("execution_nonce"), "observed_in": row["observed_in"]}
        for row in model["unattributed"]
    ]
    totals["unattributed"] = len(unattributed)
    return {"totals": dict(sorted(totals.items())), "pairs": rows, "unattributed": unattributed}


def _host_state() -> Optional[Dict[str, Any]]:
    """host の wrapper が渡した container と lock の観測（渡されなければ None = 未観測）。"""
    import os

    text = os.environ.get("EVAL_HOST_STATE")
    if not text:
        return None
    try:
        value = json.loads(text)
    except ValueError:
        return None
    return value if isinstance(value, dict) else None


def completion(repo: Path, out: Path, wrapper: Path, matrix: str) -> Dict[str, Any]:
    """評価が完了したか、再開してよいか（``summary`` と ``start`` が共有する唯一の判定）。

    返り値の ``verdict`` は COMPLETE / INCOMPLETE / UNVERIFIABLE、``reasons`` は
    ``{code, category, detail}`` の列（分類は ``protocol.REASONS``）。``checks`` には
    ``protocol.MANDATORY_CHECKS`` のすべてを、実施した（``done``）か、出力の状態から該当しない
    （``not_applicable`` と理由）かで必ず書く。初回・出力が無い・空・開始の記録の前に止まった
    出力（``output_state``）でも、wrapper の記録・恒久的な失敗・回収の状態・execution との対応の
    検査は省かない。各条件の判定は owner の結果を読むだけで、条件を足しも緩めもしない。
    """
    from scripts.function_tracer_pcode.reporting.execution_identity import source_tree_digest

    reasons: List[Dict[str, str]] = []
    checks: Dict[str, Dict[str, str]] = {}

    def reason(code: str, detail: str) -> None:
        # 分類は登録表（protocol.REASONS）だけが決める。
        reasons.append({"code": code, "category": protocol.REASONS[code], "detail": detail})

    def done(name: str) -> None:
        checks[name] = {"status": protocol.CHECK_DONE}

    def not_applicable(name: str, because: str) -> None:
        checks[name] = {"status": protocol.CHECK_NOT_APPLICABLE, "because": because}

    result: Dict[str, Any] = {"schema": COMPLETION_SCHEMA, "matrix": matrix,
                              "output": str(out), "wrapper": str(wrapper), "checks": checks}
    # 出力の分類は records.classify_output（execution_chain.read_chain_records の分類）だけ。
    # 「開始前」は owner が書きかけの残骸だけと言えたときだけで、確定した証跡の欠損・破損・
    # 未知の entry は damaged（退避しない・再開しない）。
    output = records.classify_output(out)
    state = output.state
    result["output_state"] = state
    result["output_class"] = {"started": output.started, "damage": output.damage,
                              "evidence": output.evidence[:20], "debris": output.debris[:20]}
    for problem in output.damage:
        reason("output_damaged", problem)
    done("output")

    # meta（評価の条件）。「無い」「正常」「破損」は records.read_meta だけが決め、破損を
    # 初回や「条件なし」に落とさない（この出力先の meta であることも read_meta が確かめる）。
    meta = records.read_meta(wrapper, matrix=matrix)
    result["meta_state"] = meta.state
    result["meta_problems"] = meta.problems
    fingerprint = meta.fingerprint if meta.state == records.META_VALID else None
    result["fingerprint"] = fingerprint
    result["freeze_commit"] = meta.conditions["freeze_commit"] if fingerprint else None
    if meta.state == records.META_ABSENT:
        if state in (protocol.OUTPUT_ABSENT, protocol.OUTPUT_EMPTY):
            reason("evaluation_not_started", "no wrapper records and no output yet")
        else:
            reason("output_without_records",
                   f"the output holds entries ({state}) but this wrapper never recorded starting it")
    elif meta.state == records.META_DAMAGED:
        reason("meta_invalid", "; ".join(meta.problems))
    done("meta")

    host = _host_state()
    result["host_state"] = host
    if host is None or host.get("observed") is not True:
        reason("container_unobserved", "the evaluation container's state was not observed")
    elif host.get("container") != "absent":
        reason("container_present", f"an evaluation container is {host.get('container')}")
    done("container")

    # wrapper の記録（破損・回収の状態）と、恒久的な失敗。出力の状態によらず必ず読む。
    check = records.read_records(wrapper)
    result["records"] = {"launches": [_launch_view(launch) for launch in check.launches],
                         "problems": check.problems, "debris": check.debris,
                         "unfinished": None if check.unfinished is None else {
                             "launch": check.unfinished.number,
                             "state": check.unfinished.state}}
    for problem in check.problems:
        reason("records_damaged", problem)
    if check.unfinished is not None:
        reason("unfinished_launch", f"launch {check.unfinished.number} is {check.unfinished.state}")
    done("records")
    for launch in check.launches:
        if launch.exit_kind == records.KIND_EXIT_UNOBSERVED:
            reason("exit_unobserved", f"launch {launch.number}: {launch.exit.get('reason')}")
    done("permanent")
    result["_check"] = check

    # 要求した条件・launch の記録・起動した container が同じ条件か（meta が valid でなければ
    # 照合の基準が無く、meta_invalid が判定できないことを報告する）。
    for problem in records.launch_condition_problems(check, fingerprint):
        reason("launch_conditions_differ", problem)
    done("conditions")

    # launch が記録した execution と、出力にある（開始の記録が確定した）execution の対応。
    # 出力が無い・開始前の出力でも、launch が execution を記録していれば食い違いとして残る。
    for problem in records.attribution_problems(check, output.started):
        reason("execution_attribution", problem)
    done("attribution")

    if state in (protocol.OUTPUT_STARTED, protocol.OUTPUT_DAMAGED):
        try:
            result["current_source_digest"] = source_tree_digest(repo)
        except Exception as exc:  # noqa: BLE001
            reason("source_digest_unreadable", f"{type(exc).__name__}: {exc}")
    else:
        why = f"the output is {state}: no execution started, nothing to verify"
        if state == protocol.OUTPUT_NEVER_STARTED:
            reason("output_never_started",
                   "the output holds only what an execution wrote before it recorded its start")
        else:
            reason("output_absent", f"the output is {state}")
        result["start_source_digests"] = {}
        for name in ("chain", "fingerprints", "source", "ledger"):
            not_applicable(name, why)
        return _verdict(result, reasons)

    verify, verify_error = _verify(out)
    result["_verify"] = verify
    result["verify"] = _verify_view(verify)
    if verify is None:
        reason("verify_failed", f"execution_chain verify failed: {verify_error}")
    elif verify.get("verdict") != "CLOSED_SAME_IDENTITY":
        reason("chain_open", "execution chain is OPEN: "
               + ", ".join(verify.get("reasons") or {}))
    done("chain")
    try:
        fingerprints = start_record_fingerprints(out)
        result["start_source_digests"] = _start_values(out, "analysis_source_digest_start")
    except Exception as exc:  # noqa: BLE001
        fingerprints = {}
        result["start_source_digests"] = {}
        reason("start_records_unreadable", f"{type(exc).__name__}: {exc}")
    foreign = sorted(run_id for run_id, value in fingerprints.items() if value != fingerprint)
    result["start_record_fingerprints"] = {"executions": len(fingerprints),
                                           "differing_from_wrapper": foreign}
    if foreign and fingerprint is not None:
        reason("foreign_execution", f"{len(foreign)} execution(s) did not run under "
               f"this evaluation's conditions: {', '.join(foreign[:3])}")
    done("fingerprints")
    digests = {value for value in result["start_source_digests"].values()}
    current = result.get("current_source_digest")
    if current is not None and digests and digests != {current}:
        reason("source_differs", "the output was started from another analysis source than "
               "this worktree")
    done("source")
    try:
        formal = _formal(out, matrix, repo)
    except Exception as exc:  # noqa: BLE001
        formal = {"full_verdict": None, "reason": f"ledger row: {type(exc).__name__}: {exc}"}
    result["formal"] = formal
    if str(formal.get("reason", "")).startswith("ledger row:"):
        reason("ledger_failed", formal["reason"])
    elif formal.get("full_verdict") != REQUESTED_SCOPE_BY_MATRIX[matrix]:
        reason("no_full_verdict", f"no full verdict: {formal.get('reason')}")
    if formal.get("code_matches_head") is not None and formal.get("code_matches_head") != "yes":
        reason("head_mismatch", "not evidence about the code at HEAD: "
               f"{formal.get('code_matches_head_detail')}")
    done("ledger")
    return _verdict(result, reasons)


def _verdict(result: Dict[str, Any], reasons: List[Dict[str, str]]) -> Dict[str, Any]:
    result["reasons"] = reasons
    result["verdict"] = protocol.verdict_of(item["category"] for item in reasons)
    return result


def public(result: Mapping[str, Any]) -> Dict[str, Any]:
    """JSON に出す部分（``_`` で始まる内部の値を除く）。"""
    return {key: value for key, value in result.items() if not key.startswith("_")}


def report(repo: Path, out: Path, wrapper: Path, matrix: str) -> Dict[str, Any]:
    """``completion`` の判定に、集計の欄を足す（欄の失敗は判定を変えず、別に報告する）。"""
    result = completion(repo, out, wrapper, matrix)
    result["schema"] = SUMMARY_SCHEMA
    result["report_errors"] = []
    timings: Dict[str, float] = {}

    def timed(name, call, fallback=None):
        started = time.monotonic()
        try:
            return call()
        except Exception as exc:  # noqa: BLE001 - 作れなかった欄として報告する
            result["report_errors"].append(f"{name}: {type(exc).__name__}: {exc}")
            return fallback
        finally:
            timings[name] = round(time.monotonic() - started, 1)

    check = result["_check"]
    result["interruptions"] = timed("interruptions", lambda: interruptions(check.launches),
                                    {"totals": {}, "pairs": []})
    if result.get("output_state") in (protocol.OUTPUT_STARTED, protocol.OUTPUT_DAMAGED):
        from scripts.function_tracer_pcode.reporting.outcome_transition import tree_completeness
        from scripts.function_tracer_pcode.reporting.pair_runtime_receipt import (
            load_chain_measurements,
        )

        soundness_report, soundness = timed("soundness_gate", lambda: _soundness(out), (None, {}))
        if soundness.get("status") == "unavailable":
            result["report_errors"].append(f"soundness gate: {soundness.get('detail')}")
        result["census"] = {
            "execution_chain": result.get("verify"),
            "tree_completeness": timed("tree_completeness",
                                       lambda: tree_completeness(out).as_dict(), {}),
            "observed_statuses": timed("observed_statuses", lambda: observed_statuses(out), {}),
            "note": "decided = attributed by the execution chain verifier; observed counts are "
                    "not verified",
        }
        result["gates"] = {
            "execution_chain": {"verdict": (result.get("verify") or {}).get("verdict"),
                                "reasons": (result.get("verify") or {}).get("reasons")},
            "identity_audit": timed("identity_audit", lambda: _identity_audit(out), {}),
            "soundness": soundness,
            "benchmark": _benchmark_gate(out),
        }
        result["raw"] = timed("raw_aggregate",
                              lambda: raw_aggregate(out, matrix, soundness_report), {})
        result["time"] = timed("chain_coverage",
                               lambda: load_chain_measurements(out).as_dict(), {})
        result["time"]["note"] = (
            "each pair is timed by the execution that produced it; executions may have run "
            "under different host load; missing measurements are counted, never 0")
    result["timings_seconds"] = timings
    return result


def exit_code(result: Mapping[str, Any]) -> int:
    return protocol.summary_exit_code(result)


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
        completeness = census.get("tree_completeness") or {}
        lines += ["", "1. Census (are all pairs there?)",
                  _line("pairs_expected", chain.get("pairs_expected")),
                  _line("decided_by_execution", [
                      {"run_id": e.get("runtime_run_id"), "sealed": e.get("sealed"),
                       "decided": e.get("decided_pairs_attributed")}
                      for e in chain.get("executions") or []]),
                  _line("pairs_reused / proven",
                        f"{chain.get('pairs_reused')} / {chain.get('pairs_reused_proven')}"),
                  _line("tree_completeness", f"{completeness.get('status')} "
                        f"({completeness.get('detail')}); missing {completeness.get('pairs_missing')}"),
                  _line("observed_statuses (unverified)", census.get("observed_statuses")),
                  _line("never_started_executions", chain.get("never_started_executions")),
                  _line("uncommitted_debris", chain.get("uncommitted_debris"))]
        gates = result.get("gates") or {}
        lines += ["", "2. Gates",
                  _line("execution_chain", f"{gates.get('execution_chain', {}).get('verdict')} "
                        f"{json.dumps(gates.get('execution_chain', {}).get('reasons') or {}, sort_keys=True)}"),
                  _line("identity_audit", gates.get("identity_audit")),
                  _line("soundness_gate", gates.get("soundness")),
                  _line("benchmark_validation_gate", gates.get("benchmark")),
                  _line("start_record_fingerprints", result.get("start_record_fingerprints"))]
        formal = result.get("formal") or {}
        lines += ["", "3. Formal verdict (verification ledger)",
                  _line("full_verdict", formal.get("full_verdict") or "NO"),
                  _line("reason", formal.get("reason") or "-"),
                  _line("completed_scope",
                        f"{formal.get('completed_scope')} ({formal.get('completed_scope_detail')})"),
                  _line("code_matches_head",
                        f"{formal.get('code_matches_head')} ({formal.get('code_matches_head_detail')})")]
        raw = result.get("raw") or {}
        lines += ["", "4. Raw totals (canonical outcome of every pair status; final only when "
                  "the chain is CLOSED)",
                  _line("pairs / functions", f"{raw.get('pairs')} / {raw.get('functions')}"),
                  _line("outcomes", raw.get("outcomes"))]
        if "neq_core" in raw:
            lines.append(_line("neq_core", raw["neq_core"]))
        lines += [_line("identical_fast_path_eq", raw.get("identical_fast_path_eq")),
                  _line("error_by_kind", raw.get("error_by_kind")),
                  _line("environment_dependent_error_by_kind",
                        raw.get("environment_dependent_error_by_kind")),
                  _line("by_isa", raw.get("by_isa")),
                  "", "5. NOT_EQ by ground truth (consistent = confirmed; unconfirmed kept apart)",
                  _line("not_eq", raw.get("not_eq_by_ground_truth")),
                  _line("ground_truth", raw.get("ground_truth")),
                  "", "6. Time (chain coverage)", _line("coverage", result.get("time"))]
    interrupted = result.get("interruptions") or {"totals": {}, "pairs": []}
    lines += ["", "7. Launches, interruptions and OOM", _line("totals", interrupted["totals"])]
    for row in interrupted["pairs"][:50]:
        lines.append(_line("pair", row))
    if len(interrupted["pairs"]) > 50:
        lines.append(f"  ... {len(interrupted['pairs']) - 50} more (see --json)")
    for row in (interrupted.get("unattributed") or [])[:20]:
        lines.append(_line("unattributed (not counted for any launch)", row))
    recorded = result.get("records") or {}
    for launch in recorded.get("launches") or []:
        lines.append(_line("launch", launch))
    lines.append(_line("record_problems", recorded.get("problems")))
    lines.append(_line("timings_seconds", result.get("timings_seconds")))
    for error in result.get("report_errors") or []:
        lines.append(f"  SUMMARY SECTION FAILED: {error}")
    lines += ["", f"VERDICT: {result.get('verdict')}"]
    lines += [f"  - [{item['category']}] {item['code']}: {item['detail']}"
              for item in result.get("reasons") or []]
    return "\n".join(lines) + "\n"


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("completion", "verify", "launch-evidence", "report"):
        command = sub.add_parser(name)
        command.add_argument("--repo", required=True, type=Path)
        command.add_argument("--out", required=True, type=Path)
        command.add_argument("--wrapper", required=True, type=Path)
        command.add_argument("--matrix", required=True, choices=sorted(REQUESTED_SCOPE_BY_MATRIX))
        command.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    sys.path.insert(0, str(args.repo))
    if args.command == "completion":
        print(json.dumps(public(completion(args.repo, args.out, args.wrapper, args.matrix)),
                         sort_keys=True, default=str))
        return 0
    if args.command == "verify":
        print(json.dumps(verify_report(args.out), sort_keys=True))
        return 0
    if args.command == "launch-evidence":
        print(json.dumps(launch_evidence(args.out), sort_keys=True))
        return 0
    result = report(args.repo, args.out, args.wrapper, args.matrix)
    if args.json:
        print(json.dumps(public(result), indent=1, sort_keys=True, default=str))
    else:
        sys.stdout.write(format_report(result))
    return exit_code(result)


if __name__ == "__main__":
    sys.exit(main())

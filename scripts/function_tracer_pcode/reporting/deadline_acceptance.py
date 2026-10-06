# -*- coding: utf-8 -*-
"""協調的 deadline の targeted pair の受理判定（Issue #106 PR-106-A、計画 v5 §7.E / E13）。

before（期限なし）と after（期限あり）の run を pair ごとに突き合わせ、targeted pair の
結果を **safety / fallback** と **observed improvement** の 2 軸で判定する。判定の規則は
`classify_target` の 1 箇所にだけあり、CLI も test も同じ関数を通る。

受理（accepted）の規則:

========== ==================================================================
Class A    期限の中で止まることを backend / path が保証する。accepted は ground truth と
           **整合が確認された** EQ / NOT_EQ、または reason 付きの UNKNOWN。ground truth で
           確かめられない EQ / NOT_EQ は ``unconfirmed``（accepted ではない）。process
           TIMEOUT・ERROR・矛盾する判定・reason の無い UNKNOWN は not accepted
Class B    保証しない。safe は supervisor の TIMEOUT（fallback）、止められなかった worker が
           自分で返った後の結果（`worker_stop=not_stoppable` の証拠付き）、整合が確認された
           判定、reason 付きの UNKNOWN。確かめられない判定は ``unconfirmed``（safe ではない）。
           ERROR・矛盾する判定は unsafe。どれも **改善には数えない**
========== ==================================================================

ground truth との関係は `outcome_transition.correctness_axis` の値（``confirmed_consistent`` /
``confirmed_contradicted`` / ``unconfirmed`` / ``not_applicable``）をそのまま受け取り、ここで
読み替えない。判定（EQ / NOT_EQ）に値が無い（``None``）ときは ``unconfirmed`` と同じ扱い
（整合を主張できない）。未知の値は拒む。

改善（improvement）は before が **process の TIMEOUT**（`timeout_kind` が supervisor の process
deadline を示す: `timeout_hotspot_summary.PROCESS_DEADLINE_KINDS`）で、after が Class A の accepted な
結果のときだけ。checker 自身の solver の terminal timeout（`child_solver_timeout`）や、証拠の足りない
TIMEOUT は「process TIMEOUT から改善した」とは数えない（Issue #106 PR-106-B review 1）。
soundness violation は after の EQ / NOT_EQ が ground truth と矛盾するとき（Class に依らない）。
完了は、Class A が全件 accepted・Class B が全件 safe・改善が 1 件以上・violation 0（``unconfirmed``
が 1 件でもあれば完了にしない）。

ここは報告だけを作る（判定 authority にも runner の policy にも入力を渡さない）。
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

CLASS_A = "A"
CLASS_B = "B"

OUTCOME_EQ = "EQUIVALENT"
OUTCOME_NOT_EQ = "NOT_EQ"
OUTCOME_UNKNOWN = "UNKNOWN"
OUTCOME_TIMEOUT = "TIMEOUT"
OUTCOME_ERROR = "ERROR"
DECISIVE = frozenset({OUTCOME_EQ, OUTCOME_NOT_EQ})

from scripts.function_tracer_pcode.core.errors import (  # noqa: E402
    DeadlineExceeded as _DeadlineExceeded,
    PairStopState as _PairStopState,
)

#: 語彙の正本は `core.errors`（ここで綴りを持たない）
DEADLINE_REASON = _DeadlineExceeded.REASON_ID
DEADLINE_STOP_STATE = _PairStopState.PAIR_TERMINAL_DEADLINE.value
from scripts.function_tracer_pcode.smt.parallel import (  # noqa: E402
    WORKER_NOT_STOPPABLE_EVIDENCE,
)
from scripts.function_tracer_pcode.reporting.timeout_hotspot_summary import (  # noqa: E402
    PROCESS_DEADLINE_KINDS,
)
SNAPSHOT_HEADER = "=== deadline_tripped"

VERDICT_ACCEPTED = "accepted"
VERDICT_NOT_ACCEPTED = "not_accepted"
VERDICT_FALLBACK_SAFE = "fallback_safe"
VERDICT_UNSAFE = "unsafe"
#: 判定が出たが ground truth で確かめられない（accepted でも safe でもない）
VERDICT_UNCONFIRMED = "unconfirmed"

#: ground truth との関係（`outcome_transition.correctness_axis` の値。語彙の正本はそちら）
from scripts.function_tracer_pcode.reporting.outcome_transition import (  # noqa: E402
    CORRECTNESS_CONSISTENT as TRUTH_CONSISTENT,
    CORRECTNESS_CONTRADICTED as TRUTH_CONTRADICTED,
    CORRECTNESS_NOT_APPLICABLE as TRUTH_NOT_APPLICABLE,
    CORRECTNESS_UNCONFIRMED as TRUTH_UNCONFIRMED,
)

_KNOWN_TRUTHS = frozenset({
    None, TRUTH_CONSISTENT, TRUTH_CONTRADICTED, TRUTH_UNCONFIRMED, TRUTH_NOT_APPLICABLE,
})


@dataclass(frozen=True)
class TargetObservation:
    """1 つの targeted pair について、判定に使う観測（run の出力から読む）。"""

    key: str
    guarantee_class: str
    before_outcome: str
    after_outcome: str
    #: after の EQ / NOT_EQ が ground truth と矛盾しないか（`TRUTH_*`、判定でなければ None）
    after_truth: Optional[str] = None
    after_reasons: Tuple[str, ...] = ()
    #: after の限界の診断（`failures.analysis_limitation`）の site と evidence
    limitation_site: Optional[str] = None
    limitation_evidence: Tuple[str, ...] = ()
    pair_stop_state: Optional[str] = None
    stack_snapshot: bool = False
    #: TIMEOUT の終わり方（`timeout_hotspot_summary.classify_timeout_kind`。TIMEOUT でなければ None）
    before_timeout_kind: Optional[str] = None
    after_timeout_kind: Optional[str] = None


@dataclass(frozen=True)
class TargetVerdict:
    key: str
    guarantee_class: str
    before_outcome: str
    after_outcome: str
    deadline_result: str
    worker_termination: str
    stack_snapshot: bool
    verdict: str
    improvement: bool
    soundness_violation: bool
    detail: str
    before_timeout_kind: Optional[str] = None


def _process_timeout(outcome: str, kind: Optional[str]) -> bool:
    """supervisor の process deadline が終端を決めた TIMEOUT か（証拠で。outcome だけでは決めない）。"""

    return outcome == OUTCOME_TIMEOUT and kind in PROCESS_DEADLINE_KINDS


def _worker_termination(observation: TargetObservation) -> str:
    if WORKER_NOT_STOPPABLE_EVIDENCE in observation.limitation_evidence:
        return "not_stoppable"
    if _process_timeout(observation.after_outcome, observation.after_timeout_kind):
        return "process_killed"
    if observation.after_outcome == OUTCOME_TIMEOUT:
        return f"timeout:{observation.after_timeout_kind or 'unclassified'}"
    return "stopped"


def _deadline_result(observation: TargetObservation) -> str:
    if observation.after_outcome != OUTCOME_UNKNOWN:
        return "none"
    if DEADLINE_REASON in observation.after_reasons and (
        observation.pair_stop_state == DEADLINE_STOP_STATE
    ):
        return f"deadline_unknown@{observation.limitation_site}"
    return "unknown_other_reason"


def _decision_truth(observation: TargetObservation) -> Optional[str]:
    """EQ / NOT_EQ の ground truth との関係（判定でなければ ``None``）。"""

    if observation.after_truth not in _KNOWN_TRUTHS:
        raise ValueError(f"unknown ground-truth relation: {observation.after_truth!r}")
    if observation.after_outcome not in DECISIVE:
        return None
    if observation.after_truth in (TRUTH_CONSISTENT, TRUTH_CONTRADICTED):
        return observation.after_truth
    # 値が無い・未確認・対象外: 整合を主張できない
    return TRUTH_UNCONFIRMED


def classify_target(observation: TargetObservation) -> TargetVerdict:
    """**受理判定の唯一の規則**（module docstring の表）。"""

    if observation.guarantee_class not in (CLASS_A, CLASS_B):
        raise ValueError(f"unknown guarantee class: {observation.guarantee_class!r}")
    outcome = observation.after_outcome
    truth = _decision_truth(observation)
    contradicted = truth == TRUTH_CONTRADICTED
    worker = _worker_termination(observation)
    deadline_result = _deadline_result(observation)
    if observation.guarantee_class == CLASS_A:
        if contradicted:
            verdict, detail = VERDICT_NOT_ACCEPTED, "decision contradicts the ground truth"
        elif truth == TRUTH_UNCONFIRMED:
            verdict, detail = VERDICT_UNCONFIRMED, "decision the ground truth does not confirm"
        elif truth == TRUTH_CONSISTENT:
            verdict, detail = VERDICT_ACCEPTED, "decision consistent with the ground truth"
        elif outcome == OUTCOME_UNKNOWN and observation.after_reasons and worker != "not_stoppable":
            verdict, detail = VERDICT_ACCEPTED, "UNKNOWN with registered reasons"
        elif outcome == OUTCOME_UNKNOWN and worker == "not_stoppable":
            verdict, detail = VERDICT_NOT_ACCEPTED, "a worker was not stoppable on a Class A path"
        elif outcome == OUTCOME_UNKNOWN:
            verdict, detail = VERDICT_NOT_ACCEPTED, "UNKNOWN without a reason"
        else:
            verdict, detail = VERDICT_NOT_ACCEPTED, f"{outcome} is not an accepted terminal result"
    else:
        if contradicted or outcome == OUTCOME_ERROR:
            verdict, detail = VERDICT_UNSAFE, f"{outcome} is not a safe fallback"
        elif truth == TRUTH_UNCONFIRMED:
            verdict, detail = VERDICT_UNCONFIRMED, "decision the ground truth does not confirm"
        elif _process_timeout(outcome, observation.after_timeout_kind):
            verdict, detail = VERDICT_FALLBACK_SAFE, "supervisor TIMEOUT fallback"
        elif outcome == OUTCOME_TIMEOUT:
            verdict, detail = VERDICT_FALLBACK_SAFE, (
                f"terminal TIMEOUT ({observation.after_timeout_kind or 'unclassified'}), "
                "not the supervisor's fallback"
            )
        elif worker == "not_stoppable":
            verdict, detail = VERDICT_FALLBACK_SAFE, "result after a non-stoppable worker returned by itself"
        elif truth == TRUTH_CONSISTENT or (outcome == OUTCOME_UNKNOWN and observation.after_reasons):
            verdict, detail = VERDICT_FALLBACK_SAFE, "terminal result (not counted as a guarantee)"
        else:
            verdict, detail = VERDICT_UNSAFE, f"{outcome} without a reason"
    improvement = (
        observation.guarantee_class == CLASS_A
        and verdict == VERDICT_ACCEPTED
        and _process_timeout(observation.before_outcome, observation.before_timeout_kind)
    )
    return TargetVerdict(
        key=observation.key,
        guarantee_class=observation.guarantee_class,
        before_outcome=observation.before_outcome,
        after_outcome=outcome,
        deadline_result=deadline_result,
        worker_termination=worker,
        stack_snapshot=observation.stack_snapshot,
        verdict=verdict,
        improvement=improvement,
        soundness_violation=contradicted,
        detail=detail,
        before_timeout_kind=observation.before_timeout_kind,
    )


@dataclass(frozen=True)
class AcceptanceSummary:
    targets: int
    class_a_accepted: bool
    class_b_safe: bool
    improvements: int
    soundness_violations: int
    unconfirmed: int
    complete: bool


def summarize(verdicts: Sequence[TargetVerdict]) -> AcceptanceSummary:
    """完了条件（計画 §7.E）: Class A は全件 accepted、Class B は全件 safe、改善 ≥ 1、violation 0、
    ground truth で確かめられない判定 0。"""

    class_a = [row for row in verdicts if row.guarantee_class == CLASS_A]
    class_b = [row for row in verdicts if row.guarantee_class == CLASS_B]
    a_ok = all(row.verdict == VERDICT_ACCEPTED for row in class_a)
    b_ok = all(row.verdict == VERDICT_FALLBACK_SAFE for row in class_b)
    improvements = sum(1 for row in verdicts if row.improvement)
    violations = sum(1 for row in verdicts if row.soundness_violation)
    unconfirmed = sum(1 for row in verdicts if row.verdict == VERDICT_UNCONFIRMED)
    return AcceptanceSummary(
        targets=len(verdicts),
        class_a_accepted=a_ok,
        class_b_safe=b_ok,
        improvements=improvements,
        soundness_violations=violations,
        unconfirmed=unconfirmed,
        complete=(
            bool(verdicts) and a_ok and b_ok and improvements >= 1 and violations == 0
            and unconfirmed == 0
        ),
    )


# ---------------------------------------------------------------------------
# run の出力から観測を読む（CLI 用）
# ---------------------------------------------------------------------------


def _limitation_block(payload: Optional[Mapping[str, Any]]) -> Mapping[str, Any]:
    failures = ((payload or {}).get("diagnostics") or {}).get("failures") or {}
    block = failures.get("analysis_limitation")
    return block if isinstance(block, Mapping) else {}


def _stack_snapshot(evidence: Optional[Any]) -> bool:
    """**この pair の** stack dump に trip の header があるか（同じ dir の別 pair の dump は見ない）。"""

    if evidence is None:
        return False
    try:
        return SNAPSHOT_HEADER in evidence.paths.stack_dump.read_text(errors="replace")
    except OSError:
        return False


def _timeout_kind(record: Any, evidence: Optional[Any]) -> Optional[str]:
    if record is None or record.outcome != OUTCOME_TIMEOUT or evidence is None:
        return None
    return evidence.timeout_kind_report().kind


def observe_runs(
    before_root: Path, after_root: Path, targets: Mapping[str, str],
) -> List[TargetObservation]:
    """`targets` = pair key 文字列（`sample|function|left|right`）→ guarantee class。"""

    from scripts.function_tracer_pcode.reporting.outcome_transition import (
        correctness_axis,
        final_reason_set,
        final_result_payload,
        load_ground_truth,
    )
    from scripts.function_tracer_pcode.reporting.pair_outcomes import load_pair_outcomes
    from scripts.function_tracer_pcode.reporting.timeout_hotspot_summary import (
        load_pair_evidence,
    )

    before = load_pair_outcomes(before_root)
    after = load_pair_outcomes(after_root)
    manifest, _source = load_ground_truth(after_root)

    def _key(pair_key: Iterable[str]) -> str:
        return "|".join(str(part) for part in pair_key)

    before_by = {_key(key): record for key, record in before.items()}
    after_by = {_key(key): record for key, record in after.items()}
    rows = []
    for key, guarantee_class in targets.items():
        record_before = before_by.get(key)
        record_after = after_by.get(key)
        evidence_before = (
            load_pair_evidence(record_before.status_path) if record_before is not None else None
        )
        evidence_after = (
            load_pair_evidence(record_after.status_path) if record_after is not None else None
        )
        payload = final_result_payload(record_after)
        block = _limitation_block(payload)
        rows.append(TargetObservation(
            key=key,
            guarantee_class=guarantee_class,
            before_outcome=record_before.outcome if record_before is not None else "MISSING",
            after_outcome=record_after.outcome if record_after is not None else "MISSING",
            after_truth=correctness_axis(record_after, manifest),
            after_reasons=tuple(final_reason_set(record_after) or ()),
            limitation_site=block.get("site"),
            limitation_evidence=tuple(str(item) for item in block.get("evidence_refs") or ()),
            pair_stop_state=((payload or {}).get("diagnostics") or {}).get("failures", {}).get(
                "pair_stop_state"
            ) if payload else None,
            stack_snapshot=_stack_snapshot(evidence_after),
            before_timeout_kind=_timeout_kind(record_before, evidence_before),
            after_timeout_kind=_timeout_kind(record_after, evidence_after),
        ))
    return rows


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--before", required=True, type=Path)
    parser.add_argument("--after", required=True, type=Path)
    parser.add_argument(
        "--targets", required=True, type=Path,
        help="JSON object: pair key (sample|function|left|right) -> guarantee class (A/B)",
    )
    parser.add_argument("--json", type=Path, default=None)
    args = parser.parse_args(argv)
    targets = json.loads(args.targets.read_text())
    verdicts = [classify_target(row) for row in observe_runs(args.before, args.after, targets)]
    summary = summarize(verdicts)
    header = (
        "key", "class", "before", "before_timeout_kind", "after", "deadline_result", "worker",
        "snapshot", "verdict", "improvement", "violation",
    )

    print("\t".join(header))
    for row in verdicts:
        print("\t".join(str(item) for item in (
            row.key, row.guarantee_class, row.before_outcome, row.before_timeout_kind,
            row.after_outcome,
            row.deadline_result, row.worker_termination, row.stack_snapshot, row.verdict,
            row.improvement, row.soundness_violation,
        )))
    print(json.dumps(asdict(summary), sort_keys=True))
    if args.json is not None:
        args.json.write_text(json.dumps(
            {"verdicts": [asdict(row) for row in verdicts], "summary": asdict(summary)},
            indent=2, sort_keys=True,
        ))
    return 0 if summary.complete else 1


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())

# -*- coding: utf-8 -*-
"""記録済み pair 1 件の実行と検証（Issue #109）。**唯一の validator**。

PR gate（軽い 7 replay）も full corpus（9 replay の matrix）も、この
:func:`validate_replay` を呼ぶだけで、fast 専用 / full 専用の soundness 実装は
存在しない。片方だけ緩い検査になる余地を構造で消しておく。

judgement の分け方は変えていない:

1. **semantic ground truth** — 正本は `scripts/eqbench/neq_ground_truth.tsv` と、
   Eq sample に対する単一 source 規則。`dataset_label`（EqBench の directory 名）は
   ground truth では**ない**ので、label だけで soundness violation にしない。
2. **observation contract coverage** — その observable が観測面に入っているか。
3. **current implementation capability** — assert に使わない。

soundness assert は (1) と (2) が揃った case にだけ。conditional 列は、receipt の
**全 premise** が compatibility `verified` のときだけ GT に対して判定する。

逃げ道は置かない: z3 が無い・fixture が無い・schema が壊れている・API surface が
足りない・budget を超えた、はすべて **fail**。per-case budget は実際の deadline
として worker の process group に効き、超えたら待たずに落として
:class:`RecordedReplayBudgetExceeded` になる。これは harness の失敗条件で、
production の UNKNOWN / TIMEOUT へは変換しない。
"""

from __future__ import annotations

import importlib
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple, cast

pytest = cast(Any, importlib.import_module("pytest"))

from scripts.function_tracer_pcode.tests.fixtures.pcode.corpus import (
    CASES,
    FIXTURE_ROOT,
    ReplayRecord,
    ReplaySpec,
    VARIANT_DEFAULT,
    VARIANT_FAST_PATH_OFF,
    VARIANT_FAST_PATH_ON,
    WORKER_FAST_PATH,
)
from scripts.function_tracer_pcode.tests.fixtures.pcode.replay import (
    DECOMPILER_MODULE,
    REPLAY_REPORT_SCHEMA,
)
from scripts.function_tracer_pcode.tests.fixtures.pcode.snapshot import check_snapshot

REPO_ROOT = Path(__file__).resolve().parents[5]
EQBENCH_SCRIPTS = REPO_ROOT / "scripts" / "eqbench"

GROUND_TRUTH_SCHEMA = "verified-ground-truth-ref-v1"
EXPECTED_SCHEMA = "recorded-pair-expected-v1"

VERIFICATION_VERIFIED = "verified"
VERIFICATION_SOURCE_WITNESS_ONLY = "source_witness_only"
COMPATIBILITY_VERIFIED = "verified"

RELATION_NOT_EQ = "NOT_EQ"
RELATION_EQ = "EQ"
OUTCOME_EQUIVALENT = "EQUIVALENT"
OUTCOME_NOT_EQ = "NOT_EQ"
OUTCOME_UNKNOWN = "UNKNOWN"

#: verdict（tsv / manifest の語彙）→ fixture GT file の relation。
RELATION_BY_VERDICT = {"CONFIRMED_NOT_EQ": RELATION_NOT_EQ, "CONFIRMED_EQ": RELATION_EQ}

#: identical fast path が立てる decisive proof の provenance。
IDENTITY_PROVENANCE_KIND = "identical_function_identity"
EQ_CLOSURE = "EQ_CLOSURE"

#: `verification_method` → その method が主張する事実。metadata が「やっていない
#: 確認」を名乗らないよう、散文ではなくこの表で照合する。
VERIFICATION_METHODS = {
    "source_review_and_native_execution": {
        "requires_native_witness": True,
        "requires_source_witness": True,
        "registry_key": "file",
    },
    "eq_sample_single_source": {
        "requires_native_witness": False,
        "requires_source_witness": False,
        "registry_key": "kind",
    },
}

#: native 実行 witness が名乗るべき field（どれが欠けても「実行した」と言えない）。
NATIVE_WITNESS_FIELDS = (
    "toolchain", "command", "input", "left_output", "right_output",
)

WORKER_MODULE = "scripts.function_tracer_pcode.tests.fixtures.pcode.replay_worker"


def read_json(path) -> Any:
    return json.loads(Path(path).read_text(encoding="utf-8"))


def variant_id(case_id: str, variant: str) -> str:
    return case_id if variant == VARIANT_DEFAULT else case_id + "." + variant


def expected_path(case_id: str, variant: str) -> Path:
    return FIXTURE_ROOT / "expected" / (variant_id(case_id, variant) + ".json")


def require_z3() -> None:
    """z3 が無ければ **fail**。skip escape hatch は置かない。

    recorded corpus の意味は「本物の solver を通した production path を Ghidra
    無しで回す」ことなので、solver の無い環境で静かに skip すると CI が緑のまま
    corpus を走らせていない状態になる。
    """

    if shutil.which("z3") is None:
        pytest.fail(
            "the z3 CLI is required by the recorded corpus and must be on "
            "PATH; this test never skips (see .github/workflows/unit.yml)"
        )


def load_registry_annotations() -> Dict[Tuple[str, str], str]:
    """`scripts/eqbench/neq_ground_truth.tsv` の (sample, function) → verdict。

    `function_diff_manifest` は sibling import を使う script なので、既存の
    `test_function_diff_manifest.py` と同じ流儀で `scripts/eqbench` を
    `sys.path` に入れてから読む。Ghidra も EqBench の checkout も要らない。
    """

    if str(EQBENCH_SCRIPTS) not in sys.path:
        sys.path.insert(0, str(EQBENCH_SCRIPTS))
    fdm = importlib.import_module("function_diff_manifest")
    return {
        (row.sample, row.function): row.verdict
        for row in fdm.load_ground_truth(fdm.DEFAULT_GROUND_TRUTH_FILE)
    }


def load_compatibility():
    from scripts.function_tracer_pcode.reporting.soundness_gate import (
        DEFAULT_COMPATIBILITY_PATH,
        load_conditional_compatibility,
    )

    return load_conditional_compatibility(DEFAULT_COMPATIBILITY_PATH)


def ground_truth_of(case: Mapping[str, Any]) -> Optional[Mapping[str, Any]]:
    reference = case.get("ground_truth_file")
    if reference is None:
        return None
    payload = read_json(FIXTURE_ROOT / reference)
    if payload.get("schema") != GROUND_TRUTH_SCHEMA:
        raise ValueError(
            "unexpected ground truth reference schema in {}: {!r}".format(
                reference, payload.get("schema")
            )
        )
    return payload


def soundness_is_assertable(ground_truth: Optional[Mapping[str, Any]]) -> bool:
    """unconditional soundness を assert してよいか。

    verdict が verified で、かつ差が観測契約の中にある case だけ。GT 無し /
    `source_witness_only` / 契約外は判定しない（report に回す）。
    """

    if ground_truth is None:
        return False
    if ground_truth["verification_status"] != VERIFICATION_VERIFIED:
        return False
    return bool(ground_truth["observation_contract"]["covered_by_contract"])


def _validate_expectation(expected: Mapping[str, Any], where: str) -> None:
    """expectation 自身の整合性（毎回検査する）。

    reason 比較式が意味を持つのは、stable と unstable が互いに素で、どちらにも
    重複が無く、unstable の各行が「なぜ揺れるか」と「どの run で揺れたか」を
    持っているときだけ。「揺れるかもしれない」で unstable へ逃がすのを防ぐ。
    """

    if expected.get("schema") != EXPECTED_SCHEMA:
        raise ValueError(
            "unexpected regression expectation schema in {}: {!r}".format(
                where, expected.get("schema")
            )
        )
    stable = expected["expected_stable_reason_ids"]
    unstable_rows = expected["allowed_unstable_reason_ids"]
    assert len(stable) == len(set(stable)), (
        where + ": expected_stable_reason_ids has a duplicate"
    )
    unstable = [row["reason_id"] for row in unstable_rows]
    assert len(unstable) == len(set(unstable)), (
        where + ": allowed_unstable_reason_ids has a duplicate reason_id"
    )
    assert not (set(stable) & set(unstable)), (
        where + ": a reason is both stable and unstable: "
        + repr(sorted(set(stable) & set(unstable)))
    )
    assert len(expected["recorded_at_commit"]) == 40, (
        where + ": recorded_at_commit must name the commit whose fixtures "
        "produced these values"
    )
    for row in unstable_rows:
        assert row.get("justification"), (
            where + ": unstable reason " + row["reason_id"]
            + " has no justification; a reason may only be registered as"
            " unstable after it was observed to vary"
        )
        assert row.get("observed_in"), (
            where + ": unstable reason " + row["reason_id"]
            + " names no run it was observed to vary in"
        )


def _reason_ids(payload: Mapping[str, Any]) -> Set[str]:
    return {str(row.get("reason_id")) for row in (payload.get("c_active_base") or [])}


def _assumption_kinds(payload: Mapping[str, Any]) -> List[str]:
    receipt = payload.get("conditional_decision_receipt") or {}
    return sorted({
        premise["kind"] for premise in (receipt.get("assumption_set") or [])
    })


def _compare_regression(
    payload: Mapping[str, Any], expected: Mapping[str, Any], where: str,
) -> None:
    """判定面の遷移検出。

    不一致は「遷移」であって、新しい結果の正誤はここでは判定しない。
    """

    snapshot = check_snapshot(payload)
    transition = (
        "{}: the recorded pair moved. Update fixtures/pcode/expected/ and put "
        "the transition table in the PR; whether the new result is right is a "
        "separate judgement."
    ).format(where)

    actual = _reason_ids(payload)
    allowed_unstable = {
        row["reason_id"] for row in expected["allowed_unstable_reason_ids"]
    }
    stable = set(expected["expected_stable_reason_ids"])
    assert actual - allowed_unstable == stable, (
        "{} reason ids: actual={} allowed_unstable={} expected_stable={}".format(
            transition, sorted(actual), sorted(allowed_unstable), sorted(stable)
        )
    )
    assert snapshot["final_outcome"] == expected["final_outcome"], transition
    assert snapshot["decisive_proof_kinds"] == expected["decisive_proof_kinds"], (
        transition
    )
    assert snapshot["conditional_outcome"] == expected["conditional_outcome"], (
        transition
    )
    assert _assumption_kinds(payload) == expected["conditional_assumption_kinds"], (
        transition
    )
    assert snapshot["stage_path"] == expected["stage_path"], transition


def _conditional_view(payload: Mapping[str, Any]) -> Optional[Mapping[str, Any]]:
    """conditional 列を authority 自身の codec で再検証して返す。

    ここに弱い言い直しは置かない: receipt の digest 再計算・canonical な
    assumption set・unconditional 決定との join は
    `conditional_outcome_from_payload` が行う。整合性違反は握り潰さず fail。
    """

    from scripts.function_tracer_pcode.authority.decision.conditional import (
        assumption_dependencies_digest,
        assumption_set_from_payload,
        conditional_decision_receipt_from_payload,
    )
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        conditional_outcome_from_payload,
    )

    outcome = conditional_outcome_from_payload(payload)
    if outcome is None:
        return None
    receipt_payload = payload["conditional_decision_receipt"]
    receipt = conditional_decision_receipt_from_payload(receipt_payload)
    premises = assumption_set_from_payload(receipt_payload["assumption_set"])
    assert premises, "a conditional decision carries an empty assumption set"
    assert assumption_dependencies_digest(premises) == receipt.assumption_set_digest, (
        "conditional assumption dependencies digest mismatch"
    )
    return {
        "outcome": outcome.value,
        "premises": tuple(
            (premise.kind.value, premise.subject) for premise in premises
        ),
    }


# ---------------------------------------------------------------------------
# 1 replay の実行（per-case budget を実際の deadline として適用）
# ---------------------------------------------------------------------------


class RecordedReplayBudgetExceeded(AssertionError):
    """worker が per-case budget 内に終わらず、deadline で止められた。

    **production の UNKNOWN / TIMEOUT ではない。** production の timeout は
    supervisor が受領証付きで出す判定で、これは「この test harness がこの機械で
    待つと決めた上限」でしかない。両者を同じ語彙にすると、harness の都合が
    判定結果の分布に混ざる。だから harness の失敗（``AssertionError``）として
    投げ、report にも payload にも変換しない。
    """

    def __init__(self, case_id: str, variant: str, budget_seconds: int) -> None:
        super().__init__(
            "{}: the replay worker did not finish inside its {}s per-case "
            "harness budget and its process group was killed "
            "(case_id={!r}, variant={!r}). This is a test-harness failure "
            "condition; it is not converted into a production UNKNOWN or "
            "TIMEOUT outcome.".format(
                variant_id(case_id, variant), budget_seconds, case_id, variant,
            )
        )
        self.case_id = case_id
        self.variant = variant
        self.budget_seconds = budget_seconds


def kill_process_group(process: "subprocess.Popen") -> None:
    """worker と、それが起動した solver ごと落とす。

    ``start_new_session=True`` で作った process group を SIGKILL する。worker
    だけを kill すると、解いている最中の z3 が孤児として残り、次の case と
    CPU を取り合う。
    """

    try:
        os.killpg(os.getpgid(process.pid), signal.SIGKILL)
    except (OSError, ProcessLookupError):
        # group を落とせない環境でも、せめて直接の子は止める。
        try:
            process.kill()
        except OSError:
            pass


def run_replay_worker(
    command: Sequence[str], *, case_id: str, variant: str, budget_seconds: int,
) -> Tuple[int, str, str]:
    """worker を起動し、per-case budget を **実際の deadline** として適用する。

    budget を過ぎたら待ち続けずに process group を落とし、
    :class:`RecordedReplayBudgetExceeded` を送出する。worker が hang しても
    job 全体の timeout まで待たない。
    """

    process = subprocess.Popen(
        list(command), cwd=str(REPO_ROOT),
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=budget_seconds)
    except subprocess.TimeoutExpired as expired:
        kill_process_group(process)
        try:
            process.communicate(timeout=30)
        except subprocess.TimeoutExpired:  # pragma: no cover - kill 後は来ない
            pass
        raise RecordedReplayBudgetExceeded(
            case_id, variant, budget_seconds,
        ) from expired
    return process.returncode, stdout, stderr


def _replay_case(case: Mapping[str, Any], variant: str) -> Mapping[str, Any]:
    """1 件の再生を **子 process で 1 回だけ**走らせ、観測を読み戻す。

    production は pair ごとに process を分ける。1 つの pytest process で 9 件
    続けて再生すると production に無い条件になり、実測でも同じ fixture の 2 回目
    が別の stage 経路（`S_MONOLITHIC_FALLBACK`）へ入り、outcome が NOT_EQ から
    `counterexample_partition_replay_ambiguous` 付きの UNKNOWN に変わって記録に
    無い surface を要求した（Issue #161 に evidence を追記）。子 process にする
    ことで、どの case も「その process の最初の判定」という記録時と同じ条件で
    走る。

    子は採点しない。ここで受け取るのは観測だけで、判定はこの後の assert が行う。
    """

    case_id = case["case_id"]
    budget_seconds = int(case["budget_seconds"])
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="recorded-pair-") as work:
        output = Path(work) / "report.json"
        command = [
            sys.executable, "-B", "-m", WORKER_MODULE,
            "--case-dir", str(FIXTURE_ROOT / case_id),
            "--case-id", case_id,
            "--variant", variant,
            "--fast-path", WORKER_FAST_PATH[variant],
            "--output", str(output),
        ]
        if variant == VARIANT_FAST_PATH_ON:
            command.append("--forbid-solver")
        returncode, stdout, stderr = run_replay_worker(
            command, case_id=case_id, variant=variant,
            budget_seconds=budget_seconds,
        )
        if returncode != 0 or not output.is_file():
            raise AssertionError(
                "the replay worker failed for {} (exit {}).\nstdout:\n{}\n"
                "stderr:\n{}".format(
                    variant_id(case_id, variant), returncode,
                    stdout[-4000:], stderr[-4000:],
                )
            )
        report = read_json(output)
    # budget に数えるのは **親から見た wall clock**（子 process の起動と import を
    # 含む）。AC が言っているのはこの test file の所要なので、内側だけを測ると
    # 実測より小さく出る。子が測った再生自体の秒数は report に残す。
    elapsed = time.monotonic() - started
    if report.get("schema") != REPLAY_REPORT_SCHEMA:
        raise ValueError("unexpected replay report schema: " + repr(report.get("schema")))
    return dict(report, wall_clock_seconds=elapsed)


def _assert_identity_fast_path_was_decisive(
    payload: Mapping[str, Any], report: Mapping[str, Any], where: str,
) -> None:
    """ON replay: identity proof だけで決まり、記録済み P-code を読まないこと。"""

    snapshot = check_snapshot(payload)
    assert snapshot["final_outcome"] == OUTCOME_EQUIVALENT, where
    assert snapshot["decisive_proof_kinds"] == [EQ_CLOSURE], where
    provenance = payload.get("decisive_proof_provenance") or {}
    assert provenance.get("kind") == IDENTITY_PROVENANCE_KIND, where
    assert provenance.get("proof_artifact_digest"), where
    assert payload["identical_fast_path_disposition"] == {
        "applicable": True, "applied": True, "reason": "applied",
    }, where
    assert payload["function1_identity"], where
    assert payload["function2_identity"], where
    # solver を禁止した状態で走り切ったこと（動いていたら worker が落ちる）。
    assert report["solver_forbidden"] is True, where
    # 解析器も decompiler も触らずに決まったこと。
    assert report["analyzer_factory_calls"] == [], (
        where + ": the analyzer was built on the identical fast path"
    )
    assert report["decompiler_access"] == {"left": [], "right": []}, (
        where + ": the recorded decompiler was used on the identical fast path"
    )
    assert report["decompiled_ir_access"] == {"left": 0, "right": 0}, (
        where + ": recorded P-code was read on the identical fast path"
    )


def _assert_production_pcode_path_was_used(
    report: Mapping[str, Any], where: str,
) -> None:
    """OFF / default replay: 記録済み Program と decompiler を実際に通ること。"""

    assert report["analyzer_factory_calls"], (
        where + ": no analyzer was built, so the production path did not run"
    )
    decompiler = report["decompiler_access"]
    assert decompiler["left"] and decompiler["right"], (
        where + ": the recorded decompiler was not used on both sides: "
        + repr(decompiler)
    )
    ir_reads = report["decompiled_ir_access"]
    assert ir_reads["left"] > 0 and ir_reads["right"] > 0, (
        where + ": no recorded P-code was read: " + repr(ir_reads)
    )


# ---------------------------------------------------------------------------
# 1 replay の検証（fast / full が共有する唯一の実装）
# ---------------------------------------------------------------------------


def _assert_snapshot_bodies_match_distinct_witnesses(report: Mapping[str, Any], where: str) -> None:
    """本体の実行回数（外から数えた）== 保存した distinct な witness の数。

    本体は canonical な経路で読んだ値から snapshot を作る部分（`assemble_snapshot`）。再生は逐次なので、
    witness を作れない（比べる途中の再帰の深さ）呼び出しは無く、miss はすべて保存される。通常の本体へ
    回した呼び出し（`bypass:*`）は理由つきで別に数える。distinct な fingerprint の数との一致は求めない
    （別 object の同じ内容は別の witness）。
    """

    observed = report["snapshot_reuse"]
    stores = observed["stores"]
    assert stores, where + ": no snapshot reuse scope was closed during the replay"
    totals: Dict[str, int] = {}
    entries = 0
    for store in stores:
        entries += store["entries"]
        for name, value in store["counts"].items():
            totals[name] = totals.get(name, 0) + value
    witness_failures = {name: value for name, value in totals.items() if name.startswith("bypass:witness_failed")}
    assert not witness_failures, (
        where + ": a sequential replay had unbuildable witnesses: " + json.dumps(totals, sort_keys=True)
    )
    assert observed["body_executions_in_scope"] == totals.get("body_executions", 0), (
        where + ": the counted body executions are not the actual executions: "
        + json.dumps({"actual": observed["body_executions_in_scope"], **totals}, sort_keys=True)
    )
    assert observed["body_executions_in_scope"] == entries, (
        where + ": a body ran for an already stored witness: "
        + json.dumps({"actual": observed["body_executions_in_scope"], "entries": entries, **totals}, sort_keys=True)
    )


def validate_replay(
    spec: ReplaySpec, *, record_property=None,
) -> ReplayRecord:
    """1 件の replay を走らせ、契約をすべて検査して記録を返す。"""

    def _report(name: str, value: str) -> None:
        if record_property is not None:
            record_property(name, value)

    require_z3()
    case_id, variant = spec.case_id, spec.variant
    case = CASES[case_id]
    where = spec.variant_id
    ground_truth = ground_truth_of(case)
    expected = read_json(expected_path(case_id, variant))
    _validate_expectation(expected, where)

    report = _replay_case(case, variant)
    elapsed = float(report["wall_clock_seconds"])
    # 実 decompiler を組み立てる遅延生成に入っていないこと。型判定 probe の
    # import 失敗は Ghidra 無し環境と同じなので許す。
    assert report["decompiler_module_imported"] is False, where
    assert report["decompiler_module_blocked"] is False, (
        where + ": the replay tried to import " + DECOMPILER_MODULE
    )
    assert report["failure"] is None, (
        "{}: replaying the recorded pair raised {}: {}".format(
            where, report["failure"] and report["failure"]["type"],
            report["failure"] and report["failure"]["message"],
        )
    )
    payload = report["payload"]
    assert payload is not None, where

    # (1) unconditional soundness -- verified GT かつ contract covered のときだけ
    relation = None if ground_truth is None else ground_truth["relation"]
    if soundness_is_assertable(ground_truth):
        if relation == RELATION_NOT_EQ:
            assert payload["final_outcome"] != OUTCOME_EQUIVALENT, (
                where + ": the reviewed relation is NOT_EQ but the checker "
                "returned EQUIVALENT (false equivalence)"
            )
        elif relation == RELATION_EQ:
            assert payload["final_outcome"] != OUTCOME_NOT_EQ, (
                where + ": the reviewed relation is EQ but the checker "
                "returned NOT_EQ (false disequivalence)"
            )
        else:
            raise AssertionError(where + ": unknown relation " + repr(relation))
    else:
        # dataset label と outcome が食い違っても、それだけでは soundness
        # violation にしない（label は ground truth ではない）。報告だけ。
        _report("ground_truth_not_verified", json.dumps({
            "case_id": case_id, "variant": variant,
            "dataset_label": case["dataset_label"],
            "final_outcome": payload["final_outcome"],
            "verification_status": (
                None if ground_truth is None
                else ground_truth["verification_status"]
            ),
        }, sort_keys=True))

    # (2) conditional soundness -- 整合性は常に、GT 判定は compatibility が
    #     全 premise verified のときだけ
    conditional = _conditional_view(payload)
    if conditional is not None:
        assert payload["final_outcome"] == OUTCOME_UNKNOWN, (
            where + ": a conditional column sits on a decided pair"
        )
        compatibility = load_compatibility()
        registry = (ground_truth or {}).get("registry") or {}
        statuses = [
            compatibility.status(
                registry.get("sample", ""), registry.get("function", ""),
                kind, subject,
            )
            for kind, subject in conditional["premises"]
        ]
        all_verified = bool(statuses) and all(
            status == COMPATIBILITY_VERIFIED for status in statuses
        )
        if all_verified and soundness_is_assertable(ground_truth):
            if relation == RELATION_NOT_EQ:
                assert conditional["outcome"] != OUTCOME_EQUIVALENT, (
                    where + ": the reviewed relation is NOT_EQ and every "
                    "premise is verified, but the conditional lane returned "
                    "EQUIVALENT"
                )
            elif relation == RELATION_EQ:
                assert conditional["outcome"] != OUTCOME_NOT_EQ, (
                    where + ": the reviewed relation is EQ and every premise "
                    "is verified, but the conditional lane returned NOT_EQ"
                )
        else:
            _report(
                "conditional_assumption_compatibility_unknown", json.dumps({
                    "case_id": case_id, "variant": variant,
                    "conditional_outcome": conditional["outcome"],
                    "premises": [
                        {"kind": kind, "subject": subject, "status": status}
                        for (kind, subject), status in zip(
                            conditional["premises"], statuses
                        )
                    ],
                }, sort_keys=True),
            )

    # (3) authority の決定面まで降りていること
    from scripts.function_tracer_pcode.authority.decision.production_cutover import (
        outcome_from_payload,
    )

    assert payload["decision_receipt"], where
    assert outcome_from_payload(payload).value == payload["final_outcome"], where
    assert payload.get("canonical_result_finalization_bundle"), (
        where + ": the canonical finalization bundle was not built"
    )

    # (4) fixture の完全性。未記録 surface は既定値へ丸めず、ここで落とす。
    assert report["missing_accesses"] == {"left": [], "right": []}, (
        where + ": the recorded surface was incomplete: "
        + json.dumps(report["missing_accesses"], sort_keys=True)[:2000]
    )

    # (5) snapshot の再利用（Issue #219 AC1）: 逐次の replay では、本体の実行は distinct な
    # safe witness ごとに 1 回（再利用しない呼び出しは理由つきで数えた分だけ）
    _assert_snapshot_bodies_match_distinct_witnesses(report, where)

    # ON / OFF の経路そのもの
    if variant == VARIANT_FAST_PATH_ON:
        assert case["left"]["sha256"] == case["right"]["sha256"], (
            where + ": the fast path variant needs byte-identical inputs"
        )
        _assert_identity_fast_path_was_decisive(payload, report, where)
    else:
        _assert_production_pcode_path_was_used(report, where)
        if variant == VARIANT_FAST_PATH_OFF:
            assert payload["identical_fast_path_disposition"] == {
                "applicable": True, "applied": False, "reason": "disabled",
            }, where
            assert payload["function1_identity"], where
            assert payload["function2_identity"], where

    # (5) regression（遷移検出）
    _compare_regression(payload, expected, where)

    # (5b) Issue #105 PR-105-B（D14）: 既定の予算では条件簡約の fallback の予算に当たらない。
    #      当たったなら、既定値を決めた decision gate の前提（正しい pair は予算の内側で
    #      答えが出る）が崩れているので、値を見直す（遷移と同じく PR に表を残す）。
    simplify = ((payload.get("diagnostics") or {}).get("condition_simplify") or {})
    assert not simplify.get("budget_events_total"), (
        where + ": the default condition-simplification budgets were hit: "
        + json.dumps(simplify.get("budget_events"), sort_keys=True)[:2000]
    )

    # (6) wall clock。per-case budget は `run_replay_worker` が **deadline として**
    #     適用済みで、ここへ来た時点で budget 内に終わっている（超過した replay は
    #     worker を落として RecordedReplayBudgetExceeded になる）。所要は報告する。
    _report("replay_seconds", "{} wall={:.2f} replay={:.2f} budget={}".format(
        where, elapsed, float(report["seconds"]), case["budget_seconds"],
    ))
    return ReplayRecord(
        case_id=case_id, variant=variant, seconds=elapsed, outcome="passed",
    )



__all__ = [
    "COMPATIBILITY_VERIFIED",
    "EXPECTED_SCHEMA",
    "GROUND_TRUTH_SCHEMA",
    "NATIVE_WITNESS_FIELDS",
    "RELATION_BY_VERDICT",
    "RELATION_EQ",
    "RELATION_NOT_EQ",
    "RecordedReplayBudgetExceeded",
    "VERIFICATION_METHODS",
    "VERIFICATION_SOURCE_WITNESS_ONLY",
    "VERIFICATION_VERIFIED",
    "expected_path",
    "kill_process_group",
    "ground_truth_of",
    "load_compatibility",
    "load_registry_annotations",
    "read_json",
    "require_z3",
    "run_replay_worker",
    "soundness_is_assertable",
    "validate_replay",
    "variant_id",
]

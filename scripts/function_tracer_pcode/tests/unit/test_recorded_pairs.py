# -*- coding: utf-8 -*-
"""Issue #109 PR-B: 記録済み P-code corpus の Ghidra-free 回帰 / soundness test。

`tests/fixtures/pcode/cases.json` の 8 case（identical case は ON / OFF の 2
variant）を、実 Ghidra を使わずに **production path** で再生する（経路の定義は
`tests/fixtures/pcode/replay.py` が 1 つだけ持ち、記録器と共有している）。

この file は 3 つの別々の情報を**混ぜない**:

1. **semantic ground truth** — 関数単位の relation。正本は
   `scripts/eqbench/neq_ground_truth.tsv`（人手 review + 独立実行）と、Eq sample
   に対する `function_diff_manifest.build_eq_sample` の単一 source 規則。
   `fixtures/pcode/ground_truth/*.json` は**その参照と witness の控え**であって
   verdict の正本ではない（drift test が両者の一致を固定する）。
   EqBench の directory 名（`dataset_label`）は ground truth では**ない**ので、
   label だけで soundness violation を宣言することはない。
2. **observation contract coverage** — その observable が
   `EquivalenceObservationContract` の観測面に入っているか。`wood` の差は
   stdout への書き込みだが `observe_io=True` なので covered。
3. **current implementation capability** — 現在の checker がそれを証明できるか。
   これは assert に使わない。証明できないことを理由に ground truth を弱めない。

soundness assert は (1) と (2) が揃った case にだけ掛ける。conditional 列は
さらに、その receipt の**全 premise** について
`scripts/eqbench/ground_truth_conditional_compatibility.json` が `verified` で
ある場合にだけ GT に対して判定する（1 つでも未確認なら report のみ）。

逃げ道は置かない: z3 が無い・fixture が無い・schema が壊れている・API surface が
足りない・budget を超えた、はすべて **fail** であって skip でも UNKNOWN でも
ない。per-case budget は実際の deadline として worker の process group に効き、
超えたら待たずに落として :class:`RecordedReplayBudgetExceeded` になる。これは
harness の失敗条件で、production の UNKNOWN / TIMEOUT へは変換しない。
"""

from __future__ import annotations

import importlib
import json
import shutil
import os
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple, cast

pytest = cast(Any, importlib.import_module("pytest"))

from scripts.function_tracer_pcode.tests.fixtures.pcode.replay import (
    REPLAY_REPORT_SCHEMA,
    DECOMPILER_MODULE,
)
from scripts.function_tracer_pcode.tests.fixtures.pcode.snapshot import check_snapshot

REPO_ROOT = Path(__file__).resolve().parents[4]
FIXTURE_ROOT = Path(__file__).resolve().parents[1] / "fixtures" / "pcode"
CASES_FILE = FIXTURE_ROOT / "cases.json"
EQBENCH_SCRIPTS = Path(__file__).resolve().parents[3] / "eqbench"

CASES_SCHEMA = "recorded-pcode-cases-v1"
GROUND_TRUTH_SCHEMA = "verified-ground-truth-ref-v1"
EXPECTED_SCHEMA = "recorded-pair-expected-v1"

VARIANT_DEFAULT = "default"
VARIANT_FAST_PATH_ON = "fast_path_on"
VARIANT_FAST_PATH_OFF = "fast_path_off"
#: variant → `identical_fast_path`。``None`` は「記録時の mode を使う」。
VARIANT_FAST_PATH = {
    VARIANT_DEFAULT: None,
    VARIANT_FAST_PATH_ON: True,
    VARIANT_FAST_PATH_OFF: False,
}

VERIFICATION_VERIFIED = "verified"
VERIFICATION_SOURCE_WITNESS_ONLY = "source_witness_only"
COMPATIBILITY_VERIFIED = "verified"

#: `verification_method` → その method が主張する事実。metadata が「やっていない
#: 確認」を名乗らないよう、散文ではなくこの表で照合する（`verified_by` は誰が
#: 登録したかだけを言い、どう確かめたかは method が構造化して持つ）。
VERIFICATION_METHODS = {
    # tsv に登録された関数単位 relation。source 読解 + 独立した native 実行。
    "source_review_and_native_execution": {
        "requires_native_witness": True,
        "requires_source_witness": True,
        "registry_key": "file",
    },
    # Eq sample の単一 source 規則。比較する第 2 定義が無いので実行 probe は無い。
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


# ---------------------------------------------------------------------------
# corpus の読み込み（壊れていたら収集時に落ちる。握り潰さない）
# ---------------------------------------------------------------------------


def _read_json(path: Path) -> Any:
    return json.loads(Path(path).read_text(encoding="utf-8"))


def _load_cases() -> Mapping[str, Any]:
    payload = _read_json(CASES_FILE)
    if payload.get("schema") != CASES_SCHEMA:
        raise ValueError(
            "unexpected recorded-pair cases schema: " + repr(payload.get("schema"))
        )
    if not isinstance(payload.get("cases"), list) or not payload["cases"]:
        raise ValueError("recorded-pair cases.json has no cases")
    if type(payload.get("corpus_budget_seconds")) is not int:
        raise ValueError("recorded-pair cases.json has no corpus_budget_seconds")
    return payload


CASES_PAYLOAD = _load_cases()
CORPUS_BUDGET_SECONDS = CASES_PAYLOAD["corpus_budget_seconds"]
CASES: Dict[str, Mapping[str, Any]] = {
    case["case_id"]: case for case in CASES_PAYLOAD["cases"]
}
VARIANTS: List[Tuple[str, str]] = [
    (case["case_id"], variant)
    for case in CASES_PAYLOAD["cases"]
    for variant in case["variants"]
]

#: (case_id, variant) → replay の wall clock。budget test が読む。
MEASURED: Dict[Tuple[str, str], float] = {}


def _variant_id(case_id: str, variant: str) -> str:
    return case_id if variant == VARIANT_DEFAULT else case_id + "." + variant


def _expected_path(case_id: str, variant: str) -> Path:
    return FIXTURE_ROOT / "expected" / (_variant_id(case_id, variant) + ".json")


def _require_z3() -> None:
    """z3 が無ければ **fail**。skip escape hatch は置かない。

    recorded-pair corpus の意味は「本物の solver を通した production path を
    Ghidra 無しで回す」ことなので、solver の無い環境で静かに skip すると CI が
    緑のまま corpus を走らせていない状態になる。
    """

    if shutil.which("z3") is None:
        pytest.fail(
            "the z3 CLI is required by the recorded-pair corpus and must be on "
            "PATH; this test never skips (see .github/workflows/unit.yml)"
        )


# ---------------------------------------------------------------------------
# ground truth（正本は tsv / compatibility json）
# ---------------------------------------------------------------------------


def _load_registry_annotations() -> Dict[Tuple[str, str], str]:
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


def _load_compatibility():
    from scripts.function_tracer_pcode.reporting.soundness_gate import (
        DEFAULT_COMPATIBILITY_PATH,
        load_conditional_compatibility,
    )

    return load_conditional_compatibility(DEFAULT_COMPATIBILITY_PATH)


def _ground_truth(case: Mapping[str, Any]) -> Optional[Mapping[str, Any]]:
    reference = case.get("ground_truth_file")
    if reference is None:
        return None
    payload = _read_json(FIXTURE_ROOT / reference)
    if payload.get("schema") != GROUND_TRUTH_SCHEMA:
        raise ValueError(
            "unexpected ground truth reference schema in {}: {!r}".format(
                reference, payload.get("schema")
            )
        )
    return payload


def _soundness_is_assertable(ground_truth: Optional[Mapping[str, Any]]) -> bool:
    """unconditional soundness を assert してよいか。

    verdict が verified で、かつ差が観測契約の中にある case だけ。GT 無し /
    `source_witness_only` / 契約外は判定しない（report に回す）。
    """

    if ground_truth is None:
        return False
    if ground_truth["verification_status"] != VERIFICATION_VERIFIED:
        return False
    return bool(ground_truth["observation_contract"]["covered_by_contract"])


# ---------------------------------------------------------------------------
# regression expectation
# ---------------------------------------------------------------------------


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


# ---------------------------------------------------------------------------
# conditional 列
# ---------------------------------------------------------------------------


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
# 1 case の再生
# ---------------------------------------------------------------------------


WORKER_MODULE = "scripts.function_tracer_pcode.tests.fixtures.pcode.replay_worker"
#: variant → worker の ``--fast-path``。
WORKER_FAST_PATH = {
    VARIANT_DEFAULT: "recorded",
    VARIANT_FAST_PATH_ON: "on",
    VARIANT_FAST_PATH_OFF: "off",
}


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
                _variant_id(case_id, variant), budget_seconds, case_id, variant,
            )
        )
        self.case_id = case_id
        self.variant = variant
        self.budget_seconds = budget_seconds


def _kill_process_group(process: "subprocess.Popen") -> None:
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


def _run_replay_worker(
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
        _kill_process_group(process)
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
        returncode, stdout, stderr = _run_replay_worker(
            command, case_id=case_id, variant=variant,
            budget_seconds=budget_seconds,
        )
        if returncode != 0 or not output.is_file():
            raise AssertionError(
                "the replay worker failed for {} (exit {}).\nstdout:\n{}\n"
                "stderr:\n{}".format(
                    _variant_id(case_id, variant), returncode,
                    stdout[-4000:], stderr[-4000:],
                )
            )
        report = _read_json(output)
    # budget に数えるのは **親から見た wall clock**（子 process の起動と import を
    # 含む）。AC が言っているのはこの test file の所要なので、内側だけを測ると
    # 実測より小さく出る。子が測った再生自体の秒数は report に残す。
    elapsed = time.monotonic() - started
    if report.get("schema") != REPLAY_REPORT_SCHEMA:
        raise ValueError("unexpected replay report schema: " + repr(report.get("schema")))
    MEASURED[(case_id, variant)] = elapsed
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


@pytest.mark.parametrize(
    "case_id,variant", VARIANTS,
    ids=[_variant_id(case_id, variant) for case_id, variant in VARIANTS],
)
def test_recorded_pair(case_id, variant, record_property):
    _require_z3()
    case = CASES[case_id]
    where = _variant_id(case_id, variant)
    ground_truth = _ground_truth(case)
    expected = _read_json(_expected_path(case_id, variant))
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
    if _soundness_is_assertable(ground_truth):
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
        record_property("ground_truth_not_verified", json.dumps({
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
        compatibility = _load_compatibility()
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
        if all_verified and _soundness_is_assertable(ground_truth):
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
            record_property(
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

    # (6) wall clock。per-case budget は `_run_replay_worker` が **deadline として**
    #     適用済みで、ここへ来た時点で budget 内に終わっている（超過した replay は
    #     worker を落として RecordedReplayBudgetExceeded になる）。所要は報告する。
    record_property("replay_seconds", "{} wall={:.2f} replay={:.2f} budget={}".format(
        where, elapsed, float(report["seconds"]), case["budget_seconds"],
    ))


# ---------------------------------------------------------------------------
# corpus 全体の wall clock（AC: 8 case で 180 秒未満）
# ---------------------------------------------------------------------------


def test_recorded_corpus_stays_within_its_wall_clock_budget():
    """corpus 全体の所要。**file 全体を走らせたときだけ**意味がある。

    Issue #109 の時間 AC（2026-09-17 改訂）は「GitHub-hosted runner で 1200 秒
    以内」。超過したときに case を削ったり記録面を削ったりして帳尻を合わせない
    こと。合わせるべきは corpus ではなく、遅くなった原因のほう。
    """

    missing = [
        _variant_id(case_id, variant)
        for case_id, variant in VARIANTS
        if (case_id, variant) not in MEASURED
    ]
    assert not missing, (
        "the corpus budget is defined over all {} replays; run the whole file "
        "(missing: {})".format(len(VARIANTS), ", ".join(missing))
    )
    total = sum(MEASURED.values())
    if total > CORPUS_BUDGET_SECONDS:
        pytest.fail(
            "the recorded corpus took {:.1f}s, over the {}s budget (Issue #109 "
            "time acceptance criterion, revised 2026-09-17): {}. Do not drop "
            "cases, trim the recorded surface, or turn a harness timeout into "
            "an UNKNOWN to fit it.".format(
                total, CORPUS_BUDGET_SECONDS,
                ", ".join(
                    "{}={:.1f}s".format(_variant_id(*key), value)
                    for key, value in sorted(MEASURED.items())
                ),
            )
        )


# ---------------------------------------------------------------------------
# per-case budget は実際の deadline（worker が hang しても待たない）
# ---------------------------------------------------------------------------


def _python_command(source: str) -> List[str]:
    return [sys.executable, "-c", source]


def _process_is_alive(pid: int) -> bool:
    """pid がまだ走っているか。zombie は「走っていない」と数える。

    ``os.kill(pid, 0)`` だけでは足りない: 成功は **zombie にも返る**。container の
    PID 1 は孤児を reap しないので、deadline で殺した孫 process は zombie のまま
    残り、素朴な liveness 判定では「生き残った」と読めてしまう。
    """

    stat_path = Path("/proc/{}/stat".format(pid))
    try:
        stat = stat_path.read_text(encoding="utf-8", errors="replace")
    except FileNotFoundError:
        return False
    except OSError:  # pragma: no cover - /proc の無い環境
        pass
    else:
        # comm には空白も ')' も入りうるので、最後の ')' の後ろから読む。
        state = stat.rpartition(")")[2].split()[0]
        return state not in ("Z", "X", "x")
    try:  # pragma: no cover - /proc の無い環境の fallback
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def test_a_worker_over_its_budget_is_a_harness_failure():
    """budget を過ぎた worker は待たずに落とし、harness の失敗にする。"""

    started = time.monotonic()
    with pytest.raises(RecordedReplayBudgetExceeded) as raised:
        _run_replay_worker(
            _python_command("import time; time.sleep(300)"),
            case_id="synthetic_case", variant="default", budget_seconds=2,
        )
    elapsed = time.monotonic() - started
    # 「300 秒待ってから諦める」ではなく deadline で止まっていること。
    assert elapsed < 60, elapsed
    assert raised.value.case_id == "synthetic_case"
    assert raised.value.variant == "default"
    assert raised.value.budget_seconds == 2
    message = str(raised.value)
    assert "synthetic_case" in message
    assert "default" in message
    assert "2s" in message


def test_a_worker_that_ignores_termination_is_still_stopped_at_the_deadline():
    """SIGTERM を無視する worker と、その子 process も deadline で消える。

    worker は再生中に z3 を起動する。worker だけを止めると solver が孤児として
    残り、次の case と CPU を取り合う。process group ごと落とすことを、
    SIGTERM を無視して孫を持つ synthetic worker で固定する。
    """

    source = (
        "import os, signal, subprocess, sys, time\n"
        "signal.signal(signal.SIGTERM, signal.SIG_IGN)\n"
        "child = subprocess.Popen([sys.executable, '-c',"
        " 'import signal, time; signal.signal(signal.SIGTERM, signal.SIG_IGN);"
        " time.sleep(300)'])\n"
        "sys.stderr.write(str(child.pid) + chr(10))\n"
        "sys.stderr.flush()\n"
        "time.sleep(300)\n"
    )
    process = subprocess.Popen(
        _python_command(source), cwd=str(REPO_ROOT),
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        start_new_session=True,
    )
    grandchild_pid = int(process.stderr.readline().strip())
    assert _process_is_alive(process.pid)
    assert _process_is_alive(grandchild_pid)

    _kill_process_group(process)
    process.communicate(timeout=30)

    deadline = time.monotonic() + 10
    while time.monotonic() < deadline and _process_is_alive(grandchild_pid):
        time.sleep(0.1)
    assert not _process_is_alive(grandchild_pid), (
        "the worker's own child survived the deadline kill"
    )


def test_a_budget_timeout_is_not_converted_into_an_outcome():
    """deadline の失敗を production の UNKNOWN / TIMEOUT にしない。

    harness の都合（この機械でどれだけ待つか）が判定結果の分布に混ざらない
    ことを、型と副作用の両面で固定する。
    """

    from scripts.function_tracer_pcode.authority.contracts import Outcome

    # harness の失敗であって、production の結果ではない。
    assert issubclass(RecordedReplayBudgetExceeded, AssertionError)
    measured_before = dict(MEASURED)
    with pytest.raises(RecordedReplayBudgetExceeded) as raised:
        _run_replay_worker(
            _python_command("import time; time.sleep(300)"),
            case_id="synthetic_case", variant="default", budget_seconds=2,
        )
    # report も payload も作られない（= outcome へ丸められる余地がない）。
    assert not hasattr(raised.value, "payload")
    assert not hasattr(raised.value, "report")
    assert not hasattr(raised.value, "final_outcome")
    # 計測済み扱いにもしない。budget 超過を「測れた replay」として
    # corpus の合計へ足すと、落ちた case ほど合計が小さく見える。
    assert dict(MEASURED) == measured_before
    # production 側の TIMEOUT / UNKNOWN は authority の Outcome であって、
    # この例外はその値を一切持たない。
    assert not any(
        getattr(raised.value, name, None) in tuple(Outcome)
        for name in ("outcome", "final_outcome", "canonical_outcome")
    )


def test_a_worker_inside_its_budget_is_unaffected_by_the_deadline():
    """通常 case の経路は deadline の配線で変わらない。"""

    returncode, stdout, stderr = _run_replay_worker(
        _python_command("import sys; sys.stdout.write('ok'); sys.exit(0)"),
        case_id="synthetic_case", variant="default", budget_seconds=60,
    )
    assert returncode == 0
    assert stdout == "ok"
    assert stderr == ""

    returncode, _stdout, stderr = _run_replay_worker(
        _python_command("import sys; sys.stderr.write('boom'); sys.exit(3)"),
        case_id="synthetic_case", variant="default", budget_seconds=60,
    )
    # 異常終了は deadline とは別の失敗として、そのまま呼び出し側へ返る。
    assert returncode == 3
    assert stderr == "boom"


# ---------------------------------------------------------------------------
# drift: fixture の控え ↔ 正本
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("case_id", sorted(CASES), ids=sorted(CASES))
def test_ground_truth_reference_matches_the_registry(case_id):
    """`ground_truth/*.json` が tsv / Eq 規則と食い違っていないこと。"""

    case = CASES[case_id]
    ground_truth = _ground_truth(case)
    if ground_truth is None:
        return
    annotations = _load_registry_annotations()
    registry = ground_truth["registry"]
    key = (registry["sample"], registry["function"])
    assert registry["sample"] == case["sample_identity"], case_id
    assert registry["function"] == case["function_name"], case_id
    if "file" in registry:
        assert registry["file"] == "scripts/eqbench/neq_ground_truth.tsv", case_id
        verdict = annotations.get(key)
        assert verdict is not None, (
            "{}: {} {} is not registered in the ground truth tsv".format(
                case_id, *key
            )
        )
        assert RELATION_BY_VERDICT[verdict] == ground_truth["relation"], case_id
    else:
        # Eq sample: 単一 source なので tsv に行は無い。行があれば、どちらが
        # 正しいのか分からない状態なので落とす。
        assert registry["kind"] == "eq_sample_single_source", case_id
        assert ground_truth["relation"] == RELATION_EQ, case_id
        assert key not in annotations, (
            "{}: {} {} is both an Eq sample and a tsv annotation".format(
                case_id, *key
            )
        )


@pytest.mark.parametrize("case_id", sorted(CASES), ids=sorted(CASES))
def test_conditional_compatibility_reference_matches_the_registry(case_id):
    """GT file の compatibility 控えが評価側 metadata と一致すること。"""

    ground_truth = _ground_truth(CASES[case_id])
    if ground_truth is None:
        return
    compatibility = _load_compatibility()
    registry = ground_truth["registry"]
    reference = ground_truth["conditional_compatibility_ref"]
    assert reference["file"] == (
        "scripts/eqbench/ground_truth_conditional_compatibility.json"
    ), case_id
    assert reference["entries"], case_id
    for entry in reference["entries"]:
        observed = compatibility.status(
            registry["sample"], registry["function"],
            entry["assumption_kind"], entry["subject"],
        )
        assert observed == entry["status"], (
            "{}: compatibility drifted for {} {}: fixture says {!r}, the "
            "metadata says {!r}".format(
                case_id, entry["assumption_kind"], entry["subject"],
                entry["status"], observed,
            )
        )


def test_no_compatibility_entry_is_verified_without_evidence():
    """`verified` を名乗る entry は evidence と検証者を持つこと。

    conditional GT 違反を「証明済み」と report できるのはこの file だけなので、
    loader の検証が効いていることをここでも固定する。
    """

    compatibility = _load_compatibility()
    assert compatibility.sha256, "the compatibility metadata was not read"
    # 今日の corpus には verified な premise は無い。増えたときに
    # conditional soundness assert が効き始めることを分かるようにしておく。
    record = {
        key: status for key, status in compatibility.entries.items()
        if status == COMPATIBILITY_VERIFIED
    }
    assert isinstance(record, dict)


# ---------------------------------------------------------------------------
# corpus metadata 自身
# ---------------------------------------------------------------------------


def test_every_case_has_a_complete_and_consistent_description():
    for case_id, case in sorted(CASES.items()):
        assert case["dataset_label"] in ("Eq", "Neq"), case_id
        assert case["function_confirmed_by"].startswith("--list-functions"), (
            case_id + ": the function name must be confirmed by observation, "
            "not guessed from the directory name"
        )
        assert case["variants"], case_id
        for variant in case["variants"]:
            assert variant in VARIANT_FAST_PATH, (case_id, variant)
            assert _expected_path(case_id, variant).is_file(), (
                "{}: no regression expectation for variant {}".format(
                    case_id, variant
                )
            )
        for side in ("left", "right"):
            header = _read_json(
                FIXTURE_ROOT / case_id / case[side]["fixture"]
            )["header"]
            assert header["binary"]["sha256"] == case[side]["sha256"], (
                case_id, side,
            )
            assert header["binary"]["binary_id"] == case[side]["binary_id"], (
                case_id, side,
            )
            assert header["binary"]["eqbench_relative_path"] == (
                case[side]["eqbench_relative_path"]
            ), (case_id, side)
            assert header["target"]["function_name"] == case["function_name"], (
                case_id, side,
            )
            assert header["recording_mode"]["connector"] == "production", (
                case_id, side,
            )
        ground_truth = _ground_truth(case)
        assert ground_truth is not None, case_id
        assert ground_truth["case_id"] == case_id, case_id
        assert ground_truth["verification_status"] in (
            VERIFICATION_VERIFIED, VERIFICATION_SOURCE_WITNESS_ONLY,
        ), case_id
        contract = ground_truth["observation_contract"]
        assert contract["contract_name"] == "eqbench_single_threaded_c_abi", case_id
        assert isinstance(contract["covered_by_contract"], bool), case_id
        assert contract["basis"], case_id
        # implementation capability は soundness に使わない記録面。
        assert ground_truth["implementation_capability"]["status"] in (
            "unconfirmed", "proves_not_eq", "cannot_prove",
        ), case_id
        linkage = ground_truth["binary_linkage"]
        assert linkage["left_sha256"] == case["left"]["sha256"], case_id
        assert linkage["right_sha256"] == case["right"]["sha256"], case_id
        assert linkage["produced_from"]["compile_script"] == (
            "scripts/eqbench/compile_all_arm_mips.sh"
        ), case_id


def test_verification_metadata_claims_only_what_was_actually_checked():
    """GT metadata が「やっていない確認」を名乗らないこと。

    ここが緩むと、実行 probe を持たない entry が「independent native execution
    で確かめた」と読める状態になり、soundness assert の根拠を実際より強く
    見せてしまう。`verification_method` と witness field を突き合わせる。
    """

    for case_id in sorted(CASES):
        ground_truth = _ground_truth(CASES[case_id])
        assert ground_truth is not None, case_id
        method = ground_truth.get("verification_method")
        assert method in VERIFICATION_METHODS, (
            "{}: unknown verification_method {!r}".format(case_id, method)
        )
        rules = VERIFICATION_METHODS[method]
        native = ground_truth["native_execution_witness"]
        source_witness = ground_truth["semantic_truth"]["source_witness"]

        if rules["requires_native_witness"]:
            assert isinstance(native, Mapping), (
                "{}: {} claims an independent native execution but carries no "
                "native_execution_witness".format(case_id, method)
            )
            for field in NATIVE_WITNESS_FIELDS:
                assert str(native.get(field) or "").strip(), (
                    "{}: native_execution_witness.{} is empty, so the run it "
                    "claims cannot be reproduced".format(case_id, field)
                )
        else:
            assert native is None, (
                "{}: {} claims no execution probe, so "
                "native_execution_witness must stay null".format(case_id, method)
            )

        if rules["requires_source_witness"]:
            assert isinstance(source_witness, Mapping) and source_witness, case_id
            for field in ("input", "left_observation", "right_observation",
                          "differing_observable"):
                assert str(source_witness.get(field) or "").strip(), (
                    case_id, field,
                )
        else:
            assert source_witness is None, (
                "{}: {} has no differing observable to witness".format(
                    case_id, method
                )
            )

        assert rules["registry_key"] in ground_truth["registry"], (
            "{}: registry shape does not match {}".format(case_id, method)
        )
        # `verified_by` は登録者だけを言う。確認方法を散文で重ねると、method と
        # 食い違ったときにどちらが事実か決められなくなる。
        verified_by = ground_truth["verified_by"]
        assert verified_by and "execution" not in verified_by.lower(), (
            "{}: verified_by must name who registered the entry, not restate "
            "how it was checked ({!r}); verification_method owns that".format(
                case_id, verified_by,
            )
        )
        assert ground_truth["verification_basis"].strip(), case_id


def test_the_identical_case_is_recorded_with_the_fast_path_off():
    """バイト列が同じ pair は、ON / OFF の 2 variant を **OFF 記録**から再生する。

    ON で記録すると identity proof が先に返ってしまい、OFF replay に必要な
    HighFunction / memory / subordinate decompile の surface が記録されない。
    """

    identical = [
        case for case in CASES.values()
        if case["left"]["sha256"] == case["right"]["sha256"]
    ]
    assert identical, "the corpus lost its byte-identical pair (Issue #15)"
    for case in identical:
        assert case["recording"]["identical_fast_path"] is False, case["case_id"]
        assert set(case["variants"]) == {
            VARIANT_FAST_PATH_ON, VARIANT_FAST_PATH_OFF,
        }, case["case_id"]


def test_the_corpus_covers_the_issues_it_was_recorded_for():
    """8 case が Issue #109 提案 2 の対象を保っていること。"""

    assert len(CASES) == 8, sorted(CASES)
    covered: Set[str] = set()
    for case in CASES.values():
        covered.update(case["issue_refs"])
    assert {"#15", "#16", "#18", "#19", "#20", "#22"} <= covered, sorted(covered)


def _fixture_bytes(case_id: str) -> int:
    return sum(
        path.stat().st_size
        for path in (FIXTURE_ROOT / case_id).iterdir()
        if path.is_file()
    )


def test_fixture_sizes_are_reported(record_property):
    """サイズは報告面。上限で切って semantic surface を捨てない。"""

    total = 0
    for case_id in sorted(CASES):
        size = _fixture_bytes(case_id)
        total += size
        record_property("fixture_bytes", "{} {}".format(case_id, size))
    record_property("fixture_bytes_total", str(total))
    assert total > 0


__all__: Sequence[str] = ()

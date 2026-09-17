# -*- coding: utf-8 -*-
"""記録済み corpus の **安い契約**（Issue #109）。replay は 1 件も走らせない。

ここにあるのは fixture を読むだけ / process を 1 つ起こすだけで終わる検査で、
PR ごとの `unit-fast` job が持つ:

* ground truth の控えが正本（tsv / compatibility json）と食い違わないこと
* verification metadata が「実際にやった確認」だけを名乗ること
* corpus が 1 つの clean な frozen tree から記録されていること
* case manifest の整合（fixture header との一致、variant、GT 参照）
* PR gate の選択が manifest で明示され、full corpus から何も落ちていないこと
* per-case budget が**実際の deadline** として効くこと（synthetic worker）

重い 8 case / 9 replay の実行は `test_recorded_pairs.py` が持つ。
"""

from __future__ import annotations

import ast
import importlib
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, List, Mapping, Sequence, Set, cast

pytest = cast(Any, importlib.import_module("pytest"))

from scripts.function_tracer_pcode.tests.fixtures.pcode.corpus import (
    ALL_REPLAYS,
    CASES,
    FIXTURE_ROOT,
    PR_GATE_REPLAYS,
    TIER_FULL,
    TIER_PR_GATE,
    VARIANT_FAST_PATH,
    VARIANT_FAST_PATH_OFF,
    VARIANT_FAST_PATH_ON,
    CorpusContractViolation,
    ReplayRecord,
    select_replays,
    validate_corpus,
)
from scripts.function_tracer_pcode.tests.fixtures.pcode.replay_validation import (
    COMPATIBILITY_VERIFIED,
    kill_process_group,
    NATIVE_WITNESS_FIELDS,
    RELATION_BY_VERDICT,
    RELATION_EQ,
    RecordedReplayBudgetExceeded,
    VERIFICATION_METHODS,
    VERIFICATION_SOURCE_WITNESS_ONLY,
    VERIFICATION_VERIFIED,
    expected_path,
    ground_truth_of,
    load_compatibility,
    load_registry_annotations,
    read_json,
    run_replay_worker,
)

REPO_ROOT = Path(__file__).resolve().parents[4]

_read_json = read_json
_ground_truth = ground_truth_of
_load_compatibility = load_compatibility
_load_registry_annotations = load_registry_annotations
_expected_path = expected_path
_run_replay_worker = run_replay_worker


# ---------------------------------------------------------------------------
# PR gate の選択（manifest が正本。test 名の文字列には依存しない）
# ---------------------------------------------------------------------------


def test_the_pr_gate_subset_is_declared_in_the_manifest():
    """どの replay を PR gate で走らせるかが `cases.json` に書いてあること。"""

    for spec in ALL_REPLAYS:
        assert isinstance(spec.pr_gate, bool), spec.variant_id
    gate = {spec.variant_id for spec in PR_GATE_REPLAYS}
    assert gate, "the PR gate would run no replay at all"
    assert gate == {spec.variant_id for spec in select_replays(tier=TIER_PR_GATE)}
    assert select_replays(tier=TIER_FULL) == ALL_REPLAYS


def test_no_case_is_dropped_from_the_full_corpus():
    """PR gate から外した case が full corpus からも消えていないこと。

    gate を軽くするのは実行時期の話で、回帰の範囲の話ではない。外した case が
    どこでも走らなくなっていたら、それは corpus を縮めたのと同じ。
    """

    full = {spec.variant_id for spec in select_replays(tier=TIER_FULL)}
    gate = {spec.variant_id for spec in PR_GATE_REPLAYS}
    outside = full - gate
    assert outside, (
        "every replay is in the PR gate; recorded-full would then add nothing"
    )
    # gate 外の replay も full には必ず居る（= full は gate の上位集合）。
    assert gate < full
    assert len(full) == sum(len(case["variants"]) for case in CASES.values())
    # gate 外は「重いから外した」ものだけ。budget が最大の 2 件と一致する。
    heaviest = sorted(
        CASES.values(), key=lambda case: -case["budget_seconds"],
    )[:len(outside)]
    assert {case["case_id"] for case in heaviest} == {
        spec.case_id for spec in ALL_REPLAYS if spec.variant_id in outside
    }, (
        "the replays left out of the PR gate are not the slow ones, so the "
        "split is not doing what it claims"
    )


#: 実際に再生を走らせる test を持つ module と、その中で再生を起動する呼び出し。
#: marker の付け忘れを名前の綴りではなく **呼び出しの有無**で検出する。
REPLAY_ENTRY_POINTS = {
    "test_recorded_program_roundtrip.py": "_replay",
    "test_recorded_pairs.py": "validate_replay",
}
RECORDED_REPLAY_MARKER = "recorded_replay"


def _module_marks(module: ast.Module) -> Set[str]:
    """module-level `pytestmark` が立てている marker 名。"""

    names: Set[str] = set()
    for node in module.body:
        if not isinstance(node, ast.Assign):
            continue
        if not any(
            isinstance(target, ast.Name) and target.id == "pytestmark"
            for target in node.targets
        ):
            continue
        for attribute in ast.walk(node.value):
            if isinstance(attribute, ast.Attribute):
                names.add(attribute.attr)
    return names


def _decorator_marks(function: ast.FunctionDef) -> Set[str]:
    names: Set[str] = set()
    for decorator in function.decorator_list:
        for attribute in ast.walk(decorator):
            if isinstance(attribute, ast.Attribute):
                names.add(attribute.attr)
    return names


@pytest.mark.parametrize("module_name", sorted(REPLAY_ENTRY_POINTS))
def test_every_test_that_runs_a_replay_carries_the_marker(module_name):
    """再生を走らせる test には必ず `recorded_replay` が付いていること。

    付いていない test は `unit-fast` で走ってしまい、重い実 replay が PR の
    critical path に戻る。判定は名前ではなく **再生の起動を呼んでいるか**で
    行うので、test を足しても綴りに依存しない。
    """

    path = Path(__file__).resolve().parent / module_name
    module = ast.parse(path.read_text(encoding="utf-8"))
    entry_point = REPLAY_ENTRY_POINTS[module_name]
    module_marks = _module_marks(module)

    runs_a_replay = []
    for node in module.body:
        if not isinstance(node, ast.FunctionDef):
            continue
        if not node.name.startswith("test_"):
            continue
        calls = {
            call.func.id
            for call in ast.walk(node)
            if isinstance(call, ast.Call) and isinstance(call.func, ast.Name)
        }
        if entry_point in calls:
            runs_a_replay.append(node)

    assert runs_a_replay, (
        "{}: no test calls {}(); the detector would pass vacuously".format(
            module_name, entry_point
        )
    )
    unmarked = [
        node.name for node in runs_a_replay
        if RECORDED_REPLAY_MARKER not in (_decorator_marks(node) | module_marks)
    ]
    assert not unmarked, (
        "{}: these tests run a real replay but carry no {} marker, so the "
        "per-PR unit-fast job would run them: {}".format(
            module_name, RECORDED_REPLAY_MARKER, ", ".join(sorted(unmarked))
        )
    )


def test_a_replay_test_cannot_skip_itself_when_z3_is_missing():
    """再生 test が z3 の不在を skip で逃がしていないこと。

    `skipif` で逃がすと、solver の無い環境で「E2E を飛ばしたから green」に
    なる。corpus と同じく fail-closed でなければならない。
    """

    for module_name in sorted(REPLAY_ENTRY_POINTS):
        path = Path(__file__).resolve().parent / module_name
        module = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(module):
            if not isinstance(node, ast.FunctionDef):
                continue
            marks = _decorator_marks(node)
            assert "skipif" not in marks and "skip" not in marks, (
                "{}::{} skips instead of failing; z3 must be required, not "
                "optional".format(module_name, node.name)
            )


def test_selecting_a_replay_that_does_not_exist_fails_closed():
    """matrix が間違った id を渡したら、0 件成功にせず落とすこと。"""

    with pytest.raises(Exception) as raised:
        select_replays(variant_ids=("no_such_replay",))
    assert "no such recorded replay" in str(raised.value)


# ---------------------------------------------------------------------------
# corpus 集計契約（実装は corpus.validate_corpus 1 箇所。ここは規則の固定）
# ---------------------------------------------------------------------------


def _record(spec, seconds=1.0, outcome="passed"):
    return ReplayRecord(
        case_id=spec.case_id, variant=spec.variant, seconds=seconds,
        outcome=outcome,
    )


def test_the_corpus_aggregate_rejects_a_missing_result():
    full = select_replays(tier=TIER_FULL)
    records = [_record(spec) for spec in full[:-1]]
    with pytest.raises(CorpusContractViolation) as raised:
        validate_corpus(records, expected=full)
    assert "produced no result" in str(raised.value)
    assert full[-1].variant_id in str(raised.value)


def test_the_corpus_aggregate_rejects_a_duplicate_result():
    full = select_replays(tier=TIER_FULL)
    records = [_record(spec) for spec in full] + [_record(full[0])]
    with pytest.raises(CorpusContractViolation) as raised:
        validate_corpus(records, expected=full)
    assert "more than once" in str(raised.value)


def test_the_corpus_aggregate_rejects_a_failed_shard():
    full = select_replays(tier=TIER_FULL)
    records = [_record(spec) for spec in full]
    records[0] = _record(full[0], outcome="failed")
    with pytest.raises(CorpusContractViolation) as raised:
        validate_corpus(records, expected=full)
    assert "did not pass" in str(raised.value)


def test_the_corpus_aggregate_rejects_an_unexpected_result():
    full = select_replays(tier=TIER_FULL)
    records = [_record(spec) for spec in full]
    records.append(ReplayRecord("ghost_case", "default", 1.0, "passed"))
    with pytest.raises(CorpusContractViolation) as raised:
        validate_corpus(records, expected=full)
    assert "not expected" in str(raised.value)


def test_the_corpus_budget_is_the_sum_of_the_replay_times():
    """予算は各 replay の測定時間の**合計**。並列実行の wall-clock ではない。

    matrix にすると workflow の所要は短くなるが、Issue #109 の時間 AC が
    意味するものは変わらない。ここを wall-clock に読み替えると、並列度を
    上げるだけで AC を満たせてしまう。
    """

    full = select_replays(tier=TIER_FULL)
    each = 10.0
    records = [_record(spec, seconds=each) for spec in full]
    budget = int(each * len(full)) - 1
    with pytest.raises(CorpusContractViolation) as raised:
        validate_corpus(records, expected=full, budget_seconds=budget)
    message = str(raised.value)
    assert "over the {}s budget".format(budget) in message
    assert "sum of the replay times" in message
    # 合計が予算ちょうどなら通る（境界を緩める方向へ倒さない）。
    validate_corpus(records, expected=full, budget_seconds=int(each * len(full)))


def test_the_corpus_aggregate_reports_every_replay():
    full = select_replays(tier=TIER_FULL)
    lines = validate_corpus([_record(spec) for spec in full], expected=full)
    body = "\n".join(lines)
    for spec in full:
        assert spec.variant_id in body, spec.variant_id
    assert "TOTAL" in body


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

    kill_process_group(process)
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
    records_before = list(ALL_REPLAYS)
    with pytest.raises(RecordedReplayBudgetExceeded) as raised:
        _run_replay_worker(
            _python_command("import time; time.sleep(300)"),
            case_id="synthetic_case", variant="default", budget_seconds=2,
        )
    # report も payload も作られない（= outcome へ丸められる余地がない）。
    assert not hasattr(raised.value, "payload")
    assert not hasattr(raised.value, "report")
    assert not hasattr(raised.value, "final_outcome")
    # 計測済み扱いにもしない。budget 超過を「測れた replay」として corpus の
    # 合計へ足すと、落ちた case ほど合計が小さく見える。deadline を踏んだ
    # replay は ReplayRecord を返さないので、集計にも artifact にも現れない。
    assert list(ALL_REPLAYS) == records_before
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


def test_the_corpus_was_recorded_from_one_clean_source_tree():
    """8 case が同じ clean な source tree から記録されていること。

    `recording_dirty=true` の fixture は「どの source から取ったか」が
    commit だけでは決まらない。corpus を 1 case ずつ記録すると、先に書いた
    fixture 自身が tree を汚して 2 件目以降が dirty になるので、記録出力は
    repo の外へ出し、全 case を 1 つの凍結した tree から取る。
    """

    recordings = set()
    for case_id in sorted(CASES):
        case = CASES[case_id]
        recording = case["recording"]
        assert recording["dirty"] is False, (
            "{}: recorded from a dirty tree; re-record from a clean, frozen "
            "checkout with the output written outside the repository".format(
                case_id
            )
        )
        assert len(recording["commit"]) == 40, case_id
        assert len(recording["analysis_source_digest"]) == 64, case_id
        recordings.add(
            (recording["commit"], recording["analysis_source_digest"])
        )
        for side in ("left", "right"):
            header = _read_json(
                FIXTURE_ROOT / case_id / case[side]["fixture"]
            )["header"]
            assert header["recording_dirty"] is False, (case_id, side)
            assert header["recording_commit"] == recording["commit"], (
                case_id, side,
            )
            assert header["analysis_source_digest"] == (
                recording["analysis_source_digest"]
            ), (case_id, side)
    assert len(recordings) == 1, (
        "the corpus was recorded from more than one source tree, so its "
        "fixtures cannot be reproduced from a single checkout: "
        + repr(sorted(recordings))
    )


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

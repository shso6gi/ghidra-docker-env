# -*- coding: utf-8 -*-
"""PR #278 review 4: 入力（meta・出力）の状態は 1 つの owner が分類し、破損を初回・開始前へ落とさない。

契約（期待値はここから導く。実装の表を写さない）:

* meta は「無い」「正常」「破損（読めない・形が違う・必須項目が不正・要約が条件と合わない）」
  の 3 つで、破損は初回にも「照合しない」にもしない。どの profile の条件でも ``start`` は
  何も書かずに拒否し（container を起動しない）、``summary`` は判定できない。
* 要求した条件・launch の記録・supervisor が実際に使う条件（``docker run`` の引数・環境・label・
  container の記録）は同じ要約。照合できなければ起動しない。
* 出力の確定した証跡（開始・issue・seal の記録）の欠損・破損・未知の entry は、wrapper の終了の
  記録の前でも後でも「開始前」にならず、退避も再開もしない。書きかけの残骸だけの出力は証拠を
  残して退避・再開できる。

本番の wrapper（fake docker）と本番の writer（``execution_chain`` の record_*、``ChainTree``）。
"""

from __future__ import annotations

import json
import os
from pathlib import Path

import pytest

import protocol
import records
import wrapper
from harness import COMMIT, PROFILE, Harness
from scripts.function_tracer_pcode.reporting.execution_identity import source_tree_digest
from scripts.function_tracer_pcode.tests.unit import test_execution_chain as fixture
from test_review3 import _refused_without_anything


@pytest.fixture
def h(tmp_path, monkeypatch):
    harness = Harness(tmp_path, monkeypatch)
    yield harness
    _cleanup(harness)


def _cleanup(harness):
    try:
        harness.update(lambda d: d.update({"fail": {}, "respond": {}}))
        harness.end_container(exit_code=137)
        harness.wait_released(timeout=60)
    except (OSError, ValueError, KeyError, AssertionError):
        pass


def _summary(h, capsys):
    capsys.readouterr()
    code = h.run("summary", "--json")
    return code, json.loads(capsys.readouterr().out)


# ---------------------------------------------------------------------------
# meta の破損 × profile の条件
# ---------------------------------------------------------------------------


def _drop(key):
    return lambda meta: meta.pop(key)


def _set(path, value):
    def change(meta):
        target = meta
        for key in path[:-1]:
            target = target[key]
        target[path[-1]] = value
    return change


def _resummarize(change):
    """条件を書き換え、fingerprint をそれに合わせて付け直す（形は正しいが別の評価の meta）。"""
    def apply(meta):
        change(meta)
        meta["fingerprint"] = records.fingerprint_of(meta["conditions"])
    return apply


META_DAMAGE = {
    "schema_missing": _drop("schema"),
    "schema_other": _set(("schema",), "eval-wrapper-meta-v0"),
    "conditions_missing": _drop("conditions"),
    "probe_missing": lambda meta: meta["conditions"].pop("probe"),
    "grace_not_an_integer": _set(("conditions", "container", "stop_grace_seconds"), "120"),
    "image_id_empty": _set(("conditions", "image", "id"), ""),
    "unknown_key": _set(("note",), "x"),
    # 条件と要約が食い違う（片方だけ書き換えた）。
    "fingerprint_of_other_conditions": _set(("fingerprint",), "eval-env-v1:" + "0" * 64),
    "conditions_edited_fingerprint_kept": _set(
        ("conditions", "profile", "values", "PARALLEL_JOBS"), "3"),
    # 要約は合うが、profile の値とそこから作った欄が食い違う。
    "profile_values_disagree": _resummarize(lambda meta: meta["conditions"]["container"].update(
        memory="48g", memory_swap="48g")),
    # 要約は合うが、別の出力先・別の matrix の条件。
    "another_output": _resummarize(
        _set(("conditions", "container_paths", "output"), "/workspace/logs/EqBench/other")),
    "another_matrix": _resummarize(_set(("conditions", "matrix"), "eq")),
}


def _damage_meta(h, damage):
    path = h.ev.wrapper / records.META
    if damage == "not_json":
        path.write_text("{not json")
    elif damage == "missing":
        path.unlink()
    else:
        meta = json.loads(path.read_text())
        META_DAMAGE[damage](meta)
        path.write_text(json.dumps(meta))


@pytest.mark.parametrize("profile", ["same", "changed"])
@pytest.mark.parametrize("damage", [*META_DAMAGE, "not_json", "missing"])
def test_a_damaged_meta_refuses_the_start_whatever_the_profile(h, capsys, damage, profile):
    h.finished_launch()
    assert records.read_meta(h.ev.wrapper, matrix="neq").state == records.META_VALID
    _damage_meta(h, damage)
    meta = records.read_meta(h.ev.wrapper, matrix="neq")
    assert meta.state == records.META_DAMAGED and meta.problems, damage
    if profile == "changed":
        h.profile.write_text(PROFILE.replace("PARALLEL_JOBS=2", "PARALLEL_JOBS=3"))
    err = _refused_without_anything(h, capsys, launches=1)
    assert "meta.json is damaged" in err
    code, result = _summary(h, capsys)
    assert code == 2 and result["meta_state"] == "damaged"
    assert "meta_invalid" in [r["code"] for r in result["reasons"]]
    capsys.readouterr()
    h.run("status")
    assert "DAMAGED: meta" in capsys.readouterr().out


def test_a_wrapper_dir_without_meta_is_not_a_first_start(h, capsys):
    h.ev.wrapper.mkdir(parents=True)
    (h.ev.wrapper / "notes").write_text("x")
    assert records.read_meta(h.ev.wrapper).state == records.META_DAMAGED
    err = _refused_without_anything(h, capsys, launches=0)
    assert "meta.json is missing" in err


def test_meta_damaged_while_the_launch_waits_for_its_supervisor_starts_nothing(h):
    """preflight の後・supervisor の前に meta が壊れた: supervisor は破損した meta で起動しない。"""
    mark = h.tmp / "crash.mark"
    h.cli("start", extra_env={"EVAL_TEST_CRASH": "start:supervise:before",
                              "EVAL_TEST_CRASH_MARK": str(mark)})
    assert mark.exists()
    _damage_meta(h, "schema_other")
    assert _supervise(h) == wrapper.EXIT_FAILED
    assert not [c for c in h.read_state()["calls"] if c[:2] == ["run", "-d"]]
    (launch,) = h.records().launches
    assert launch.exit_kind == records.KIND_NOT_STARTED and launch.terminal
    assert "launch_refused" in h.journal()


# ---------------------------------------------------------------------------
# 要求した条件・launch の記録・実際の起動が一致する
# ---------------------------------------------------------------------------


def _supervise(h) -> int:
    lock = wrapper.open_lock(h.ev)
    assert wrapper.try_lock(lock)
    return wrapper.main(["--matrix", "neq", "_supervise", "--freeze", COMMIT, "--launch", "1",
                         "--lock-fd", str(lock)])


def test_the_requested_conditions_are_the_ones_the_container_runs_with(h, capsys):
    h.profile.write_text(PROFILE.replace("PARALLEL_JOBS=2", "PARALLEL_JOBS=5"))
    assert h.start() == wrapper.EXIT_OK
    meta = records.read_meta(h.ev.wrapper, matrix="neq")
    assert meta.state == records.META_VALID
    conditions = meta.conditions
    expected = records.fingerprint_of(conditions)
    (run,) = h.detached_runs()
    launch_record = json.loads((h.ev.launch_dir(1) / records.LAUNCH).read_text())
    container_record = json.loads((h.ev.launch_dir(1) / records.CONTAINER).read_text())
    # 要約: meta・launch の要求・runner の環境・container の label・container の記録が同じ。
    assert meta.fingerprint == expected == launch_record["fingerprint"]
    assert run["env"]["EQBENCH_ENVIRONMENT_FINGERPRINT"] == expected
    assert run["labels"][wrapper.LABEL_FINGERPRINT] == expected
    assert container_record["fingerprint"] == expected
    # 中身: 要求した profile の値と資源上限が docker run の引数と環境そのもの。
    assert conditions["profile"]["values"]["PARALLEL_JOBS"] == "5"
    assert run["env"]["PARALLEL_JOBS"] == "5" and run["env"]["NEQ_RUN_SCOPE"] == "FULL_NEQ"
    assert run["memory"] == conditions["container"]["memory"] == "24g"
    assert run["memory_swap"] == conditions["container"]["memory_swap"] == "24g"
    assert run["stop_timeout"] == str(conditions["container"]["stop_grace_seconds"]) == "120"
    assert run["network"] == "none" and run["init"] is True
    assert run["user"] == conditions["container"]["user"] and run["image"] == conditions["image"]["id"]
    assert run["command"] == ["bash", conditions["runner"]]
    assert run["env"]["OUTPUT_BASE_DIR"] == conditions["container_paths"]["output"]
    h.end_container(exit_code=0)
    h.wait_released()
    _code, result = _summary(h, capsys)
    assert result["checks"]["conditions"]["status"] == "done"
    assert "launch_conditions_differ" not in [r["code"] for r in result["reasons"]]


def test_a_launch_requested_under_other_conditions_is_not_started(h):
    """launch の要求の条件と、この評価の条件（meta）が食い違う: supervisor は起動しない。"""
    mark = h.tmp / "crash.mark"
    h.cli("start", extra_env={"EVAL_TEST_CRASH": "start:supervise:before",
                              "EVAL_TEST_CRASH_MARK": str(mark)})
    path = h.ev.launch_dir(1) / records.LAUNCH
    payload = json.loads(path.read_text())
    payload["fingerprint"] = records.FINGERPRINT_PREFIX + "f" * 64
    path.write_text(json.dumps(payload))
    assert _supervise(h) == wrapper.EXIT_FAILED
    assert not [c for c in h.read_state()["calls"] if c[:2] == ["run", "-d"]]
    (launch,) = h.records().launches
    assert launch.exit_kind == records.KIND_NOT_STARTED


@pytest.mark.parametrize("record", ["launch", "container"])
def test_a_launch_that_ran_under_other_conditions_is_permanent(h, capsys, record):
    h.finished_launch()
    name = records.LAUNCH if record == "launch" else records.CONTAINER
    path = h.ev.launch_dir(1) / name
    payload = json.loads(path.read_text())
    payload["fingerprint"] = records.FINGERPRINT_PREFIX + "e" * 64
    path.write_text(json.dumps(payload))
    _code, result = _summary(h, capsys)
    reasons = {r["code"]: r["category"] for r in result["reasons"]}
    assert reasons.get("launch_conditions_differ") == "permanent", result["reasons"]
    err = _refused_without_anything(h, capsys, launches=1)
    assert "another --tag" in err


# ---------------------------------------------------------------------------
# 確定した証跡の欠損 × wrapper の終了の記録の前・後
# ---------------------------------------------------------------------------


def _tree(h):
    original = fixture.SOURCE
    fixture.SOURCE = source_tree_digest(wrapper.REPO)
    try:
        return fixture.ChainTree(h.ev.out)
    finally:
        fixture.SOURCE = original


def _start_execution(h, tree, run_id):
    fields = dict(environment_fingerprint=h.meta()["fingerprint"], git_commit=fixture_commit(),
                  git_dirty="0")
    original = fixture.SOURCE
    fixture.SOURCE = source_tree_digest(wrapper.REPO)
    try:
        tree.start(run_id, **fields)
    finally:
        fixture.SOURCE = original


def fixture_commit():
    from harness import repo_head

    return repo_head()


E1 = fixture._run_id(1)


def _lose_start(h, run_id):
    """manifest と開始の記録だけを消す（issue・seal などの確定した記録は残る）。"""
    (h.ev.out / "run_manifest.txt").unlink()
    (h.ev.out / ".executions" / run_id / records.START_RECORD).unlink()


DAMAGE = {
    # issue を確定した後に開始の記録が消えた（review 4 の時系列）。
    "issued_then_start_lost": lambda h, tree: (tree.leave_incomplete(E1, tree.pairs[0]),
                                               _lose_start(h, E1)),
    # 決定した pair（署名済み status）も残る。
    "decided_then_start_lost": lambda h, tree: (tree.decide(E1, tree.pairs[0]),
                                                _lose_start(h, E1)),
    # 確定した issue の記録が壊れた。
    "issue_corrupted": lambda h, tree: (tree.leave_incomplete(E1, tree.pairs[0]), [
        p.write_text("{") for p in (h.ev.out / ".executions" / E1 / "issued").iterdir()]),
    # .executions に未知の entry。
    "unknown_entry": lambda h, tree: (h.ev.out / ".executions" / "notes.txt").write_text("x"),
}


@pytest.mark.parametrize("damage", sorted(DAMAGE))
@pytest.mark.parametrize("when", ["before_exit_observed", "before_exit_unobserved", "after_exit"])
def test_lost_or_damaged_evidence_is_never_moved_aside_or_resumed(tmp_path, monkeypatch, capsys,
                                                                   damage, when):
    # 観測の間隔: 終了の前の欠損を、実行中に観測した場合と観測していない場合の両方で作る。
    h = Harness(tmp_path, monkeypatch, poll="60" if when == "before_exit_unobserved" else "0.2")
    try:
        assert h.start() == wrapper.EXIT_OK
        if when == "before_exit_unobserved":
            h.wait_for(lambda: (h.ev.launch_dir(1) / records.WATCH).exists(),
                       message="the first observation")
        tree = _tree(h)
        _start_execution(h, tree, E1)
        if when == "before_exit_observed":
            h.wait_for(lambda: any(E1 in (row.get("executions") or [])
                                   for row in records.read_launch(h.ev.launch_dir(1), 1).watch),
                       message="an observation of the execution")
        if when != "after_exit":
            DAMAGE[damage](h, tree)
        h.end_container(exit_code=137)
        h.wait_released()
        if when == "after_exit":
            DAMAGE[damage](h, tree)
        (launch,) = h.records().launches
        recorded = launch.exit["runtime_run_ids"]
        # 開始の記録が残る破損なら終了の時点の分類にも入る。開始の記録が消え、実行中にも観測して
        # いなければ記録に残らないが、出力の分類が破損として報告する（下）。
        lost_start = damage.endswith("start_lost")
        expected = [] if (when == "before_exit_unobserved" and lost_start) else [E1]
        assert recorded == expected, recorded
        assert records.classify_output(h.ev.out).state == protocol.OUTPUT_DAMAGED
        code, result = _summary(h, capsys)
        assert code == 2 and result["output_state"] == "damaged"
        assert "output_damaged" in [r["code"] for r in result["reasons"]]
        # 破損した出力でも検証器・ledger まで判定する（「開始前」の省略の経路に入らない）。
        assert result["checks"]["chain"]["status"] == "done"
        _refused_without_anything(h, capsys, launches=1)
    finally:
        _cleanup(h)


@pytest.mark.parametrize("evidence", ["debris_only", "committed_issue"])
def test_debris_is_recovered_and_committed_evidence_is_not(h, capsys, evidence):
    """同じ時系列（runner が開始の記録の前後で kill された）で、残ったものだけが違う対。"""
    assert h.start() == wrapper.EXIT_OK
    tree = _tree(h)  # 準備の file（pair-status-verification-key.json）
    (h.ev.out / "neq_source_pairs.tsv").write_text("S0\tx\ty\n")
    directory = h.ev.out / ".executions" / E1
    directory.mkdir(parents=True)
    (directory / ".run_manifest.start.txt.uncommitted-abc123").write_text("partial")
    if evidence == "committed_issue":
        _start_execution(h, tree, E1)
        tree.leave_incomplete(E1, tree.pairs[0])
        _lose_start(h, E1)
    h.end_container(exit_code=137)
    h.wait_released()
    before = h.snapshot()
    if evidence == "debris_only":
        assert records.classify_output(h.ev.out).state == protocol.OUTPUT_NEVER_STARTED
        assert h.start() == wrapper.EXIT_OK
        launch2 = json.loads((h.ev.launch_dir(2) / records.LAUNCH).read_text())
        aside = Path(launch2["moved_aside_output"])
        assert (aside / ".executions" / E1 / ".run_manifest.start.txt.uncommitted-abc123").exists()
        assert (aside / "neq_source_pairs.tsv").exists() and not h.ev.out.exists()
        h.end_container(exit_code=0)
        h.wait_released()
        _code, result = _summary(h, capsys)
        assert result["verdict"] != "UNVERIFIABLE", result["reasons"]
    else:
        assert records.classify_output(h.ev.out).state == protocol.OUTPUT_DAMAGED
        _refused_without_anything(h, capsys, launches=1)
        assert h.snapshot() == before


def test_the_output_classification_follows_the_execution_chain_reader(tmp_path):
    """``classify_output`` は ``read_chain_records`` の分類を使い、file の有無で決めない。"""
    from scripts.function_tracer_pcode.reporting import execution_chain

    tree, e1, e2 = fixture.two_executions(tmp_path)
    out = tree.root
    result = records.classify_output(out)
    assert result.state == protocol.OUTPUT_STARTED and result.started == sorted([e1, e2])
    assert result.damage == []
    # 開始の記録の file はあるが、別の execution を名乗る: owner の分類では破損。
    start = out / ".executions" / e1 / records.START_RECORD
    start.write_text(start.read_text().replace(e1, e2))
    chain = execution_chain.read_chain_records(out)
    assert chain.executions[e1].problems
    assert records.classify_output(out).state == protocol.OUTPUT_DAMAGED
    assert e1 not in records.classify_output(out).started


def test_a_symlinked_or_unlistable_output_is_damaged_not_started(tmp_path):
    target = tmp_path / "elsewhere"
    target.mkdir()
    (tmp_path / "out").symlink_to(target)
    assert records.classify_output(tmp_path / "out").state == protocol.OUTPUT_DAMAGED
    (tmp_path / "file").write_text("x")
    assert records.classify_output(tmp_path / "file").state == protocol.OUTPUT_DAMAGED
    if os.getuid() != 0:
        locked = tmp_path / "locked"
        (locked / ".executions").mkdir(parents=True)
        (locked / ".executions").chmod(0)
        try:
            assert records.classify_output(locked).state == protocol.OUTPUT_DAMAGED
        finally:
            (locked / ".executions").chmod(0o700)


@pytest.mark.parametrize("left, expected", [
    # runner が manifest の前に置く準備の file だけ: 開始前。
    ({"neq_source_pairs.tsv": "x", "pair-status-verification-key.json": "{}",
      "CLEVER/LoopSub/Neq/new-old/functions.txt": "f"}, protocol.OUTPUT_NEVER_STARTED),
    # 書きかけの開始の記録・書きかけの issue（残骸）も開始前。
    ({".executions/" + "a" * 32 + "/.run_manifest.start.txt.uncommitted-x1": "partial"},
     protocol.OUTPUT_NEVER_STARTED),
    # 確定した証跡がどれか 1 つでもあれば、開始前ではない（退避しない）。
    ({"run_manifest.txt": "x=1"}, protocol.OUTPUT_STARTED),
    ({"matrix-publication-manifest.json": "{}"}, protocol.OUTPUT_STARTED),
    ({"validation-execution-receipt.json": "{}"}, protocol.OUTPUT_STARTED),
    ({"S/f/f_B1_B2.pair-status.json": "{}"}, protocol.OUTPUT_STARTED),
    ({"S/.runtime-metrics/f_B1_B2.progress.json": "{}"}, protocol.OUTPUT_STARTED),
    ({".executions/" + "a" * 32 + "/issued/" + "0" * 48 + ".json": "{}"}, protocol.OUTPUT_DAMAGED),
    ({".executions/" + "a" * 32 + "/seal/run_manifest.end.txt": "x"}, protocol.OUTPUT_DAMAGED),
    ({".executions/" + "a" * 32 + "/run_manifest.start.txt": "not a manifest"},
     protocol.OUTPUT_DAMAGED),
    ({".executions/" + "a" * 32 + "/stray": "x"}, protocol.OUTPUT_DAMAGED),
    ({".executions/stray": "x"}, protocol.OUTPUT_DAMAGED),
])
def test_only_debris_and_preparation_files_make_an_output_never_started(tmp_path, left, expected):
    out = tmp_path / "out"
    for relative, text in left.items():
        (out / relative).parent.mkdir(parents=True, exist_ok=True)
        (out / relative).write_text(text)
    assert records.classify_output(out).state == expected

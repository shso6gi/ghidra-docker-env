# -*- coding: utf-8 -*-
"""PR #278 review 4（続き）: 連鎖の OPEN を一律に「再開すれば進む」としない。

契約（期待値はここから導く）:

* 正常な中断（execution の kill・pair の kill・publication の前の停止）で検証器が OPEN と言う
  理由は、次の execution が書き直すものだけで、``start`` は再開する（resumable）。
* どの execution も書き直さない確定した証跡（帰属できない status・同じ nonce の issue・別の
  開始の条件の execution の開始の記録など）による OPEN は、再開しても CLOSED にならない。
  ``start`` は全件の処理を再開せず、何も書かずに拒否し、別の ``--tag`` を案内する（permanent）。
* 再開で直るかが入力のどちらの側が違うかで決まる理由（build receipt と binary）と、分類表に
  無い理由は、再開の根拠にしない（判定できない）。
* 検証器の判定（CLOSED / OPEN と理由）はそのまま使い、緩めない。

本番の wrapper（fake docker）と本番の writer（``ChainTree``）。
"""

from __future__ import annotations

import json

import pytest

import protocol
import summarize
import wrapper
from harness import Harness, repo_head
from scripts.function_tracer_pcode.reporting import execution_chain
from scripts.function_tracer_pcode.reporting.execution_identity import source_tree_digest
from scripts.function_tracer_pcode.tests.unit import test_execution_chain as fixture
from test_review3 import _refused_without_anything

E1, E2, E3 = fixture._run_id(1), fixture._run_id(2), fixture._run_id(3)


@pytest.fixture
def h(tmp_path, monkeypatch):
    harness = Harness(tmp_path, monkeypatch)
    yield harness
    try:
        harness.update(lambda d: d.update({"fail": {}, "respond": {}}))
        harness.end_container(exit_code=137)
        harness.wait_released(timeout=60)
    except (OSError, ValueError, KeyError, AssertionError):
        pass


def test_every_verifier_reason_is_classified_exactly_once():
    """検証器の理由（``execution_chain.R_*``）はすべて、ちょうど 1 つの種類に入る。"""
    verifier = {value for name, value in vars(execution_chain).items()
                if name.startswith("R_") and isinstance(value, str)}
    kinds = [codes for _kind, codes in protocol.CHAIN_REASON_KINDS]
    assert set().union(*kinds) == verifier
    assert sum(len(codes) for codes in kinds) == len(verifier)


def _fields(h, **overrides):
    return dict(environment_fingerprint=h.meta()["fingerprint"], git_commit=repo_head(),
                git_dirty="0", **overrides)


class _Source:
    def __enter__(self):
        self.original = fixture.SOURCE
        fixture.SOURCE = source_tree_digest(wrapper.REPO)

    def __exit__(self, *exc):
        fixture.SOURCE = self.original


def _verify(h):
    return execution_chain.verify_execution_chain(h.ev.out)


def _judged(h, capsys):
    capsys.readouterr()
    h.run("summary", "--json")
    return json.loads(capsys.readouterr().out)


# ---------------------------------------------------------------------------
# 正常な中断: 再開する
# ---------------------------------------------------------------------------


def _killed_before_publishing(h, tree):
    tree.start(E1, **_fields(h))
    tree.decide(E1, tree.pairs[0])
    tree.leave_incomplete(E1, tree.pairs[1])


def _killed_after_an_earlier_publication(h, tree):
    tree.start(E1, **_fields(h))
    for pair in tree.pairs[:2]:
        tree.decide(E1, pair)
    tree.leave_incomplete(E1, tree.pairs[2])
    tree.start(E2, **_fields(h))
    for pair in tree.pairs[2:]:
        tree.decide(E2, pair, outcome="NOT_EQ")
    tree.finish(E2, reused=tree.pairs[:2], end_overrides={"run_pair_failures": "1"})
    tree.start(E3, **_fields(h))          # 次の execution が始まり、kill された
    tree.leave_incomplete(E3, tree.pairs[0])


INTERRUPTIONS = {"killed_before_publishing": _killed_before_publishing,
                 "killed_after_an_earlier_publication": _killed_after_an_earlier_publication}


@pytest.mark.parametrize("interruption", sorted(INTERRUPTIONS))
def test_a_normal_interruption_is_resumed(h, capsys, interruption):
    assert h.start() == wrapper.EXIT_OK
    with _Source():
        tree = fixture.ChainTree(h.ev.out)
        INTERRUPTIONS[interruption](h, tree)
    h.end_container(exit_code=137)
    h.wait_released()
    verify = _verify(h)
    assert verify["verdict"] == execution_chain.VERDICT_OPEN and verify["reasons"]
    assert set(verify["reasons"]) <= protocol.CHAIN_REASONS_REWRITTEN_BY_RESUME, verify["reasons"]
    result = _judged(h, capsys)
    assert {r["category"] for r in result["reasons"]} == {"resumable"}, result["reasons"]
    assert "chain_open" in [r["code"] for r in result["reasons"]]
    runs = len(h.detached_runs())
    assert h.start() == wrapper.EXIT_OK
    assert len(h.detached_runs()) == runs + 1


# ---------------------------------------------------------------------------
# 確定した証跡が原因: 再開しない
# ---------------------------------------------------------------------------


def _unattributed(h, tree):
    fixture.t_unattributed(tree, E1, E2)


def _duplicate_issue(h, tree):
    fixture.t_duplicate_issue(tree, E1, E2)


def _other_start_conditions(h, tree):
    record = h.ev.out / ".executions" / E1 / execution_chain.START_RECORD
    with _Source():
        fields = tree.start_fields(E1, **_fields(h, parallel_jobs="20"))
    record.chmod(0o644)
    record.write_text("".join(f"{k}={v}\n" for k, v in fields.items()))


EVIDENCE = {
    "unattributed": (_unattributed, execution_chain.R_UNATTRIBUTED),
    "duplicate_issue": (_duplicate_issue, execution_chain.R_DUPLICATE_ISSUE),
    "other_start_conditions": (_other_start_conditions, execution_chain.R_CONDITIONS),
}


@pytest.mark.parametrize("evidence", sorted(EVIDENCE))
def test_an_open_chain_caused_by_committed_evidence_is_not_resumed(h, capsys, evidence):
    h.complete_evaluation()
    assert _verify(h)["verdict"] == execution_chain.VERDICT_CLOSED
    damage, expected = EVIDENCE[evidence]
    with _Source():
        damage(h, _tree_of(h))
    verify = _verify(h)
    assert expected in verify["reasons"], verify["reasons"]
    result = _judged(h, capsys)
    codes = {r["code"]: r["category"] for r in result["reasons"]}
    assert codes.get("chain_blocked_by_evidence") == "permanent", result["reasons"]
    assert result["records"]["problems"] == [] and result["output_state"] == "started"
    err = _refused_without_anything(h, capsys, launches=1)
    assert "another --tag" in err


def _tree_of(h):
    """harness が作った tree を、同じ鍵で書き足せる ``ChainTree`` として開き直す。"""
    tree = fixture.ChainTree.__new__(fixture.ChainTree)
    tree.root = h.ev.out
    tree.scope = "FULL_NEQ"
    tree.private_key = h.ev.out.parent / f"{h.ev.out.name}-pair-status.key"
    tree.public_key = h.ev.out / execution_chain.PUBLIC_KEY_FILE
    tree.pairs = [("S0", "f", "B1", f"B{index + 2}") for index in range(4)]
    tree.prefilter = ["targets/EqBench/benchmarks/S0.c"]
    tree.nonce_counter = 1000
    tree.config_overrides = {}
    return tree


def test_receipt_and_binary_disagreeing_is_not_a_reason_to_resume(h, capsys):
    h.complete_evaluation()
    with _Source():
        fixture.t_binary_sha(_tree_of(h), E1, E2)
    assert execution_chain.R_BINARY in _verify(h)["reasons"]
    result = _judged(h, capsys)
    codes = {r["code"]: r["category"] for r in result["reasons"]}
    assert codes.get("chain_inputs_disagree") == "unverifiable", result["reasons"]
    _refused_without_anything(h, capsys, launches=1)


@pytest.mark.parametrize("reasons, code", [
    ({"a_reason_added_later": ["x"]}, "chain_reason_unclassified"),
    ({}, "chain_reason_unclassified"),
    ({execution_chain.R_OBSERVATION: ["x"]}, "verify_failed"),
])
def test_an_unclassified_or_unreadable_open_chain_is_not_resumed(h, monkeypatch, reasons, code):
    h.complete_evaluation()
    monkeypatch.setattr(execution_chain, "verify_execution_chain",
                        lambda out: {"verdict": "OPEN", "reasons": reasons})
    monkeypatch.setenv("EVAL_HOST_STATE", json.dumps({"container": "absent", "observed": True}))
    result = summarize.completion(wrapper.REPO, h.ev.out, h.ev.wrapper, "neq")
    assert code in [r["code"] for r in result["reasons"]]
    assert result["verdict"] == "UNVERIFIABLE"
    assert protocol.start_decision(result)[0] == protocol.DECISION_REFUSE

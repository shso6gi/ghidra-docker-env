# -*- coding: utf-8 -*-
"""eval/protocol.py の契約（評価計画 v2 PR-D、review 2）。

* ``start`` の決定は、理由の分類の **すべての組合せ** について、契約から導いた期待と一致する:
  理由が無ければ完了、判定できない・未知の分類があれば拒否、permanent が 1 つでもあれば
  （他の理由が何であっても）元の評価では再開せずに拒否、blocking があれば拒否、resumable だけ
  のときだけ再開。期待は実装の表ではなく、この規則から作る。
* reader の応答は、要求ごとの終了コードと応答の形の **両方** を満たすときだけ受理する。
  終了コード × 応答の形（正しい・別の形・途中で切れた・空・登録と違う分類・verdict と理由の
  食い違い）のすべての組合せを確かめる。
"""

from __future__ import annotations

from itertools import chain, combinations
import json

import pytest

import protocol

CATEGORIES = list(protocol.CATEGORIES) + ["something new"]
CODE_OF = {category: next(code for code, c in protocol.REASONS.items() if c == category)
           for category in protocol.CATEGORIES}
CODE_OF["something new"] = "not_registered"


ALL_CHECKS = {name: {"status": "done"} for name in protocol.MANDATORY_CHECKS}


def _judgement(verdict, reasons, **extra):
    """completion の応答の形（必須の検査をすべて含む）。"""
    return {"schema": protocol.COMPLETION_SCHEMA, "verdict": verdict, "reasons": reasons,
            "checks": dict(ALL_CHECKS), "output_state": "started", **extra}


def _subsets(items):
    return chain.from_iterable(combinations(items, n) for n in range(len(items) + 1))


def _expected(categories) -> str:
    """契約から（実装を見ずに）導いた決定。"""
    categories = set(categories)
    if not categories:
        return protocol.DECISION_COMPLETE
    if categories - set(protocol.CATEGORIES) or protocol.UNVERIFIABLE in categories:
        return protocol.DECISION_REFUSE
    if protocol.PERMANENT in categories or protocol.BLOCKING in categories:
        return protocol.DECISION_REFUSE
    return protocol.DECISION_LAUNCH


@pytest.mark.parametrize("categories", list(_subsets(CATEGORIES)), ids=lambda c: "+".join(c) or "none")
def test_the_start_decision_follows_the_contract_for_every_combination(categories):
    reasons = [{"code": CODE_OF[c], "category": c, "detail": "x"} for c in categories]
    completion = _judgement(protocol.verdict_of(categories), reasons)
    decision, text = protocol.start_decision(completion)
    assert decision == _expected(categories)
    if protocol.PERMANENT in categories and decision == protocol.DECISION_REFUSE and not (
            set(categories) - set(protocol.CATEGORIES) or protocol.UNVERIFIABLE in categories):
        assert "separate evaluation (another --tag)" in text


def test_a_completion_that_claims_complete_with_reasons_is_refused():
    completion = _judgement("COMPLETE", [{"code": "chain_open", "category": "resumable",
                                          "detail": "x"}])
    assert protocol.start_decision(completion)[0] == protocol.DECISION_REFUSE


def test_every_registered_reason_has_a_known_category():
    assert set(protocol.REASONS.values()) <= set(protocol.CATEGORIES)
    assert protocol.REASONS["foreign_execution"] == protocol.PERMANENT
    assert protocol.REASONS["exit_unobserved"] == protocol.PERMANENT


# ---------------------------------------------------------------------------
# 応答の受理: 終了コード × 応答の形
# ---------------------------------------------------------------------------

def _completion(verdict="INCOMPLETE", reasons=None):
    reasons = [{"code": "chain_open", "category": "resumable", "detail": "x"}] if reasons is None else reasons
    return _judgement(verdict, reasons)


VALID = {
    "completion": _completion(),
    "launch-evidence": {"schema": protocol.EVIDENCE_SCHEMA, "captured_at_epoch": 1.0,
                        "unterminated_pairs": [{"pair": "a/f/f_B1_B2.pair-status.json",
                                                "kind": "concluded_incomplete"}],
                        "verify": {"verdict": "OPEN"}, "verify_error": None},
    "verify": {"schema": protocol.VERIFY_SCHEMA, "verify": {"verdict": "OPEN"}, "verify_error": None},
    "report": {**_completion(), "schema": protocol.SUMMARY_SCHEMA, "report_errors": []},
}
BROKEN = {
    "other_schema": lambda v: {**v, "schema": "something-else"},
    "not_an_object": lambda v: [v],
    "missing_field": lambda v: {k: x for k, x in v.items() if k not in ("reasons", "unterminated_pairs", "verify")},
}


def _body(request, shape):
    value = VALID[request]
    if shape == "valid":
        return json.dumps(value)
    if shape == "truncated":
        text = json.dumps(value)
        return text[: len(text) // 2]
    if shape == "empty":
        return ""
    return json.dumps(BROKEN[shape](value))


@pytest.mark.parametrize("request_name", sorted(protocol.CONTRACTS))
@pytest.mark.parametrize("returncode", [0, 1, 2, 3, 137, None])
@pytest.mark.parametrize("shape", ["valid", "truncated", "empty", *sorted(BROKEN)])
def test_a_response_is_accepted_only_with_both_the_exit_code_and_the_shape(request_name, returncode, shape):
    codes, _validate, consistency = protocol.CONTRACTS[request_name]
    body = _body(request_name, shape)
    should_accept = shape == "valid" and returncode in codes and (
        consistency is None or consistency(VALID[request_name]) == returncode)
    if should_accept:
        assert protocol.accept(request_name, returncode, body) == json.loads(body)
    else:
        with pytest.raises(protocol.Rejected):
            protocol.accept(request_name, returncode, body)


@pytest.mark.parametrize("reasons, verdict", [
    ([{"code": "chain_open", "category": "blocking", "detail": "x"}], "INCOMPLETE"),  # 登録と違う分類
    ([{"code": "made_up", "category": "resumable", "detail": "x"}], "INCOMPLETE"),     # 未登録の code
    ([{"code": "chain_open", "category": "resumable", "detail": "x"}], "COMPLETE"),    # verdict の食い違い
    ([], "INCOMPLETE"),
    ([{"code": "records_damaged", "category": "unverifiable", "detail": "x"}], "INCOMPLETE"),
])
def test_a_completion_inconsistent_with_the_registry_is_rejected(reasons, verdict):
    with pytest.raises(protocol.Rejected):
        protocol.accept("completion", 0, json.dumps(_completion(verdict, reasons)))


def test_an_unknown_category_is_refused_even_when_the_verdict_claims_incomplete():
    """受理の検査を経ない入力でも、決定は未知の分類で再開しない（二重の防御）。"""
    completion = {**_judgement("INCOMPLETE", [{"code": "chain_open", "category": "resumable",
                                               "detail": "x"}]),
                  "reasons": [{"code": "x", "category": "something new", "detail": "x"},
                              {"code": "chain_open", "category": "resumable", "detail": "x"}]}
    assert protocol.start_decision(completion)[0] == protocol.DECISION_REFUSE

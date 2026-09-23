# -*- coding: utf-8 -*-
"""Issue #167: 比較の中で作った証拠と、その比較の最終 relation の束縛。

relation の lifetime は 1 つの raw pair の比較で、analysis object の lifetime ではない。

* 比較の中で作った証拠 record は、その比較の relation の digest を持つ。
* gate は、digest が現在の比較の relation と値で一致する record だけを採用する。
* 後で実行する仕事（worklist の producer / replanner）は、登録した比較の relation で
  照合する。
* stage runner は、branch の結果を作った比較の relation の下で gate を実行する。
* 証拠の合流は record の束縛を保ち、同じ proof でも relation が違えば別の証拠にする。
"""

from __future__ import annotations

from types import SimpleNamespace

import pytest

from scripts.function_tracer_pcode.checker.recovery_proofs import RecoveryProofMixin
from scripts.function_tracer_pcode.core import Expression, FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    OUTSIDE_COMPARISON,
    RELATION_DIGEST_KEY,
    bind_evidence_to_comparison,
    bind_evidence_to_relation,
    build_input_correspondence_set,
    comparison_evidence,
    comparison_relation_scope,
    current_relation_digest,
    merge_new_evidence,
)
from scripts.function_tracer_pcode.proof.cause_identity import ProofRequirementContract, ProofRequirementId
from scripts.function_tracer_pcode.proof.obligations.runtime import ObligationRuntimeSession
from scripts.function_tracer_pcode.proof.obligations.stage_runner import branch_comparison_relation


def _analysis(name, parameter_sizes, binary_id="bin"):
    x = Expression.parameter("p0", 0, data_type="int", size=parameter_sizes[0])
    return FunctionReturnAnalysis(
        function_name=name,
        entry_point="0x1000",
        parameters=[
            {"name": f"p{index}", "index": index, "size": size, "data_type": "int"}
            for index, size in enumerate(parameter_sizes)
        ],
        returns=[ReturnInfo("0x1010", x, [])],
        return_type="int",
        binary_id=binary_id,
    )


def _two_relations():
    a = build_input_correspondence_set(_analysis("f", [4]), _analysis("g", [4]))
    b = build_input_correspondence_set(_analysis("f", [4, 4]), _analysis("g", [4, 4]))
    assert a.digest != b.digest
    return a, b


def test_evidence_made_in_a_comparison_is_adopted_only_in_that_comparison():
    a, b = _two_relations()
    with comparison_relation_scope(a):
        record = bind_evidence_to_comparison({"proof_obligation_id": ("p",)})
        assert record[RELATION_DIGEST_KEY] == a.digest
        assert comparison_evidence((record,)) == (record,)
        with comparison_relation_scope(b):
            # 入れ子の比較は自分の relation を持ち、外の比較の証拠を採用しない。
            assert comparison_evidence((record,)) == ()
        assert current_relation_digest() == a.digest
    assert comparison_evidence((record,)) == ()
    with comparison_relation_scope(None):
        assert comparison_evidence((record,)) == ()


def test_evidence_made_outside_any_comparison_is_never_adopted():
    record = bind_evidence_to_comparison({"proof_obligation_id": ("p",)})
    assert record[RELATION_DIGEST_KEY] == OUTSIDE_COMPARISON
    a, _b = _two_relations()
    assert comparison_evidence((record,)) == ()
    with comparison_relation_scope(a):
        assert comparison_evidence((record,)) == ()


def test_relation_independent_evidence_carries_no_binding():
    """比較の前に関数単体で作った事実（analysis 層の証拠）は relation に依存しない。"""

    a, _b = _two_relations()
    record = {"proof_obligation_id": ("unary",)}
    assert comparison_evidence((record,)) == (record,)
    with comparison_relation_scope(a):
        assert comparison_evidence((record,)) == (record,)


def test_merging_keeps_records_of_the_same_proof_from_different_relations():
    a, b = _two_relations()
    from_a = bind_evidence_to_relation({"proof_obligation_id": ("p",)}, a)
    from_b = bind_evidence_to_relation({"proof_obligation_id": ["p"]}, b)
    merged = merge_new_evidence((from_a,), (from_b, dict(from_a)))
    assert [record[RELATION_DIGEST_KEY] for record in merged] == [a.digest, b.digest]
    assert merge_new_evidence(merged, (from_b,)) is None

    # result からの合流（checker）も同じ規則。
    analysis = SimpleNamespace(completed_recovery_proof_evidence=(from_a,))
    checker = SimpleNamespace(enable_completed_recovery_proofs=True)
    result = SimpleNamespace(completed_recovery_proof_evidence=[
        {"side": "function1", "evidence": from_b},
        {"side": "function1", "evidence": from_a},
    ])
    RecoveryProofMixin._merge_completed_recovery_proofs_from_result(checker, analysis, analysis, result)
    assert [record[RELATION_DIGEST_KEY] for record in analysis.completed_recovery_proof_evidence] == [
        a.digest, b.digest,
    ]


def _requirement(name):
    return ProofRequirementId.create(
        "value_relation", ("pair_query", name), ProofRequirementContract(proposition=name),
    )


def test_deferred_producers_run_in_the_comparison_that_scheduled_them():
    a, b = _two_relations()
    runtime = ObligationRuntimeSession.create(_analysis("f", [4]), _analysis("g", [4]))
    seen = []
    with comparison_relation_scope(a):
        runtime.schedule(_requirement("deferred"), "value_relation", lambda: seen.append(current_relation_digest()))
    with comparison_relation_scope(b):
        runtime.run_next()
    assert seen == [a.digest]


def test_replanners_plan_and_produce_in_the_comparison_that_registered_them():
    a, b = _two_relations()
    runtime = ObligationRuntimeSession.create(_analysis("f", [4]), _analysis("g", [4]))
    seen = []

    def replan(*_args):
        seen.append(("plan", current_relation_digest()))
        return _requirement("replanned"), "value_relation", lambda: seen.append(("produce", current_relation_digest()))

    with comparison_relation_scope(a):
        runtime.register_pair_query_replanner("pair", "value_relation", replan)
        runtime.register_target_query_replanner(("target",), replan)
        runtime.register_counterexample_safety_replanner("pair", replan)
    planners = (
        runtime.pair_query_replanners[("pair", "value_relation")],
        runtime.target_query_replanners[next(iter(runtime.target_query_replanners))][0],
        runtime.counterexample_safety_replanners["pair"],
    )
    for planner in planners:
        seen.clear()
        with comparison_relation_scope(b):
            _requirement_id, _kind, producer = planner(None) if planner is planners[2] else planner()
            producer()
        assert seen == [("plan", a.digest), ("produce", a.digest)]


def test_stage_runner_gates_use_the_relation_of_the_comparison_that_made_the_result():
    raw = build_input_correspondence_set(_analysis("f", [4]), _analysis("g", [4]))
    abstracted = build_input_correspondence_set(_analysis("f", [4, 4]), _analysis("g", [4, 4]))

    def result_for(input_correspondence):
        frame = SimpleNamespace(prepared=SimpleNamespace(input_correspondence=input_correspondence))
        return SimpleNamespace(_prepared_dispatch_frame=frame)

    assert branch_comparison_relation(result_for(raw)) is raw
    # 再帰抽象化の branch は、抽象 analysis を比べた内側の比較の relation。
    assert branch_comparison_relation(result_for(abstracted)) is abstracted
    # frame の無い結果（互換経路）には relation が無く、束縛された証拠は採用されない。
    assert branch_comparison_relation(result_for(None)) is None
    assert branch_comparison_relation(SimpleNamespace()) is None


def test_a_prepared_strategy_refuses_to_run_outside_its_relations_comparison(monkeypatch):
    """frame の relation と、証拠を束縛する比較の relation は同じでなければならない。"""

    from unittest.mock import Mock

    from scripts.function_tracer_pcode.proof.call_effect import preflight
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy

    raw1, raw2 = _analysis("f", [4]), _analysis("g", [4])
    relation = build_input_correspondence_set(raw1, raw2)
    _a, other = _two_relations()
    assert other.digest != relation.digest
    frame = SimpleNamespace(prepared=SimpleNamespace(analysis1=raw1, analysis2=raw2, input_correspondence=relation))
    monkeypatch.setattr(preflight, "current_dispatch_depth", lambda: 1)
    monkeypatch.setattr(preflight, "consume_prepared_dispatch_frame", lambda *_args: frame)
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    for scope in (None, other):
        with comparison_relation_scope(scope), pytest.raises(RuntimeError, match="comparison_relation_scope_mismatch"):
            strategy.check(raw1, raw2)

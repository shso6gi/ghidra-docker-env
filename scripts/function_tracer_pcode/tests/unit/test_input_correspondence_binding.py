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


@pytest.mark.parametrize("strategy_name", ["pairwise", "monolithic"])
def test_a_prepared_strategy_refuses_to_run_outside_its_relations_comparison(monkeypatch, strategy_name):
    """frame の relation と、証拠を束縛する比較の relation は同じでなければならない。"""

    from unittest.mock import Mock

    from scripts.function_tracer_pcode.proof.call_effect import preflight
    from scripts.function_tracer_pcode.proof.strategies.monolithic import MonolithicStrategy
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy

    raw1, raw2 = _analysis("f", [4]), _analysis("g", [4])
    relation = build_input_correspondence_set(raw1, raw2)
    _a, other = _two_relations()
    assert other.digest != relation.digest
    frame = SimpleNamespace(prepared=SimpleNamespace(analysis1=raw1, analysis2=raw2, input_correspondence=relation))
    monkeypatch.setattr(preflight, "current_dispatch_depth", lambda: 1)
    monkeypatch.setattr(preflight, "consume_prepared_dispatch_frame", lambda *_args: frame)
    strategy = {"pairwise": PairwiseStrategy, "monolithic": MonolithicStrategy}[strategy_name](
        Mock(), Mock(), debug=False,
    )
    for scope in (None, other):
        with comparison_relation_scope(scope), pytest.raises(RuntimeError, match="comparison_relation_scope_mismatch"):
            strategy.check(raw1, raw2)


def test_gate_outcomes_of_another_relation_do_not_discharge_this_comparisons_reason():
    """runtime の obligation と proof outcome は relation ごと（review で見つけた blocker）。

    再帰抽象化の branch（relation B）と後の branch（relation A）は 1 つの runtime を
    共有する。B で出た gate outcome と B の証拠が、同じ requirement を持つ A の reason を
    解消してはならない（A の gate は A の relation で実行し直す）。
    """

    from scripts.function_tracer_pcode.proof.obligations.model import FunctionProofOutcome

    relation_a, relation_b = _two_relations()
    runtime = ObligationRuntimeSession.create(_analysis("f", [4]), _analysis("g", [4]))
    requirement = _requirement("readonly_identity")
    runs = []

    def reason():
        return SimpleNamespace(
            reason_id="readonly_identity_missing", recovery_proof_kind="", stage="S_PAIRWISE",
            proof_requirement_ids=(requirement.to_dict(),), pair_or_case=None, object_target_key=None,
        )

    def run_gates(relation, gate_reason, outcome):
        with comparison_relation_scope(relation):
            runtime.plan_proof_gates(
                SimpleNamespace(unknown_reasons=[gate_reason]), {},
                lambda *_args: lambda: runs.append(current_relation_digest()) or outcome,
            )
            while runtime.run_next()[0] is not None:
                pass

    evidence_b = bind_evidence_to_relation({
        "proof_requirement_id": requirement.to_dict(), "status": "complete", "proof_source": "gate_test",
    }, relation_b)

    reason_b, reason_a = reason(), reason()
    run_gates(relation_b, reason_b, FunctionProofOutcome.EQUIVALENT)
    # A の gate は B の証拠を採用しないので INCONCLUSIVE を返す。A の比較で実行されること。
    run_gates(relation_a, reason_a, FunctionProofOutcome.INCONCLUSIVE)
    assert runs == [relation_b.digest, relation_a.digest]
    with comparison_relation_scope(relation_a):
        # B の証拠は A の比較の view を作らず、B の outcome は A の reason を解消しない。
        assert runtime.apply_completed_evidence(({"evidence": evidence_b},)) == ()
        assert runtime.outcome_for_reason(reason_a) == FunctionProofOutcome.INCONCLUSIVE
    with comparison_relation_scope(relation_b):
        # B の比較の中では、B の証拠と outcome が B の reason を解消する。
        assert len(runtime.apply_completed_evidence(({"evidence": evidence_b},))) == 1
        assert runtime.outcome_for_reason(reason_b) == FunctionProofOutcome.EQUIVALENT
    with comparison_relation_scope(relation_a):
        assert runtime.outcome_for_reason(reason_a) == FunctionProofOutcome.INCONCLUSIVE


def test_run_strategy_branch_runs_the_strategy_in_the_frames_relation():
    from unittest.mock import Mock, patch

    from scripts.function_tracer_pcode.checker import strategy_execution as se
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy

    relation, _other = _two_relations()
    seen = []
    strategy = Mock(spec=PairwiseStrategy)
    strategy.check.side_effect = lambda *_args: seen.append(current_relation_digest()) or SimpleNamespace(
        is_equivalent=None, comparison_execution_receipt=None,
    )
    frame = SimpleNamespace(
        obligation_runtime=None, replan_successor_plan=None, pair_disposition_ledger=None, receipt=None,
        cleanup_complete=False, close=Mock(), prepared=SimpleNamespace(input_correspondence=relation),
    )
    ctx = SimpleNamespace(strategy=strategy, replan_plan=None, branch_id="S_PAIRWISE")
    with patch.object(se, "push_prepared_dispatch_frame", return_value="token"), \
         patch.object(se, "close_prepared_dispatch_frame", return_value=True), \
         patch.object(se, "diagnostic_projection", side_effect=lambda manifest, _frame: dict(manifest)):
        se.run_strategy_branch(
            ctx, frame, SimpleNamespace(), "a1", "a2", False,
            locally_issued_branch_authority=None, call_effect_shadow_manifest={},
            debug_print=lambda _message: None, apply_preflight_final_gate=Mock(),
        )
    assert seen == [relation.digest]
    assert current_relation_digest() is None

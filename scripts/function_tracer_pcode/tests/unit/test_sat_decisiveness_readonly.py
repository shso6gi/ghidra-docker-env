from scripts.function_tracer_pcode.tests.unit._sat_decisiveness_fixtures import *

import pytest


@pytest.fixture(autouse=True)
def _gate_runs_in_the_fixture_comparison():
    # readonly projection の proof は、それを作った比較（relation）の中でだけ
    # 採用される（Issue #167）。各 test はその比較の中で gate を呼ぶ。
    with _readonly_fixture_comparison():
        yield

def test_readonly_identity_completed_evidence_connects_to_recovery_gate():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _readonly_identity_reason()
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _readonly_identity_evidence(action)
    analysis1 = _analysis_with_completed_evidence(evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == (reason.proof_obligation_id,)
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is True

def test_readonly_identity_completed_evidence_rejects_relationless_target():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    relationless_target = _readonly_identity_target()[:4]
    reason = _readonly_identity_reason(target=relationless_target)
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _readonly_identity_evidence(action)
    analysis1 = _analysis_with_completed_evidence(evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is False

def test_readonly_identity_completed_evidence_rejects_missing_relation_marker():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    weak_target = (*_readonly_identity_target()[:4], ("readonly_identity_relation", ("kind", "missing_readonly_ref")))
    reason = _readonly_identity_reason(target=weak_target)
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _readonly_identity_evidence(action)
    analysis1 = _analysis_with_completed_evidence(evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is False

def test_readonly_identity_completed_evidence_rejects_malformed_storage_relation():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    malformed_target = (
        *_readonly_identity_target()[:4],
        (
            "readonly_identity_relation",
            ("shared_count_identities", (("parameter", 1),)),
            (
                "count_storage_relation",
                (
                    "same_register_base_projection",
                    ("base", (-1, 12756, 64)),
                    ("left_bits", 0, 64),
                ),
            ),
        ),
    )
    reason = _readonly_identity_reason(target=malformed_target)
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _readonly_identity_evidence(action)
    analysis1 = _analysis_with_completed_evidence(evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is False

def test_readonly_identity_completed_evidence_rejects_missing_side_payload():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _readonly_identity_reason()
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _readonly_identity_evidence(action)
    evidence["proof_content"].pop("left_side")
    analysis1 = _analysis_with_completed_evidence(evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is False

def test_readonly_identity_completed_evidence_rejects_projection_without_extension_payload():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _readonly_identity_reason()
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _readonly_identity_evidence(action)
    evidence["proof_content"].pop("parameter_extension")
    analysis1 = _analysis_with_completed_evidence(evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._readonly_identity_proof_is_complete(reason, analysis1, analysis2) is False

def test_method_b_closure_requires_both_completed_actions_for_recovery_gate():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _method_b_reason()
    actions = build_unknown_recovery_actions([reason])
    covering_evidence = _method_b_evidence(actions[0])
    guard_evidence = _method_b_evidence(actions[1])
    analysis2 = _analysis_with_completed_evidence()

    partial = _analysis_with_completed_evidence(covering_evidence)
    assert strategy._method_b_closure_proof_is_complete(reason, partial, analysis2) is False

    complete = _analysis_with_completed_evidence(covering_evidence, guard_evidence)
    assert PairwiseStrategy._completed_recovery_proof_ids(complete) == tuple(
        action.proof_obligation_id for action in actions
    )
    assert strategy._method_b_closure_proof_is_complete(reason, complete, analysis2) is True

def test_method_b_closure_completed_evidence_rejects_status_only_payload():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _method_b_reason()
    actions = build_unknown_recovery_actions([reason])
    evidence = [_method_b_evidence(action) for action in actions]
    for item in evidence:
        content = item["proof_content"]
        item["proof_content"] = {
            key: content[key]
            for key in (
                "object_derived",
                "object_target_key",
                "seed_compensation",
                "term_sequence",
                "pure_side_effect_profile",
                "guard_partition",
                "partition_coverage_proof",
            )
            if key in content
        }
    analysis1 = _analysis_with_completed_evidence(*evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False

def test_method_b_closure_completed_evidence_rejects_term_payload_mismatch():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _method_b_reason()
    actions = build_unknown_recovery_actions([reason])
    covering_evidence = _method_b_evidence(actions[0])
    guard_evidence = _method_b_evidence(actions[1])
    covering_evidence["proof_content"]["exact_terms"] = (("readonly_reduction_term", 0, 4),)
    analysis1 = _analysis_with_completed_evidence(covering_evidence, guard_evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == (actions[1].proof_obligation_id,)
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False

def test_method_b_closure_completed_evidence_rejects_side_payload_mismatch():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _method_b_reason()
    actions = build_unknown_recovery_actions([reason])
    covering_evidence = _method_b_evidence(actions[0])
    guard_evidence = _method_b_evidence(actions[1])
    covering_evidence["proof_content"]["summary_side"] = "left"
    analysis1 = _analysis_with_completed_evidence(covering_evidence, guard_evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == (actions[1].proof_obligation_id,)
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False

def test_method_b_closure_completed_evidence_accepts_count_membership_payload():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _method_b_reason()
    actions = build_unknown_recovery_actions([reason])
    covering_evidence = _method_b_evidence(actions[0])
    guard_evidence = _method_b_evidence(actions[1])
    guard_evidence["proof_content"]["count_value"] = 3
    guard_evidence["proof_content"]["count_values"] = (3, 4)
    guard_evidence["proof_content"]["guard_evidence"] = "reduction_count_membership_implication"
    analysis1 = _analysis_with_completed_evidence(covering_evidence, guard_evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == tuple(
        action.proof_obligation_id for action in actions
    )
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is True

def test_method_b_closure_completed_evidence_rejects_count_value_outside_membership_payload():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    reason = _method_b_reason()
    actions = build_unknown_recovery_actions([reason])
    covering_evidence = _method_b_evidence(actions[0])
    guard_evidence = _method_b_evidence(actions[1])
    guard_evidence["proof_content"]["count_value"] = 2
    guard_evidence["proof_content"]["count_values"] = (3, 4)
    guard_evidence["proof_content"]["guard_evidence"] = "reduction_count_membership_implication"
    analysis1 = _analysis_with_completed_evidence(covering_evidence, guard_evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == (actions[0].proof_obligation_id,)
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False

def test_method_b_closure_completed_evidence_rejects_relationless_target():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    relationless_target = _method_b_closure_target()[:4]
    reason = _method_b_reason(target=relationless_target)
    actions = build_unknown_recovery_actions([reason])
    evidence = tuple(_method_b_evidence(action) for action in actions)
    analysis1 = _analysis_with_completed_evidence(*evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False

def test_method_b_closure_completed_evidence_rejects_missing_summary_relation():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    weak_target = (*_method_b_closure_target()[:4], ("method_b_closure_relation", ("kind", "missing_method_b_summary")))
    reason = _method_b_reason(target=weak_target)
    actions = build_unknown_recovery_actions([reason])
    evidence = tuple(_method_b_evidence(action) for action in actions)
    analysis1 = _analysis_with_completed_evidence(*evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False

def test_method_b_closure_completed_evidence_rejects_weak_summary_profile():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    weak_target = (
        *_method_b_closure_target()[:4],
        (
            "method_b_closure_relation",
            ("kind", "one_sided_summary"),
            ("summary_side", "right"),
            ("exact_side", "left"),
            ("summary", ("method_b_summary_profile", ("runtime_ref", "summary"))),
            ("exact_terms", (("readonly_reduction_term", 0, 4), ("readonly_reduction_term", 8, 4))),
            ("exact_constant_bias", 0),
        ),
    )
    reason = _method_b_reason(target=weak_target)
    actions = build_unknown_recovery_actions([reason])
    evidence = tuple(_method_b_evidence(action) for action in actions)
    analysis1 = _analysis_with_completed_evidence(*evidence)
    analysis2 = _analysis_with_completed_evidence()

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1) == ()
    assert strategy._method_b_closure_proof_is_complete(reason, analysis1, analysis2) is False

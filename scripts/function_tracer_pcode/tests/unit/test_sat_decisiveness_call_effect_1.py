from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import echo_input_correspondence
from scripts.function_tracer_pcode.tests.unit._sat_decisiveness_fixtures import *

import pytest


@pytest.fixture(autouse=True)
def _gate_runs_in_the_fixture_comparison():
    # fixture の比較中の証拠は、それを作った比較（raw pair と relation）の中でだけ採用される
    # （Issue #167）。gate を直接呼ぶ test はその比較の中で呼ぶ。strategy.check は自分の比較を開く。
    with _fixture_comparison():
        yield

def test_function_return_analysis_marks_effect_sensitive_raw_memory_reads_as_sat_unsafe():
    params = [_param("trace", index=0, size=8, data_type="int *")]
    trace = Expression.parameter("trace", 0, size=8)
    field = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=4,
        size=4,
    )
    analysis = FunctionReturnAnalysis(
        function_name="raw_read_after_effect",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.memory(field, size=4),
                conditions=[],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace"],
            effects=[
                StoreEffect(
                    location=location,
                    value=Expression.constant(1, 4),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
    )

    assert analysis.has_effect_sensitive_raw_memory_reads() is True
    assert "effect_sensitive_raw_memory_reads" in analysis.get_decisive_sat_unsafety_reasons()

def test_function_return_analysis_ignores_effect_sensitive_raw_reads_under_incompatible_guards():
    params = [
        _param("trace", index=0, size=8, data_type="int *"),
        _param("flag", index=1, size=4, data_type="int"),
    ]
    trace = Expression.parameter("trace", 0, size=8)
    flag = Expression.parameter("flag", 1, size=4)
    field = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=4,
        size=4,
    )
    analysis = FunctionReturnAnalysis(
        function_name="guarded_raw_read_after_effect",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.memory(field, size=4),
                conditions=[_eq(flag, _const(0))],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace", "flag"],
            effects=[
                StoreEffect(
                    location=location,
                    value=Expression.constant(1, 4),
                    conditions=[_ne(flag, _const(0))],
                    order_key=1,
                )
            ],
        ),
    )

    assert analysis.has_effect_sensitive_raw_memory_reads() is False
    assert "effect_sensitive_raw_memory_reads" not in analysis.get_decisive_sat_unsafety_reasons()

def test_function_return_analysis_checks_raw_read_alias_under_effect_guard():
    params = [
        _param("p", index=0, size=8, data_type="int *"),
        _param("q", index=1, size=8, data_type="int *"),
    ]
    p = Expression.parameter("p", 0, size=8)
    q = Expression.parameter("q", 1, size=8)
    analysis = FunctionReturnAnalysis(
        function_name="guarded_alias_raw_read_after_effect",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.memory(q, size=4),
                conditions=[],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["p", "q"],
            effects=[
                StoreEffect(
                    location=CanonicalLocation(
                        base_ref=LocationBaseRef.parameter("p", index=0),
                        offset=0,
                        size=4,
                    ),
                    value=Expression.constant(1, 4),
                    conditions=[_eq(p, q)],
                    order_key=1,
                )
            ],
        ),
    )

    assert analysis.has_effect_sensitive_raw_memory_reads() is True
    assert "effect_sensitive_raw_memory_reads" in analysis.get_decisive_sat_unsafety_reasons()

def test_function_return_analysis_blocks_equivalence_when_effect_summary_is_unsupported():
    analysis = FunctionReturnAnalysis(
        function_name="unsupported_effect_summary",
        entry_point="0x1000",
        parameters=[],
        returns=[ReturnInfo(address="0x1000", value=_const(0), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=[],
            effects=[],
            has_unsupported_call=True,
        ),
    )

    assert "unsupported_call_effect_summary" in analysis.get_decisive_sat_unsafety_reasons()
    assert "unsupported_call_effect_summary" in analysis.get_equivalence_blocking_unsafety_reasons()

def test_unsupported_call_effect_reason_group_is_used_for_signature_matching():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)

    assert strategy._unsupported_call_effect_reason_is_compatible(
        "target_identity_unavailable",
        "callee_unsupported_call_may_expose_parameter_memory",
    )
    assert not strategy._unsupported_call_effect_reason_is_compatible(
        "target_identity_unavailable",
        "return_storage_missing_identity",
    )
    signature = strategy._unsupported_call_effect_reason_signature(
        "target_identity_unavailable",
    )
    assert "target_identity_unavailable" in signature
    assert "callee_unsupported_call_may_expose_parameter_memory" in signature

def test_unsupported_call_effect_semantics_respects_compatible_reason_groups():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)

    left = (
        "unsupported_call_effect",
        "function1",
        "analysis-1",
        (
            "runtime_ref",
            "unsupported_call_effect",
            ("callee_identity", ("unknown", "B1", ("target_expression", ("target", "A")))),
            ("typed_target_expression", ("target", "A")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        (
            "callsite_storage",
            ("callee_identity", ("unknown", "B1", ("target_expression", ("target", "A")))),
            ("target_expression", ("target", "A")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        ("effect_ordinal", 0),
        "target_identity_unavailable",
    )
    right = (
        "unsupported_call_effect",
        "function2",
        "analysis-2",
        (
            "runtime_ref",
            "unsupported_call_effect",
            ("callee_identity", ("unknown", "B2", ("target_expression", ("target", "A")))),
            ("typed_target_expression", ("target", "A")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        (
            "callsite_storage",
            ("callee_identity", ("unknown", "B2", ("target_expression", ("target", "A")))),
            ("target_expression", ("target", "A")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        ("effect_ordinal", 0),
        "callee_unsupported_call_may_expose_parameter_memory",
    )
    assert strategy._unsupported_call_effects_semantically_match(left, right)

    different_target = (
        right[0],
        right[1],
        right[2],
        (
            "runtime_ref",
            "unsupported_call_effect",
            ("callee_identity", ("unknown", "B2", ("target_expression", ("target", "B")))),
            ("typed_target_expression", ("target", "B")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        (
            "callsite_storage",
            ("callee_identity", ("unknown", "B2", ("target_expression", ("target", "B")))),
            ("target_expression", ("target", "B")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        right[5],
        right[6],
    )
    assert not strategy._unsupported_call_effects_semantically_match(left, different_target)

    right = tuple(list(right[:-1]) + ["return_storage_missing_identity"])
    assert not strategy._unsupported_call_effects_semantically_match(left, right)

def test_unsupported_call_effect_completed_proof_requires_compatibility_policy():
    evidence = _complete_call_effect_summary_proof_evidence(
        _call_effect_summary_proof_evidence()["object_target_key"]
    )

    assert _completed_proof_ids_for_call_effect_evidence(evidence)
    evidence["proof_content"].pop("compatibility_policy")

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()

def test_call_effect_blocker_completed_proof_revalidates_selected_candidate_policy():
    selected_candidate = _call_effect_summary_proof_evidence()["object_target_key"]
    object_target_key = (
        "call_effect_blocker",
        "function1",
        ("function_ref", ("function", "B1", 0x1000)),
        "unsupported_call_effect_summary",
        "unsupported_call_effect_summary",
        (selected_candidate,),
        (),
        (),
        (),
    )
    selected_content = _call_effect_summary_proof_content(selected_candidate)
    expected_refs = PairwiseStrategy._expected_call_effect_proof_content_refs(
        object_target_key,
        candidate=selected_candidate,
    )
    assert expected_refs is not None
    runtime_ref, callsite_storage = expected_refs
    proof_content = {
        "object_derived": True,
        "status": "complete",
        "proof_rule": "call_effect_blocker_resolution",
        "object_target_key": object_target_key,
        "selected_candidate_key": selected_candidate,
        "selected_candidate_kind": "unsupported_call_effect",
        "selected_candidate_proof_content": selected_content,
        "peer_object_target_key": selected_content["peer_object_target_key"],
        "call_effect_summary": {
            "status": "complete",
            "summary_source": ("effect_summary", "call_effect_blocker"),
            "evidence_kind": "call_effect_summary",
            "object_target_key": object_target_key,
        },
        "runtime_ref": {
            "status": "complete",
            "runtime_ref": runtime_ref,
        },
        "callsite_storage": {
            "status": "complete",
            "callsite_storage": callsite_storage,
        },
    }
    evidence = _call_effect_summary_proof_evidence(object_target_key=object_target_key)
    evidence["proof_content"] = proof_content

    assert _completed_proof_ids_for_call_effect_evidence(evidence)

    incomplete = deepcopy(evidence)
    incomplete["proof_content"]["selected_candidate_proof_content"].pop(
        "compatibility_policy"
    )

    assert _completed_proof_ids_for_call_effect_evidence(incomplete) == ()

def test_unsupported_call_effect_semantics_requires_exact_target_expression_match_for_same_reason():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)

    left = (
        "unsupported_call_effect",
        "function1",
        "analysis-1",
        (
            "runtime_ref",
            "unsupported_call_effect",
            ("callee_identity", ("unknown", "B1", ("target_expression", ("target", "A")))),
            ("typed_target_expression", ("target", "A")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        (
            "callsite_storage",
            ("callee_identity", ("unknown", "B1", ("target_expression", ("target", "A")))),
            ("target_expression", ("target", "A")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        ("effect_ordinal", 0),
        "target_identity_unavailable",
    )
    right = (
        "unsupported_call_effect",
        "function1",
        "analysis-1",
        (
            "runtime_ref",
            "unsupported_call_effect",
            ("callee_identity", ("unknown", "B1", ("target_expression", ("target", "B")))),
            ("typed_target_expression", ("target", "B")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        (
            "callsite_storage",
            ("callee_identity", ("unknown", "B1", ("target_expression", ("target", "B")))),
            ("target_expression", ("target", "B")),
            ("argument_keys", (("argument", 0, ("arg", 0)),)),
        ),
        ("effect_ordinal", 0),
        "target_identity_unavailable",
    )

    assert not strategy._unsupported_call_effects_semantically_match(left, right)

def test_pairwise_strategy_does_not_prove_equivalent_with_incomplete_effect_summary(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            incomplete_reasons=("effect_summary_path_coverage_incomplete",),
        ),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(1),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(1),
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "func1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_after_guard = Mock(
        return_value=_solver_bound_query_result(True)
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0

def test_pairwise_strategy_does_not_prove_equivalent_with_unsupported_effect_summary(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            incomplete_reasons=(),
        ),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(1),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(1),
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "func1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_after_guard = Mock(
        return_value=_solver_bound_query_result(True)
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0

def test_pairwise_call_effect_summary_proof_pending_blocks_equivalent(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == "unsupported_call_effect_semantics"
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert result.unknown_reasons[0].proof_obligation_id is not None

def test_pairwise_call_effect_summary_proof_wrong_id_does_not_recover(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    wrong_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    analysis1.completed_recovery_proof_ids = (
        (
            wrong_reason.reason_id,
            wrong_reason.proof_stage,
            wrong_reason.recovery_proof_kind,
            wrong_reason.evidence_kind,
            ("unsupported_call_effect", "different-callsite"),
        ),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value

def test_pairwise_call_effect_summary_bare_completed_proof_id_does_not_recover(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    analysis1.completed_recovery_proof_ids = (completed_reason.proof_obligation_id,)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value

def test_pairwise_call_effect_summary_missing_completed_proof_id_does_not_recover(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    evidence = _call_effect_summary_proof_evidence(
        object_target_key=completed_reason.object_target_key,
        proof_obligation_id=completed_reason.proof_obligation_id,
    )
    evidence.pop("proof_obligation_id", None)
    analysis1.completed_recovery_proof_evidence = (evidence,)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value

def test_pairwise_call_effect_summary_producer_connects_completed_target_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    analysis1.completed_recovery_proof_evidence = (
        _complete_call_effect_summary_proof_evidence(
            completed_reason.object_target_key,
            proof_obligation_id=completed_reason.proof_obligation_id,
        ),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    _evidence_of_this_pair(analysis1, analysis2)
    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0

def test_pairwise_self_recursive_no_store_requires_validated_recurrence_artifact(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_self_recursive_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0
    evidence = [
        item
        for item in analysis1.completed_recovery_proof_evidence
        if item.get("evidence_kind") == "call_effect_summary"
    ]
    assert evidence == []

def test_pairwise_preproducer_complete_call_argument_evidence_requires_pending_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(
        formula_builder,
        solver_runner,
        debug=False,
        enable_completed_recovery_proofs=False,
    )
    analysis1 = _analysis_with_effect_call_argument_evidence()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    reason = result.unknown_reasons[0]
    assert reason.reason_id == "call_argument_extraction_incomplete"
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.detail == "function1:effect_call_argument_evidence"
    assert reason.object_target_key[0] == "call_argument_evidence"
    assert reason.object_evidence is not None
    assert reason.object_evidence["object_derived"] is True
    assert reason.object_evidence["runtime_ref"] == (
        "runtime_ref",
        "call_argument",
        ("pcode_op_ref", reason.object_target_key[3]),
        ("callee_identity", reason.object_target_key[4]),
    )
    assert reason.object_evidence["argument_storage"] == reason.object_target_key[5]
    assert reason.object_evidence["callsite_storage"] == (
        "callsite_storage",
        "call_argument",
        ("argument_keys", reason.object_target_key[5]),
    )

def test_pairwise_complete_call_argument_evidence_requires_explicit_phase15_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_effect_call_argument_evidence()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].detail == "function1:effect_call_argument_evidence"
    evidence = [
        item
        for item in analysis1.completed_recovery_proof_evidence
        if item.get("proof_source") == "call_argument_evidence_complete"
    ]
    assert evidence == []

def test_pairwise_preserves_call_effect_reason_alongside_return_coverage_gap(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.effect_summary = _analysis_with_effect_call_argument_evidence().effect_summary
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    reason_ids = [reason.reason_id for reason in result.unknown_reasons]
    assert UnknownReasonId.RETURN_COVERAGE_GAP.value in reason_ids
    assert "call_argument_extraction_incomplete" in reason_ids
    effect_reasons = [
        reason
        for reason in result.unknown_reasons
        if reason.reason_id == "call_argument_extraction_incomplete"
    ]
    assert effect_reasons
    assert effect_reasons[0].detail == "function1:effect_call_argument_evidence"
    assert effect_reasons[0].recovery_proof_kind == (
        UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value
    )

def test_pairwise_matched_unknown_indirect_no_store_call_effect_recovers(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    for analysis in (analysis1, analysis2):
        evidence = [
            item
            for item in analysis.completed_recovery_proof_evidence
            if item.get("proof_source") == "matched_unknown_indirect_no_store_call_effect"
        ]
        assert len(evidence) == 1
        content = evidence[0]["proof_content"]
        assert content["proof_rule"] == "matched_unknown_indirect_no_store_call_effect"
        assert (
            content["call_effect_summary"]["matching_local_unsupported_call_site_count"]
            == 1
        )
        assert (
            content["call_effect_summary"]["matching_peer_unsupported_call_site_count"]
            == 1
        )
        assert content["call_effect_surface"]["guard_equivalence_mode"] == "path_guard_equivalence"
        assert (
            content["call_effect_surface"]["caller_observed_memory_write"][
                "local_store_effect_count"
            ]
            == 0
        )
        assert (
            content["call_effect_surface"]["call_output_use"]["classification"]
            == "not_exposed_to_return_or_call_effect_surface"
        )
        assert content["runtime_ref"]["matched_target_expression_key"]
        assert content["callsite_storage"]["matched_argument_keys"]

def test_pairwise_unknown_indirect_callsite_path_guard_mismatch_keeps_unknown(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    a = Expression.parameter("a", 1, size=4)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        path_conditions=(_eq(a, _const(0)),),
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        path_conditions=(_ne(a, _const(0)),),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_unknown_indirect_no_store_call_effect"
    ]

def test_call_effect_summary_proof_rejects_occurrence_index_mismatch():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
    )
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    evidence = _complete_call_effect_summary_proof_evidence(reason.object_target_key)
    evidence["proof_content"]["call_effect_surface"]["peer_call_occurrence"][
        "occurrence_index"
    ] = 1

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()

def test_pairwise_unknown_indirect_output_used_as_later_call_argument_keeps_unknown(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
    )
    first = analysis1.effect_summary.unsupported_call_sites[0]
    later = UnsupportedCallEffectRef(
        pcode_op_ref=PcodeOpRef(
            address_offset=0x1050,
            seq_time=6,
            seq_order=3,
            block_index=0,
            mnemonic="CALLIND",
            input_sizes=(8, 4),
            binary_id="B10",
            function_entry_space="ram",
            function_entry_offset=0x1000,
            target_space="ram",
            target_offset=0x1050,
            opcode=8,
            local_op_ordinal=2,
        ),
        target_ref=first.target_ref,
        target_expr=Expression.parameter("fp", 0, size=8),
        arguments=(Expression.unknown("first_call_result", runtime_ref=first.pcode_op_ref),),
        path_conditions=first.path_conditions,
        reason=first.reason,
        order_key=11,
    )
    analysis1.effect_summary.unsupported_call_sites = (first, later)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_unknown_indirect_no_store_call_effect"
    ]

def test_pairwise_unknown_indirect_duplicate_call_effect_does_not_auto_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
    )
    original = analysis1.effect_summary.unsupported_call_sites[0]
    duplicate = UnsupportedCallEffectRef(
        pcode_op_ref=PcodeOpRef(
            address_offset=0x1040,
            seq_time=5,
            seq_order=2,
            block_index=0,
            mnemonic="CALLIND",
            input_sizes=(8, 4, 4),
            binary_id="B10",
            function_entry_space="ram",
            function_entry_offset=0x1000,
            target_space="ram",
            target_offset=0x1040,
            opcode=8,
            local_op_ordinal=1,
        ),
        target_ref=original.target_ref,
        target_expr=original.target_expr,
        arguments=original.arguments,
        reason=original.reason,
        order_key=9,
    )
    analysis1.effect_summary.unsupported_call_sites = (original, duplicate)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_unknown_indirect_no_store_call_effect"
    ]

def test_pairwise_matched_parameter_exposure_unsupported_call_effect_recovers(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        reason="callee_unsupported_call_may_expose_parameter_memory",
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        reason="callee_unsupported_call_may_expose_parameter_memory",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    for analysis in (analysis1, analysis2):
        evidence = [
            item
            for item in analysis.completed_recovery_proof_evidence
            if item.get("proof_source")
            == "matched_unsupported_call_parameter_exposure_no_store_call_effect"
        ]
        assert len(evidence) == 1
        content = evidence[0]["proof_content"]
        assert content["proof_rule"] == "matched_unsupported_call_parameter_exposure_no_store_call_effect"
        assert (
            content["call_effect_summary"]["unsupported_reason"]
            == "callee_unsupported_call_may_expose_parameter_memory"
        )

def test_pairwise_mixed_unsupported_call_reason_is_compatible_recovers(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        reason="callee_unsupported_call_may_expose_parameter_memory",
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        reason="target_identity_unavailable",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert len([
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_unknown_indirect_no_store_call_effect"
    ]) == 2

def test_pairwise_incompatible_unsupported_call_reason_keeps_unknown(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        reason="target_identity_unavailable",
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        reason="callee_effect_summary_incomplete",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert len(result.unknown_reasons) == 2
    assert all(
        not [
            item
            for item in analysis.completed_recovery_proof_evidence
            if item.get("proof_source")
            in (
                "matched_unknown_indirect_no_store_call_effect",
                "matched_unsupported_call_parameter_exposure_no_store_call_effect",
            )
        ]
        for analysis in (analysis1, analysis2)
    )

def test_pairwise_matched_deferred_call_argument_evidence_recovers(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    for analysis in (analysis1, analysis2):
        evidence = [
            item
            for item in analysis.completed_recovery_proof_evidence
            if item.get("proof_source") == "matched_deferred_call_argument_evidence"
        ]
        assert len(evidence) == 1
        content = evidence[0]["proof_content"]
        assert content["proof_rule"] == "matched_deferred_call_argument_evidence"
        assert content["runtime_ref"]["matched_target_expression_key"]
        assert content["callsite_storage"]["matched_argument_keys"]
        assert content["call_effect_summary"]["matching_local_deferred_call_count"] == 1
        assert content["call_effect_summary"]["matching_peer_deferred_call_count"] == 1

def test_pairwise_unresolved_deferred_call_return_lowers_with_matched_argument_evidence(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        return_deferred_unknown=True,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        return_deferred_unknown=True,
    )
    _patch_pairwise_single_case(monkeypatch, strategy, analysis1, analysis2)
    solver_runner.run_sequential = Mock(
        side_effect=[
            ParallelResult(
                results=[
                    SolverResult(
                        solver_name="z3",
                        status=SolverStatus.SAT,
                        elapsed_time=0.001,
                    )
                ]
            ),
            ParallelResult(
                results=[
                    SolverResult(
                        solver_name="z3",
                        status=SolverStatus.UNSAT,
                        elapsed_time=0.001,
                    )
                ]
            ),
        ]
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert solver_runner.run_sequential.call_count == 2
    assertions = base_ctx["pairwise_extra_assertions_by_pair"]["(0,0)"]
    assert assertions[0].startswith("; unresolved_expression runtime-unknown equality")
    assert any(line.startswith("(assert (= rtunk_") for line in assertions)
    query = solver_runner.run_sequential.call_args_list[1].args[0]
    assert "; Pair-local object-derived assumptions" in query
    assert any(line in query for line in assertions if line.startswith("(assert (= rtunk_"))
    evidence = base_ctx["pairwise_unresolved_deferred_call_lowering_evidence_by_pair"]["(0,0)"]
    assert len(evidence) == 1
    assert evidence[0][0] == "matched_deferred_call_runtime_unknown"
    assert ("lowering_kind", "deferred_call") in evidence[0]

def test_pairwise_unresolved_deferred_call_missing_target_expr_stays_unknown(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        target_expr_missing=True,
        return_deferred_unknown=True,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        target_expr_missing=True,
        return_deferred_unknown=True,
    )
    _patch_pairwise_single_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_after_guard = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        "call_argument_extraction_incomplete",
        "call_argument_extraction_incomplete",
    ]
    assert {
        reason.detail for reason in result.unknown_reasons
    } == {
        "function1:effect_call_argument_evidence_incomplete",
        "function2:effect_call_argument_evidence_incomplete",
    }
    assert "pairwise_extra_assertions_by_pair" not in formula_builder.build_base_context.return_value
    strategy._solve_query_after_guard.assert_not_called()

def test_pairwise_unresolved_deferred_call_width_mismatch_stays_unknown(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        return_deferred_unknown=True,
        unknown_size=4,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        return_deferred_unknown=True,
        unknown_size=8,
    )
    _patch_pairwise_single_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_after_guard = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        "expression_translation_incomplete"
    ]
    strategy._solve_query_after_guard.assert_not_called()

def test_pairwise_deferred_call_missing_target_expr_does_not_auto_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        target_expr_missing=True,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        target_expr_missing=True,
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert {
        reason.detail for reason in result.unknown_reasons
    } == {
        "function1:effect_call_argument_evidence_incomplete",
        "function2:effect_call_argument_evidence_incomplete",
    }
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_deferred_call_argument_evidence"
    ]

def test_pairwise_deferred_call_argument_mismatch_does_not_auto_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        argument_indices=(1, 2),
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        argument_indices=(2, 1),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert len(result.unknown_reasons) == 2
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_deferred_call_argument_evidence"
    ]

def test_pairwise_deferred_call_empty_arguments_does_not_auto_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        argument_indices=(),
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        argument_indices=(),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert {
        reason.detail for reason in result.unknown_reasons
    } == {
        "function1:effect_call_argument_evidence_incomplete",
        "function2:effect_call_argument_evidence_incomplete",
    }
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_deferred_call_argument_evidence"
    ]

def test_pairwise_unresolved_deferred_call_empty_arguments_stays_unknown(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        argument_indices=(),
        return_deferred_unknown=True,
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        argument_indices=(),
        return_deferred_unknown=True,
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
    )
    _patch_pairwise_single_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_after_guard = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        "expression_translation_incomplete"
    ]
    strategy._solve_query_after_guard.assert_not_called()

def test_pairwise_unresolved_deferred_call_store_effect_stays_unknown(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        return_deferred_unknown=True,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        return_deferred_unknown=True,
    )
    analysis1.effect_summary.effects = [
        StoreEffect(
            location=CanonicalLocation("fp", 0, 4),
            value=_const(1),
            conditions=[],
            order_key=1,
        )
    ]
    _patch_pairwise_single_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_after_guard = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert "pairwise_extra_assertions_by_pair" not in base_ctx
    strategy._solve_query_after_guard.assert_not_called()

def test_pairwise_unresolved_deferred_call_incomplete_summary_stays_unknown(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        return_deferred_unknown=True,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        return_deferred_unknown=True,
    )
    analysis2.effect_summary.incomplete_reasons = ("effect_summary_path_coverage_incomplete",)
    _patch_pairwise_single_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_after_guard = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert "pairwise_extra_assertions_by_pair" not in base_ctx
    strategy._solve_query_after_guard.assert_not_called()

def test_pairwise_deferred_call_duplicate_candidate_does_not_auto_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        duplicate=True,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_deferred_call_argument_evidence"
    ]

def test_pairwise_deferred_call_weak_completed_evidence_does_not_recover(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
    )
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    analysis1.completed_recovery_proof_evidence = (
        _call_effect_summary_proof_evidence(
            object_target_key=reason.object_target_key,
            proof_obligation_id=reason.proof_obligation_id,
            proof_source="matched_deferred_call_argument_evidence",
            proof_content={
                "object_derived": True,
                "status": "complete",
                "proof_rule": "matched_deferred_call_argument_evidence",
                "object_target_key": reason.object_target_key,
                "call_effect_summary": {
                    "status": "complete",
                    "summary_source": ("effect_summary", "deferred_call"),
                    "evidence_kind": "call_effect_summary",
                    "object_target_key": reason.object_target_key,
                },
                "runtime_ref": {
                    "status": "complete",
                    "runtime_ref": PairwiseStrategy._expected_deferred_call_proof_content_refs(
                        reason.object_target_key
                    )[0],
                },
                "callsite_storage": {
                    "status": "complete",
                    "callsite_storage": PairwiseStrategy._expected_deferred_call_proof_content_refs(
                        reason.object_target_key
                    )[1],
                },
            },
        ),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    _evidence_of_this_pair(analysis1, analysis2)
    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons

def test_pairwise_deferred_call_empty_argument_completed_evidence_does_not_recover(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_deferred_call_argument_blocker(
        function_name="func1",
        binary_id="B1",
        entry=0x1000,
        argument_indices=(),
    )
    analysis2 = _analysis_with_deferred_call_argument_blocker(
        function_name="func2",
        binary_id="B14",
        entry=0x2000,
        argument_indices=(),
    )
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    peer_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function2:effect_call_argument_evidence_incomplete",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    runtime_ref, callsite_storage = PairwiseStrategy._expected_deferred_call_proof_content_refs(
        reason.object_target_key
    )
    peer_runtime_ref, peer_callsite_storage = PairwiseStrategy._expected_deferred_call_proof_content_refs(
        peer_reason.object_target_key
    )
    target_key = PairwiseStrategy._cross_binary_call_effect_component_key(
        PairwiseStrategy._deferred_call_target_expression_key(reason.object_target_key)
    )
    analysis1.completed_recovery_proof_evidence = (
        _call_effect_summary_proof_evidence(
            object_target_key=reason.object_target_key,
            proof_obligation_id=reason.proof_obligation_id,
            proof_source="matched_deferred_call_argument_evidence",
            proof_content={
                "object_derived": True,
                "status": "complete",
                "proof_rule": "matched_deferred_call_argument_evidence",
                "object_target_key": reason.object_target_key,
                "peer_object_target_key": peer_reason.object_target_key,
                "call_effect_summary": {
                    "status": "complete",
                    "summary_source": ("effect_summary", "deferred_call"),
                    "evidence_kind": "call_effect_summary",
                    "object_target_key": reason.object_target_key,
                    "peer_object_target_key": peer_reason.object_target_key,
                    "local_store_effect_count": 0,
                    "matching_local_deferred_call_count": 1,
                    "matching_peer_deferred_call_count": 1,
                },
                "runtime_ref": {
                    "status": "complete",
                    "runtime_ref": runtime_ref,
                    "peer_runtime_ref": peer_runtime_ref,
                    "matched_target_expression_key": target_key,
                },
                "callsite_storage": {
                    "status": "complete",
                    "callsite_storage": callsite_storage,
                    "peer_callsite_storage": peer_callsite_storage,
                    "matched_argument_keys": (),
                },
            },
        ),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons

def test_pairwise_incomplete_call_argument_evidence_does_not_auto_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_effect_call_argument_evidence()
    complete_evidence = next(iter(analysis1.effect_summary.call_argument_evidence.values()))
    incomplete_evidence = CallArgumentEvidence(
        pcode_op_ref=complete_evidence.pcode_op_ref,
        target_ref=complete_evidence.target_ref,
        callee_param_identities=complete_evidence.callee_param_identities,
        arguments=(),
        sources=(),
        path_conditions=complete_evidence.path_conditions,
        coverage_complete=False,
        recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        reason="argument_recovery_inconclusive",
    )
    analysis1.effect_summary.call_argument_evidence = {
        complete_evidence.pcode_op_ref.stable_key(): incomplete_evidence,
    }
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].detail == "function1:effect_call_argument_evidence"
    assert not [
        item
        for item in analysis1.completed_recovery_proof_evidence
        if item.get("recovery_proof_kind") == UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value
    ]

def test_pairwise_bounded_call_argument_evidence_auto_records_phase15_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_effect_call_argument_evidence()
    analysis1.analysis_notes.append("bounded_call_refinement_deferred_expanded")
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        analysis1,
    )
    _attach_bounded_call_refinement_expansion_evidence(analysis1, object_target_key)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    evidence = [
        item
        for item in analysis1.completed_recovery_proof_evidence
        if item.get("proof_source") == "call_argument_evidence_phase15_complete"
    ]
    assert len(evidence) == 1
    content = evidence[0]["proof_content"]
    assert content["proof_rule"] == "call_argument_evidence_phase15_complete"
    assert content["callee_summary_completion"]["return_coverage_status"] == "complete"
    assert content["callee_precondition"]["abi_coercion"]["callee_parameter_interpretation"]
    assert content["argument_value_provenance"]["value_provenance_equivalent"] is True
    assert content["bounded_refinement"]["evidence_kind"] == "bounded_call_refinement_expansion"

def test_pairwise_bounded_call_argument_note_without_evidence_does_not_auto_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_effect_call_argument_evidence()
    analysis1.analysis_notes.append("bounded_call_refinement_deferred_expanded")
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert not [
        item
        for item in analysis1.completed_recovery_proof_evidence
        if item.get("proof_source") == "call_argument_evidence_phase15_complete"
    ]

def test_call_argument_evidence_ignores_metadata_only_completed_proof():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _call_effect_summary_proof_evidence(object_target_key=object_target_key)

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()

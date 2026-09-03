from scripts.function_tracer_pcode.tests.unit._sat_decisiveness_fixtures import *

def test_pairwise_strategy_downgrades_sat_when_return_cases_leave_coverage_gap(monkeypatch):
    formula_builder = Mock()
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
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    x = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x, _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(2), conditions=[])],
        return_type="int",
    )

    case1 = ReturnCase(
        index=0,
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=_const(1),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(2),
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
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.proof.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("pairwise counterexample validation should not run when coverage is incomplete")
        ),
    )
    strategy._solve_query_after_guard = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 7, "x_2": 7},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    assert "return_case_coverage_gap" in analysis1.analysis_notes
    assert analysis2.analysis_notes == []

def test_pairwise_strategy_does_not_prove_equivalent_with_return_coverage_gap(monkeypatch):
    formula_builder = Mock()
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
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    x = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x, _const(0))])],
        return_type="int",
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
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
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
    assert "return_case_coverage_gap" in analysis1.analysis_notes

def test_pairwise_return_coverage_covered_side_emits_completed_proof_evidence(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert analysis1.completed_recovery_proof_evidence == ()
    evidence = analysis2.completed_recovery_proof_evidence
    assert {item["proof_stage"] for item in evidence} == {
        "return_partition_extraction",
        "return_guard_coverage",
    }
    assert all(item["object_derived"] is True for item in evidence)
    assert all(item["coverage_status"] == "covered" for item in evidence)

    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function2:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    expected_actions = build_unknown_recovery_actions([completed_reason])
    assert {
        tuple(item["proof_obligation_id"])
        for item in evidence
    } == {action.proof_obligation_id for action in expected_actions}
    assert PairwiseStrategy._completed_recovery_proof_ids(analysis2) == tuple(
        action.proof_obligation_id for action in expected_actions
    )

    strategy.check(analysis1, analysis2)

    assert len(analysis2.completed_recovery_proof_evidence) == 2

def test_pairwise_collect_return_coverage_reason_uses_current_coverage_check_when_notes_are_stale(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(
        formula_builder,
        solver_runner,
        debug=False,
        enable_completed_recovery_proofs=False,
    )
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.analysis_notes = ["return_case_coverage_inconclusive"]
    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ReturnCoverageCheckResult("covered"),
    )

    reasons = strategy._collect_return_coverage_unsafety_reasons(
        _base_context_for_single_int_param(),
        [],
        [],
        lambda value: value,
        lambda value: value,
        analysis1,
        analysis2,
    )

    assert reasons == []

def test_pairwise_return_coverage_gap_requires_all_completed_proof_ids(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.get_decisive_sat_unsafety_reasons = lambda: ["return_coverage_gap"]
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([pending_reason])
    analysis1.completed_recovery_proof_evidence = (
        _return_coverage_completion_evidence(actions[0]),
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value

def test_pairwise_return_coverage_gap_completed_proofs_allow_equivalent(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.get_decisive_sat_unsafety_reasons = lambda: ["return_coverage_gap"]
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([pending_reason])
    analysis1.completed_recovery_proof_evidence = tuple(
        _return_coverage_completion_evidence(action)
        for action in actions
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0

def test_return_coverage_proof_content_requires_disjunction_and_normalized_guard():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    proof_stage_actions = build_unknown_recovery_actions([pending_reason])
    action = proof_stage_actions[0]
    evidence = _return_coverage_completion_evidence(action, reason_id=UnknownReasonId.RETURN_COVERAGE_GAP)
    assert strategy._return_coverage_proof_content_is_complete(
        evidence,
        UnknownReasonId.RETURN_COVERAGE_GAP,
    )

    invalid_empty_cases = dict(evidence)
    invalid_empty_cases["proof_content"] = {
        "case_guard_disjunction": {
            "status": "complete",
            "query_cases": ("(true)",),
        },
        "normalized_guard_formula": {
            "status": "complete",
            "query": "(or true)",
        },
    }
    assert not strategy._return_coverage_proof_content_is_complete(
        invalid_empty_cases,
        UnknownReasonId.RETURN_COVERAGE_GAP,
    )

    valid_guard_evidence = deepcopy(evidence)
    assert strategy._return_coverage_proof_content_is_complete(
        valid_guard_evidence,
        UnknownReasonId.RETURN_COVERAGE_GAP,
    )

def test_return_coverage_proof_completion_rejects_empty_case_guard_disjunction(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})
        ]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.get_decisive_sat_unsafety_reasons = lambda: ["return_coverage_gap"]
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([pending_reason])
    analysis1.completed_recovery_proof_evidence = (
        _return_coverage_completion_evidence(
            actions[0],
            reason_id=UnknownReasonId.RETURN_COVERAGE_GAP,
            proof_content={
                "case_guard_disjunction": {
                    "status": "complete",
                    "query_cases": (),
                },
                "normalized_guard_formula": {
                    "status": "complete",
                    "query": "(or true)",
                },
            },
        ),
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value

def test_pairwise_return_coverage_gap_wrong_completed_proof_id_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([pending_reason])
    wrong_id = build_proof_obligation_id(
        UnknownReasonId.RETURN_COVERAGE_GAP,
        actions[0].proof_stage,
        UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
        actions[0].evidence_kind,
        ("return_coverage", "different-target"),
    )
    analysis1.completed_recovery_proof_evidence = (
        _return_coverage_completion_evidence(actions[0], proof_obligation_id=wrong_id),
        _return_coverage_completion_evidence(actions[1]),
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value

def test_pairwise_return_coverage_gap_missing_completed_proof_id_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    pending_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([pending_reason])
    analysis1.completed_recovery_proof_evidence = tuple(
        _return_coverage_completion_evidence_without_proof_id(action)
        for action in actions
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value

def test_pairwise_return_coverage_inconclusive_unknown_does_not_complete_proof(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    for label, analysis in (("function1", analysis1), ("function2", analysis2)):
        blocking_reason = f"{label}:return_coverage_inconclusive"
        reason = strategy._make_blocking_unsafety_unknown_reason(
            blocking_reason,
            analysis1,
            analysis2,
            stage="S_PAIRWISE",
        )
        actions = build_unknown_recovery_actions([reason])
        analysis.completed_recovery_proof_evidence = tuple(
            _return_coverage_completion_evidence(
                action,
                reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            )
            for action in actions
        )
    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
        ),
    )
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE.value,
        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE.value,
    ]
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0

def test_pairwise_return_coverage_inconclusive_query_unknown_records_recovery_proof(monkeypatch):
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))])],
        return_type="int",
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
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            can_record_completion_proof=True,
            detail="function1 return-case coverage query was inconclusive",
        ),
    )
    reasons = strategy._collect_return_coverage_unsafety_reasons(
        _base_context_for_single_int_param(),
        [case1],
        [case2],
        lambda value: value,
        lambda value: value,
        analysis1,
        analysis2,
    )

    assert reasons == ["function1:return_coverage_inconclusive", "function2:return_coverage_inconclusive"]
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_inconclusive",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([reason])
    assert actions
    assert analysis1.completed_recovery_proof_evidence == ()

def test_pairwise_return_coverage_inconclusive_unresolved_expression_does_not_auto_complete(monkeypatch):
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    case1 = ReturnCase(
        index=0,
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            detail=(
                "function1 return-case coverage query skipped:"
                " unresolved condition expression"
            ),
        ),
    )
    reasons = strategy._collect_return_coverage_unsafety_reasons(
        _base_context_for_single_int_param(),
        [case1],
        [case2],
        lambda value: value,
        lambda value: value,
        analysis1,
        analysis2,
    )

    assert reasons == ["function1:return_coverage_inconclusive", "function2:return_coverage_inconclusive"]
    assert analysis1.completed_recovery_proof_evidence == ()


def test_pairwise_return_coverage_accepts_typed_v2_string_reason(monkeypatch):
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )
    monkeypatch.setattr(
        strategy,
        "_outcome_partition_covered_labels",
        lambda *_args, **_kwargs: set(),
    )
    monkeypatch.setattr(
        strategy,
        "_outcome_partition_inconclusive_labels",
        lambda *_args, **_kwargs: {"function1"},
    )
    strategy._last_unary_outcome_blockers = {
        "function1": "outcome_partition_completion_unproven",
    }

    reasons = strategy._collect_return_coverage_unsafety_reasons(
        _base_context_for_single_int_param(),
        [case1],
        [case2],
        lambda value: value,
        lambda value: value,
        analysis1,
        analysis2,
    )

    assert reasons[0] == "function1:outcome_partition_completion_unproven"

def test_pairwise_return_coverage_non_dischargeable_inconclusive_causes_do_not_auto_complete(monkeypatch):
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    case1 = ReturnCase(
        index=0,
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )

    for cause in ("object_identity_unsupported", "unresolved_expression", "missing_header_context"):
        analysis1.completed_recovery_proof_evidence = ()
        monkeypatch.setattr(
            strategy,
            "_check_return_case_coverage_gap",
            lambda *_args, cause=cause, **_kwargs: ReturnCoverageCheckResult(
                status="inconclusive",
                reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
                can_record_completion_proof=True,
                inconclusive_cause=cause,
            ),
        )
        reasons = strategy._collect_return_coverage_unsafety_reasons(
            _base_context_for_single_int_param(),
            [case1],
            [case2],
            lambda value: value,
            lambda value: value,
            analysis1,
            analysis2,
        )

        assert reasons == ["function1:return_coverage_inconclusive", "function2:return_coverage_inconclusive"]
        assert analysis1.completed_recovery_proof_evidence == ()

def test_pairwise_return_coverage_inconclusive_invalid_proof_content_is_not_recorded(monkeypatch):
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    case1 = ReturnCase(
        index=0,
        conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type=analysis1.return_type or "int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type=analysis2.return_type or "int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_check_return_case_coverage_gap",
        lambda *_args, **_kwargs: ReturnCoverageCheckResult(
            status="inconclusive",
            reason_id=UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
            can_record_completion_proof=True,
            detail="function1 return-case coverage query was inconclusive",
        ),
    )
    monkeypatch.setattr(
        strategy,
        "_return_coverage_inconclusive_proof_content",
        lambda **_kwargs: {},
    )
    reasons = strategy._collect_return_coverage_unsafety_reasons(
        _base_context_for_single_int_param(),
        [case1],
        [case2],
        lambda value: value,
        lambda value: value,
        analysis1,
        analysis2,
    )

    assert reasons == ["function1:return_coverage_inconclusive", "function2:return_coverage_inconclusive"]
    assert analysis1.completed_recovery_proof_evidence == ()

def test_return_coverage_non_smt_covered_proof_content_does_not_claim_unsat():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis = FunctionReturnAnalysis(
        function_name="func",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[])],
        return_type="int",
    )
    case = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis.returns[0].value,
        return_info=analysis.returns[0],
        return_type=analysis.return_type or "int",
        parameters=analysis.parameters,
    )

    proof_content = strategy._return_coverage_covered_proof_content(
        base_ctx=_base_context_for_single_int_param(),
        label="function1",
        cases=[case],
        replace_fn=lambda value: value,
        coverage_proof_method="unconditional_return_case",
        solver_status=None,
    )

    assert proof_content["coverage_solver_evidence"]["status"] == "not_applicable"
    assert proof_content["coverage_solver_evidence"]["proof_method"] == "unconditional_return_case"

def test_pairwise_keeps_global_coverage_gap_with_sat_unsafety(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.effect_summary = _analysis_with_unsupported_call_effect().effect_summary
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)
    sat_result = _solver_bound_query_result(
        False,
        model={"x_1": 0, "x_2": 0},
        query="(assert (distinct (_ bv1 32) (_ bv2 32)))\n(check-sat)",
    )
    strategy._solve_query_after_guard = Mock(return_value=sat_result)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    reason_ids = {reason.reason_id for reason in result.unknown_reasons}
    assert "counterexample_analysis_safety_unproven" in reason_ids
    assert UnknownReasonId.RETURN_COVERAGE_GAP.value in reason_ids
    assert result.unknown_reasons[0].reason_id == "counterexample_analysis_safety_unproven"
    assert any(
        reason.reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
        and reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
        for reason in result.unknown_reasons
    )

def test_monolithic_strategy_downgrades_sat_when_return_cases_leave_coverage_gap():
    class _CoverageGapSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(
                results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
            )

        def run_sequential(self, query: str):
            if "Return coverage gap query: function1" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
                )
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    x1 = Expression.parameter("x", 0, size=4)
    x2 = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x1, _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x2, conditions=[])],
        return_type="int",
    )

    params1 = [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)]
    params2 = [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)]
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": params1,
        "params2": params2,
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _CoverageGapSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None

def test_monolithic_strategy_does_not_accept_unsat_with_return_coverage_gap():
    class _CoverageGapUnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, query: str):
            if "Return coverage gap query: function1" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
                )
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    x1 = Expression.parameter("x", 0, size=4)
    x2 = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(x1, _const(0))])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x2, conditions=[])],
        return_type="int",
    )

    params1 = [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)]
    params2 = [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)]
    formula_builder = Mock()
    formula_builder.build_equivalence_formula_extended.return_value = FormulaBuilderResult(
        formula="(set-logic QF_BV)\n(check-sat)",
        return_var1="return_1",
        return_var2="return_2",
        constrained_fragments=[],
        extra_vars1=[],
        extra_vars2=[],
        param_fragment_constrained=[],
    )
    formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const x_1 (_ BitVec 32))",
            "(declare-const x_2 (_ BitVec 32))",
            "(assert (= x_1 x_2))",
        ],
        "params1": params1,
        "params2": params2,
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _CoverageGapUnsatSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None
    assert "return_case_coverage_gap" in analysis1.analysis_notes
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert result.unknown_reasons[0].stage == "S_MONOLITHIC_FALLBACK"
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert result.unknown_reasons[0].recovery_action == "return_coverage_proof_required"
    assert result.unknown_reasons[0].object_target_key[0] == "return_coverage"
    actions = build_unknown_recovery_actions(result.unknown_reasons)
    assert {action.status for action in actions} == {UnknownRecoveryActionStatus.PENDING_PROOF.value}
    assert all(action.proof_obligation_id is not None for action in actions)

def test_monolithic_return_coverage_gap_completed_proofs_allow_equivalent():
    strategy, analysis1, analysis2 = _monolithic_return_coverage_gap_setup()
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_MONOLITHIC_FALLBACK",
    )
    actions = build_unknown_recovery_actions([completed_reason])
    analysis1.completed_recovery_proof_evidence = tuple(
        _return_coverage_completion_evidence(action)
        for action in actions
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert result.counterexample_raw is None

def test_monolithic_return_coverage_gap_missing_completed_proof_id_does_not_recover():
    strategy, analysis1, analysis2 = _monolithic_return_coverage_gap_setup()
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_MONOLITHIC_FALLBACK",
    )
    actions = build_unknown_recovery_actions([completed_reason])
    analysis1.completed_recovery_proof_evidence = tuple(
        _return_coverage_completion_evidence_without_proof_id(action)
        for action in actions
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert result.unknown_reasons[0].action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert result.counterexample_raw is None

def test_function_return_analysis_skips_monolithic_fallback_when_coverage_gap_note_is_present():
    analysis = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=_const(1), conditions=[_eq(Expression.parameter("x", 0, size=4), _const(0))])],
        return_type="int",
        analysis_notes=["return_case_coverage_gap"],
    )

    assert analysis.should_skip_monolithic_fallback() is True
    assert "return_case_coverage_gap" in analysis.get_decisive_sat_unsafety_reasons()

def test_blocking_unsafety_reason_mapping_accepts_detail_suffix_for_return_coverage():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)

    assert (
        strategy._unknown_reason_id_for_blocking_unsafety("function1:return_coverage_gap:case=3")
        == UnknownReasonId.RETURN_COVERAGE_GAP
    )
    assert (
        strategy._unknown_reason_id_for_blocking_unsafety("function2:return_coverage_inconclusive:branch=exit")
        == UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE
    )

def test_analysis_requires_completed_return_coverage_proof_uses_reason_kind_for_suffixes():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)

    class _Analysis:
        def get_decisive_sat_unsafety_reasons(self):
            return (
                "return_case_coverage_inconclusive:branch=exit",
                "effect_summary_path_coverage_incomplete",
            )

    analysis = _Analysis()
    assert (
        strategy._analysis_requires_completed_return_coverage_proof(
            analysis,
            ignored_reason_ids=(),
        )
        is not None
    )
    assert (
        strategy._analysis_requires_completed_return_coverage_proof(
            analysis,
            ignored_reason_ids=(UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,),
        )
        == "effect_observation_coverage_incomplete"
    )
    assert (
        strategy._unknown_reason_id_for_blocking_unsafety(
            "function1:effect_summary_path_coverage_incomplete"
        )
        == "effect_observation_coverage_incomplete"
    )

def test_return_coverage_gap_emits_object_derived_pending_proof_backlog():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    x = Expression.parameter("x", 0, size=4)
    return_ref = PcodeOpRef(
        address_offset=0x401020,
        seq_time=0x401020,
        seq_order=3,
        block_index=1,
        mnemonic="RETURN",
        input_sizes=(8, 4),
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x401000",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(
                address="0x401020",
                value=_const(1),
                conditions=[_eq(x, _const(0))],
                pcode_op_ref=return_ref,
            )
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x402000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x402020", value=_const(1), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([reason])

    assert reason.reason_id == UnknownReasonId.RETURN_COVERAGE_GAP.value
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.recovery_action == "return_coverage_proof_required"
    assert reason.object_target_key[0] == "return_coverage"
    assert _nested_contains(reason.object_target_key, return_ref.stable_key())
    assert ("return_storage", "return_value", 32, None, "int") in reason.object_target_key
    assert [action.proof_stage for action in actions] == [
        "return_partition_extraction",
        "return_guard_coverage",
    ]
    assert {action.status for action in actions} == {
        UnknownRecoveryActionStatus.PENDING_PROOF.value
    }
    assert actions[0].proof_obligation_id == build_proof_obligation_id(
        UnknownReasonId.RETURN_COVERAGE_GAP,
        "return_partition_extraction",
        UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
        "missing_return_guard",
        reason.object_target_key,
    )

def test_return_coverage_inconclusive_emits_smt_disambiguation_pending_proof_backlog():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    x = Expression.parameter("x", 0, size=4)
    return_ref = PcodeOpRef(
        address_offset=0x401020,
        seq_time=0x401020,
        seq_order=3,
        block_index=1,
        mnemonic="RETURN",
        input_sizes=(8, 4),
    )
    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x401000",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(
                address="0x401020",
                value=_const(1),
                conditions=[_eq(x, _const(0))],
                pcode_op_ref=return_ref,
            )
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x402000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x402020", value=_const(1), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_inconclusive",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    actions = build_unknown_recovery_actions([reason])

    assert reason.reason_id == UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE.value
    assert reason.recovery_action == "return_coverage_proof_required"
    assert [action.proof_stage for action in actions] == [
        "return_coverage_smt_disambiguation",
    ]
    assert actions[0].evidence_kind == "case_guard_disjunction"
    assert actions[0].proof_obligation_id == build_proof_obligation_id(
        UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE,
        "return_coverage_smt_disambiguation",
        UnknownRecoveryProofKind.RETURN_COVERAGE_COMPLETION,
        "case_guard_disjunction",
        reason.object_target_key,
    )

def test_return_coverage_target_identity_is_deterministic_for_rebuilt_ast_and_case_order():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    other = _coverage_identity_analysis(binary_id="B2")
    first = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        _coverage_identity_analysis(binary_id="B1", returns_order=(0, 1)),
        other,
    )
    rebuilt = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        _coverage_identity_analysis(binary_id="B1", returns_order=(0, 1)),
        other,
    )
    reordered = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        _coverage_identity_analysis(binary_id="B1", returns_order=(1, 0)),
        other,
    )

    assert first == rebuilt
    assert first == reordered
    assert strategy._return_coverage_object_target_key_is_valid(first)

def test_return_coverage_target_identity_distinguishes_binary_identity():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    other = _coverage_identity_analysis(binary_id="B9")
    target_b1 = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        _coverage_identity_analysis(binary_id="B1"),
        other,
    )
    target_b2 = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        _coverage_identity_analysis(binary_id="B2"),
        other,
    )

    assert target_b1 != target_b2

def test_return_coverage_completed_evidence_rejects_exact_target_and_schema_mismatch():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    valid = _return_coverage_completion_evidence(action)
    assert strategy._return_coverage_proof_id_from_evidence(valid) == action.proof_obligation_id

    side_mismatch = deepcopy(valid)
    side_target = list(side_mismatch["object_target_key"])
    side_target[2] = "function2"
    side_mismatch["object_target_key"] = tuple(side_target)
    assert strategy._return_coverage_proof_id_from_evidence(side_mismatch) is None

    schema_mismatch = deepcopy(valid)
    schema_mismatch["target_schema_version"] = -1
    assert strategy._return_coverage_proof_id_from_evidence(schema_mismatch) is None

    target_content_mismatch = deepcopy(valid)
    target_content_mismatch["proof_content"] = dict(target_content_mismatch["proof_content"])
    target_content_mismatch["proof_content"]["proof_target_identity"] = ("return_coverage", "different")
    assert strategy._return_coverage_proof_id_from_evidence(target_content_mismatch) is None

    solver_unknown = deepcopy(valid)
    solver_unknown["proof_content"] = deepcopy(solver_unknown["proof_content"])
    solver_unknown["proof_content"]["coverage_solver_evidence"] = {"status": "unknown"}
    assert strategy._return_coverage_proof_id_from_evidence(solver_unknown) is None

def test_return_coverage_completed_evidence_rejects_structural_content_mismatch():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    valid = _return_coverage_completion_evidence(action)
    assert strategy._return_coverage_proof_id_from_evidence(valid) == action.proof_obligation_id

    guard_mismatch = deepcopy(valid)
    guard_mismatch["proof_content"] = deepcopy(guard_mismatch["proof_content"])
    guard_keys = list(guard_mismatch["proof_content"]["structural_guard_keys"]["keys"])
    first_guard = list(guard_keys[0])
    first_guard[2] = ("guard_structural_keys", (("return_guard", False, ("wrong",), ("wrong",)),))
    guard_keys[0] = tuple(first_guard)
    guard_mismatch["proof_content"]["structural_guard_keys"]["keys"] = tuple(guard_keys)
    assert strategy._return_coverage_proof_id_from_evidence(guard_mismatch) is None

    return_value_mismatch = deepcopy(valid)
    return_value_mismatch["proof_content"] = deepcopy(return_value_mismatch["proof_content"])
    value_keys = list(return_value_mismatch["proof_content"]["structural_guard_keys"]["keys"])
    first_value = list(value_keys[0])
    first_value[3] = ("return_value_structural_key", ("expression", "wrong_return_value"))
    value_keys[0] = tuple(first_value)
    return_value_mismatch["proof_content"]["structural_guard_keys"]["keys"] = tuple(value_keys)
    assert strategy._return_coverage_proof_id_from_evidence(return_value_mismatch) is None

    miss_mismatch = deepcopy(valid)
    miss_mismatch["proof_content"] = deepcopy(miss_mismatch["proof_content"])
    miss_keys = list(miss_mismatch["proof_content"]["structural_miss_formula_keys"]["keys"])
    miss_keys[0] = ("case_miss_formula", 0, ("expression", "wrong_miss_formula"))
    miss_mismatch["proof_content"]["structural_miss_formula_keys"]["keys"] = tuple(miss_keys)
    assert strategy._return_coverage_proof_id_from_evidence(miss_mismatch) is None

def test_return_coverage_normalization_required_uses_normalization_aware_schema():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    strict_evidence = _return_coverage_completion_evidence(action)
    strict_evidence["normalization_required"] = True
    strict_evidence["proof_content"] = deepcopy(strict_evidence["proof_content"])
    strict_evidence["proof_content"]["normalization_required"] = True
    assert strategy._return_coverage_proof_id_from_evidence(strict_evidence) is None

    normalization_aware = _normalization_aware_return_coverage_evidence(action)
    assert strategy._return_coverage_proof_id_from_evidence(normalization_aware) == action.proof_obligation_id

def test_return_coverage_normalization_required_by_target_digest_rejects_strict_schema():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    normalization_aware = _normalization_aware_return_coverage_evidence(action)
    digest = normalization_aware["proof_content"]["normalization_policy_digest"]
    target_with_digest = action.object_target_key + (("normalization_policy_digest", digest),)

    strict_evidence = _retarget_return_coverage_evidence(
        _return_coverage_completion_evidence(action),
        target_with_digest,
    )
    assert strategy._return_coverage_proof_id_from_evidence(strict_evidence) is None

    retargeted_normalized = _retarget_return_coverage_evidence(
        normalization_aware,
        target_with_digest,
    )
    assert strategy._return_coverage_proof_id_from_evidence(
        retargeted_normalized
    ) == retargeted_normalized["proof_obligation_id"]

    digest_mismatch = deepcopy(retargeted_normalized)
    digest_mismatch["proof_content"]["normalization_policy_digest"] = "0" * 64
    assert strategy._return_coverage_proof_id_from_evidence(digest_mismatch) is None

def test_return_coverage_normalization_policy_digest_is_canonical():
    policy_a = PairwiseStrategy._return_coverage_normalization_policy(
        rules=(
            {"rule_id": "z_rule", "width": 64},
            {"width": 32, "rule_id": "a_rule"},
        )
    )
    policy_b = {
        "rules": (
            {"rule_id": "a_rule", "width": 32},
            {"width": 64, "rule_id": "z_rule"},
        ),
        "canonical_encoding_version": PairwiseStrategy._RETURN_COVERAGE_NORMALIZATION_CANONICAL_ENCODING_VERSION,
        "rule_set_version": PairwiseStrategy._RETURN_COVERAGE_NORMALIZATION_RULESET_VERSION,
        "normalization_schema_version": PairwiseStrategy._RETURN_COVERAGE_NORMALIZATION_SCHEMA_VERSION,
        "normalization_policy_id": PairwiseStrategy._RETURN_COVERAGE_NORMALIZATION_POLICY_ID,
    }

    assert PairwiseStrategy._return_coverage_normalization_policy_digest(policy_a) == (
        PairwiseStrategy._return_coverage_normalization_policy_digest(policy_b)
    )

def test_return_coverage_normalization_policy_rejects_unsupported_ruleset_version():
    policy = PairwiseStrategy._return_coverage_normalization_policy(
        rules=({"rule_id": "a_rule", "width": 32},)
    )
    unsupported = dict(policy)
    unsupported["rule_set_version"] = 999

    assert PairwiseStrategy._return_coverage_normalization_policy_digest(unsupported) is None

def test_return_coverage_normalization_aware_rejects_payload_mismatch():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    valid = _normalization_aware_return_coverage_evidence(action)
    assert strategy._return_coverage_proof_id_from_evidence(valid) == action.proof_obligation_id

    digest_mismatch = deepcopy(valid)
    digest_mismatch["proof_content"]["normalization_policy_digest"] = "0" * 64
    assert strategy._return_coverage_proof_id_from_evidence(digest_mismatch) is None

    correspondence_mismatch = deepcopy(valid)
    correspondence_mismatch["proof_content"]["raw_normalized_correspondence"][
        "normalized_guard_identity"
    ] = ("normalized_guard_identity", ("guard", "different"))
    assert strategy._return_coverage_proof_id_from_evidence(correspondence_mismatch) is None

    hash_mismatch = deepcopy(valid)
    hash_mismatch["proof_content"]["normalized_guard_payload"]["final_query_sha256"] = "1" * 64
    assert strategy._return_coverage_proof_id_from_evidence(hash_mismatch) is None

    missing_hash = deepcopy(valid)
    missing_hash["proof_content"]["normalized_guard_payload"].pop("final_query_sha256")
    assert strategy._return_coverage_proof_id_from_evidence(missing_hash) is None

    broken_value_payload = deepcopy(valid)
    query = broken_value_payload["proof_content"]["normalized_guard_formula"]["query"]
    digest = broken_value_payload["proof_content"]["normalization_policy_digest"]
    broken_value_payload["proof_content"]["raw_normalized_correspondence"][
        "raw_value_identity"
    ] = ("raw_value_identity", ("value", "raw"))
    broken_value_payload["proof_content"]["raw_normalized_correspondence"][
        "normalized_value_identity"
    ] = ("normalized_value_identity", ("value", "normalized"))
    broken_value_payload["proof_content"]["normalized_value_payload"] = {
        "normalization_policy_digest": digest,
        "raw_identity": ("raw_value_identity", ("value", "raw")),
        "normalized_identity": ("normalized_value_identity", ("value", "different")),
        "final_query_sha256": hashlib.sha256(query.encode("utf-8")).hexdigest(),
    }
    assert strategy._return_coverage_proof_id_from_evidence(broken_value_payload) is None

    value_without_correspondence = deepcopy(valid)
    value_without_correspondence["proof_content"]["normalized_value_payload"] = {
        "normalization_policy_digest": value_without_correspondence["proof_content"][
            "normalization_policy_digest"
        ],
        "raw_identity": ("raw_value_identity", ("value", "raw")),
        "normalized_identity": ("normalized_value_identity", ("value", "normalized")),
        "final_query_sha256": hashlib.sha256(
            value_without_correspondence["proof_content"]["normalized_guard_formula"]["query"].encode(
                "utf-8"
            )
        ).hexdigest(),
    }
    assert strategy._return_coverage_proof_id_from_evidence(value_without_correspondence) is None

    address_without_correspondence = deepcopy(valid)
    address_without_correspondence["proof_content"]["normalized_address_payload"] = {
        "normalization_policy_digest": address_without_correspondence["proof_content"][
            "normalization_policy_digest"
        ],
        "raw_identity": ("raw_address_identity", ("address", "raw")),
        "normalized_identity": ("normalized_address_identity", ("address", "normalized")),
        "final_query_sha256": hashlib.sha256(
            address_without_correspondence["proof_content"]["normalized_guard_formula"][
                "query"
            ].encode("utf-8")
        ).hexdigest(),
    }
    assert strategy._return_coverage_proof_id_from_evidence(address_without_correspondence) is None

def test_return_coverage_common_proof_reason_scope_is_enforced():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _return_coverage_completion_evidence(action)
    evidence["proof_content"] = deepcopy(evidence["proof_content"])
    evidence["proof_content"]["applicable_reason_ids"] = (UnknownReasonId.RETURN_COVERAGE_INCONCLUSIVE.value,)

    assert strategy._return_coverage_proof_id_from_evidence(evidence) is None

def test_return_coverage_target_identity_validator_rejects_raw_object_leaf():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    target = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        _coverage_identity_analysis(binary_id="B1"),
        _coverage_identity_analysis(binary_id="B2"),
    )
    poisoned = list(target)
    function_identity = list(poisoned[3])
    function_identity.append(("raw_object", object()))
    poisoned[3] = tuple(function_identity)

    assert not strategy._return_coverage_object_target_key_is_valid(tuple(poisoned))

def test_return_coverage_target_identity_rejects_opaque_return_address():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    analysis1.returns[0].address = object()

    target = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
    )

    assert _nested_contains(target, "opaque")
    assert not strategy._return_coverage_object_target_key_is_valid(target)

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _return_coverage_completion_evidence(action)
    assert strategy._return_coverage_proof_id_from_evidence(evidence) is None

def test_return_coverage_target_identity_rejects_opaque_parameter_storage():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = _coverage_identity_analysis(binary_id="B1")
    analysis2 = _coverage_identity_analysis(binary_id="B2")
    analysis1.parameters[0]["storage"] = object()

    target = strategy._return_coverage_object_target_key(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
    )

    assert _nested_contains(target, "opaque")
    assert not strategy._return_coverage_object_target_key_is_valid(target)

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    evidence = _return_coverage_completion_evidence(action)
    assert strategy._return_coverage_proof_id_from_evidence(evidence) is None

def test_return_coverage_object_target_ignores_diagnostic_suffix():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    x = Expression.parameter("x", 0, size=4)
    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x401000",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(address="0x401020", value=_const(1), conditions=[_eq(x, _const(0))])
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x402000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x402020", value=_const(1), conditions=[])],
        return_type="int",
    )

    plain_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    suffixed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap:case=3",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )

    assert plain_reason.object_target_key == suffixed_reason.object_target_key
    assert build_unknown_recovery_actions([plain_reason])[0].proof_obligation_id == (
        build_unknown_recovery_actions([suffixed_reason])[0].proof_obligation_id
    )

def test_return_coverage_object_target_distinguishes_guard_partitions():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    x = Expression.parameter("x", 0, size=4)
    left_zero = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x401000",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(address="0x401020", value=_const(1), conditions=[_eq(x, _const(0))])
        ],
        return_type="int",
    )
    left_one = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x401000",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(address="0x401020", value=_const(1), conditions=[_eq(x, _const(1))])
        ],
        return_type="int",
    )
    right = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x402000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x402020", value=_const(1), conditions=[])],
        return_type="int",
    )

    zero_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        left_zero,
        right,
        stage="S_PAIRWISE",
    )
    one_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:return_coverage_gap",
        left_one,
        right,
        stage="S_PAIRWISE",
    )

    assert zero_reason.object_target_key != one_reason.object_target_key
    assert build_unknown_recovery_actions([zero_reason])[0].proof_obligation_id != (
        build_unknown_recovery_actions([one_reason])[0].proof_obligation_id
    )

from scripts.function_tracer_pcode.tests.unit._sat_decisiveness_fixtures import *

def test_function_return_analysis_marks_symbolic_post_state_reads_as_sat_unsafe():
    analysis = _build_symbolic_post_state_analysis("with_locread")

    assert analysis.has_symbolic_post_state_reads() is True
    assert "symbolic_post_state_reads" in analysis.get_decisive_sat_unsafety_reasons()

def test_function_return_analysis_treats_lowerable_post_state_reads_as_sat_safe():
    params = [
        _param("trace", index=0, size=8, data_type="int *"),
        _param("delta", index=1, size=4, data_type="int"),
    ]
    trace = Expression.parameter("trace", 0, size=8)
    delta = Expression.parameter("delta", 1, size=4)
    location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=0,
        size=4,
    )
    analysis = FunctionReturnAnalysis(
        function_name="lowerable",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=post_state_read_expression_for_location(
                    location,
                    params,
                    symbolic=True,
                ),
                conditions=[],
            )
        ],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["trace", "delta"],
            effects=[
                StoreEffect(
                    location=location,
                    value=Expression.binary_op("INT_ADD", Expression.memory(trace, size=4), delta),
                    conditions=[],
                    order_key=1,
                )
            ],
        ),
    )

    assert analysis.has_symbolic_post_state_reads() is False
    assert "symbolic_post_state_reads" not in analysis.get_decisive_sat_unsafety_reasons()

def test_pairwise_strategy_downgrades_sat_when_analysis_retains_symbolic_post_state_reads(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    analysis1 = _build_symbolic_post_state_analysis("f1")
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x2000",
        parameters=[_param("trace", index=0, size=8, data_type="int *")],
        returns=[ReturnInfo(address="0x2000", value=_const(0), conditions=[])],
        return_type="int",
    )

    trace = Expression.parameter("trace", 0, size=8)
    symbolic_case = ReturnCase(
        index=0,
        conditions=[],
        value_expr=post_state_read_expression_for_location(
            CanonicalLocation("trace", 0, 4),
            analysis1.parameters,
            symbolic=True,
        ),
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    const_case = ReturnCase(
        index=0,
        conditions=[],
        value_expr=_const(0),
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [symbolic_case] if analysis.function_name == "f1" else [const_case],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("ambiguous-model validation should not run for SAT-unsafe analyses")
        ),
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"trace_1": 1, "trace_2": 1},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1

def test_monolithic_strategy_downgrades_ambiguous_sat_counterexample_to_unknown():
    class _ValidationSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(
                results=[
                    SolverResult(
                        "fake",
                        SolverStatus.SAT,
                        elapsed_time=0.01,
                        model={"x_1": 5, "x_2": 5},
                    )
                ]
            )

        def run_sequential(self, query: str):
            if "(assert (= (_ bv7 32) (_ bv7 32)))" in query:
                return ParallelResult(
                    results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 5, "x_2": 5})]
                )
            if "(assert (= x_1 (bvadd x_2 (_ bv1 32))))" in query:
                return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])
            return ParallelResult(
                results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 5, "x_2": 5})]
            )

    x1 = Expression.parameter("x", 0, size=4)
    x2 = Expression.parameter("x", 0, size=4)
    cond1 = _eq(x1, _const(5))
    cond2 = _eq(x2, _const(5))

    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(address="0x1", value=x1, conditions=[]),
            ReturnInfo(address="0x2", value=_const(7), conditions=[cond1]),
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[
            ReturnInfo(
                address="0x3",
                value=Expression.binary_op("INT_ADD", x2, _const(1)),
                conditions=[],
            ),
            ReturnInfo(address="0x4", value=_const(7), conditions=[cond2]),
        ],
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

    strategy = MonolithicStrategy(formula_builder, _ValidationSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None

def test_monolithic_same_function_sat_requires_counterexample_replay(monkeypatch):
    class _SatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(
                results=[
                    SolverResult(
                        "fake",
                        SolverStatus.SAT,
                        elapsed_time=0.01,
                        model={"x_1": 0, "x_2": 0},
                    )
                ]
            )

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
    analysis1 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    strategy = MonolithicStrategy(formula_builder, _SatSolverRunner(), debug=False)
    monkeypatch.setattr(strategy, "_collect_monolithic_return_coverage_unsafety_reasons", lambda *_args: [])

    def _validated_counterexample(*_args):
        strategy._last_counterexample_replay_fixed_model_assertion_count = 2
        return True

    monkeypatch.setattr(strategy, "_counterexample_is_decisive_across_case_split", _validated_counterexample)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.SAT_UNSAFETY.value
    assert reason.evidence_refs == ("counterexample_replay_missing",)
    assert not any(
        evidence.get("proof_source") == "monolithic_global_counterexample_validation"
        for evidence in analysis1.completed_recovery_proof_evidence
    )

def test_monolithic_same_function_sat_accepts_prior_completed_counterexample_replay(monkeypatch):
    class _SatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(
                results=[
                    SolverResult(
                        "fake",
                        SolverStatus.SAT,
                        elapsed_time=0.01,
                        model={"x_1": 0, "x_2": 0},
                    )
                ]
            )

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
    analysis1 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    strategy = MonolithicStrategy(formula_builder, _SatSolverRunner(), debug=False)
    monkeypatch.setattr(strategy, "_collect_monolithic_return_coverage_unsafety_reasons", lambda *_args: [])
    monkeypatch.setattr(strategy, "_counterexample_is_decisive_across_case_split", lambda *_args: True)
    pending_reason = strategy._make_sat_unsafety_unknown_reason(
        ("counterexample_replay_missing",),
        analysis1,
        analysis2,
        case1=None,
        case2=None,
        pair_id="monolithic",
        stage="S_MONOLITHIC_FALLBACK",
    )
    action = build_unknown_recovery_actions([pending_reason])[0]
    analysis1.completed_recovery_proof_evidence = (
        _sat_unsafety_resolution_evidence(action),
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is False
    assert result.counterexample_raw == {"x_1": 0, "x_2": 0}
    assert result.unknown_reasons == []

def test_monolithic_same_function_sat_with_unfixed_model_is_unknown():
    class _ReturnOnlySatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(
                results=[
                    SolverResult(
                        "fake",
                        SolverStatus.SAT,
                        elapsed_time=0.01,
                        model={"return_1": 1, "return_2": 2},
                    )
                ]
            )

        def run_sequential(self, _query: str, timeout=None):
            raise AssertionError("unfixed model should be rejected before replay queries")

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
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    analysis1 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    strategy = MonolithicStrategy(formula_builder, _ReturnOnlySatSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value
    assert reason.recovery_proof_kind == UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value
    assert reason.proof_stage == "sat_counterexample_safety"
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.evidence_kind == "case_partition_replay"
    action = build_unknown_recovery_actions([reason])[0]
    assert action.reason_id == UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value
    assert action.proof_kind == UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value
    assert action.proof_stage == "sat_counterexample_safety"
    assert action.status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert analysis1.completed_recovery_proof_evidence == ()

def test_sat_counterexample_ambiguous_reason_has_object_proof_action():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type="int",
        parameters=analysis2.parameters,
    )

    reason = strategy._make_sat_counterexample_ambiguous_unknown_reason(
        ("with-ineq",),
        analysis1,
        analysis2,
        case1=case1,
        case2=case2,
        pair_id="(0,0)",
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]

    assert reason.reason_id == UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value
    assert reason.decision_effect == "blocks_disequivalence"
    assert reason.reason_scope == "pair"
    assert reason.recovery_proof_kind == UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value
    assert reason.proof_stage == "sat_counterexample_safety"
    assert reason.evidence_kind == "case_partition_replay"
    assert reason.object_target_key[0] == "sat_counterexample_ambiguous"
    assert reason.object_evidence["object_derived"] is True
    assert reason.object_evidence["ambiguity_evidence_refs"] == ("with-ineq",)
    assert action.count_kind == "proof_action"
    assert action.reason_id == UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value
    assert action.proof_kind == UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value
    assert action.proof_stage == "sat_counterexample_safety"
    assert action.evidence_kind == "case_partition_replay"
    assert action.status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert action.proof_obligation_id == build_proof_obligation_id(
        UnknownReasonId.SAT_COUNTEREXAMPLE_AMBIGUOUS.value,
        "sat_counterexample_safety",
        UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value,
        "case_partition_replay",
        reason.object_target_key,
    )

def test_pairwise_sat_unsafety_emits_object_derived_pending_proof_backlog(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 0, "x_2": 0},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.SAT_UNSAFETY.value
    assert reason.decision_effect == "blocks_disequivalence"
    assert reason.recovery_proof_kind == UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION.value
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.recovery_action == "sat_unsafety_resolution_required"
    assert reason.object_target_key[0] == "sat_unsafety"
    assert reason.object_evidence is not None
    assert reason.object_evidence["object_derived"] is True
    assert reason.object_evidence["evidence_kind"] == "active_unsafety_summary"
    assert reason.object_evidence["object_target_key"] == reason.object_target_key
    active_unsafety = reason.object_evidence["active_unsafety"]
    assert len(active_unsafety) == 1
    assert active_unsafety[0]["reason_kind"] == "unsupported_call_effect_summary"
    assert active_unsafety[0]["call_effect"]["object_derived"] is True
    assert active_unsafety[0]["call_effect"]["object_target_kind"] == "unsupported_call_effect"
    assert reason.proof_obligation_id == build_proof_obligation_id(
        UnknownReasonId.SAT_UNSAFETY,
        "sat_counterexample_safety",
        UnknownRecoveryProofKind.SAT_UNSAFETY_RESOLUTION,
        "active_unsafety_summary",
        reason.object_target_key,
    )
    actions = build_unknown_recovery_actions([reason])
    assert len(actions) == 1
    assert actions[0].required_evidence == (
        "counterexample_replay",
        "active_unsafety_discharge",
        "coverage_effect_safety",
    )
    assert actions[0].proof_obligation_id == reason.proof_obligation_id

def test_pairwise_sat_unsafety_completed_proof_allows_decisive_sat(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
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
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == analysis1.function_name else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: True,
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 0, "x_2": 0},
        )
    )
    reason = strategy._make_sat_unsafety_unknown_reason(
        ("function1:unsupported_call_effect_summary",),
        analysis1,
        analysis2,
        case1=case1,
        case2=case2,
        pair_id="(0,0)",
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([reason])[0]
    analysis1.completed_recovery_proof_evidence = (
        _sat_unsafety_resolution_evidence(action),
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is False
    assert result.sat_pairs == 1
    assert result.unknown_reasons == []

def test_pairwise_same_function_sat_accepts_completed_counterexample_replay(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
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
        "_extract_return_cases",
        lambda analysis: [case1] if analysis is analysis1 else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: True,
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 0, "x_2": 0},
        )
    )
    pending_reason = strategy._make_sat_unsafety_unknown_reason(
        ("counterexample_replay_missing",),
        analysis1,
        analysis2,
        case1=case1,
        case2=case2,
        pair_id="(0,0)",
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([pending_reason])[0]
    analysis1.completed_recovery_proof_evidence = (
        _sat_unsafety_resolution_evidence(action),
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is False
    assert result.sat_pairs == 1
    assert result.unknown_pairs == 0
    assert result.unknown_reasons == []

def test_pairwise_same_function_sat_with_model_still_requires_prior_counterexample_replay(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
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
        "_extract_return_cases",
        lambda analysis: [case1] if analysis is analysis1 else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: True,
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 0, "x_2": 0},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.SAT_UNSAFETY.value
    assert reason.evidence_refs == ("counterexample_replay_missing",)
    assert not any(
        evidence.get("proof_source") == "pairwise_case_split_counterexample_validation"
        for evidence in analysis1.completed_recovery_proof_evidence
    )

def test_pairwise_same_function_sat_without_model_still_requires_counterexample_replay(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
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
        "_extract_return_cases",
        lambda analysis: [case1] if analysis is analysis1 else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: True,
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw=None,
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.SAT_UNSAFETY.value
    assert reason.evidence_refs == ("counterexample_replay_missing",)
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.proof_obligation_id is not None

def test_pairwise_same_function_sat_with_unfixed_model_still_requires_counterexample_replay(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="same_func",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
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
        "_extract_return_cases",
        lambda analysis: [case1] if analysis is analysis1 else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.equivalence.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_args, **_kwargs: True,
    )
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"return_1": 1, "return_2": 2},
        )
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    assert result.unknown_pairs == 1
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.SAT_UNSAFETY.value
    assert reason.evidence_refs == ("counterexample_replay_missing",)
    assert not any(
        evidence.get("proof_source") == "pairwise_case_split_counterexample_validation"
        for evidence in analysis1.completed_recovery_proof_evidence
    )

def test_sat_unsafety_completed_proof_rejects_active_blocker_fields_on_evidence():
    action = _sat_unsafety_resolution_action()
    blocker_fields = (
        "active_coverage_gap_reasons",
        "unsupported_call_effect_reasons",
        "unsupported_memory_effect_reasons",
    )

    for field_name in blocker_fields:
        evidence = _sat_unsafety_resolution_evidence(action, **{field_name: ("still-active",)})

        assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(evidence) is None

def test_sat_unsafety_completed_proof_rejects_active_blocker_fields_inside_proof_content():
    action = _sat_unsafety_resolution_action()
    blocker_fields = (
        "active_coverage_gap_reasons",
        "unsupported_call_effect_reasons",
        "unsupported_memory_effect_reasons",
    )

    for field_name in blocker_fields:
        evidence = deepcopy(_sat_unsafety_resolution_evidence(action))
        evidence["proof_content"]["coverage_effect_safety"][field_name] = ("still-active",)

        assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(evidence) is None

def test_sat_unsafety_completed_proof_requires_object_derived_proof_content():
    action = _sat_unsafety_resolution_action()
    evidence = deepcopy(_sat_unsafety_resolution_evidence(action))
    evidence["proof_content"].pop("object_derived", None)

    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(evidence) is None

def test_sat_unsafety_completed_proof_requires_fixed_counterexample_replay_model():
    action = _sat_unsafety_resolution_action()

    missing_hash = deepcopy(_sat_unsafety_resolution_evidence(action))
    missing_hash["proof_content"]["counterexample_replay"].pop(
        "counterexample_model_sha256",
        None,
    )
    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(missing_hash) is None

    malformed_hash = deepcopy(_sat_unsafety_resolution_evidence(action))
    malformed_hash["proof_content"]["counterexample_replay"]["counterexample_model_sha256"] = "a" * 63
    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(malformed_hash) is None

    missing_count = deepcopy(_sat_unsafety_resolution_evidence(action))
    missing_count["proof_content"]["counterexample_replay"].pop(
        "fixed_model_assertion_count",
        None,
    )
    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(missing_count) is None

    zero_count = deepcopy(_sat_unsafety_resolution_evidence(action))
    zero_count["proof_content"]["counterexample_replay"]["fixed_model_assertion_count"] = 0
    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(zero_count) is None

    missing_keys = deepcopy(_sat_unsafety_resolution_evidence(action))
    missing_keys["proof_content"]["counterexample_replay"].pop(
        "counterexample_symbol_keys",
        None,
    )
    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(missing_keys) is None

    empty_keys = deepcopy(_sat_unsafety_resolution_evidence(action))
    empty_keys["proof_content"]["counterexample_replay"]["counterexample_symbol_keys"] = ()
    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(empty_keys) is None

def test_sat_unsafety_completed_proof_requires_current_counterexample_model_match():
    action = _sat_unsafety_resolution_action()
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    reason = make_unknown_reason(
        UnknownReasonId.SAT_UNSAFETY,
        stage=action.stage,
        pair_or_case=action.pair_or_case,
        evidence_refs=action.evidence_refs,
        recovery_proof_kind=action.proof_kind,
        recovery_proof_obligations=(
            UnknownRecoveryProofObligation.create(
                action.proof_kind,
                action.proof_stage,
                required_evidence=action.required_evidence,
            ),
        ),
        proof_stage=action.proof_stage,
        evidence_kind=action.evidence_kind,
        object_target_key=action.object_target_key,
        proof_obligation_id=action.proof_obligation_id,
        action_status=UnknownRecoveryActionStatus.PENDING_PROOF.value,
    )
    analysis1.completed_recovery_proof_evidence = (
        _sat_unsafety_resolution_evidence(
            action,
            counterexample_raw={"x_1": 0, "x_2": 0},
        ),
    )

    assert strategy._sat_unsafety_resolution_proof_is_complete(
        reason,
        analysis1,
        analysis2,
        current_counterexample_raw={"x_1": 0, "x_2": 0},
    )
    assert not strategy._sat_unsafety_resolution_proof_is_complete(
        reason,
        analysis1,
        analysis2,
        current_counterexample_raw=None,
    )
    assert not strategy._sat_unsafety_resolution_proof_is_complete(
        reason,
        analysis1,
        analysis2,
        current_counterexample_raw={},
    )
    assert not strategy._sat_unsafety_resolution_proof_is_complete(
        reason,
        analysis1,
        analysis2,
        current_counterexample_raw={"x_1": 1, "x_2": 0},
    )

def test_sat_unsafety_completed_proof_rejects_nested_blocker_fields_inside_proof_content():
    action = _sat_unsafety_resolution_action()
    evidence = deepcopy(_sat_unsafety_resolution_evidence(action))
    evidence["proof_content"]["coverage_effect_safety"]["details"] = {
        "unsupported_call_effect_reasons": ("still-active",),
    }

    assert PairwiseStrategy._sat_unsafety_resolution_proof_id_from_evidence(evidence) is None

def test_pairwise_sat_unsafety_metadata_only_completed_proof_does_not_recover(monkeypatch):
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(2), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_twostage = Mock(
        return_value=QueryResult(
            is_equivalent=False,
            counterexample_raw={"x_1": 0, "x_2": 0},
        )
    )
    pending_reason = strategy._make_sat_unsafety_unknown_reason(
        ("function1:unsupported_call_effect_summary",),
        analysis1,
        analysis2,
        case1=ReturnCase(
            index=0,
            conditions=[],
            value_expr=analysis1.returns[0].value,
            return_info=analysis1.returns[0],
            return_type=analysis1.return_type or "int",
            parameters=analysis1.parameters,
        ),
        case2=ReturnCase(
            index=0,
            conditions=[],
            value_expr=analysis2.returns[0].value,
            return_info=analysis2.returns[0],
            return_type=analysis2.return_type or "int",
            parameters=analysis2.parameters,
        ),
        pair_id="(0,0)",
        stage="S_PAIRWISE",
    )
    action = build_unknown_recovery_actions([pending_reason])[0]
    evidence = _sat_unsafety_resolution_evidence(action)
    evidence.pop("proof_content", None)
    analysis1.completed_recovery_proof_evidence = (evidence,)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == UnknownReasonId.SAT_UNSAFETY.value

def test_pairwise_phi_circular_guard_solver_replay_sat_stays_unknown(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = Mock()
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_phi_circular_guard(
        function_name="func1",
        binary_id="B11",
        entry=0x1000,
    )
    analysis2 = _analysis_with_phi_circular_guard(
        function_name="func2",
        binary_id="B12",
        entry=0x1000,
    )
    _patch_pairwise_return_cases_from_returns(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_internal = Mock(
        side_effect=[
            QueryResult(is_equivalent=True),
            QueryResult(is_equivalent=False),
        ]
    )
    strategy._solve_query_twostage = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.UNRESOLVED_EXPRESSION.value
    ]
    assert "pairwise_extra_assertions_by_pair" not in base_ctx
    assert analysis1.completed_recovery_proof_evidence == ()
    strategy._solve_query_twostage.assert_not_called()
    strategy._solve_query_internal.assert_not_called()

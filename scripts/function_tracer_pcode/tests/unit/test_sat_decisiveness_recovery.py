from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import echo_input_correspondence
from scripts.function_tracer_pcode.tests.unit._sat_decisiveness_fixtures import *

def test_function_return_analysis_scans_raw_sibling_after_lowerable_post_state_read():
    params = [
        _param("trace", index=0, size=8, data_type="int *"),
        _param("flag", index=1, size=4, data_type="int"),
    ]
    trace = Expression.parameter("trace", 0, size=8)
    flag = Expression.parameter("flag", 1, size=4)
    total_location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=0,
        size=4,
    )
    count_location = CanonicalLocation(
        base_ref=LocationBaseRef.parameter("trace", index=0),
        offset=4,
        size=4,
    )
    count_addr = Expression.binary_op("INT_ADD", trace, Expression.constant(4, 8))
    analysis = FunctionReturnAnalysis(
        function_name="mixed_post_state_and_raw_read",
        entry_point="0x1000",
        parameters=params,
        returns=[
            ReturnInfo(
                address="0x1000",
                value=Expression.binary_op(
                    "INT_ADD",
                    post_state_read_expression_for_location(
                        total_location,
                        params,
                        symbolic=True,
                    ),
                    Expression.memory(count_addr, size=4),
                ),
                conditions=[],
            )
        ],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
        effect_summary=EffectSummary(
            parameter_names=["trace"],
            effects=[
                StoreEffect(
                    location=total_location,
                    value=Expression.constant(7, 4),
                    conditions=[],
                    order_key=1,
                ),
                StoreEffect(
                    location=count_location,
                    value=Expression.constant(9, 4),
                    conditions=[_ne(flag, _const(0))],
                    order_key=2,
                ),
            ],
        ),
    )

    assert analysis.has_symbolic_post_state_reads() is False
    assert analysis.has_effect_sensitive_raw_memory_reads() is True
    assert "effect_sensitive_raw_memory_reads" in analysis.get_decisive_sat_unsafety_reasons()

def test_pairwise_unknown_result_preserves_recovery_action_status(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 64,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)

    analysis1 = FunctionReturnAnalysis(
        function_name="f1",
        entry_point="0x1000",
        parameters=[],
        returns=[ReturnInfo(address="0x1000", value=_const(1, size=4), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="f2",
        entry_point="0x2000",
        parameters=[],
        returns=[ReturnInfo(address="0x2000", value=_const(1, size=8), conditions=[])],
        return_type="long",
        return_abi_facts=_present_return_abi_facts("long"),
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis1.returns[0].value,
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=[],
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=analysis2.returns[0].value,
        return_info=analysis2.returns[0],
        return_type="long",
        parameters=[],
    )
    target = ("return_width_bridge", ("pair", "(0,0)"), ("return_widths", 32, 64))
    query_result = QueryResult(is_equivalent=None)
    query_result.pair_stage = "return-width-mismatch"
    query_result.blocking_reason = UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value
    query_result.blocking_detail = "pairwise value inequality: return width mismatch (32 vs 64)"
    query_result.evidence_kind = "return_width_bridge_status"
    query_result.object_target_key = target
    query_result.object_evidence = ("return_width_bridge_status", ("status", "planned"))
    query_result.action_status = UnknownRecoveryActionStatus.PLANNED

    monkeypatch.setattr(
        strategy,
        "_extract_return_cases",
        lambda analysis: [case1] if analysis.function_name == "f1" else [case2],
    )
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_args, **_kwargs: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_args, **_kwargs: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_after_guard = Mock(return_value=query_result)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_pairs == 1
    assert len(result.unknown_reasons) == 1
    reason = result.unknown_reasons[0]
    assert reason.reason_id == UnknownReasonId.RETURN_WIDTH_BRIDGE_MISSING.value
    assert reason.action_status == UnknownRecoveryActionStatus.PLANNED.value
    assert reason.object_target_key == target
    assert reason.object_evidence == query_result.object_evidence

def test_monolithic_unsupported_intrinsic_is_unresolved_expression_not_strategy_exception():
    from scripts.function_tracer_pcode.core.render_smt import UnsupportedSmtIntrinsicError

    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_equivalence_formula_extended.side_effect = (
        UnsupportedSmtIntrinsicError(mnemonic="CALLOTHER", opcode="CALLOTHER")
    )
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = MonolithicStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons[0].reason_id == "expression_semantics_unsupported"
    assert result.unknown_reasons[0].evidence_refs == ("unsupported_intrinsic_smt_lowering",)
    solver_runner.run_parallel.assert_not_called()


def test_monolithic_does_not_classify_arbitrary_value_error_from_message_text():
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_equivalence_formula_extended.side_effect = ValueError(
        "Unsupported intrinsic for SMT lowering: forged diagnostic text"
    )
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = MonolithicStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="left", entry_point="0x1000", parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right", entry_point="0x2000", parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.error_pairs == 1
    assert result.pairwise_debug_stats == {"strategy_exception_error": 1}
    assert result.unknown_reasons == []
    assert result.error_kind == "strategy_exception"
    assert "Unsupported intrinsic" in result.error_message

def test_pairwise_global_blocker_dominates_pair_local_unresolved_expression(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _return_coverage_gap_analyses()
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: True)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_pairs == 1
    assert {reason.reason_id for reason in result.unknown_reasons} == {
        UnknownReasonId.RETURN_COVERAGE_GAP.value,
    }
    assert all(
        reason.reason_id != UnknownReasonId.UNRESOLVED_EXPRESSION.value
        for reason in result.unknown_reasons
    )
    assert "return_case_coverage_gap" in analysis1.analysis_notes

def test_pairwise_equivalence_blocker_dominates_pair_local_unresolved_expression(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 0, "x_2": 0})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
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
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: True)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_pairs == 1
    assert {reason.reason_id for reason in result.unknown_reasons} == {
        "unsupported_call_effect_semantics",
    }
    assert all(
        reason.reason_id != UnknownReasonId.UNRESOLVED_EXPRESSION.value
        for reason in result.unknown_reasons
    )

def test_pairwise_completed_recovery_proofs_can_be_disabled(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 7, "x_2": 7})]
    )
    strategy = PairwiseStrategy(
        formula_builder,
        solver_runner,
        debug=False,
        enable_completed_recovery_proofs=False,
    )
    analysis1, analysis2 = _return_coverage_gap_analyses()
    _patch_pairwise_return_coverage_gap_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        UnknownReasonId.RETURN_COVERAGE_GAP.value,
    ]
    assert {reason.action_status for reason in result.unknown_reasons} == {
        UnknownRecoveryActionStatus.PENDING_PROOF.value
    }
    assert analysis1.completed_recovery_proof_evidence == ()
    assert analysis2.completed_recovery_proof_evidence == ()

def test_pairwise_disabled_completed_proofs_do_not_create_new_return_gap_without_active_blocker(monkeypatch):
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
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.analysis_notes = []
    analysis2.analysis_notes = []
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
    assert analysis1.completed_recovery_proof_evidence == ()
    assert analysis2.completed_recovery_proof_evidence == ()

def test_pairwise_disabled_completed_proofs_ignore_stale_summary_dependency_note(monkeypatch):
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
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.analysis_notes = []
    analysis2.analysis_notes = ["state_transition_loop_summary"]
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
    assert analysis1.completed_recovery_proof_evidence == ()
    assert analysis2.completed_recovery_proof_evidence == ()

def test_pairwise_disabled_completed_proofs_do_not_block_switch_or_control_region_recovery(monkeypatch):
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
    analysis1, analysis2 = _return_coverage_gap_analyses()
    analysis1.analysis_notes = []
    analysis2.analysis_notes = [
        "switch_return_recovery",
        "control_region_return_recovery",
    ]
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
    assert analysis1.completed_recovery_proof_evidence == ()
    assert analysis2.completed_recovery_proof_evidence == ()

def test_pairwise_unknown_indirect_legacy_return_guard_mismatch_is_not_path_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        path_conditions=(_eq(Expression.parameter("a", 1, size=4), _const(0)),),
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        path_conditions=(_ne(Expression.parameter("a", 1, size=4), _const(0)),),
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

def test_pairwise_unknown_indirect_output_surface_use_keeps_unknown(monkeypatch):
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
    site = analysis1.effect_summary.unsupported_call_sites[0]
    analysis1.returns = [
        ReturnInfo(
            address="0x1000",
            value=Expression.unknown("callind_result", runtime_ref=site.pcode_op_ref),
            conditions=[],
        )
    ]
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

def test_pairwise_unknown_indirect_observed_store_keeps_unknown(monkeypatch):
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
    analysis1.effect_summary.effects = [
        StoreEffect(
            location=CanonicalLocation("global", 0, 4),
            value=_const(1),
            conditions=[],
            order_key=11,
        )
    ]
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

def test_pairwise_unknown_indirect_missing_target_expr_does_not_auto_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        target_expr_missing=True,
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        target_expr_missing=True,
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert {
        reason.detail for reason in result.unknown_reasons
    } == {
        "function1:unsupported_call_effect_summary",
        "function2:unsupported_call_effect_summary",
    }
    assert not [
        item
        for analysis in (analysis1, analysis2)
        for item in analysis.completed_recovery_proof_evidence
        if item.get("proof_source") == "matched_unknown_indirect_no_store_call_effect"
    ]

def test_pairwise_unknown_indirect_target_mismatch_does_not_auto_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        target_param_index=0,
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        target_param_index=1,
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert {
        reason.detail for reason in result.unknown_reasons
    } == {
        "function1:unsupported_call_effect_summary",
        "function2:unsupported_call_effect_summary",
    }

def test_pairwise_unknown_indirect_argument_mismatch_does_not_auto_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unknown_indirect_call_effect(
        function_name="func1",
        binary_id="B10",
        entry=0x1000,
        argument_indices=(1, 2),
    )
    analysis2 = _analysis_with_unknown_indirect_call_effect(
        function_name="func2",
        binary_id="B11",
        entry=0x2000,
        argument_indices=(2, 1),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert len(result.unknown_reasons) == 2

def test_pairwise_opaque_unresolved_return_stays_unknown(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.unknown("opaque").clone_with(size=4), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
        binary_id="B1",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.unknown("opaque").clone_with(size=4), conditions=[])],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
        binary_id="B14",
    )
    _patch_pairwise_single_case(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_after_guard = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        "expression_translation_incomplete"
    ]
    strategy._solve_query_after_guard.assert_not_called()

def test_unresolved_expression_action_status_marks_planned_without_stage_evidence():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    target = (
        "unresolved_expression",
        ("pair", "(0,1)"),
        (
            "unresolved_expression_side",
            "left",
            ("opaque_unknown", "phi_circular", "expr", "runtime", "multiequal_pcode_op", ("pcode_op", "B1")),
        ),
        (
            "unresolved_expression_side",
            "right",
            ("opaque_unknown", "phi_circular", "expr", "runtime", "multiequal_pcode_op", ("pcode_op", "B2")),
        ),
    )

    assert strategy._unresolved_expression_recovery_proof_obligations(target)
    assert (
        strategy._unresolved_expression_action_status(target, object_evidence=None)
        == UnknownRecoveryActionStatus.PLANNED
    )
    assert (
        strategy._unresolved_expression_action_status(
            target,
            object_evidence=("unresolved_expression_diagnostic_evidence",),
        )
        == UnknownRecoveryActionStatus.PENDING_PROOF
    )
    assert strategy._unresolved_expression_action_status(None, object_evidence=None) is None

def test_pairwise_phi_circular_guard_same_origin_stays_unknown_with_diagnostic_proof(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = echo_input_correspondence(Mock())
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
    strategy._solve_query_after_guard = Mock(return_value=QueryResult(is_equivalent=True))
    strategy._solve_query_internal = Mock(return_value=QueryResult(is_equivalent=None))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        "expression_translation_incomplete"
    ]
    assert "pairwise_extra_assertions_by_pair" not in base_ctx
    assert "pairwise_unresolved_lowered_unknown_keys_by_pair" not in base_ctx
    reason = result.unknown_reasons[0]
    assert reason.object_evidence is not None
    assert reason.object_evidence[0] == "unresolved_expression_diagnostic_evidence"
    assert _nested_contains(reason.object_target_key, ("unresolved_location", "return_guard_unresolved"))
    assert _nested_contains(reason.object_target_key, ("unresolved_cause", "phi_circular_integer"))
    assert _nested_contains(reason.object_target_key, ("unresolved_substage", "integer_phi_circular_guard_pending"))
    assert any(
        isinstance(item, tuple) and item and item[0] == "stage_evidence"
        for item in reason.object_evidence
    )
    assert _nested_contains(reason.object_evidence, "semantic_recurrence_query")
    assert _nested_contains(reason.object_evidence, "object_derived_query_plan")
    actions = build_unknown_recovery_actions(result.unknown_reasons)
    assert {
        action.proof_stage
        for action in actions
        if action.reason_id == "expression_translation_incomplete"
    } == {
        "phi_circular_guard_condition_lowering",
        "recursive_summary_guard_equivalence",
    }
    assert {
        action.status
        for action in actions
        if action.reason_id == "expression_translation_incomplete"
    } == {UnknownRecoveryActionStatus.PENDING_PROOF.value}
    strategy._solve_query_after_guard.assert_not_called()
    strategy._solve_query_internal.assert_not_called()

def test_pairwise_mixed_float_phi_unresolved_uses_generic_pending_lane():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    target = (
        "unresolved_expression",
        ("pair", "case0"),
        (
            "unresolved_expression_side",
            "left",
            ("function", "left"),
            ("return_storage", "reg", "v0"),
            ("return_case", 0),
            (
                "unresolved_locations",
                (
                    (
                        "unresolved_location",
                        "return_value",
                        (
                            "unresolved_classification",
                            ("location_scope", "return_value"),
                            ("unresolved_location", "return_value_unresolved"),
                            ("unresolved_cause", "mixed_float_call_read_recurrence"),
                            ("unresolved_substage", "mixed_float_call_read_recurrence_deferred"),
                            (
                                "unknown_refs",
                                (
                                    (
                                        "opaque_unknown",
                                        "phi_circular",
                                        "expr",
                                        "runtime",
                                        "multiequal_pcode_op",
                                        ("pcode_op", "B1"),
                                    ),
                                    (
                                        "unknown_runtime_ref",
                                        (
                                            "deferred_call",
                                            "call_out_of_scope",
                                            ("callee", "unknown"),
                                            ("callsite", "left"),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
        (
            "unresolved_expression_side",
            "right",
            ("function", "right"),
            ("return_storage", "reg", "v0"),
            ("return_case", 0),
            (
                "unresolved_locations",
                (
                    (
                        "unresolved_location",
                        "return_value",
                        (
                            "unresolved_classification",
                            ("location_scope", "return_value"),
                            ("unresolved_location", "return_value_unresolved"),
                            ("unresolved_cause", "mixed_float_call_read_recurrence"),
                            ("unresolved_substage", "mixed_float_call_read_recurrence_deferred"),
                            (
                                "unknown_refs",
                                (
                                    (
                                        "opaque_unknown",
                                        "phi_circular",
                                        "expr",
                                        "runtime",
                                        "multiequal_pcode_op",
                                        ("pcode_op", "B2"),
                                    ),
                                    (
                                        "unknown_runtime_ref",
                                        (
                                            "deferred_call",
                                            "call_out_of_scope",
                                            ("callee", "unknown"),
                                            ("callsite", "right"),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )

    obligations = strategy._unresolved_expression_recovery_proof_obligations(target)

    assert strategy._unresolved_expression_target_uses_generic_pending_census(target)
    assert obligations is not None
    assert {obligation.proof_stage for obligation in obligations} == {
        "typed_expression_lowering",
        "type_normalization",
    }
    evidence = strategy._unresolved_expression_generic_diagnostic_evidence(target)
    assert evidence is not None
    assert _nested_contains(evidence, ("diagnostic_rule", "mixed_float_call_read_recurrence_pending_census"))
    assert _nested_contains(evidence, ("completed_proof_allowed", False))

def test_pairwise_phi_circular_guard_solver_replay_does_not_recover_from_assumed_unknown_equality(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = echo_input_correspondence(Mock())
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
            QueryResult(is_equivalent=True),
        ]
    )
    strategy._solve_query_after_guard = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        "expression_translation_incomplete"
    ]
    assert "pairwise_extra_assertions_by_pair" not in base_ctx
    assert "pairwise_unresolved_phi_circular_lowering_evidence_by_pair" not in base_ctx
    assert not _nested_contains(result.unknown_reasons[0].object_evidence, "completed_unresolved_expression_proof")
    assert _nested_contains(result.unknown_reasons[0].object_evidence, "object_derived_query_plan")
    assert analysis1.completed_recovery_proof_evidence == ()
    strategy._solve_query_internal.assert_not_called()
    strategy._solve_query_after_guard.assert_not_called()

def test_pairwise_phi_circular_guard_polarity_mismatch_stays_unknown(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_phi_circular_guard(
        function_name="func1",
        binary_id="B11",
        entry=0x1000,
        guard_negated=False,
    )
    analysis2 = _analysis_with_phi_circular_guard(
        function_name="func2",
        binary_id="B12",
        entry=0x1000,
        guard_negated=True,
    )
    _patch_pairwise_return_cases_from_returns(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_after_guard = Mock(return_value=QueryResult(is_equivalent=True))
    strategy._solve_query_internal = Mock(return_value=QueryResult(is_equivalent=None))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        "expression_translation_incomplete"
    ]
    assert "pairwise_extra_assertions_by_pair" not in base_ctx
    strategy._solve_query_after_guard.assert_not_called()

def test_pairwise_phi_circular_guard_overlap_does_not_prune_without_semantic_proof(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_phi_circular_guard(
        function_name="func1",
        binary_id="B11",
        entry=0x1000,
        guard_negated=False,
    )
    analysis2 = _analysis_with_phi_circular_guard(
        function_name="func2",
        binary_id="B12",
        entry=0x1000,
        guard_negated=True,
    )
    _patch_pairwise_return_cases_from_returns(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_internal = Mock(return_value=QueryResult(is_equivalent=True))
    strategy._solve_query_after_guard = Mock(return_value=QueryResult(is_equivalent=False))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        "expression_translation_incomplete"
    ]
    assert strategy._solve_query_internal.call_count == 0
    assert analysis1.completed_recovery_proof_evidence == ()
    strategy._solve_query_after_guard.assert_not_called()

def test_pairwise_phi_circular_guard_origin_mismatch_stays_unknown(monkeypatch):
    base_ctx = _base_context_for_single_int_param()
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = base_ctx
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_phi_circular_guard(
        function_name="func1",
        binary_id="B11",
        entry=0x1000,
        seq_time=98,
    )
    analysis2 = _analysis_with_phi_circular_guard(
        function_name="func2",
        binary_id="B12",
        entry=0x1000,
        seq_time=99,
    )
    _patch_pairwise_return_cases_from_returns(monkeypatch, strategy, analysis1, analysis2)
    strategy._solve_query_after_guard = Mock(return_value=QueryResult(is_equivalent=True))

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert [reason.reason_id for reason in result.unknown_reasons] == [
        "expression_translation_incomplete"
    ]
    assert "pairwise_extra_assertions_by_pair" not in base_ctx
    strategy._solve_query_after_guard.assert_not_called()

def test_expression_provenance_key_handles_very_deep_target_expression_without_recursion_error():
    left_key = expression_provenance_key(_deep_zext_target("fp", 0, depth=900))
    right_key = expression_provenance_key(_deep_zext_target("gp", 1, depth=900))

    assert left_key != right_key

def test_expression_provenance_key_distinguishes_sources_beyond_digest_node_limit():
    left_key = expression_provenance_key(_deep_zext_target("fp", 0, depth=8200))
    right_key = expression_provenance_key(_deep_zext_target("gp", 1, depth=8200))

    assert left_key != right_key

def test_expression_provenance_key_distinguishes_deep_tail_structure_beyond_digest_node_limit():
    zext_key = expression_provenance_key(
        _deep_target_with_tail_op("fp", 0, "INT_ZEXT", depth=8200)
    )
    sext_key = expression_provenance_key(
        _deep_target_with_tail_op("fp", 0, "INT_SEXT", depth=8200)
    )

    assert zext_key != sext_key

def test_expression_provenance_key_prefers_parameter_runtime_ref_over_storage():
    storage = StorageInfo(
        is_register=True,
        space_name="register",
        offset=32,
        size=8,
        register_name="a0",
        base_register_name="a0",
        base_register_size_bits=64,
    )
    parameter_ref = LocationBaseRef.parameter(
        "op",
        index=0,
        owner_program_id=1234,
        owner_entry_offset=0x401000,
    )
    expr = Expression.parameter(
        "op",
        0,
        "int (*)(int, int)",
        size=8,
        storage_info=storage,
        runtime_ref=parameter_ref,
    )

    key = expression_provenance_key(expr)

    assert key == ("runtime_ref", ("parameter", 1234, 0x401000, 0))
    assert key[0] != "storage"

def test_artifact_stable_key_rewrites_parameter_runtime_ref_program_ids():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    program_id = 3734980569294953568
    analysis = FunctionReturnAnalysis(
        function_name="fc_apply_indirect",
        entry_point="0x101000",
        parameters=[],
        returns=[],
        return_type="int",
        return_abi_facts=_present_return_abi_facts(),
    )
    analysis.binary_id = "B10"
    key = (
        "typed_target_expression",
        ("runtime_ref", ("parameter", program_id, 0x101000, 0)),
    )

    normalized = strategy._artifact_stable_key_for_analysis(key, analysis)

    assert not _nested_contains(normalized, program_id)
    assert _nested_contains(normalized, "B10")
    assert _nested_contains(normalized, 0x101000)

from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import echo_input_correspondence
from scripts.function_tracer_pcode.tests.unit._sat_decisiveness_fixtures import *

import pytest
from scripts.function_tracer_pcode.tests.unit._publication import raw_function_analysis
from scripts.function_tracer_pcode.tests.unit._premise_support import assume_satisfiable_premise


@pytest.fixture(autouse=True)
def _gate_runs_in_the_fixture_comparison():
    # fixture の比較中の証拠は、それを作った比較（raw pair と relation）の中でだけ採用される
    # （Issue #167）。gate を直接呼ぶ test はその比較の中で呼ぶ。strategy.check は自分の比較を開く。
    with _fixture_comparison():
        yield

def test_call_argument_proof_rejects_unrelated_proof_content_sections():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _call_effect_summary_proof_evidence(object_target_key=object_target_key)
    evidence["proof_content"] = {
        "object_derived": True,
        "status": "complete",
        "proof_rule": "call_effect_object_evidence_complete",
        "object_target_key": object_target_key,
        "call_effect_summary": {"status": "complete", "foo": "bar"},
        "runtime_ref": {"status": "complete", "foo": "bar"},
        "callsite_storage": {"status": "complete", "foo": "bar"},
    }

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()

def test_call_argument_proof_rejects_mismatched_runtime_ref_payload():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["runtime_ref"]["runtime_ref"] = ("runtime_ref", "different-callsite")

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()

def test_call_argument_proof_rejects_summary_without_target_kind_and_evidence_kind():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["call_effect_summary"]["summary_source"] = (
        "effect_summary",
        "different_target",
    )
    evidence["proof_content"]["call_effect_summary"].pop("evidence_kind")

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()

def test_call_argument_proof_rejects_missing_phase15_sections():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"].pop("callee_summary_completion")

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()

def test_call_argument_proof_rejects_abi_coercion_mismatch():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["callee_precondition"]["abi_coercion"].pop(
        "callee_parameter_interpretation"
    )

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()

def test_call_argument_proof_rejects_bounded_refinement_dependency_cycle():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["bounded_refinement"]["dependency_cycle"] = True

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()

def test_call_argument_proof_rejects_truncated_bounded_refinement():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["bounded_refinement"]["truncated"] = True

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()

def test_call_argument_proof_rejects_bounded_refinement_ref_mismatch():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["callee_summary_completion"][
        "bounded_refinement_evidence_ref"
    ] = ("bounded_call_refinement_expansion", "different")

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()

def test_call_argument_proof_rejects_bounded_refinement_partition_mismatch():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["callee_summary_completion"][
        "callee_return_partition_key"
    ] = (("return", "different"),)

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()

def test_call_argument_proof_rejects_summary_callee_without_completed_proof_ids():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_argument_evidence",
        _analysis_with_effect_call_argument_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["bounded_refinement"][
        "callee_summary_requires_completed_proof"
    ] = True
    evidence["proof_content"]["bounded_refinement"]["callee_completed_proof_ids"] = ()
    evidence["proof_content"]["bounded_refinement"][
        "callee_completed_proof_evidence_ids"
    ] = ()

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()

def test_pairwise_call_argument_evidence_recovers_with_matching_completed_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    assume_satisfiable_premise(strategy)
    analysis1 = _analysis_with_effect_call_argument_evidence()
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    analysis1.completed_recovery_proof_evidence = (
        _complete_call_effect_summary_proof_evidence(object_target_key=reason.object_target_key),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    _evidence_of_this_pair(analysis1, analysis2)
    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []

def test_pairwise_preproducer_call_target_resolution_requires_pending_proof(monkeypatch):
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
    analysis1 = _analysis_with_effect_call_target_resolution_evidence()
    analysis2 = raw_function_analysis(
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
    assert reason.reason_id == "call_target_resolution_unproven"
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.detail == "function1:effect_call_target_resolution_evidence"
    assert reason.object_target_key[0] == "call_target_resolution_evidence"
    assert _object_target_key_is_specific(reason.object_target_key) is True
    assert reason.proof_obligation_id == build_proof_obligation_id(
        reason.reason_id,
        reason.proof_stage,
        reason.recovery_proof_kind,
        reason.evidence_kind,
        reason.object_target_key,
    )
    assert reason.object_evidence == {
        "object_derived": True,
        "evidence_version": 1,
        "evidence_kind": "call_effect_summary",
        "blocker_reason": "function1:effect_call_target_resolution_evidence",
        "blocker_reason_kind": "effect_call_target_resolution_evidence",
        "object_target_kind": "call_target_resolution_evidence",
        "left_function": "func1",
        "right_function": "func2",
        "side": "function1",
        "analysis_key": reason.object_target_key[2],
        "runtime_ref": reason.object_target_key[3],
        "callsite_storage": reason.object_target_key[4],
        "resolution_kind": reason.object_target_key[5],
        "path_conditions": reason.object_target_key[6],
        "target_conditions": reason.object_target_key[7],
        "effect_ordinal": reason.object_target_key[8],
        "call_effect_summary_status": "target_resolution_pending_proof",
    }

def test_pairwise_call_target_resolution_requires_matching_completed_proof_by_default(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_effect_call_target_resolution_evidence()
    analysis2 = raw_function_analysis(
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
    assert result.unknown_reasons[0].detail == "function1:effect_call_target_resolution_evidence"

def test_pairwise_call_target_resolution_rejects_incomplete_completed_proof_content(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_effect_call_target_resolution_evidence()
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_target_resolution_evidence",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    evidence = _complete_call_effect_summary_proof_evidence(
        object_target_key=reason.object_target_key,
    )
    evidence["proof_content"].pop("runtime_ref")
    analysis1.completed_recovery_proof_evidence = (evidence,)
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.unknown_reasons[0].detail == "function1:effect_call_target_resolution_evidence"

def test_call_target_resolution_proof_rejects_mismatched_callsite_storage_payload():
    object_target_key = _blocking_unsafety_object_target_key(
        "function1:effect_call_target_resolution_evidence",
        _analysis_with_effect_call_target_resolution_evidence(),
    )
    evidence = _complete_call_effect_summary_proof_evidence(object_target_key)
    evidence["proof_content"]["callsite_storage"]["callsite_storage"] = (
        "callsite_storage",
        "different-callsite",
    )

    assert _completed_proof_ids_for_call_effect_evidence(evidence) == ()

def test_pairwise_call_target_resolution_recovers_with_matching_completed_proof(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    assume_satisfiable_premise(strategy)
    analysis1 = _analysis_with_effect_call_target_resolution_evidence()
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x2000",
        # Issue #167: parameter の対応が完全でないと EQ は確定しない。この test は
        # call target 回復だけを見るので、左と同じ parameter を持たせる。
        parameters=[_param("fp", index=0, size=8), _param("selector", index=1)],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_target_resolution_evidence",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    analysis1.completed_recovery_proof_evidence = (
        _complete_call_effect_summary_proof_evidence(object_target_key=reason.object_target_key),
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    _evidence_of_this_pair(analysis1, analysis2)
    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []

def test_pairwise_self_recursive_call_effect_proof_rejects_non_self_target(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_self_recursive_unsupported_call_effect(
        target_entry=0x2000,
        target_name="callee",
    )
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x3000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x3000", value=_const(1), conditions=[])],
        return_type="int",
    )
    _patch_pairwise_single_unsat_case(monkeypatch, strategy, analysis1, analysis2)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert [
        item
        for item in analysis1.completed_recovery_proof_evidence
        if item.get("evidence_kind") == "call_effect_summary"
    ] == []

def test_pairwise_unknown_indirect_call_effect_proof_is_not_auto_completed(monkeypatch):
    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = _base_context_for_single_int_param()
    solver_runner = Mock()
    solver_runner.timeout = 5
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = raw_function_analysis(
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
    assert [
        item
        for item in analysis1.completed_recovery_proof_evidence
        if item.get("evidence_kind") == "call_effect_summary"
    ] == []

def test_call_effect_summary_producer_emits_only_object_derived_full_ids():
    bare = _call_effect_summary_proof_evidence()
    evidence = _complete_call_effect_summary_proof_evidence(
        bare["object_target_key"],
        proof_obligation_id=bare["proof_obligation_id"],
    )
    analysis = raw_function_analysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        completed_recovery_proof_evidence=(evidence,),
    )

    proof_ids = PairwiseStrategy._completed_recovery_proof_ids(analysis)

    assert proof_ids == (_expected_call_effect_summary_proof_id(evidence),)

def test_call_effect_summary_producer_rejects_missing_unknown_indirect_target_expression():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
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
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    evidence = _complete_call_effect_summary_proof_evidence(
        reason.object_target_key,
        proof_obligation_id=reason.proof_obligation_id,
    )
    analysis1.completed_recovery_proof_evidence = (evidence,)

    assert PairwiseStrategy._completed_call_effect_summary_proof_ids(analysis1, analysis2) == ()
    assert strategy._call_effect_summary_proof_is_complete(reason, analysis1, analysis2) is False

def test_call_effect_summary_producer_rejects_missing_full_proof_id():
    evidence = _call_effect_summary_proof_evidence()
    evidence.pop("proof_obligation_id", None)
    analysis = raw_function_analysis(
        function_name="func1",
        entry_point="0x1000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=_const(1), conditions=[])],
        return_type="int",
        completed_recovery_proof_evidence=(evidence,),
    )

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis) == ()

def test_call_effect_summary_producer_rejects_non_object_derived_evidence():
    analysis = _analysis_with_call_effect_summary_proof_evidence(object_derived=False)

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis) == ()

def test_call_effect_summary_producer_rejects_mismatched_full_proof_id():
    evidence = _call_effect_summary_proof_evidence()
    wrong_id = build_proof_obligation_id(
        UnknownReasonId.EQUIVALENCE_BLOCKING_UNSAFETY.value,
        evidence["proof_stage"],
        evidence["recovery_proof_kind"],
        evidence["evidence_kind"],
        ("unsupported_call_effect", "different-callsite"),
    )
    analysis = _analysis_with_call_effect_summary_proof_evidence(
        proof_obligation_id=wrong_id,
    )

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis) == ()

def test_call_effect_summary_producer_rejects_active_safety_blockers():
    coverage_blocked = _analysis_with_call_effect_summary_proof_evidence()
    coverage_blocked.analysis_notes.append("return_case_coverage_gap")
    sat_blocked = _analysis_with_call_effect_summary_proof_evidence()
    sat_blocked.analysis_notes.append("indirect_control_flow_unresolved")
    unsupported_blocked = _analysis_with_call_effect_summary_proof_evidence(
        unsupported_effect_reasons=("target_identity_unavailable",),
    )

    assert PairwiseStrategy._completed_recovery_proof_ids(coverage_blocked) == ()
    assert PairwiseStrategy._completed_recovery_proof_ids(sat_blocked) == ()
    assert PairwiseStrategy._completed_recovery_proof_ids(unsupported_blocked) == ()

def test_call_effect_summary_reason_accepts_targeted_clean_proof_with_analysis_blocker():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = _analysis_with_unsupported_call_effect()
    analysis1.analysis_notes.append("indirect_control_flow_unresolved")
    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )
    evidence = _complete_call_effect_summary_proof_evidence(
        reason.object_target_key,
        proof_obligation_id=reason.proof_obligation_id,
    )
    analysis1.completed_recovery_proof_evidence = (evidence,)

    assert PairwiseStrategy._completed_recovery_proof_ids(analysis1, analysis2) == ()
    assert strategy._call_effect_summary_proof_is_complete(reason, analysis1, analysis2) is True

def test_monolithic_strategy_does_not_accept_unsat_with_incomplete_effect_summary():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1 = raw_function_analysis(
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
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )

    formula_builder = echo_input_correspondence(Mock())
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
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None

def test_monolithic_strategy_does_not_accept_unsat_with_unsupported_effect_summary():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1 = raw_function_analysis(
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
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=_const(1), conditions=[])],
        return_type="int",
    )

    formula_builder = echo_input_correspondence(Mock())
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
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None

def test_monolithic_call_effect_summary_proof_complete_allows_recovery():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    formula_builder = echo_input_correspondence(Mock())
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
    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)
    assume_satisfiable_premise(strategy)
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_MONOLITHIC_FALLBACK",
    )
    analysis1.completed_recovery_proof_evidence = (
        _complete_call_effect_summary_proof_evidence(
            completed_reason.object_target_key,
            proof_obligation_id=completed_reason.proof_obligation_id,
        ),
    )

    _evidence_of_this_pair(analysis1, analysis2)
    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.unknown_reasons == []
    assert result.counterexample_raw is None

def test_monolithic_call_effect_summary_bare_completed_proof_id_does_not_recover():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    formula_builder = echo_input_correspondence(Mock())
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
    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)
    assume_satisfiable_premise(strategy)
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_MONOLITHIC_FALLBACK",
    )
    analysis1.completed_recovery_proof_ids = (completed_reason.proof_obligation_id,)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.counterexample_raw is None

def test_monolithic_call_effect_summary_missing_completed_proof_id_does_not_recover():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    analysis1 = _analysis_with_unsupported_call_effect()
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )
    formula_builder = echo_input_correspondence(Mock())
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
    strategy = MonolithicStrategy(formula_builder, _UnsatSolverRunner(), debug=False)
    assume_satisfiable_premise(strategy)
    completed_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_MONOLITHIC_FALLBACK",
    )
    evidence = _call_effect_summary_proof_evidence(
        object_target_key=completed_reason.object_target_key,
        proof_obligation_id=completed_reason.proof_obligation_id,
    )
    evidence.pop("proof_obligation_id", None)
    analysis1.completed_recovery_proof_evidence = (evidence,)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unknown_reasons
    assert result.counterexample_raw is None

def test_pairwise_strategy_downgrades_unsat_when_deferred_call_recovery_is_inconclusive(monkeypatch):
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

    x = Expression.parameter("x", 0, size=4)
    pcode_ref = PcodeOpRef(address_offset=0x3000, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee"),
        arguments=[Expression.parameter("param_1", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee"),
            sequence=0,
        ),
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        call_argument_recovery_reason="argument_recovery_inconclusive",
    )
    analysis1 = raw_function_analysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=x, conditions=[])],
        return_type="int",
    )
    analysis1.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x, conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=x,
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=x,
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
    monkeypatch.setattr(
        strategy,
        "_case_contains_unresolved_expression",
        lambda *_args, **_kwargs: False,
    )
    strategy._solve_query_after_guard = Mock(
        return_value=_solver_bound_query_result(True)
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.unsat_pairs == 1
    assert result.unknown_pairs == 0

def test_pairwise_strategy_records_call_effect_blocker_as_pending_object_proof(monkeypatch):
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

    x = Expression.parameter("x", 0, size=4)
    pcode_ref = PcodeOpRef(address_offset=0x3000, seq_time=1, seq_order=0, mnemonic="CALL")
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
        arguments=[Expression.parameter("param_1", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            caller_program_id=1,
            caller_entry_offset=0x400000,
            pcode_op_ref=pcode_ref,
            target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
            sequence=0,
        ),
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        call_argument_recovery_reason="argument_recovery_inconclusive",
    )
    analysis1 = raw_function_analysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=x, conditions=[])],
        return_type="int",
    )
    analysis1.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x, conditions=[])],
        return_type="int",
    )
    case1 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=x,
        return_info=analysis1.returns[0],
        return_type="int",
        parameters=analysis1.parameters,
    )
    case2 = ReturnCase(
        index=0,
        conditions=[],
        value_expr=x,
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
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_args, **_kwargs: False)
    strategy._solve_query_after_guard = Mock(
        return_value=_solver_bound_query_result(True)
    )

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert len(result.unknown_reasons) == 1
    reason = result.unknown_reasons[0]
    assert reason.reason_id == "call_argument_extraction_incomplete"
    assert reason.recovery_proof_kind == UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value
    assert reason.proof_stage == "object_evidence_collected"
    assert reason.evidence_kind == "call_effect_summary"
    assert reason.recovery_action == "call_effect_summary_proof_required"
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.object_target_key[0] == "deferred_call"
    assert _nested_contains(reason.object_target_key, pcode_ref.stable_key())

def test_pairwise_strategy_records_recoverable_candidate_for_call_effect_blocker():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    analysis1, incomplete_pcode_ref, complete_pcode_ref = (
        _analysis_with_two_effect_call_argument_evidences()
    )
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=_const(1), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )

    assert reason.object_target_key[0] == "call_effect_blocker"
    assert _nested_contains(reason.object_target_key, incomplete_pcode_ref.stable_key())
    assert _nested_contains(reason.object_target_key, complete_pcode_ref.stable_key())

    strategy._record_completed_call_effect_summary_proof_if_safe(reason, analysis1, analysis2)

    proofs = [
        item
        for item in getattr(analysis1, "completed_recovery_proof_evidence", ())
        if item.get("proof_obligation_id") == reason.proof_obligation_id
    ]
    assert proofs == []

def test_pairwise_strategy_uses_unsupported_call_site_object_ref_for_blocking_proof():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    site = UnsupportedCallEffectRef(
        pcode_op_ref=pcode_ref,
        target_ref=None,
        reason="target_identity_unavailable",
        order_key=9,
    )
    analysis1 = raw_function_analysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )

    assert reason.recovery_proof_kind == UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value
    assert reason.action_status == UnknownRecoveryActionStatus.PENDING_PROOF.value
    assert reason.object_target_key[0] == "unsupported_call_effect"
    assert _nested_contains(reason.object_target_key, pcode_ref.stable_key())

def test_pairwise_unsupported_call_effect_uses_phase2_specific_object_key():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    pcode_ref = PcodeOpRef(
        address_offset=0x401020,
        seq_time=31,
        seq_order=7,
        mnemonic="CALLIND",
        binary_id="B10",
        program_uid=12345,
        function_entry_space="ram",
        function_entry_offset=0x401000,
        target_space="ram",
        target_offset=0x401020,
        opcode=8,
        local_op_ordinal=0,
    )
    site = UnsupportedCallEffectRef(
        pcode_op_ref=pcode_ref,
        target_ref=CallTargetRef.from_code_address(0x401234, program_id=12345),
        target_expr=Expression.parameter("fp", 0, size=8),
        reason="target_identity_unavailable",
        order_key=9,
    )
    analysis1 = raw_function_analysis(
        function_name="func1",
        entry_point="0x401000",
        function_ref=CallTargetRef.from_name("func1", program_id=12345, entry_offset=0x401000),
        binary_id="B10",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x401000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    analysis2 = raw_function_analysis(
        function_name="func2",
        entry_point="0x402000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x402000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis1,
        analysis2,
        stage="S_PAIRWISE",
    )

    assert reason.object_target_key[0] == "unsupported_call_effect"
    assert reason.object_target_key[2] == ("function_ref", ("function", "B10", 0x401000))
    assert reason.object_target_key[3][0] == "runtime_ref"
    assert ("pcode_op_ref", pcode_ref.stable_key()) in reason.object_target_key[3]
    assert ("callee_identity", ("code_address", "B10", 0x401234)) in reason.object_target_key[3]
    assert reason.object_target_key[4][0] == "callsite_storage"
    assert ("pcode_op_ref", pcode_ref.stable_key()) in reason.object_target_key[4]
    assert ("callee_identity", ("code_address", "B10", 0x401234)) in reason.object_target_key[4]
    assert reason.object_target_key[5] == ("effect_ordinal", 9)
    assert _object_target_key_is_specific(reason.object_target_key) is True
    assert reason.proof_obligation_id == build_proof_obligation_id(
        reason.reason_id,
        "object_evidence_collected",
        UnknownRecoveryProofKind.CALL_EFFECT_SUMMARY_PROOF.value,
        "call_effect_summary",
        reason.object_target_key,
    )
    assert reason.object_evidence == {
        "object_derived": True,
        "evidence_version": 1,
        "evidence_kind": "call_effect_summary",
        "blocker_reason": "function1:unsupported_call_effect_summary",
        "blocker_reason_kind": "unsupported_call_effect_summary",
        "object_target_kind": "unsupported_call_effect",
        "left_function": "func1",
        "right_function": "func2",
        "side": "function1",
        "analysis_key": ("function_ref", ("function", "B10", 0x401000)),
        "runtime_ref": reason.object_target_key[3],
        "callsite_storage": reason.object_target_key[4],
        "argument_storage": (),
        "effect_ordinal": ("effect_ordinal", 9),
        "unsupported_reason": "target_identity_unavailable",
        "call_effect_summary_status": "target_identity_unavailable",
    }
    assert UnknownReasonRecord.from_dict(reason.to_dict()).object_evidence == reason.object_evidence

def test_unsupported_call_site_object_key_keeps_caller_identity_distinct():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    site = UnsupportedCallEffectRef(
        pcode_op_ref=pcode_ref,
        target_ref=None,
        reason="target_identity_unavailable",
        order_key=9,
    )
    left = raw_function_analysis(
        function_name="func",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    right = raw_function_analysis(
        function_name="func",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func", program_id=2, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )

    left_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        left,
        right,
        stage="S_PAIRWISE",
    )
    right_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function2:unsupported_call_effect_summary",
        left,
        right,
        stage="S_PAIRWISE",
    )

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id
    assert ("function_ref", ("function", 1, 0x1000)) in left_reason.object_target_key
    assert ("function_ref", ("function", 2, 0x1000)) in right_reason.object_target_key

def test_unsupported_call_effect_blocker_prefers_unsupported_site_over_deferred_call():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    unsupported_pcode = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    deferred_pcode = PcodeOpRef(address_offset=0x4000, seq_time=7, seq_order=2, mnemonic="CALL")
    site = UnsupportedCallEffectRef(
        pcode_op_ref=unsupported_pcode,
        target_ref=None,
        reason="target_identity_unavailable",
        order_key=9,
    )
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
        arguments=[Expression.parameter("x", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            caller_program_id=1,
            caller_entry_offset=0x1000,
            pcode_op_ref=deferred_pcode,
            target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
            sequence=0,
        ),
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
    )
    analysis = raw_function_analysis(
        function_name="func",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    other = raw_function_analysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis,
        other,
        stage="S_PAIRWISE",
    )

    assert reason.object_target_key[0] == "unsupported_call_effect"
    assert _nested_contains(reason.object_target_key, unsupported_pcode.stable_key())
    assert not _nested_contains(reason.object_target_key, deferred_pcode.stable_key())

def test_bounded_deferred_target_blocker_uses_concrete_callsite_fallback():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    unsupported_pcode = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    deferred_pcode = PcodeOpRef(address_offset=0x4000, seq_time=7, seq_order=2, mnemonic="CALL")
    site = UnsupportedCallEffectRef(
        pcode_op_ref=unsupported_pcode,
        target_ref=None,
        reason="target_identity_unavailable",
        order_key=9,
    )
    deferred = DeferredCallInfo(
        placeholder_name="call_out_of_scope:callee#0",
        target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
        arguments=[Expression.parameter("x", 0, size=4)],
        deferred_call_ref=DeferredCallRef(
            caller_program_id=1,
            caller_entry_offset=0x1000,
            pcode_op_ref=deferred_pcode,
            target_ref=CallTargetRef.from_name("callee", program_id=1, entry_offset=0x401000),
            sequence=0,
        ),
        call_argument_recovery_status=CallArgumentEvidence.RECOVERY_COMPLETE,
    )
    analysis = raw_function_analysis(
        function_name="func",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    other = raw_function_analysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:bounded_call_refinement_deferred_target_unresolved",
        analysis,
        other,
        stage="S_PAIRWISE",
    )

    assert reason.object_target_key[0] == "deferred_call"
    assert _nested_contains(reason.object_target_key, deferred_pcode.stable_key())
    assert not _nested_contains(reason.object_target_key, unsupported_pcode.stable_key())
    assert not _nested_contains(reason.object_target_key, "call_effect_blocker")

def test_deferred_call_object_key_distinguishes_unknown_target_expression_provenance():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    deferred_ref = DeferredCallRef(
        caller_program_id=1,
        caller_entry_offset=0x1000,
        pcode_op_ref=pcode_ref,
        target_ref=CallTargetRef.unknown(),
        sequence=0,
    )

    def _analysis_with_target_expr(target_expr: Expression) -> FunctionReturnAnalysis:
        deferred = DeferredCallInfo(
            placeholder_name="indirect",
            target_ref=CallTargetRef.unknown(),
            arguments=[Expression.parameter("x", 0, size=4)],
            call_target_expr=target_expr,
            deferred_call_ref=deferred_ref,
            call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        )
        analysis = raw_function_analysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
        return analysis

    left = _analysis_with_target_expr(Expression.parameter("fp", 0, size=8))
    right = _analysis_with_target_expr(Expression.parameter("gp", 1, size=8))
    other = raw_function_analysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    left_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        left,
        other,
        stage="S_PAIRWISE",
    )
    right_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        right,
        other,
        stage="S_PAIRWISE",
    )

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id
    assert _nested_contains(
        left_reason.object_target_key,
        ("typed_target_expression", ("expression", ("parameter", "fp", ("int", 0), 8))),
    )
    assert _nested_contains(
        right_reason.object_target_key,
        ("typed_target_expression", ("expression", ("parameter", "gp", ("int", 1), 8))),
    )

def test_deferred_call_object_key_distinguishes_truncated_target_expression_provenance():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")
    deferred_ref = DeferredCallRef(
        caller_program_id=1,
        caller_entry_offset=0x1000,
        pcode_op_ref=pcode_ref,
        target_ref=CallTargetRef.unknown(),
        sequence=0,
    )

    def _analysis_with_target_expr(target_expr: Expression) -> FunctionReturnAnalysis:
        deferred = DeferredCallInfo(
            placeholder_name="indirect",
            target_ref=CallTargetRef.unknown(),
            arguments=[Expression.parameter("x", 0, size=4)],
            call_target_expr=target_expr,
            deferred_call_ref=deferred_ref,
            call_argument_recovery_status=CallArgumentEvidence.RECOVERY_INCONCLUSIVE,
        )
        analysis = raw_function_analysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        analysis.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
        return analysis

    left = _analysis_with_target_expr(_deep_zext_target("fp", 0))
    right = _analysis_with_target_expr(_deep_zext_target("gp", 1))
    other = raw_function_analysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    left_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        left,
        other,
        stage="S_PAIRWISE",
    )
    right_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:effect_call_argument_evidence_incomplete",
        right,
        other,
        stage="S_PAIRWISE",
    )

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id

def test_unsupported_call_effect_object_key_distinguishes_target_expression_provenance():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3020, seq_time=4, seq_order=1, mnemonic="CALLIND")

    def _analysis_with_site(target_expr: Expression) -> FunctionReturnAnalysis:
        site = UnsupportedCallEffectRef(
            pcode_op_ref=pcode_ref,
            target_ref=None,
            target_expr=target_expr,
            reason="target_identity_unavailable",
            order_key=9,
        )
        return raw_function_analysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            binary_id="B10",
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                has_unsupported_call=True,
                unsupported_call_sites=(site,),
            ),
        )

    left = _analysis_with_site(Expression.parameter("fp", 0, size=8))
    right = _analysis_with_site(Expression.parameter("gp", 1, size=8))
    other = raw_function_analysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    left_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        left,
        other,
        stage="S_PAIRWISE",
    )
    right_reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        right,
        other,
        stage="S_PAIRWISE",
    )

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id
    assert _nested_contains(
        left_reason.object_target_key,
        ("typed_target_expression", ("expression", ("parameter", "fp", ("int", 0), 8))),
    )
    assert _nested_contains(
        left_reason.object_target_key,
        (
            "callee_identity",
            (
                "unknown",
                "B10",
                (
                    "target_expression",
                    ("typed_target_expression", ("expression", ("parameter", "fp", ("int", 0), 8))),
                ),
            ),
        ),
    )
    assert _nested_contains(
        right_reason.object_target_key,
        ("typed_target_expression", ("expression", ("parameter", "gp", ("int", 1), 8))),
    )

def test_unsupported_call_effect_object_key_does_not_embed_process_local_target_expression_id():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3030, seq_time=5, seq_order=1, mnemonic="CALLIND")
    target_expr = _deep_zext_target("fp", 0)

    site = UnsupportedCallEffectRef(
        pcode_op_ref=pcode_ref,
        target_ref=None,
        target_expr=target_expr,
        reason="target_identity_unavailable",
        order_key=10,
    )
    analysis = raw_function_analysis(
        function_name="func",
        entry_point="0x1000",
        function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
        effect_summary=EffectSummary(
            parameter_names=["x"],
            effects=[],
            has_unsupported_call=True,
            unsupported_call_sites=(site,),
        ),
    )
    other = raw_function_analysis(
        function_name="other",
        entry_point="0x2000",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
        return_type="int",
    )

    reason = strategy._make_blocking_unsafety_unknown_reason(
        "function1:unsupported_call_effect_summary",
        analysis,
        other,
        stage="S_PAIRWISE",
    )

    target_identity = id(target_expr)
    assert not _nested_contains(site.stable_key(), target_identity)
    assert not _nested_contains(reason.object_target_key, target_identity)
    assert not _nested_contains(reason.proof_obligation_id, target_identity)

def test_unsupported_call_effect_object_key_distinguishes_truncated_target_expression_provenance():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3030, seq_time=5, seq_order=1, mnemonic="CALLIND")

    def _reason_for(target_expr: Expression):
        site = UnsupportedCallEffectRef(
            pcode_op_ref=pcode_ref,
            target_ref=None,
            target_expr=target_expr,
            reason="target_identity_unavailable",
            order_key=10,
        )
        analysis = raw_function_analysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                has_unsupported_call=True,
                unsupported_call_sites=(site,),
            ),
        )
        other = raw_function_analysis(
            function_name="other",
            entry_point="0x2000",
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        return site, strategy._make_blocking_unsafety_unknown_reason(
            "function1:unsupported_call_effect_summary",
            analysis,
            other,
            stage="S_PAIRWISE",
        )

    left_site, left_reason = _reason_for(_deep_zext_target("fp", 0))
    right_site, right_reason = _reason_for(_deep_zext_target("gp", 1))

    assert left_site.stable_key() != right_site.stable_key()
    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id

def test_unsupported_call_effect_object_key_handles_very_deep_target_expression_without_recursion_error():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3030, seq_time=5, seq_order=1, mnemonic="CALLIND")

    def _reason_for(target_expr: Expression):
        site = UnsupportedCallEffectRef(
            pcode_op_ref=pcode_ref,
            target_ref=None,
            target_expr=target_expr,
            reason="target_identity_unavailable",
            order_key=10,
        )
        analysis = raw_function_analysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                has_unsupported_call=True,
                unsupported_call_sites=(site,),
            ),
        )
        other = raw_function_analysis(
            function_name="other",
            entry_point="0x2000",
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        return strategy._make_blocking_unsafety_unknown_reason(
            "function1:unsupported_call_effect_summary",
            analysis,
            other,
            stage="S_PAIRWISE",
        )

    left_reason = _reason_for(_deep_zext_target("fp", 0, depth=900))
    right_reason = _reason_for(_deep_zext_target("gp", 1, depth=900))

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id

def test_unsupported_call_effect_object_key_distinguishes_sources_beyond_digest_node_limit():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3030, seq_time=5, seq_order=1, mnemonic="CALLIND")

    def _reason_for(target_expr: Expression):
        site = UnsupportedCallEffectRef(
            pcode_op_ref=pcode_ref,
            target_ref=None,
            target_expr=target_expr,
            reason="target_identity_unavailable",
            order_key=10,
        )
        analysis = raw_function_analysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                has_unsupported_call=True,
                unsupported_call_sites=(site,),
            ),
        )
        other = raw_function_analysis(
            function_name="other",
            entry_point="0x2000",
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        return strategy._make_blocking_unsafety_unknown_reason(
            "function1:unsupported_call_effect_summary",
            analysis,
            other,
            stage="S_PAIRWISE",
        )

    left_reason = _reason_for(_deep_zext_target("fp", 0, depth=8200))
    right_reason = _reason_for(_deep_zext_target("gp", 1, depth=8200))

    assert left_reason.object_target_key != right_reason.object_target_key
    assert left_reason.proof_obligation_id != right_reason.proof_obligation_id

def test_unsupported_call_effect_object_key_distinguishes_deep_tail_structure_beyond_digest_node_limit():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    pcode_ref = PcodeOpRef(address_offset=0x3030, seq_time=5, seq_order=1, mnemonic="CALLIND")

    def _reason_for(target_expr: Expression):
        site = UnsupportedCallEffectRef(
            pcode_op_ref=pcode_ref,
            target_ref=None,
            target_expr=target_expr,
            reason="target_identity_unavailable",
            order_key=10,
        )
        analysis = raw_function_analysis(
            function_name="func",
            entry_point="0x1000",
            function_ref=CallTargetRef.from_name("func", program_id=1, entry_offset=0x1000),
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x1000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
            effect_summary=EffectSummary(
                parameter_names=["x"],
                effects=[],
                has_unsupported_call=True,
                unsupported_call_sites=(site,),
            ),
        )
        other = raw_function_analysis(
            function_name="other",
            entry_point="0x2000",
            parameters=[_param("x")],
            returns=[ReturnInfo(address="0x2000", value=Expression.parameter("x", 0, size=4), conditions=[])],
            return_type="int",
        )
        return strategy._make_blocking_unsafety_unknown_reason(
            "function1:unsupported_call_effect_summary",
            analysis,
            other,
            stage="S_PAIRWISE",
        )

    zext_reason = _reason_for(_deep_target_with_tail_op("fp", 0, "INT_ZEXT", depth=8200))
    sext_reason = _reason_for(_deep_target_with_tail_op("fp", 0, "INT_SEXT", depth=8200))

    assert zext_reason.object_target_key != sext_reason.object_target_key
    assert zext_reason.proof_obligation_id != sext_reason.proof_obligation_id

def test_call_effect_blocker_candidate_score_prefers_complete_call_argument_evidence():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    incomplete = (
        "call_argument_evidence",
        "function1",
        "a",
        "b",
        "c",
        "d",
        False,
        "incomplete",
    )
    complete = (
        "call_argument_evidence",
        "function1",
        "a",
        "b",
        "c",
        "d",
        True,
        "complete",
    )
    unsupported = (
        "unsupported_call_effect",
        "function1",
        "a",
        "b",
        "c",
        "d",
        ("foo",),
    )

    assert strategy._call_effect_blocker_candidate_score(complete) > strategy._call_effect_blocker_candidate_score(incomplete)
    assert strategy._call_effect_blocker_candidate_score(complete) > strategy._call_effect_blocker_candidate_score(unsupported)

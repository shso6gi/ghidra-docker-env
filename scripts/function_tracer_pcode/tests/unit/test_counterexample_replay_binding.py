"""Issue #28: replay proofs are bound to one witness and required for every SAT."""
from scripts.function_tracer_pcode.tests.unit._input_correspondence_support import comparison_of, echo_input_correspondence
from unittest.mock import Mock

from scripts.function_tracer_pcode.authority.lifecycle.production_signals import (
    SatCounterexampleEvidenceBinding,
)
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis, ReturnInfo, Expression
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
from scripts.function_tracer_pcode.proof.strategies import pairwise_query_executor as executor
from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.tests.unit._publication import raw_function_analysis


def _analysis(name):
    return raw_function_analysis(
        function_name=name, entry_point="0x1000",
        parameters=[{"name": "x", "size": 4, "index": 0, "is_signed": True}],
        returns=[ReturnInfo(address="0x1000", value=Expression.constant(1, size=4), conditions=[])],
        return_type="int",
    )


def _binding(formula="a" * 64, model="b" * 64, premise="premise-1", pair=(0, 0)):
    return SatCounterexampleEvidenceBinding(formula, model, premise, pair)


def _base_ctx():
    return {
        "params1": [ParameterInfo(original_name="x", smt_name="x_1", bit_width=32, index=0)],
        "params2": [ParameterInfo(original_name="x", smt_name="x_2", bit_width=32, index=0)],
        "extra_vars1": [], "extra_vars2": [],
    }


def test_replay_requirement_no_longer_depends_on_function_names():
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    assert strategy._counterexample_replay_reasons(_analysis("f"), _analysis("g")) == (
        "counterexample_replay_missing",
    )
    assert strategy._counterexample_replay_reasons(_analysis("f"), _analysis("f")) == (
        "counterexample_replay_missing",
    )


def test_replay_validation_fails_closed_without_a_model():
    strategy = Mock()
    strategy._debug_print = Mock()
    assert executor.validate_counterexample_across_cases(
        strategy, _base_ctx(), [], [], lambda v: v, lambda v: v, (0, 0), None,
    ) is False
    assert executor.validate_counterexample_across_cases(
        strategy, _base_ctx(), [], [], lambda v: v, lambda v: v, (0, 0), {},
    ) is False


def _strategy_with_reason(binding):
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    analysis1, analysis2 = _analysis("f"), _analysis("f")
    reason = strategy._make_sat_unsafety_unknown_reason(
        ("counterexample_replay_missing",), analysis1, analysis2,
        case1=None, case2=None, pair_id="(0,0)", stage="S_PAIRWISE",
        counterexample_binding=binding,
    )
    return strategy, analysis1, analysis2, reason


def test_bound_replay_proof_completes_only_for_the_same_witness():
    binding = _binding()
    strategy, analysis1, analysis2, reason = _strategy_with_reason(binding)
    model = {"x_1": 7, "x_2": 7}

    with comparison_of(analysis1, analysis2):
        assert strategy._record_pairwise_counterexample_replay_proof(
            reason, analysis1, analysis2, base_ctx=_base_ctx(), counterexample_raw=model,
            binding=binding, execution_receipt_digest="c" * 64, pair_id="(0,0)",
        ) is True
        assert strategy._sat_unsafety_resolution_proof_is_complete(
            reason, analysis1, analysis2, current_counterexample_raw=model,
            expected_binding=binding, expected_execution_receipt_digest="c" * 64,
        ) is True

        # Another query / premise / pair / receipt must not be discharged by this proof.
        for other in (
            _binding(formula="d" * 64), _binding(premise="premise-2"), _binding(pair=(1, 0)),
        ):
            assert strategy._sat_unsafety_resolution_proof_is_complete(
                reason, analysis1, analysis2, current_counterexample_raw=model,
                expected_binding=other, expected_execution_receipt_digest="c" * 64,
            ) is False
        assert strategy._sat_unsafety_resolution_proof_is_complete(
            reason, analysis1, analysis2, current_counterexample_raw=model,
            expected_binding=binding, expected_execution_receipt_digest="e" * 64,
        ) is False
        # A different model is not this witness either.
        assert strategy._sat_unsafety_resolution_proof_is_complete(
            reason, analysis1, analysis2, current_counterexample_raw={"x_1": 8, "x_2": 8},
            expected_binding=binding, expected_execution_receipt_digest="c" * 64,
        ) is False


def test_replay_proof_requires_model_fixed_assertions_binding_and_receipt():
    binding = _binding()
    strategy, analysis1, analysis2, reason = _strategy_with_reason(binding)
    common = dict(base_ctx=_base_ctx(), binding=binding, execution_receipt_digest="c" * 64, pair_id="(0,0)")

    assert strategy._record_pairwise_counterexample_replay_proof(
        reason, analysis1, analysis2, counterexample_raw=None, **common) is False
    assert strategy._record_pairwise_counterexample_replay_proof(
        reason, analysis1, analysis2, counterexample_raw={"return_1": 1}, **common) is False
    assert strategy._record_pairwise_counterexample_replay_proof(
        reason, analysis1, analysis2, counterexample_raw={"x_1": 1, "x_2": 1},
        base_ctx=_base_ctx(), binding=None, execution_receipt_digest="c" * 64, pair_id="(0,0)") is False
    assert strategy._record_pairwise_counterexample_replay_proof(
        reason, analysis1, analysis2, counterexample_raw={"x_1": 1, "x_2": 1},
        base_ctx=_base_ctx(), binding=binding, execution_receipt_digest=None, pair_id="(0,0)") is False
    assert analysis1.completed_recovery_proof_evidence == () or not any(
        e.get("proof_source") == "pairwise_case_split_counterexample_validation"
        for e in analysis1.completed_recovery_proof_evidence
    )


def test_closed_formula_sat_needs_no_replay_but_open_formula_does():
    strategy = Mock()
    strategy._debug_print = Mock()
    closed_ctx = {"params1": [], "params2": [], "extra_vars1": [], "extra_vars2": []}
    assert executor.counterexample_replay_targets(closed_ctx) == ()
    assert executor.validate_counterexample_across_cases(
        strategy, closed_ctx, [], [], lambda v: v, lambda v: v, (0, 0), {},
    ) is True
    assert executor.counterexample_replay_targets(_base_ctx()) == (("x_1", 32), ("x_2", 32))


def test_validated_witness_supersedes_rejected_witnesses_of_other_pairs(monkeypatch):
    """bess/SIGN shape: an earlier pair's SAT is rejected (e.g. NaN), a later pair's SAT is
    validated; the result is NOT_EQ with no witness-scoped blocker left behind."""
    from types import SimpleNamespace
    from scripts.function_tracer_pcode.core import Condition, ExpressionType
    from scripts.function_tracer_pcode.proof.obligations import SolverQueryExecutionReceipt
    from scripts.function_tracer_pcode.proof.strategies.pairwise_models import QueryResult, ReturnCase
    from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus

    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = {
        "header_lines": ["(declare-const x_1 (_ BitVec 32))", "(declare-const x_2 (_ BitVec 32))", "(assert (= x_1 x_2))"],
        **_base_ctx(), "constrained_fragments": [], "return_size1": 32, "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 1, "x_2": 1})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    x = Expression.parameter("x", 0, size=4)

    def _eq(left, right):
        return Condition(Expression(ExpressionType.BINARY_OP, operator="INT_EQUAL", operands=[left, right], size=1))

    params = [{"name": "x", "size": 4, "index": 0, "is_signed": True}]
    analysis1 = raw_function_analysis(
        function_name="left", entry_point="0x1", parameters=params,
        returns=[ReturnInfo(address="0x1", value=Expression.constant(1, size=4), conditions=[_eq(x, Expression.constant(0, size=4))]),
                 ReturnInfo(address="0x2", value=Expression.constant(2, size=4), conditions=[_eq(x, Expression.constant(1, size=4))])],
        return_type="int",
    )
    analysis2 = raw_function_analysis(
        function_name="right", entry_point="0x3", parameters=params,
        returns=[ReturnInfo(address="0x3", value=Expression.constant(9, size=4), conditions=[])],
        return_type="int",
    )
    cases1 = [ReturnCase(index=i, conditions=list(r.conditions), value_expr=r.value, return_info=r,
                         return_type="int", parameters=analysis1.parameters) for i, r in enumerate(analysis1.returns)]
    cases2 = [ReturnCase(index=0, conditions=[], value_expr=analysis2.returns[0].value,
                         return_info=analysis2.returns[0], return_type="int", parameters=analysis2.parameters)]
    monkeypatch.setattr(strategy, "_extract_return_cases",
                        lambda a: cases1 if a.function_name == "left" else cases2)
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_a, **_k: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_a, **_k: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_a, **_k: False)
    monkeypatch.setattr(strategy, "_outcome_partition_covered_labels", lambda *_a, **_k: {"function1", "function2"})
    monkeypatch.setattr(strategy, "_outcome_partition_inconclusive_labels", lambda *_a, **_k: set())
    verdicts = iter([False, True])  # first SAT pair rejected, second validated
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.proof.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_a, **_k: next(verdicts),
    )
    superseded = []
    original = strategy._supersede_rejected_witness_blocker

    def spy(kind, refs, *a, **k):
        superseded.append((kind, k["pair_id"]))
        return original(kind, refs, *a, **k)

    monkeypatch.setattr(strategy, "_supersede_rejected_witness_blocker", spy)

    def _sat_query(*args, **kwargs):
        model = {"x_1": 1, "x_2": 1}
        parallel = SimpleNamespace(is_equivalent=False, results=(), get_counterexample=lambda: model)
        qr = QueryResult(is_equivalent=False, counterexample_raw=model, solver_results=parallel)
        qr.last_query = "(check-sat)"
        pair_label = next((str(a) for a in args if isinstance(a, str) and a.startswith("(")), None)
        qr.solver_query_execution_receipt = SolverQueryExecutionReceipt.from_execution(
            query="(check-sat)", query_label=pair_label or kwargs.get("pair_id", "(0,0)"),
            proof_stage="with-ineq", parallel_result=parallel,
            solver_identity=("unit", "fake", ("fake",)), timeout_budget=5.0, use_hard_timeout=False,
        )
        return qr

    strategy._solve_query_after_guard = _sat_query

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is False
    assert result.sat_pairs == 1
    assert superseded == [("ambiguity", "(0,0)")]
    assert result.unknown_reasons == []


def test_blocked_return_width_observation_blocks_sat_decisiveness():
    from types import SimpleNamespace
    strategy = PairwiseStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    blocked = SimpleNamespace(
        proven=False,
        blockers=(SimpleNamespace(blocker_kind="input_correspondence", missing_slot="param_1"),),
    )
    proven = SimpleNamespace(proven=True, blockers=())
    plumbing_only = SimpleNamespace(
        proven=False,
        blockers=(SimpleNamespace(blocker_kind="proof_closure", missing_slot="validated_observation_proof_bundle"),),
    )
    base_ctx = {"return_width_observations_by_pair": {"(0,0)": blocked, "(0,1)": proven, "(0,2)": plumbing_only}}

    assert strategy._pair_return_width_unsafety_reasons(base_ctx, "(0,0)") == [
        "function1:return_width_observation_blocked"
    ]
    assert strategy._pair_return_width_unsafety_reasons(base_ctx, "(0,1)") == []
    assert strategy._pair_return_width_unsafety_reasons(base_ctx, "(0,2)") == []
    assert strategy._pair_return_width_unsafety_reasons({}, "(0,0)") == []


def test_pairwise_sat_on_pair_with_blocked_width_observation_is_unknown(monkeypatch):
    from types import SimpleNamespace
    from scripts.function_tracer_pcode.proof.obligations import SolverQueryExecutionReceipt
    from scripts.function_tracer_pcode.proof.strategies.pairwise_models import QueryResult, ReturnCase
    from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus

    formula_builder = echo_input_correspondence(Mock())
    formula_builder.build_base_context.return_value = {
        "header_lines": ["(declare-const x_1 (_ BitVec 32))", "(declare-const x_2 (_ BitVec 32))", "(assert (= x_1 x_2))"],
        **_base_ctx(), "constrained_fragments": [], "return_size1": 32, "return_size2": 32,
    }
    solver_runner = Mock()
    solver_runner.timeout = 5
    solver_runner.run_sequential.return_value = ParallelResult(
        results=[SolverResult("fake", SolverStatus.SAT, model={"x_1": 1, "x_2": 1})]
    )
    strategy = PairwiseStrategy(formula_builder, solver_runner, debug=False)
    analysis1, analysis2 = _analysis("left"), _analysis("right")
    case1 = ReturnCase(index=0, conditions=[], value_expr=analysis1.returns[0].value,
                       return_info=analysis1.returns[0], return_type="int", parameters=analysis1.parameters)
    case2 = ReturnCase(index=0, conditions=[], value_expr=analysis2.returns[0].value,
                       return_info=analysis2.returns[0], return_type="int", parameters=analysis2.parameters)
    monkeypatch.setattr(strategy, "_extract_return_cases", lambda a: [case1] if a.function_name == "left" else [case2])
    monkeypatch.setattr(strategy, "_prune_unreachable_cases", lambda cases, *_a, **_k: cases)
    monkeypatch.setattr(strategy, "_cases_are_contradictory", lambda *_a, **_k: False)
    monkeypatch.setattr(strategy, "_case_contains_unresolved_expression", lambda *_a, **_k: False)
    monkeypatch.setattr(strategy, "_outcome_partition_covered_labels", lambda *_a, **_k: {"function1", "function2"})
    monkeypatch.setattr(strategy, "_outcome_partition_inconclusive_labels", lambda *_a, **_k: set())
    monkeypatch.setattr(strategy, "_pair_return_width_unsafety_reasons",
                        lambda base_ctx, pair_id: ["function1:return_width_observation_blocked"])
    monkeypatch.setattr(
        "scripts.function_tracer_pcode.proof.strategies.pairwise.validate_counterexample_across_cases",
        lambda *_a, **_k: True,
    )

    def _sat_query(*args, **kwargs):
        model = {"x_1": 1, "x_2": 1}
        parallel = SimpleNamespace(is_equivalent=False, results=(), get_counterexample=lambda: model)
        qr = QueryResult(is_equivalent=False, counterexample_raw=model, solver_results=parallel)
        qr.last_query = "(check-sat)"
        qr.solver_query_execution_receipt = SolverQueryExecutionReceipt.from_execution(
            query="(check-sat)", query_label="(0,0)", proof_stage="with-ineq", parallel_result=parallel,
            solver_identity=("unit", "fake", ("fake",)), timeout_budget=5.0, use_hard_timeout=False,
        )
        return qr

    strategy._solve_query_after_guard = _sat_query
    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.sat_pairs == 0
    reason = result.unknown_reasons[0]
    assert reason.reason_id == "counterexample_analysis_safety_unproven"
    assert "function1:return_width_observation_blocked" in reason.evidence_refs


def test_monolithic_reason_with_binding_only_completes_with_matching_bound_proof():
    """Issue #39: the monolithic self-recorded proof carries the witness binding and
    the safety-receipt digest; a proof for another witness does not complete it."""
    from scripts.function_tracer_pcode.proof.strategies.monolithic import MonolithicStrategy
    strategy = MonolithicStrategy(echo_input_correspondence(Mock()), Mock(), debug=False)
    analysis1, analysis2 = _analysis("f"), _analysis("f")
    binding = _binding(pair=("monolithic", "region:0"))
    reason = strategy._make_sat_unsafety_unknown_reason(
        ("counterexample_replay_missing",), analysis1, analysis2,
        case1=None, case2=None, pair_id="monolithic", stage="S_MONOLITHIC_FALLBACK",
        counterexample_binding=binding,
    )
    model = {"x_1": 0, "x_2": 0}
    with comparison_of(analysis1, analysis2):
        strategy._record_completed_sat_counterexample_replay_proof(
            reason, analysis1, analysis2, counterexample_raw=model, fixed_model_assertion_count=2,
            replay_source="monolithic-counterexample-safety-receipt:" + "r" * 64,
            evidence_binding=binding, execution_receipt_digest="r" * 64,
        )
        assert strategy._sat_unsafety_resolution_proof_is_complete(
            reason, analysis1, analysis2, current_counterexample_raw=model,
            expected_binding=binding, expected_execution_receipt_digest="r" * 64,
        ) is True
        assert strategy._sat_unsafety_resolution_proof_is_complete(
            reason, analysis1, analysis2, current_counterexample_raw=model,
            expected_binding=_binding(pair=("monolithic", "region:1")), expected_execution_receipt_digest="r" * 64,
        ) is False
        assert strategy._sat_unsafety_resolution_proof_is_complete(
            reason, analysis1, analysis2, current_counterexample_raw=model,
            expected_binding=binding, expected_execution_receipt_digest="s" * 64,
        ) is False


def _open_formula_analysis(name, delta):
    x = Expression.parameter("x", 0, data_type="int", size=4)
    return raw_function_analysis(
        function_name=name, entry_point="0x1000",
        parameters=[{"name": "x", "index": 0, "size": 4, "data_type": "int"}],
        returns=[ReturnInfo("0x1010", Expression.binary_op("INT_ADD", x, Expression.constant(delta, size=4)), [])],
        return_type="int",
    )


def _run_monolithic_with_pending_unsafety(prior_evidence=None, *, disable_self_record=False):
    """Drive MonolithicStrategy.check() through the checker (dispatch frame, typed
    evidence, safety receipt) with an analysis-level unsafety obligation pending."""
    from scripts.function_tracer_pcode.checker.checker import EquivalenceChecker

    checker = EquivalenceChecker(strategy="monolithic", timeout=5, monolithic_timeout=5)
    strategy = checker.monolithic_strategy
    strategy._collect_decisive_sat_unsafety_reasons = lambda a1, a2: ["function1:incomplete_control_flow"]
    if disable_self_record:
        strategy._record_completed_sat_counterexample_replay_proof = lambda *a, **k: None
    analysis1, analysis2 = _open_formula_analysis("left", 7), _open_formula_analysis("right", 8)
    if prior_evidence is not None:
        analysis1.completed_recovery_proof_evidence = tuple(prior_evidence)
    result = checker.check(analysis1, analysis2)
    evidence = [e for e in (analysis1.completed_recovery_proof_evidence or ()) if isinstance(e, dict)]
    return result, evidence


def test_monolithic_prior_proof_with_same_binding_but_other_receipt_does_not_complete():
    """Issue #39 regression: a prior proof whose formula/model/premise/pair match the
    current witness but whose receipt digest differs must not make the SAT decisive."""
    import copy

    first, recorded = _run_monolithic_with_pending_unsafety()
    assert first.is_equivalent is False
    assert len(recorded) == 1
    replay = recorded[0]["proof_content"]["counterexample_replay"]
    assert replay["proof_source" if "proof_source" in replay else "replay_source"].startswith(
        "monolithic-counterexample-safety-receipt:"
    )
    assert len(replay["solver_execution_receipt_digest"]) == 64
    assert replay["pair_key"] == ("monolithic", "0:0") or list(replay["pair_key"]) == ["monolithic", "0:0"]

    # Same witness, same receipt: the prior proof completes this execution's obligation.
    same, _ = _run_monolithic_with_pending_unsafety(recorded, disable_self_record=True)
    assert same.is_equivalent is False

    # Same formula/model/premise/pair, different receipt: fail closed.
    other_receipt = copy.deepcopy(recorded)
    other_receipt[0]["proof_content"]["counterexample_replay"]["solver_execution_receipt_digest"] = "f" * 64
    rejected, _ = _run_monolithic_with_pending_unsafety(other_receipt, disable_self_record=True)
    assert rejected.is_equivalent is None
    assert rejected.counterexample_raw is None
    assert [r.reason_id for r in rejected.unknown_reasons] == ["counterexample_analysis_safety_unproven"]


def test_monolithic_without_this_executions_receipt_accepts_no_prior_proof():
    """Direct strategy use has no dispatch frame and therefore no safety receipt: even a
    fully matching prior proof cannot complete the obligation (fail-closed)."""
    from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
    from scripts.function_tracer_pcode.proof.strategies.monolithic import MonolithicStrategy
    from scripts.function_tracer_pcode.smt import ParallelSolverRunner

    _, recorded = _run_monolithic_with_pending_unsafety()
    strategy = MonolithicStrategy(FormulaBuilder(), ParallelSolverRunner(timeout=5))
    strategy._collect_decisive_sat_unsafety_reasons = lambda a1, a2: ["function1:incomplete_control_flow"]
    analysis1, analysis2 = _open_formula_analysis("left", 7), _open_formula_analysis("right", 8)
    analysis1.completed_recovery_proof_evidence = tuple(recorded)

    result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is None
    assert result.counterexample_raw is None
    # Both obligations (analysis unsafety, bound replay) stay open without a receipt.
    assert {r.reason_id for r in result.unknown_reasons} == {
        "counterexample_analysis_safety_unproven",
        "counterexample_replay_unproven",
    }

from scripts.function_tracer_pcode.tests.unit._sat_decisiveness_fixtures import *

def test_monolithic_strategy_does_not_accept_unsat_with_deferred_call_argument_inconclusive():
    class _UnsatSolverRunner:
        def __init__(self):
            self.timeout = 5

        def run_parallel(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

        def run_sequential(self, _query: str):
            return ParallelResult(results=[SolverResult("fake", SolverStatus.UNSAT)])

    x = Expression.parameter("x", 0, size=4)
    pcode_ref = PcodeOpRef(address_offset=0x3010, seq_time=1, seq_order=0, mnemonic="CALL")
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
    analysis1 = FunctionReturnAnalysis(
        function_name="func1",
        entry_point="0x1",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x1", value=x, conditions=[])],
        return_type="int",
    )
    analysis1.deferred_calls = {deferred.deferred_call_ref.stable_key(): deferred}
    analysis2 = FunctionReturnAnalysis(
        function_name="func2",
        entry_point="0x2",
        parameters=[_param("x")],
        returns=[ReturnInfo(address="0x2", value=x, conditions=[])],
        return_type="int",
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

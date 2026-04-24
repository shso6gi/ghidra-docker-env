# -*- coding: utf-8 -*-

import re
from unittest.mock import Mock
from unittest.mock import patch

from scripts.function_tracer_pcode.analysis.condition import ConditionSimplifier
from scripts.function_tracer_pcode.analysis.phi_resolver import ExpandedBranch, PhiHandler
from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.equivalence.formula.types import ParameterInfo
from scripts.function_tracer_pcode.model import (
    AddressValueRef,
    COUNTED_LOOP_SUM_OPCODE,
    Condition,
    CountedLoopSummaryRef,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    LocationBaseRef,
    READONLY_SUM_OPCODE,
    PTRADD_OPCODE,
    PTRSUB_OPCODE,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReturnInfo,
)
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.model.render_smt import (
    collect_intrinsic_smt_declarations,
    expression_contains_unsupported_smt_ops,
    expression_to_smt,
)
from scripts.function_tracer_pcode.transform.expander import ExpandedValue, ExpressionExpander


def _param(name: str, size: int = 8) -> Expression:
    return Expression.parameter(name, size=size)


def _const(value: int, size: int = 8) -> Expression:
    return Expression.constant(value, size=size)


def _counted_loop_sum_value(*, signed_loop: bool, data_type: str = "int") -> Expression:
    return Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), Expression.parameter("param_1", size=4, data_type=data_type)],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=signed_loop,
            residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )


class _UnsatProofRunner:
    def __init__(self):
        self.queries = []

    def run_sequential(self, query, timeout=None):
        self.queries.append(query)
        return ParallelResult(
            results=[
                SolverResult(
                    solver_name="proof",
                    status=SolverStatus.UNSAT,
                    elapsed_time=0.0,
                )
            ],
            first_definitive=SolverResult(
                solver_name="proof",
                status=SolverStatus.UNSAT,
                elapsed_time=0.0,
            ),
            is_equivalent=True,
        )

    def run_parallel(self, query):
        raise AssertionError("partition proof should not need normal pairwise solving")


class _FirstSatProofRunner(_UnsatProofRunner):
    def run_sequential(self, query, timeout=None):
        self.queries.append(query)
        if len(self.queries) == 1:
            return ParallelResult(
                results=[
                    SolverResult(
                        solver_name="proof",
                        status=SolverStatus.SAT,
                        elapsed_time=0.0,
                        model={},
                    )
                ],
                first_definitive=SolverResult(
                    solver_name="proof",
                    status=SolverStatus.SAT,
                    elapsed_time=0.0,
                    model={},
                ),
                is_equivalent=False,
            )
        return super().run_sequential(query, timeout=timeout)


def test_expression_to_smt_lowers_ptradd_intrinsic_without_uninterpreted_symbol():
    expr = Expression.intrinsic(
        "PTRADD",
        [_param("base"), _const(1), _const(8)],
        size=8,
        opcode=PTRADD_OPCODE,
    )

    smt = expression_to_smt(expr)

    assert expression_contains_unsupported_smt_ops(expr) is False
    assert smt == "(bvadd base (bvmul (_ bv1 64) (_ bv8 64)))"
    assert "PTRADD" not in smt


def test_pairwise_supported_intrinsic_is_not_marked_unresolved():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    expr = Expression.intrinsic(
        "PTRADD",
        [_param("base"), _const(2), _const(4)],
        size=8,
        opcode=PTRADD_OPCODE,
    )

    assert strategy._expression_contains_unresolved(expr) is False
    assert strategy._expression_contains_unresolved(Expression.call("callee", [_param("base")])) is True


def test_expression_to_smt_lowers_readonly_sum_as_declared_object_centric_function():
    expr = Expression.intrinsic(
        "READONLY_SUM",
        [_param("base"), Expression.parameter("count", size=4, data_type="int")],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="readonly_sum",
            pointer_base_ref=LocationBaseRef.parameter("base", index=0),
            count_parameter_name="count",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
        ),
        opcode=READONLY_SUM_OPCODE,
    )

    smt = expression_to_smt(expr)
    declarations = collect_intrinsic_smt_declarations(expr)
    declared_name = re.search(r"\(declare-fun ([^ ]+)", declarations[0]).group(1)

    assert expression_contains_unsupported_smt_ops(expr) is False
    assert smt.startswith(f"({declared_name} ")
    assert declared_name.startswith("rt_readonly_sum_")
    assert declarations == [
        f"(declare-fun {declared_name} ((_ BitVec 64) (_ BitVec 32)) (_ BitVec 32))"
    ]


def test_counted_loop_sum_lowers_to_exact_smt_without_uninterpreted_symbol():
    left = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", size=4, data_type="int")],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )

    smt = expression_to_smt(left)

    assert collect_intrinsic_smt_declarations(left) == []
    assert "rt_counted_loop_sum_" not in smt
    assert "(ite " in smt
    assert "bvlshr" in smt


def test_pairwise_shortcuts_counted_loop_runtime_refs_with_matching_signedness():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", size=4, data_type="int")],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    right_expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", size=4, data_type="int")],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    left_case = ReturnCase(0, [], left_expr, ReturnInfo("left", left_expr))
    right_case = ReturnCase(0, [], right_expr, ReturnInfo("right", right_expr))

    assert strategy._cases_have_equivalent_runtime_reductions(left_case, right_case) is True


def test_pairwise_does_not_shortcut_counted_loop_runtime_refs_when_signedness_differs():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", size=4, data_type="int")],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    right_expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", size=4, data_type="uint")],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=False,
            residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    left_case = ReturnCase(0, [], left_expr, ReturnInfo("left", left_expr))
    right_case = ReturnCase(0, [], right_expr, ReturnInfo("right", right_expr))

    assert strategy._cases_have_equivalent_runtime_reductions(left_case, right_case) is False


def test_pairwise_shortcuts_counted_loop_runtime_refs_when_signedness_differs_but_pair_guards_prove_equivalent():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", size=4, data_type="int")],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    right_expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", size=4, data_type="uint")],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=False,
            residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    left_case = ReturnCase(
        0,
        [Condition(Expression.binary_op("INT_SLESS", _const(0, size=4), _param("count", size=4)), False)],
        left_expr,
        ReturnInfo("left", left_expr),
        parameters=[{"name": "count", "size": 4, "index": 0, "data_type": "int"}],
    )
    right_case = ReturnCase(
        0,
        [Condition(Expression.binary_op("INT_SLESS", _param("count", size=4), _const(1, size=4)), True)],
        right_expr,
        ReturnInfo("right", right_expr),
        parameters=[{"name": "count", "size": 4, "index": 0, "data_type": "uint"}],
    )

    assert strategy._cases_have_equivalent_runtime_reductions(left_case, right_case) is True


def test_pairwise_does_not_shortcut_counted_loop_runtime_refs_when_guards_differ():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    runtime_ref_left = CountedLoopSummaryRef(
        induction_step=1,
        result_size=4,
        signed_loop=True,
        residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
    )
    runtime_ref_right = CountedLoopSummaryRef(
        induction_step=1,
        result_size=4,
        signed_loop=False,
        residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
    )
    left_expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", size=4, data_type="int")],
        size=4,
        runtime_ref=runtime_ref_left,
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    right_expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", size=4, data_type="uint")],
        size=4,
        runtime_ref=runtime_ref_right,
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    left_case = ReturnCase(
        0,
        [Condition(Expression.binary_op("INT_NOTEQUAL", Expression.parameter("count", size=4), _const(0, size=4)), False)],
        left_expr,
        ReturnInfo("left", left_expr),
    )
    right_case = ReturnCase(
        0,
        [Condition(Expression.binary_op("INT_NOTEQUAL", Expression.parameter("count", size=4), _const(0, size=4)), False)],
        right_expr,
        ReturnInfo("right", right_expr),
    )

    assert strategy._cases_have_equivalent_runtime_reductions(left_case, right_case) is False


def test_pairwise_does_not_shortcut_intrinsics_without_explicit_runtime_ref_contract():
    class _AdHocRuntimeRef:
        def stable_key(self):
            return ("adhoc", 1)

        def semantic_key(self):
            return ("adhoc", 1)

    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", size=4)],
        size=4,
        runtime_ref=_AdHocRuntimeRef(),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    right_expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", size=4)],
        size=4,
        runtime_ref=_AdHocRuntimeRef(),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    left_case = ReturnCase(0, [], left_expr, ReturnInfo("left", left_expr))
    right_case = ReturnCase(0, [], right_expr, ReturnInfo("right", right_expr))

    assert strategy._cases_have_equivalent_runtime_reductions(left_case, right_case) is False


def test_pairwise_shortcuts_equivalent_counted_loop_partition_without_solver():
    proof_runner = _UnsatProofRunner()
    strategy = PairwiseStrategy(Mock(), proof_runner, debug=False)
    strategy.formula_builder.build_base_context.return_value = {
        "header_lines": [
            "(declare-const param_1_1 (_ BitVec 32))",
            "(declare-const param_1_2 (_ BitVec 32))",
            "(assert (= param_1_1 param_1_2))",
        ],
        "params1": [ParameterInfo("param_1", "param_1_1", 32, 0)],
        "params2": [ParameterInfo("param_1", "param_1_2", 32, 0)],
        "extra_vars1": [],
        "extra_vars2": [],
        "constrained_fragments": [],
        "return_size1": 32,
        "return_size2": 32,
    }

    analysis1 = FunctionReturnAnalysis(
        function_name="left",
        entry_point="0x1000",
        parameters=[{"name": "param_1", "data_type": "int", "size": 4, "index": 0, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x1001",
                value=_const(0, size=4),
                conditions=[Condition(Expression.binary_op("INT_SLESSEQUAL", _param("param_1", size=4), _const(0, size=4)), False)],
            ),
            ReturnInfo(
                address="0x1002",
                value=_counted_loop_sum_value(signed_loop=True, data_type="int"),
                conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0, size=4), _param("param_1", size=4)), False)],
            ),
        ],
        return_type="int",
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="right",
        entry_point="0x2000",
        parameters=[{"name": "param_1", "data_type": "int", "size": 4, "index": 0, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x2001",
                value=_counted_loop_sum_value(signed_loop=True, data_type="int"),
                conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0, size=4), _param("param_1", size=4)), False)],
            ),
            ReturnInfo(
                address="0x2002",
                value=_const(0, size=4),
                conditions=[Condition(Expression.binary_op("INT_SLESS", _const(0, size=4), _param("param_1", size=4)), True)],
            ),
        ],
        return_type="int",
    )

    with patch.object(strategy, "_collect_return_coverage_unsafety_reasons", return_value=[]):
        result = strategy.check(analysis1, analysis2)

    assert result.is_equivalent is True
    assert result.total_pairs == 4
    assert result.unsat_pairs == 4
    assert result.unknown_pairs == 0
    assert proof_runner.queries


def test_partition_shortcut_rejects_unsafe_analysis_inputs():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    base_ctx = {
        "header_lines": [],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
    }
    left_case = ReturnCase(0, [], _counted_loop_sum_value(signed_loop=True), ReturnInfo("left", _counted_loop_sum_value(signed_loop=True)))
    right_case = ReturnCase(0, [], _counted_loop_sum_value(signed_loop=False, data_type="uint"), ReturnInfo("right", _counted_loop_sum_value(signed_loop=False, data_type="uint")))

    assert strategy._cases_form_equivalent_partition(
        [left_case],
        [right_case],
        base_ctx=base_ctx,
        render_fn1=None,
        render_fn2=None,
        sat_unsafety_reasons=["function1:return_coverage_gap"],
    ) is False


def test_partition_shortcut_requires_smt_proven_case_disjointness():
    strategy = PairwiseStrategy(Mock(), _FirstSatProofRunner(), debug=False)
    base_ctx = {
        "header_lines": ["(declare-const param_1 (_ BitVec 32))"],
        "params1": [],
        "params2": [],
        "extra_vars1": [],
        "extra_vars2": [],
        "return_size1": 32,
        "return_size2": 32,
    }
    param = _param("param_1", size=4)
    zero = _const(0, size=4)
    ten = _const(10, size=4)
    lower_region = Condition(Expression.binary_op("INT_SLESSEQUAL", zero, param), False)
    upper_region = Condition(Expression.binary_op("INT_SLESSEQUAL", param, ten), False)
    left_cases = [
        ReturnCase(0, [lower_region], _const(1, size=4), ReturnInfo("left0", _const(1, size=4))),
        ReturnCase(1, [upper_region], _const(2, size=4), ReturnInfo("left1", _const(2, size=4))),
    ]
    right_cases = [
        ReturnCase(0, [lower_region], _const(1, size=4), ReturnInfo("right0", _const(1, size=4))),
        ReturnCase(1, [upper_region], _const(2, size=4), ReturnInfo("right1", _const(2, size=4))),
    ]

    assert strategy._cases_form_equivalent_partition(
        left_cases,
        right_cases,
        base_ctx=base_ctx,
        render_fn1=None,
        render_fn2=None,
        sat_unsafety_reasons=[],
    ) is False


def test_readonly_sum_smt_declarations_distinguish_different_loop_shapes():
    left = Expression.intrinsic(
        "READONLY_SUM",
        [_param("base"), Expression.parameter("count", size=4, data_type="int")],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="readonly_sum",
            pointer_base_ref=LocationBaseRef.parameter("base", index=0),
            count_parameter_name="count",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    right = Expression.intrinsic(
        "READONLY_SUM",
        [_param("base"), Expression.parameter("count", size=4, data_type="int")],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="readonly_sum",
            pointer_base_ref=LocationBaseRef.parameter("base", index=0),
            count_parameter_name="count",
            count_parameter_index=1,
            stride=8,
            element_size=8,
            result_size=4,
            signed_counter=True,
        ),
        opcode=READONLY_SUM_OPCODE,
    )

    left_name = re.search(r"\(declare-fun ([^ ]+)", collect_intrinsic_smt_declarations(left)[0]).group(1)
    right_name = re.search(r"\(declare-fun ([^ ]+)", collect_intrinsic_smt_declarations(right)[0]).group(1)

    assert left_name != right_name


def test_readonly_sum_smt_declarations_share_semantic_identity_when_witness_prefix_matches():
    shared_prefix = (
        ReadonlyReductionWitness(
            exact_count=1,
            terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
        ),
        ReadonlyReductionWitness(
            exact_count=2,
            terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ),
        ),
        ReadonlyReductionWitness(
            exact_count=3,
            terms=(
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
            ),
        ),
    )
    left = Expression.intrinsic(
        "READONLY_SUM",
        [_param("base"), Expression.parameter("count", size=4, data_type="int")],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="readonly_sum",
            pointer_base_ref=LocationBaseRef.parameter("base", index=0),
            count_parameter_name="count",
            count_parameter_index=1,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
            semantic_witnesses=shared_prefix,
        ),
        opcode=READONLY_SUM_OPCODE,
    )
    right = Expression.intrinsic(
        "READONLY_SUM",
        [_param("base"), Expression.parameter("count", size=4, data_type="uint")],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="readonly_sum",
            pointer_base_ref=LocationBaseRef.parameter("base", index=0),
            count_parameter_name="count",
            count_parameter_index=1,
            stride=16,
            element_size=8,
            result_size=4,
            signed_counter=False,
            semantic_witnesses=shared_prefix,
        ),
        opcode=READONLY_SUM_OPCODE,
    )

    left_name = re.search(r"\(declare-fun ([^ ]+)", collect_intrinsic_smt_declarations(left)[0]).group(1)
    right_name = re.search(r"\(declare-fun ([^ ]+)", collect_intrinsic_smt_declarations(right)[0]).group(1)

    assert left_name == right_name


def test_expander_combines_three_input_ptradd_as_intrinsic(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)

    monkeypatch.setattr(
        ConditionSimplifier,
        "is_contradiction",
        classmethod(lambda cls, conds: False),
    )
    monkeypatch.setattr(
        ConditionSimplifier,
        "simplify_conditions",
        classmethod(lambda cls, conds: list(conds)),
    )

    result = expander._combine_input_expansions_with_conditions(
        "PTRADD",
        [
            [ExpandedValue(_param("base"), [])],
            [ExpandedValue(_const(3), [])],
            [ExpandedValue(_const(8), [])],
        ],
        [],
        depth=0,
        output_size=8,
        opcode=PTRADD_OPCODE,
    )

    assert len(result) == 1
    assert result[0].value.expr_type == ExpressionType.INTRINSIC
    assert result[0].value.opcode == PTRADD_OPCODE
    assert expression_to_smt(result[0].value) == "(bvadd base (bvmul (_ bv3 64) (_ bv8 64)))"


def test_phi_handler_combines_ptrsub_as_intrinsic_even_for_two_inputs():
    tracer = type("Tracer", (), {"debug": False})()
    tracker = Mock()
    handler = PhiHandler(tracer, tracker)

    result = handler._combine_expansions(
        "PTRSUB",
        [
            [ExpandedBranch([], _param("base"))],
            [ExpandedBranch([], _const(0x20))],
        ],
        [],
        opcode=PTRSUB_OPCODE,
        output_size=8,
    )

    assert len(result) == 1
    assert result[0].value.expr_type == ExpressionType.INTRINSIC
    assert result[0].value.opcode == PTRSUB_OPCODE
    assert expression_to_smt(result[0].value) == "(bvadd base (_ bv32 64))"


def test_tracer_emits_ptrsub_intrinsic_with_derived_address_runtime_ref():
    anchor_ref = AddressValueRef(
        address_offset=0x00112008,
        source="unit_test",
        display_hint="ptr_anchor",
        symbol_name="PTR_lookup_table",
        block_name=".rodata",
        is_initialized=True,
        can_read=True,
        can_write=False,
        can_execute=False,
        is_volatile=False,
    )
    base_expr = Expression.constant(0, size=8)
    anchor_expr = Expression.constant(
        anchor_ref.address_offset,
        size=8,
        runtime_ref=anchor_ref,
    )

    class _FakeOutput:
        def getSize(self):
            return 8

    class _FakePcodeOp:
        def __init__(self, inputs):
            self._inputs = inputs

        def getMnemonic(self):
            return "PTRSUB"

        def getNumInputs(self):
            return len(self._inputs)

        def getInput(self, index):
            return self._inputs[index]

        def getOutput(self):
            return _FakeOutput()

    input_base = object()
    input_offset = object()
    tracer = object.__new__(PcodeTracer)
    tracer._debug_available = lambda: False
    tracer.trace_varnode = lambda varnode, depth, use_cache: {
        input_base: base_expr,
        input_offset: anchor_expr,
    }[varnode]
    tracer._derive_pointer_runtime_ref = lambda expr, display_name=None: AddressValueRef(
        address_offset=0x00112008,
        source="derived_test",
        display_hint=display_name,
        symbol_name="PTR_lookup_table",
        block_name=".rodata",
        is_initialized=True,
        can_read=True,
        can_write=False,
        can_execute=False,
        is_volatile=False,
    )

    expr = PcodeTracer._trace_pcode_op_internal(
        tracer,
        _FakePcodeOp([input_base, input_offset]),
        0,
        True,
    )

    assert expr.expr_type == ExpressionType.INTRINSIC
    assert expr.opcode == PTRSUB_OPCODE
    assert expr.runtime_ref.address_offset == 0x00112008


def test_tracer_promotes_constant_varnode_to_address_object_when_ghidra_exposes_readonly_data():
    class _FakeSpace:
        def getSpaceID(self):
            return 1

        def getName(self):
            return "ram"

    class _FakeAddress:
        def __init__(self, offset):
            self._offset = offset
            self._space = _FakeSpace()

        def getOffset(self):
            return self._offset

        def getAddressSpace(self):
            return self._space

    class _FakeDefaultSpace:
        def getAddress(self, offset):
            return _FakeAddress(offset)

    class _FakeAddressFactory:
        def getDefaultAddressSpace(self):
            return _FakeDefaultSpace()

    class _FakeBlock:
        def getName(self):
            return ".rodata"

        def isInitialized(self):
            return True

        def isRead(self):
            return True

        def isWrite(self):
            return False

        def isExecute(self):
            return False

        def isVolatile(self):
            return False

    class _FakeMemory:
        def getBlock(self, _address):
            return _FakeBlock()

    class _FakeData:
        def getPrimarySymbol(self):
            return None

    class _FakeListing:
        def getDataAt(self, _address):
            return _FakeData()

        def getDataContaining(self, _address):
            return None

    class _FakeSymbolTable:
        def getPrimarySymbol(self, _address):
            return None

    class _FakeProgram:
        def getAddressFactory(self):
            return _FakeAddressFactory()

        def getMemory(self):
            return _FakeMemory()

        def getListing(self):
            return _FakeListing()

        def getSymbolTable(self):
            return _FakeSymbolTable()

    class _FakeConstantVarnode:
        def isConstant(self):
            return True

        def getOffset(self):
            return 0x00112008

        def getSize(self):
            return 8

    tracer = object.__new__(PcodeTracer)
    tracer.program = _FakeProgram()
    tracer.debug = False
    tracer._debug_available = lambda: False

    expr = PcodeTracer._trace_varnode_internal(
        tracer,
        _FakeConstantVarnode(),
        0,
        True,
    )

    assert expr.expr_type == ExpressionType.CONSTANT
    assert isinstance(expr.runtime_ref, AddressValueRef)
    assert expr.runtime_ref.address_offset == 0x00112008
    assert expr.runtime_ref.block_name == ".rodata"

# -*- coding: utf-8 -*-

import re
from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.condition import ConditionSimplifier
from scripts.function_tracer_pcode.analysis.phi_resolver import ExpandedBranch, PhiHandler
from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.equivalence.strategies.pairwise import PairwiseStrategy
from scripts.function_tracer_pcode.equivalence.strategies import pairwise_models as pairwise_models_module
from scripts.function_tracer_pcode.equivalence.strategies.pairwise_models import ReturnCase
from scripts.function_tracer_pcode.equivalence.strategies.expression_safety import (
    ConditionBinding,
    ExpressionSafetyChecker,
)
from scripts.function_tracer_pcode.equivalence.normalize.guard_prover import prove_guard_condition
from scripts.function_tracer_pcode.model import (
    AddressValueRef,
    COUNTED_LOOP_SUM_OPCODE,
    Condition,
    CountedLoopSummaryRef,
    Expression,
    ExpressionType,
    LocationBaseRef,
    LoopSummaryRef,
    LoopTermDescriptorRef,
    READONLY_SUM_OPCODE,
    PTRADD_OPCODE,
    PTRSUB_OPCODE,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReturnInfo,
)
from scripts.function_tracer_pcode.model.render_smt import (
    collect_intrinsic_smt_declarations,
    expression_contains_unsupported_smt_ops,
    expression_to_smt,
)
from scripts.function_tracer_pcode.smt.interface import SolverStatus
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver
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
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", index=0, size=4, data_type="int")],
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


def test_counted_loop_sum_exact_smt_clamps_no_iteration_span_to_base():
    expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(7, size=4), _const(5, size=4), _const(3, size=4)],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((1, 0, 1, 0),),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )

    smt = expression_to_smt(expr)
    query = "\n".join(
        [
            "(set-logic QF_BV)",
            f"(assert (not (= {smt} (_ bv7 32))))",
            "(check-sat)",
        ]
    )

    assert "rt_counted_loop_sum_" not in smt
    assert "(ite (bvsle " in smt
    assert Z3Solver(timeout=2).check_equivalence_direct(query).status == SolverStatus.UNSAT


def test_counted_loop_sum_exact_smt_uses_unsigned_clamp_for_unsigned_loop():
    expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=8), _const((1 << 63) + 1, size=8)],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=False,
            residue_cases=((1, 0, 0, 1),),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )

    smt = expression_to_smt(expr)
    query = "\n".join(
        [
            "(set-logic QF_BV)",
            f"(assert (not (= {smt} (_ bv1 32))))",
            "(check-sat)",
        ]
    )

    assert "rt_counted_loop_sum_" not in smt
    assert "bvule" in smt
    assert Z3Solver(timeout=2).check_equivalence_direct(query).status == SolverStatus.UNSAT


def test_counted_loop_sum_exact_smt_avoids_unsigned_ceil_div_overflow():
    expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=8), _const((1 << 64) - 2, size=8)],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=3,
            result_size=4,
            signed_loop=False,
            residue_cases=((1, 0, 0, 1),),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )
    expected = ((1 << 64) // 3) & 0xFFFFFFFF

    smt = expression_to_smt(expr)
    query = "\n".join(
        [
            "(set-logic QF_BV)",
            f"(assert (not (= {smt} (_ bv{expected} 32))))",
            "(check-sat)",
        ]
    )

    assert expected == 0x55555555
    assert "bvudiv (bvsub" in smt
    assert Z3Solver(timeout=2).check_equivalence_direct(query).status == SolverStatus.UNSAT


def test_counted_loop_sum_exact_smt_uses_unsigned_distance_for_signed_residue_reachability():
    expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(1 << 63, size=8), _const(1, size=8)],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((2, 0, 0, 1),),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )

    smt = expression_to_smt(expr)
    query = "\n".join(
        [
            "(set-logic QF_BV)",
            f"(assert (not (= {smt} (_ bv1 32))))",
            "(check-sat)",
        ]
    )

    assert "rt_counted_loop_sum_" not in smt
    assert "bvsle" in smt
    assert "bvule (bvsub" in smt
    assert Z3Solver(timeout=2).check_equivalence_direct(query).status == SolverStatus.UNSAT


def test_counted_loop_sum_fallback_declares_uninterpreted_function():
    expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", index=0, size=4, data_type="int")],
        size=4,
        runtime_ref=CountedLoopSummaryRef(
            induction_step=1,
            result_size=4,
            signed_loop=True,
            residue_cases=((3, 0, 1, 0), (3, 1, -1, 0), (3, 2, 2, 0)),
        ),
        opcode=COUNTED_LOOP_SUM_OPCODE,
    )

    smt = expression_to_smt(expr)
    declarations = collect_intrinsic_smt_declarations(expr)
    declared_name = re.search(r"\(declare-fun ([^ ]+)", declarations[0]).group(1)

    assert smt.startswith(f"({declared_name} ")
    assert declarations == [
        f"(declare-fun {declared_name} ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))"
    ]


def test_pairwise_shortcuts_counted_loop_runtime_refs_with_matching_signedness():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", index=0, size=4, data_type="int")],
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


def test_pairwise_intrinsic_auxiliary_query_refuses_unresolved_variable_symbol():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    count = Expression.parameter("count", index=0, size=4, data_type="int")
    aux_var = Expression.variable("__loop_acc", size=4)
    condition = Condition(Expression.binary_op("INT_SLESS", _const(0, size=4), count), False)
    left = Expression.binary_op("INT_ADD", aux_var, count)
    right = Expression.binary_op("INT_ADD", aux_var, count)

    query = strategy._build_intrinsic_equivalence_query(
        left,
        right,
        [condition],
        [
            {"name": "count", "index": 0, "size": 4, "data_type": "int"},
            {"name": "__loop_acc", "index": -1, "size": 4},
        ],
    )

    assert query is None


def test_pairwise_auxiliary_query_uses_fp_logic_for_float_guards():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    a = Expression.parameter("a", index=0, data_type="double", size=8)
    b = Expression.parameter("b", index=1, data_type="double", size=8)
    condition = Condition(Expression.binary_op("FLOAT_LESS", a, b), False)

    query = strategy._build_intrinsic_equivalence_query(
        a,
        a,
        [condition],
        [
            {"name": "a", "index": 0, "size": 8, "data_type": "double", "identity": ("parameter_index", 0), "aux_name": "aux_param_0", "aux_index": 0},
            {"name": "b", "index": 1, "size": 8, "data_type": "double", "identity": ("parameter_index", 1), "aux_name": "aux_param_1", "aux_index": 1},
        ],
    )

    assert query is not None
    assert "(set-logic QF_FPBV)" in query
    assert "fp.lt" in query
    assert "float_less" not in query
    assert "fp.isNaN" not in query


def test_return_case_smt_cache_is_scoped_by_renderer_float_mode():
    a = Expression.parameter("a", index=0, data_type="double", size=8)
    b = Expression.parameter("b", index=1, data_type="double", size=8)
    comparison = Expression.binary_op("FLOAT_LESS", a, b)
    condition = Condition(comparison, False)
    case = ReturnCase(0, [condition], comparison, ReturnInfo("float_case", comparison))

    uf_renderer = lambda node: node.to_smt()
    fp_renderer = lambda node: node.to_smt(float_mode="fp")

    uf_conditions = case.get_conditions_smt(uf_renderer)
    fp_conditions = case.get_conditions_smt(fp_renderer)
    uf_value = case.get_value_smt(uf_renderer)
    fp_value = case.get_value_smt(fp_renderer)

    assert "float_less" in uf_conditions[0]
    assert "fp.lt" in fp_conditions[0]
    assert "float_less" not in fp_conditions[0]
    assert "float_less" in uf_value
    assert "fp.lt" in fp_value
    assert "float_less" not in fp_value


def test_return_case_fallback_rendering_keeps_fp_mode_for_object_renderers():
    a = Expression.parameter("a", index=0, data_type="double", size=8)
    b = Expression.parameter("b", index=1, data_type="double", size=8)
    comparison = Expression.binary_op("FLOAT_LESS", a, b)
    condition = Condition(comparison, False)
    case = ReturnCase(0, [condition], comparison, ReturnInfo("float_case", comparison))

    def object_renderer(node):
        return node

    conditions = case.get_conditions_smt(object_renderer)
    value = case.get_value_smt(object_renderer)

    assert "fp.lt" in conditions[0]
    assert "float_less" not in conditions[0]
    assert "fp.lt" in value
    assert "float_less" not in value


def test_return_case_typeerror_fallback_uses_fp_mode_string_input():
    a = Expression.parameter("a", index=0, data_type="double", size=8)
    b = Expression.parameter("b", index=1, data_type="double", size=8)
    comparison = Expression.binary_op("FLOAT_LESS", a, b)
    condition = Condition(comparison, False)
    case = ReturnCase(0, [condition], comparison, ReturnInfo("float_case", comparison))

    def string_only_renderer(node):
        if not isinstance(node, str):
            raise TypeError("string input only")
        return node

    conditions = case.get_conditions_smt(string_only_renderer)
    value = case.get_value_smt(string_only_renderer)

    assert "fp.lt" in conditions[0]
    assert "float_less" not in conditions[0]
    assert "fp.lt" in value
    assert "float_less" not in value


def test_return_case_update_conditions_clears_condition_dependent_value_cache(monkeypatch):
    value = Expression.parameter("post", index=0, size=4)
    first_condition = Condition(Expression.binary_op("INT_EQUAL", _param("x", size=4), _const(0, size=4)))
    second_condition = Condition(Expression.binary_op("INT_EQUAL", _param("x", size=4), _const(1, size=4)))
    case = ReturnCase(
        0,
        [first_condition],
        value,
        ReturnInfo("post_case", value),
        effect_summary=Mock(effects=[object()]),
    )

    def fake_lower(_value_expr, conditions, _effects, _parameters):
        return Expression.constant(len(conditions), size=4)

    monkeypatch.setattr(
        pairwise_models_module,
        "lower_post_state_expression_for_smt_if_needed",
        fake_lower,
    )

    before = case.get_value_smt(lambda expr: expr.to_smt(float_mode="fp"))
    case.update_conditions([first_condition, second_condition])
    after = case.get_value_smt(lambda expr: expr.to_smt(float_mode="fp"))

    assert before == "(_ bv1 32)"
    assert after == "(_ bv2 32)"


def test_expression_safety_reachability_query_uses_base_fp_logic():
    captured = {}

    class FakeRunner:
        def run_sequential(self, query, timeout=None):
            captured["query"] = query
            return Mock(is_equivalent=False, results=[])

    a = Expression.parameter("a", index=0, data_type="double", size=8)
    b = Expression.parameter("b", index=1, data_type="double", size=8)
    condition = Condition(Expression.binary_op("FLOAT_LESS", a, b), False)
    checker = ExpressionSafetyChecker(
        solver_runner=FakeRunner(),
        debug_print=lambda *_args, **_kwargs: None,
        per_query_timeout=1,
        base_ctx={
            "smt_logic": "QF_FPBV",
            "header_lines": [
                "(declare-const a (_ BitVec 64))",
                "(declare-const b (_ BitVec 64))",
            ],
        },
    )

    assert checker._query_bindings_feasibility(
        [ConditionBinding(condition, None)],
        query_label="fp-guard",
    ) is True

    assert "(set-logic QF_FPBV)" in captured["query"]
    assert "fp.lt" in captured["query"]
    assert "float_less" not in captured["query"]


def test_guard_prover_uses_base_fp_logic_for_float_guards():
    captured = {}

    class FakeRunner:
        def run_sequential(self, query, timeout=None):
            captured["query"] = query
            return Mock(is_equivalent=True, results=[])

    proven, error = prove_guard_condition(
        {
            "smt_logic": "QF_FPBV",
            "header_lines": [
                "(declare-const a (_ BitVec 64))",
                "(declare-const b (_ BitVec 64))",
            ],
        },
        [],
        [],
        "(fp.lt ((_ to_fp 11 53) a) ((_ to_fp 11 53) b))",
        FakeRunner(),
    )

    assert proven is True
    assert error == ""
    assert "(set-logic QF_FPBV)" in captured["query"]
    assert "fp.lt" in captured["query"]


def test_pairwise_does_not_shortcut_counted_loop_runtime_refs_when_signedness_differs():
    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    left_expr = Expression.intrinsic(
        "COUNTED_LOOP_SUM",
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", index=0, size=4, data_type="int")],
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
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", index=0, size=4, data_type="uint")],
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
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", index=0, size=4, data_type="int")],
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
        [_const(0, size=4), _const(0, size=4), Expression.parameter("count", index=0, size=4, data_type="uint")],
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
        [
            Condition(
                Expression.binary_op(
                    "INT_SLESS",
                    _const(0, size=4),
                    Expression.parameter("count", index=0, size=4, data_type="int"),
                ),
                False,
            )
        ],
        left_expr,
        ReturnInfo("left", left_expr),
        parameters=[{"name": "count", "size": 4, "index": 0, "data_type": "int"}],
    )
    right_case = ReturnCase(
        0,
        [
            Condition(
                Expression.binary_op(
                    "INT_SLESS",
                    Expression.parameter("count", index=0, size=4, data_type="uint"),
                    _const(1, size=4),
                ),
                True,
            )
        ],
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


def test_readonly_sum_smt_declarations_distinguish_constant_bias():
    def _expr(bias: int) -> Expression:
        summary = LoopSummaryRef(
            start_expr=Expression.constant(0, size=4),
            limit_expr=Expression.parameter("count", size=4, data_type="int"),
            step_expr=Expression.constant(1, size=4),
            term_descriptor=LoopTermDescriptorRef(
                kind="memory_load",
                reduction_kind="sum",
                location_base_ref=LocationBaseRef.parameter("base", index=0),
                start_offset=0,
                stride=4,
                element_size=4,
                result_size=4,
            ),
            loop_var_unit="element_index",
            constant_bias=bias,
        )
        return Expression.intrinsic(
            "READONLY_SUM",
            [_param("base"), Expression.parameter("count", size=4, data_type="int")],
            size=4,
            runtime_ref=ReadonlyReductionRef(
                reduction_kind="memory_sum",
                pointer_base_ref=LocationBaseRef.parameter("base", index=0),
                count_parameter_name="count",
                count_parameter_index=1,
                stride=4,
                element_size=4,
                result_size=4,
                signed_counter=True,
                loop_summary=summary,
                constant_bias=bias,
            ),
            opcode=READONLY_SUM_OPCODE,
        )

    unbiased = _expr(0)
    biased = _expr(5)
    same_bias = _expr(5)

    unbiased_name = re.search(r"\(declare-fun ([^ ]+)", collect_intrinsic_smt_declarations(unbiased)[0]).group(1)
    biased_name = re.search(r"\(declare-fun ([^ ]+)", collect_intrinsic_smt_declarations(biased)[0]).group(1)
    same_bias_name = re.search(r"\(declare-fun ([^ ]+)", collect_intrinsic_smt_declarations(same_bias)[0]).group(1)

    assert biased_name != unbiased_name
    assert same_bias_name == biased_name


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


def test_readonly_sum_smt_declarations_share_method_b_seed_compensated_identity():
    def _loop_summary(start: int, seed_terms=()):
        return LoopSummaryRef(
            start_expr=Expression.constant(start, size=4),
            limit_expr=Expression.parameter("count", index=1, size=4, data_type="int"),
            step_expr=Expression.constant(1, size=4),
            term_descriptor=LoopTermDescriptorRef(
                kind="memory_load",
                reduction_kind="sum",
                location_base_ref=LocationBaseRef.parameter("base", index=0),
                start_offset=0,
                stride=4,
                element_size=4,
                result_size=4,
            ),
            seed_terms=tuple(seed_terms),
            loop_var_unit="element_index",
        )

    def _expr(summary):
        return Expression.intrinsic(
            "READONLY_SUM",
            [
                Expression.parameter("base", index=0, size=8, data_type="int *"),
                Expression.parameter("count", index=1, size=4, data_type="int"),
            ],
            size=4,
            runtime_ref=ReadonlyReductionRef(
                reduction_kind="memory_sum",
                pointer_base_ref=LocationBaseRef.parameter("base", index=0),
                count_parameter_name="count",
                count_parameter_index=1,
                stride=4,
                element_size=4,
                result_size=4,
                signed_counter=True,
                loop_summary=summary,
            ),
            opcode=READONLY_SUM_OPCODE,
        )

    left = _expr(_loop_summary(0))
    right = _expr(
        _loop_summary(
            3,
            (
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
                ReadonlyReductionTermRef(byte_offset=8, access_size=4),
            ),
        )
    )
    mismatch = _expr(
        _loop_summary(
            3,
            (
                ReadonlyReductionTermRef(byte_offset=0, access_size=4),
                ReadonlyReductionTermRef(byte_offset=4, access_size=4),
            ),
        )
    )

    left_name = re.search(r"\(declare-fun ([^ ]+)", collect_intrinsic_smt_declarations(left)[0]).group(1)
    right_name = re.search(r"\(declare-fun ([^ ]+)", collect_intrinsic_smt_declarations(right)[0]).group(1)
    mismatch_name = re.search(
        r"\(declare-fun ([^ ]+)",
        collect_intrinsic_smt_declarations(mismatch)[0],
    ).group(1)

    assert left_name == right_name
    assert left_name != mismatch_name


def test_readonly_sum_smt_identity_does_not_fallback_to_coarse_stable_key_for_unkeyable_loop_summary():
    def _expr_with_unkeyable_summary():
        loop_summary = LoopSummaryRef(
            start_expr=object(),
            limit_expr=Expression.parameter("count", size=4, data_type="int"),
            step_expr=1,
            term_descriptor=LoopTermDescriptorRef(kind="memory_load", stride=4, element_size=4),
        )
        return Expression.intrinsic(
            "READONLY_SUM",
            [_param("base"), Expression.parameter("count", size=4, data_type="int")],
            size=4,
            runtime_ref=ReadonlyReductionRef(
                reduction_kind="memory_sum",
                pointer_base_ref=LocationBaseRef.parameter("base", index=0),
                count_parameter_name="count",
                count_parameter_index=1,
                stride=4,
                element_size=4,
                result_size=4,
                signed_counter=True,
                loop_summary=loop_summary,
            ),
            opcode=READONLY_SUM_OPCODE,
        )

    left = _expr_with_unkeyable_summary()
    right = _expr_with_unkeyable_summary()

    assert left.runtime_ref.stable_key() == right.runtime_ref.stable_key()
    assert left.runtime_ref.pairwise_exact_key() is None
    left_name = re.search(r"\(declare-fun ([^ ]+)", collect_intrinsic_smt_declarations(left)[0]).group(1)
    right_name = re.search(r"\(declare-fun ([^ ]+)", collect_intrinsic_smt_declarations(right)[0]).group(1)

    assert left_name != right_name


def test_counted_loop_smt_identity_does_not_fallback_to_coarse_stable_key_for_unkeyable_loop_summary():
    def _expr_with_unkeyable_summary():
        loop_summary = LoopSummaryRef(
            start_expr=object(),
            limit_expr=Expression.parameter("limit", size=4, data_type="int"),
            step_expr=1,
            term_descriptor=LoopTermDescriptorRef(
                kind="affine_residue",
                residue_cases=((3, 0, 1, 0),),
            ),
        )
        return Expression.intrinsic(
            "COUNTED_LOOP_SUM",
            [_const(0, size=4), _const(0, size=4), Expression.parameter("limit", size=4, data_type="int")],
            size=4,
            runtime_ref=CountedLoopSummaryRef(
                induction_step=1,
                result_size=4,
                signed_loop=True,
                residue_cases=((3, 0, 1, 0),),
                loop_summary=loop_summary,
            ),
            opcode=COUNTED_LOOP_SUM_OPCODE,
        )

    left = _expr_with_unkeyable_summary()
    right = _expr_with_unkeyable_summary()

    assert left.runtime_ref.stable_key() == right.runtime_ref.stable_key()
    assert left.runtime_ref.pairwise_exact_key() is None
    left_name = re.search(r"\(declare-fun ([^ ]+)", collect_intrinsic_smt_declarations(left)[0]).group(1)
    right_name = re.search(r"\(declare-fun ([^ ]+)", collect_intrinsic_smt_declarations(right)[0]).group(1)

    assert left_name != right_name


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

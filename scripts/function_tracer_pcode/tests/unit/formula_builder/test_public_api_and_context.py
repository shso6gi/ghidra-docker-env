# -*- coding: utf-8 -*-
"""FormulaBuilder の公開 API・context 共有まわりのテスト。"""

from unittest.mock import patch

from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.equivalence.formula.returns import (
    _order_return_defs_by_specificity,
    compare_readonly_summary_values_by_priority,
)
from scripts.function_tracer_pcode.smt import SolverStatus
from scripts.function_tracer_pcode.smt.solvers.z3 import Z3Solver
from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier
from scripts.function_tracer_pcode.model import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    LocationBaseRef,
    LoopSideEffectProfileRef,
    LoopSummaryRef,
    LoopTermDescriptorRef,
    READONLY_SUM_OPCODE,
    ReductionAccumulatorProof,
    ReadonlyReductionRef,
    ReturnInfo,
)
from conftest import resolve_mock_data_type


def _simple_analysis(func_name: str, param_name: str, size: int = 4) -> FunctionReturnAnalysis:
    return FunctionReturnAnalysis(
        function_name=func_name,
        entry_point="0x00401000",
        parameters=[{"name": param_name, "size": size, "index": 0, "is_signed": True}],
        returns=[
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.PARAMETER, name=param_name, size=size),
            )
        ],
    )


def _double_param(name: str, index: int) -> Expression:
    return Expression.parameter(
        name,
        index=index,
        data_type="double",
        data_type_obj=resolve_mock_data_type("double"),
        size=8,
    )


def _max_with_less_analysis() -> FunctionReturnAnalysis:
    a = _double_param("a", 0)
    b = _double_param("b", 1)
    less = Expression.binary_op("FLOAT_LESS", b, a)
    return FunctionReturnAnalysis(
        function_name="max_less",
        entry_point="0x00401000",
        parameters=[
            {"name": "a", "size": 8, "index": 0, "data_type": "double", "data_type_obj": resolve_mock_data_type("double")},
            {"name": "b", "size": 8, "index": 1, "data_type": "double", "data_type_obj": resolve_mock_data_type("double")},
        ],
        returns=[
            ReturnInfo(address="0x00401000", conditions=[Condition(less, False)], value=a),
            ReturnInfo(address="0x00401004", conditions=[Condition(less, True)], value=b),
        ],
        return_type="double",
        return_type_obj=resolve_mock_data_type("double"),
    )


def _max_with_lessequal_analysis() -> FunctionReturnAnalysis:
    a = _double_param("a", 0)
    b = _double_param("b", 1)
    le = Expression.binary_op("FLOAT_LESSEQUAL", a, b)
    return FunctionReturnAnalysis(
        function_name="max_lessequal",
        entry_point="0x00402000",
        parameters=[
            {"name": "a", "size": 8, "index": 0, "data_type": "double", "data_type_obj": resolve_mock_data_type("double")},
            {"name": "b", "size": 8, "index": 1, "data_type": "double", "data_type_obj": resolve_mock_data_type("double")},
        ],
        returns=[
            ReturnInfo(address="0x00402000", conditions=[Condition(le, False)], value=b),
            ReturnInfo(address="0x00402004", conditions=[Condition(le, True)], value=a),
        ],
        return_type="double",
        return_type_obj=resolve_mock_data_type("double"),
    )


def _readonly_loop_summary_expr() -> Expression:
    base = Expression.parameter("base", index=0, data_type="int *", size=8)
    count = Expression.parameter("count", index=1, data_type="int", size=4)
    loop_summary = LoopSummaryRef(
        start_expr=Expression.constant(0, size=4),
        limit_expr=count,
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
        side_effect_profile=LoopSideEffectProfileRef(profile="pure_memory_read", memory_reads=True),
        loop_var_unit="element_index",
    )
    return Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
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


def test_formula_builder_does_not_hide_nan_only_float_difference():
    result = FormulaBuilder().build_equivalence_formula_extended(
        _max_with_less_analysis(),
        _max_with_lessequal_analysis(),
    )

    assert "(set-logic QF_FPBV)" in result.formula
    assert "fp.lt" in result.formula
    assert "fp.leq" in result.formula
    assert "fp.isNaN" not in result.formula

    solver_result = Z3Solver(timeout=2).check_equivalence_direct(result.formula)

    assert solver_result.status == SolverStatus.SAT


def test_formula_builder_selects_uf_logic_for_intrinsic_declarations():
    analysis1 = FunctionReturnAnalysis(
        function_name="sum_left",
        entry_point="0x00401000",
        parameters=[
            {"name": "base", "size": 8, "index": 0, "data_type": "int *"},
            {"name": "count", "size": 4, "index": 1, "data_type": "int"},
        ],
        returns=[ReturnInfo(address="0x00401000", conditions=[], value=_readonly_loop_summary_expr())],
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="sum_right",
        entry_point="0x00402000",
        parameters=[
            {"name": "base", "size": 8, "index": 0, "data_type": "int *"},
            {"name": "count", "size": 4, "index": 1, "data_type": "int"},
        ],
        returns=[ReturnInfo(address="0x00402000", conditions=[], value=_readonly_loop_summary_expr())],
    )

    result = FormulaBuilder().build_equivalence_formula_extended(analysis1, analysis2)

    assert "(set-logic QF_AUFBV)" in result.formula
    assert "(declare-fun" in result.formula
    assert "READONLY_SUM" in result.formula


def test_formula_builder_selects_uf_logic_for_unsupported_float_predicate_width():
    x = Expression.parameter("x", index=0, data_type="long double", size=10)
    y = Expression.parameter("y", index=1, data_type="long double", size=10)
    guard = Condition(Expression.binary_op("FLOAT_LESS", x, y))
    analysis1 = FunctionReturnAnalysis(
        function_name="float80_left",
        entry_point="0x00401000",
        parameters=[
            {"name": "x", "size": 10, "index": 0, "data_type": "long double"},
            {"name": "y", "size": 10, "index": 1, "data_type": "long double"},
        ],
        returns=[ReturnInfo(address="0x00401000", conditions=[guard], value=Expression.constant(1, size=4))],
    )
    analysis2 = FunctionReturnAnalysis(
        function_name="float80_right",
        entry_point="0x00402000",
        parameters=[
            {"name": "x", "size": 10, "index": 0, "data_type": "long double"},
            {"name": "y", "size": 10, "index": 1, "data_type": "long double"},
        ],
        returns=[ReturnInfo(address="0x00402000", conditions=[guard], value=Expression.constant(1, size=4))],
    )

    result = FormulaBuilder().build_equivalence_formula_extended(analysis1, analysis2)

    assert "(set-logic QF_UFBV)" in result.formula
    assert "(declare-fun float_less ((_ BitVec 80) (_ BitVec 80)) Bool)" in result.formula
    assert "fp.lt" not in result.formula


def _readonly_return_ordering_expr(
    *,
    base_name: str,
    count_name: str = "count",
    base_index=None,
    count_index=None,
    proof_backed: bool = False,
) -> Expression:
    base = Expression.parameter(
        base_name,
        index=int(base_index) if base_index is not None else -1,
        data_type="int *",
        size=8,
    )
    count = Expression.parameter(
        count_name,
        index=int(count_index) if count_index is not None else -1,
        data_type="int",
        size=4,
    )
    pointer_ref = LocationBaseRef.parameter(base_name, index=base_index)
    proof = None
    if proof_backed:
        proof = ReductionAccumulatorProof(
            reduction_kind="memory_sum",
            pointer_base_ref=pointer_ref,
            count_parameter_name=count_name,
            count_parameter_index=count_index,
            limit_expr=count,
            result_size=4,
            stride=4,
            element_size=4,
            return_region_value_proven=True,
        )
    return Expression.intrinsic(
        "READONLY_SUM",
        [base, count],
        size=4,
        runtime_ref=ReadonlyReductionRef(
            reduction_kind="memory_sum",
            pointer_base_ref=pointer_ref,
            count_parameter_name=count_name,
            count_parameter_index=count_index,
            stride=4,
            element_size=4,
            result_size=4,
            signed_counter=True,
            accumulator_proof=proof,
        ),
        opcode=READONLY_SUM_OPCODE,
    )


def test_readonly_return_ordering_refuses_name_only_surface_identity():
    proof_backed = _readonly_return_ordering_expr(
        base_name="left_base",
        count_name="count",
        proof_backed=True,
    )
    summary_only = _readonly_return_ordering_expr(
        base_name="right_base",
        count_name="count",
        proof_backed=False,
    )

    assert compare_readonly_summary_values_by_priority(
        proof_backed,
        [],
        summary_only,
        [],
        return_size=32,
    ) == 0


def test_readonly_return_ordering_uses_indexed_surface_identity():
    proof_backed = _readonly_return_ordering_expr(
        base_name="left_base",
        count_name="count",
        base_index=0,
        count_index=1,
        proof_backed=True,
    )
    summary_only = _readonly_return_ordering_expr(
        base_name="right_base",
        count_name="count",
        base_index=0,
        count_index=1,
        proof_backed=False,
    )

    assert compare_readonly_summary_values_by_priority(
        proof_backed,
        [],
        summary_only,
        [],
        return_size=32,
    ) == -1


def test_readonly_return_ordering_does_not_let_broad_priority_shadow_specific_guard():
    count_eq_one = Condition(
        Expression.binary_op(
            "INT_EQUAL",
            Expression.parameter("count", index=1, data_type="int", size=4),
            Expression.constant(1, size=4),
        )
    )
    broad_proof = _readonly_return_ordering_expr(
        base_name="base",
        count_name="count",
        base_index=0,
        count_index=1,
        proof_backed=True,
    )
    specific_summary = _readonly_return_ordering_expr(
        base_name="base",
        count_name="count",
        base_index=0,
        count_index=1,
        proof_backed=False,
    )

    assert compare_readonly_summary_values_by_priority(
        broad_proof,
        [],
        specific_summary,
        [count_eq_one],
        return_size=32,
    ) == 0

    ordered = _order_return_defs_by_specificity(
        [
            {
                "index": 0,
                "raw_value": broad_proof,
                "raw_conditions": [],
                "condition_set": ConditionSimplifier.build_constraint_set([]),
            },
            {
                "index": 1,
                "raw_value": specific_summary,
                "raw_conditions": [count_eq_one],
                "condition_set": ConditionSimplifier.build_constraint_set([count_eq_one]),
            },
        ],
        return_size=32,
    )

    assert ordered[0]["index"] == 1


class TestPublicAPIWrappers:
    """公開 API wrapper の一貫性テスト"""

    def test_build_equivalence_formula_with_extra_assertions(self):
        builder = FormulaBuilder(debug=False)
        analysis1 = _simple_analysis("func1", "x")
        analysis2 = _simple_analysis("func2", "y")
        extra_assertions = [
            "; Test constraint",
            "(assert (bvult x_1 (_ bv100 32)))",
        ]

        formula, return_var1, return_var2 = builder.build_equivalence_formula(
            analysis1,
            analysis2,
            extra_assertions=extra_assertions,
        )

        assert isinstance(formula, str)
        assert isinstance(return_var1, str)
        assert isinstance(return_var2, str)
        assert return_var1 == "return_1"
        assert return_var2 == "return_2"
        assert "Test constraint" in formula
        assert "(assert (bvult x_1 (_ bv100 32)))" in formula

        lines = formula.split("\n")
        check_sat_index = -1
        constraint_index = -1
        for i, line in enumerate(lines):
            if "(check-sat)" in line:
                check_sat_index = i
            if "Test constraint" in line:
                constraint_index = i
        assert check_sat_index >= 0
        assert constraint_index >= 0
        assert constraint_index < check_sat_index

    def test_build_equivalence_formula_wrapper_consistency(self):
        builder = FormulaBuilder(debug=False)
        analysis1 = _simple_analysis("func1", "p")
        analysis2 = _simple_analysis("func2", "q")
        extra_assertions = [
            "; Wrapper test",
            "(assert (= p_1 q_2))",
        ]

        with patch.object(
            builder,
            "build_equivalence_formula_extended",
            wraps=builder.build_equivalence_formula_extended,
        ) as spy_extended:
            formula, return_var1, return_var2 = builder.build_equivalence_formula(
                analysis1,
                analysis2,
                func1_suffix="_1",
                func2_suffix="_2",
                extra_assertions=extra_assertions,
            )

            assert spy_extended.called
            call_args = spy_extended.call_args
            assert call_args.args[0] is analysis1
            assert call_args.args[1] is analysis2
            assert call_args.args[2] == "_1"
            assert call_args.args[3] == "_2"
            assert call_args.kwargs.get("extra_assertions") == extra_assertions

        result_extended = builder.build_equivalence_formula_extended(
            analysis1,
            analysis2,
            func1_suffix="_1",
            func2_suffix="_2",
            extra_assertions=extra_assertions,
        )

        assert formula == result_extended.formula
        assert return_var1 == "return_1"
        assert return_var2 == "return_2"
        assert return_var1 == result_extended.return_var1
        assert return_var2 == result_extended.return_var2


class TestSharedFormulaContext:
    """FormulaBuilder 内の共有 context/header 構築の回帰テスト"""

    @staticmethod
    def _build_simple_analyses():
        return _simple_analysis("func1", "x"), _simple_analysis("func2", "y")

    def test_build_base_context_reuses_extended_header_context(self):
        builder = FormulaBuilder(debug=False, exclude_ub=False)
        analysis1, analysis2 = self._build_simple_analyses()

        base_ctx = builder.build_base_context(analysis1, analysis2)
        result = builder.build_equivalence_formula_extended(analysis1, analysis2)
        header_text = "\n".join(base_ctx["header_lines"])

        assert header_text in result.formula
        assert base_ctx["extra_vars1"] == result.extra_vars1
        assert base_ctx["extra_vars2"] == result.extra_vars2
        assert base_ctx["constrained_fragments"] == result.constrained_fragments
        assert base_ctx["return_size1"] == 32
        assert base_ctx["return_size2"] == 32

    def test_build_base_context_preserves_debug_silence(self):
        builder = FormulaBuilder(debug=True, exclude_ub=False)
        analysis1, analysis2 = self._build_simple_analyses()

        with patch.object(builder, "_print_debug_info") as spy_debug:
            builder.build_base_context(analysis1, analysis2)
            spy_debug.assert_not_called()

            builder.build_equivalence_formula_extended(analysis1, analysis2)
            spy_debug.assert_called_once()


class TestBooleanReturnNormalization:
    """Bool 戻り値の SMT 正規化に関する回帰テスト"""

    @staticmethod
    def _signed_less_than_parameter(param_name: str, param_size: int, constant: int, result_size: int):
        comparison = Expression.binary_op(
            "INT_SLESS",
            Expression(ExpressionType.CONSTANT, value=constant, size=param_size),
            Expression(ExpressionType.PARAMETER, name=param_name, size=param_size),
        )
        coerced = Expression.unary_op("INT_ZEXT", comparison)
        coerced.size = result_size
        return coerced

    def test_boolean_return_expression_is_coerced_to_bitvec(self):
        builder = FormulaBuilder(debug=False)
        analysis1 = FunctionReturnAnalysis(
            function_name="func_bool_constant",
            entry_point="0x00401000",
            parameters=[{"name": "x", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression(ExpressionType.CONSTANT, value=0, size=1),
                )
            ],
            return_type="bool",
        )
        analysis2 = FunctionReturnAnalysis(
            function_name="func_bool",
            entry_point="0x00402000",
            parameters=[{"name": "y", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=Expression.binary_op(
                        "INT_LESS",
                        Expression(ExpressionType.PARAMETER, name="y", size=4),
                        Expression(ExpressionType.CONSTANT, value=10, size=4),
                    ),
                )
            ],
            return_type="bool",
        )

        formula = builder.build_equivalence_formula_extended(analysis1, analysis2).formula

        assert "(define-fun return_2 () (_ BitVec 8)" in formula
        assert "(ite (bvult y_2 (_ bv10 32)) (_ bv1 8) (_ bv0 8))" in formula
        assert "(define-fun return_2 () (_ BitVec 8)\n  (bvult" not in formula

    def test_non_boolean_byte_return_is_not_coerced(self):
        builder = FormulaBuilder(debug=False)
        analysis1 = FunctionReturnAnalysis(
            function_name="func_u8_a",
            entry_point="0x00401000",
            parameters=[],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression(ExpressionType.CONSTANT, value=255, size=1),
                )
            ],
            return_type="uchar",
        )
        analysis2 = FunctionReturnAnalysis(
            function_name="func_u8_b",
            entry_point="0x00402000",
            parameters=[],
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=Expression(ExpressionType.CONSTANT, value=255, size=1),
                )
            ],
            return_type="uchar",
        )

        formula = builder.build_equivalence_formula_extended(analysis1, analysis2).formula

        assert "(define-fun return_1 () (_ BitVec 8)\n  (_ bv255 8))" in formula
        assert "(define-fun return_2 () (_ BitVec 8)\n  (_ bv255 8))" in formula
        assert "(ite (_ bv255 8)" not in formula

    def test_nested_boolean_to_int_expression_uses_ite_instead_of_zero_extend(self):
        expr = Expression.binary_op(
            "INT_ADD",
            self._signed_less_than_parameter("x", 4, 100, 4),
            Expression(ExpressionType.CONSTANT, value=2, size=4),
        )

        smt = expr.to_smt()

        assert smt == "(bvadd (ite (bvslt (_ bv100 32) x) (_ bv1 32) (_ bv0 32)) (_ bv2 32))"
        assert "zero_extend" not in smt

    def test_formula_builder_handles_branch_bucket_style_optimized_value(self):
        builder = FormulaBuilder(debug=False)
        analysis1 = FunctionReturnAnalysis(
            function_name="func_simple",
            entry_point="0x00401000",
            parameters=[{"name": "x", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression(ExpressionType.CONSTANT, value=3, size=4),
                )
            ],
            return_type="int",
        )
        optimized_value = Expression.binary_op(
            "INT_OR",
            self._signed_less_than_parameter("y", 8, 100, 4),
            Expression(ExpressionType.CONSTANT, value=2, size=4),
        )
        analysis2 = FunctionReturnAnalysis(
            function_name="func_bucket_opt",
            entry_point="0x00402000",
            parameters=[{"name": "y", "size": 8, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=optimized_value,
                )
            ],
            return_type="int",
        )

        formula = builder.build_equivalence_formula_extended(analysis1, analysis2).formula

        assert "(bvor (ite (bvslt (_ bv100 64) y_2) (_ bv1 32) (_ bv0 32)) (_ bv2 32))" in formula
        assert "((_ zero_extend 24) (bvslt (_ bv100 64) y_2))" not in formula

    def test_formula_builder_coerces_mixed_width_return_values_to_declared_size(self):
        builder = FormulaBuilder(debug=False)
        analysis = FunctionReturnAnalysis(
            function_name="func_mixed",
            entry_point="0x00401000",
            parameters=[{"name": "x", "size": 8, "index": 0, "is_signed": False}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[
                        Condition(
                            Expression.binary_op(
                                "INT_EQUAL",
                                Expression(ExpressionType.PARAMETER, name="x", size=8),
                                Expression(ExpressionType.CONSTANT, value=0, size=8),
                            )
                        )
                    ],
                    value=Expression(ExpressionType.PARAMETER, name="x", size=8),
                ),
                ReturnInfo(
                    address="0x00401010",
                    conditions=[],
                    value=Expression(ExpressionType.CONSTANT, value=2, size=4),
                ),
            ],
            return_type="ulong",
            return_type_obj=resolve_mock_data_type("ulong"),
        )

        formula = builder.build_equivalence_formula_extended(analysis, analysis).formula

        assert "(define-fun return_1 () (_ BitVec 64)" in formula
        assert "((_ zero_extend 32) (_ bv2 32))" in formula
        assert "ite (=" in formula

    def test_formula_builder_uses_relation_lowering_for_overlapping_different_valued_returns(self):
        builder = FormulaBuilder(debug=False)
        guard = Condition(
            Expression.binary_op(
                "INT_EQUAL",
                Expression(ExpressionType.PARAMETER, name="x", size=4),
                Expression(ExpressionType.CONSTANT, value=0, size=4),
            )
        )
        analysis = FunctionReturnAnalysis(
            function_name="func_overlap",
            entry_point="0x00401000",
            parameters=[{"name": "x", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[guard],
                    value=Expression(ExpressionType.CONSTANT, value=1, size=4),
                ),
                ReturnInfo(
                    address="0x00401004",
                    conditions=[guard],
                    value=Expression(ExpressionType.CONSTANT, value=2, size=4),
                ),
            ],
            return_type="int",
        )

        formula = builder.build_equivalence_formula_extended(analysis, analysis).formula

        assert "(declare-const return_1 (_ BitVec 32))" in formula
        assert "(declare-const return_2 (_ BitVec 32))" in formula
        assert "(define-fun return_1 () (_ BitVec 32)" not in formula
        assert "(assert (or (and (= x_1 (_ bv0 32)) (= return_1 (_ bv1 32)))" in formula

    def test_declared_return_type_takes_priority_over_first_branch_size(self):
        builder = FormulaBuilder(debug=False)
        analysis = FunctionReturnAnalysis(
            function_name="func_declared_ulong",
            entry_point="0x00401000",
            parameters=[{"name": "x", "size": 8, "index": 0, "is_signed": False}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[
                        Condition(
                            Expression.binary_op(
                                "INT_EQUAL",
                                Expression(ExpressionType.PARAMETER, name="x", size=8),
                                Expression(ExpressionType.CONSTANT, value=0, size=8),
                            )
                        )
                    ],
                    value=Expression(ExpressionType.CONSTANT, value=0, size=4),
                ),
                ReturnInfo(
                    address="0x00401010",
                    conditions=[],
                    value=Expression(ExpressionType.PARAMETER, name="x", size=8),
                ),
            ],
            return_type="ulong",
            return_type_obj=resolve_mock_data_type("ulong"),
        )

        base_ctx = builder.build_base_context(analysis, analysis)
        formula = builder.build_equivalence_formula_extended(analysis, analysis).formula

        assert base_ctx["return_size1"] == 64
        assert base_ctx["return_size2"] == 64
        assert "(define-fun return_1 () (_ BitVec 64)" in formula
        assert "(define-fun return_2 () (_ BitVec 64)" in formula
        assert "((_ zero_extend 32) (_ bv0 32))" in formula

    def test_undefined8_return_type_is_treated_as_64bit(self):
        builder = FormulaBuilder(debug=False)
        analysis = FunctionReturnAnalysis(
            function_name="func_undefined8",
            entry_point="0x00401000",
            parameters=[{"name": "x", "size": 8, "index": 0, "is_signed": False}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression(ExpressionType.CONSTANT, value=0, size=4),
                )
            ],
            return_type="undefined8",
            return_type_obj=resolve_mock_data_type("undefined8"),
        )

        base_ctx = builder.build_base_context(analysis, analysis)
        formula = builder.build_equivalence_formula_extended(analysis, analysis).formula

        assert base_ctx["return_size1"] == 64
        assert "(define-fun return_1 () (_ BitVec 64)" in formula
        assert "((_ zero_extend 32) (_ bv0 32))" in formula

    def test_phi_return_branches_are_coerced_to_common_bit_width(self):
        builder = FormulaBuilder(debug=False)
        phi_expr = Expression.phi([
            (
                Condition(
                    Expression.binary_op(
                        "INT_EQUAL",
                        Expression(ExpressionType.PARAMETER, name="x", size=8),
                        Expression(ExpressionType.CONSTANT, value=0, size=8),
                    )
                ),
                Expression(ExpressionType.PARAMETER, name="x", size=8),
            ),
            (None, Expression(ExpressionType.CONSTANT, value=2, size=4)),
        ])
        phi_expr.size = 8

        analysis = FunctionReturnAnalysis(
            function_name="func_phi",
            entry_point="0x00401000",
            parameters=[{"name": "x", "size": 8, "index": 0, "is_signed": False}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=phi_expr,
                )
            ],
            return_type="ulong",
        )

        formula = builder.build_equivalence_formula_extended(analysis, analysis).formula

        assert "(define-fun return_1 () (_ BitVec 64)" in formula
        assert "((_ zero_extend 32) (_ bv2 32))" in formula
        assert "(ite (= x_1 (_ bv0 64)) x_1 ((_ zero_extend 32) (_ bv2 32)))" in formula

    def test_signed_branch_evidence_sign_extends_ambiguous_negative_return_constant(self):
        builder = FormulaBuilder(debug=False)
        analysis = FunctionReturnAnalysis(
            function_name="func_signed_bucket",
            entry_point="0x00401000",
            parameters=[{"name": "x", "size": 8, "index": 0, "is_signed": False}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[
                        Condition(
                            Expression.binary_op(
                                "INT_SLESS",
                                Expression(ExpressionType.PARAMETER, name="x", size=8),
                                Expression(ExpressionType.CONSTANT, value=-100, size=8),
                            )
                        )
                    ],
                    value=Expression(ExpressionType.CONSTANT, value=0xFFFFFFFD, size=8),
                )
            ],
            return_type="undefined8",
        )

        formula = builder.build_equivalence_formula_extended(analysis, analysis).formula

        assert "(define-fun return_1 () (_ BitVec 64)" in formula
        assert "(_ bv18446744073709551613 64)" in formula
        assert "(_ bv4294967293 64)" not in formula

    def test_phi_with_signed_branch_evidence_sign_extends_negative_constants(self):
        builder = FormulaBuilder(debug=False)
        phi_expr = Expression.phi([
            (
                Condition(
                    Expression.binary_op(
                        "INT_SLESS",
                        Expression(ExpressionType.PARAMETER, name="x", size=4),
                        Expression(ExpressionType.CONSTANT, value=-100, size=4),
                    )
                ),
                Expression(ExpressionType.CONSTANT, value=0xFFFFFFFD, size=8),
            ),
            (None, Expression(ExpressionType.CONSTANT, value=2, size=8)),
        ])
        phi_expr.size = 8

        analysis = FunctionReturnAnalysis(
            function_name="func_phi_signed_bucket",
            entry_point="0x00401000",
            parameters=[{"name": "x", "size": 8, "index": 0, "is_signed": False}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=phi_expr,
                )
            ],
            return_type="undefined8",
        )

        formula = builder.build_equivalence_formula_extended(analysis, analysis).formula

        assert "(_ bv18446744073709551613 64)" in formula
        assert "(_ bv4294967293 64)" not in formula

    def test_build_base_context_infers_fragment_constraints_from_piece_expression(self):
        builder = FormulaBuilder(debug=False)

        wide_param = Expression.binary_op(
            "PIECE",
            Expression(ExpressionType.VARIABLE, name="in_a1_hi", size=4),
            Expression(ExpressionType.PARAMETER, name="param_2", size=4, data_type="int"),
        )
        wide_param.size = 8

        analysis1 = FunctionReturnAnalysis(
            function_name="fragment_backed_guard",
            entry_point="0x00401000",
            parameters=[{"name": "param_2", "size": 4, "index": 0, "is_signed": True, "data_type": "int"}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[
                        Condition(
                            Expression.binary_op(
                                "INT_SLESS",
                                wide_param,
                                Expression(ExpressionType.CONSTANT, value=1, size=8),
                            )
                        )
                    ],
                    value=Expression(ExpressionType.CONSTANT, value=0, size=4),
                )
            ],
            return_type="int",
        )
        analysis2 = _simple_analysis("simple", "param_2")

        base_ctx = builder.build_base_context(analysis1, analysis2)
        header_text = "\n".join(base_ctx["header_lines"])

        assert "in_a1_hi_1" in base_ctx["constrained_fragments"]
        assert "(assert (= in_a1_hi_1 ((_ extract 63 32) ((_ sign_extend 32) param_2_1))))" in header_text

    def test_build_base_context_records_loop_summary_smt_identity_notes(self):
        builder = FormulaBuilder(debug=False)
        analysis1 = FunctionReturnAnalysis(
            function_name="loop_left",
            entry_point="0x00401000",
            parameters=[
                {"name": "base", "size": 8, "index": 0, "is_signed": False, "data_type": "int *"},
                {"name": "count", "size": 4, "index": 1, "is_signed": True, "data_type": "int"},
            ],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=_readonly_loop_summary_expr(),
                )
            ],
            return_type="int",
        )
        analysis2 = FunctionReturnAnalysis(
            function_name="loop_right",
            entry_point="0x00402000",
            parameters=analysis1.parameters,
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=_readonly_loop_summary_expr(),
                )
            ],
            return_type="int",
        )

        base_ctx = builder.build_base_context(analysis1, analysis2)
        header_text = "\n".join(base_ctx["header_lines"])

        assert "Loop summary SMT identities" in header_text
        assert "loop-summary READONLY_SUM ReadonlyReductionRef method_b:" in header_text

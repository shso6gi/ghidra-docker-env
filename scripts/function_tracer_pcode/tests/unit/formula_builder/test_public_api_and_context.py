# -*- coding: utf-8 -*-
"""FormulaBuilder の公開 API・context 共有まわりのテスト。"""

from unittest.mock import patch

from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.model import (
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
)


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

    def test_boolean_return_expression_is_coerced_to_bitvec(self):
        builder = FormulaBuilder(debug=False)
        analysis1 = FunctionReturnAnalysis(
            function_name="func_int",
            entry_point="0x00401000",
            parameters=[{"name": "x", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression(ExpressionType.CONSTANT, value=0, size=4),
                )
            ],
            return_type="int",
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

# -*- coding: utf-8 -*-
"""FormulaBuilder のユニットテスト（統合系・リトライ連携中心）。"""

import pytest
from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.core import (
    FunctionReturnAnalysis,
    ReturnInfo,
    Expression,
    ExpressionType,
    Condition,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence import build_input_correspondence_set


class TestIntegration:
    """統合テスト（UB制約との共存など）"""
    
    def test_extra_assertions_with_ub_constraints(self):
        """UB制約とextra_assertionsが共存できることを確認"""
        builder = FormulaBuilder(debug=False, exclude_ub=True)
        
        analysis1 = FunctionReturnAnalysis(
            function_name="func1",
            entry_point="0x00401000",
            parameters=[
                {"name": "x", "size": 4, "index": 0, "is_signed": True}
            ],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression(
                        ExpressionType.UNARY_OP,
                        operator="INT_2COMP",
                        operands=[
                            Expression(ExpressionType.PARAMETER, name="x", size=4)
                        ],
                        size=4
                    )
                )
            ]
        )
        
        analysis2 = FunctionReturnAnalysis(
            function_name="func2",
            entry_point="0x00402000",
            parameters=[
                {"name": "a", "size": 4, "index": 0, "is_signed": True}
            ],
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=Expression(
                        ExpressionType.UNARY_OP,
                        operator="INT_2COMP",
                        operands=[
                            Expression(ExpressionType.PARAMETER, name="a", size=4)
                        ],
                        size=4
                    )
                )
            ]
        )
        
        extra_assertions = [
            "; Additional constraint",
            "(assert (bvugt x_1 (_ bv10 32)))"
        ]
        
        result = builder.build_equivalence_formula_extended(
            analysis1, analysis2,
            extra_assertions=extra_assertions, input_correspondence=build_input_correspondence_set(analysis1, analysis2),
        )
        
        formula = result.formula
        
        assert "UB Exclusion Constraints" in formula
        assert "Additional constraint" in formula
        assert "(assert (bvugt x_1 (_ bv10 32)))" in formula
        
        lines = formula.split('\n')
        check_sat_index = -1
        for i, line in enumerate(lines):
            if '(check-sat)' in line:
                check_sat_index = i
                break
        
        assert check_sat_index >= 0
        
        before_check_sat = '\n'.join(lines[:check_sat_index])
        assert "UB Exclusion Constraints" in before_check_sat
        assert "Additional constraint" in before_check_sat
        
        print("\n[TEST] UB constraints (negate_min) and extra_assertions coexist correctly")

    def test_shift_count_ub_constraints_are_emitted(self):
        """可変シフトに対して shift-count UB 制約が追加されることを確認"""
        builder = FormulaBuilder(debug=False, exclude_ub=True)

        shift_amount_1 = Expression(ExpressionType.PARAMETER, name="shift", size=4)
        shift_amount_2 = Expression(ExpressionType.PARAMETER, name="shift", size=4)
        shift_base_1 = Expression(ExpressionType.CONSTANT, value=1, size=8)
        shift_base_2 = Expression(ExpressionType.CONSTANT, value=1, size=8)

        shift_expr_1 = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_LEFT",
            operands=[shift_base_1, shift_amount_1],
            size=8,
        )
        shift_expr_2 = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_LEFT",
            operands=[shift_base_2, shift_amount_2],
            size=8,
        )

        nonzero_cond_1 = Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_NOTEQUAL",
                operands=[
                    shift_expr_1,
                    Expression(ExpressionType.CONSTANT, value=0, size=8),
                ],
                size=1,
            )
        )
        nonzero_cond_2 = Condition(
            Expression(
                ExpressionType.BINARY_OP,
                operator="INT_NOTEQUAL",
                operands=[
                    shift_expr_2,
                    Expression(ExpressionType.CONSTANT, value=0, size=8),
                ],
                size=1,
            )
        )

        analysis1 = FunctionReturnAnalysis(
            function_name="func1",
            entry_point="0x00401000",
            parameters=[{"name": "shift", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[nonzero_cond_1],
                    value=shift_expr_1,
                )
            ],
        )

        analysis2 = FunctionReturnAnalysis(
            function_name="func2",
            entry_point="0x00402000",
            parameters=[{"name": "shift", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[nonzero_cond_2],
                    value=shift_expr_2,
                )
            ],
        )

        result = builder.build_equivalence_formula_extended(analysis1, analysis2, input_correspondence=build_input_correspondence_set(analysis1, analysis2))
        formula = result.formula

        assert "Exclude UB: INT_LEFT shift amount must be < 64 bits" in formula
        assert "(assert (bvult shift_1 (_ bv64 32)))" in formula
        assert "(assert (bvult shift_2 (_ bv64 32)))" in formula

        print("\n[TEST] shift-count UB constraints are emitted for variable shifts")

    def test_signed_left_shift_overflow_constraints_are_emitted_for_signed_context(self):
        """signed 文脈の 1 << shift に対して overflow UB 制約が追加されることを確認"""
        builder = FormulaBuilder(debug=False, exclude_ub=True)

        shift1 = Expression(ExpressionType.PARAMETER, name="shift", size=4)
        shift2 = Expression(ExpressionType.PARAMETER, name="shift", size=4)
        shifted1 = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_LEFT",
            operands=[Expression(ExpressionType.CONSTANT, value=1, size=8), shift1],
            size=8,
        )
        shifted2 = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_LEFT",
            operands=[Expression(ExpressionType.CONSTANT, value=1, size=8), shift2],
            size=8,
        )

        value1 = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_SDIV",
            operands=[
                Expression(ExpressionType.PARAMETER, name="x", size=8),
                shifted1,
            ],
            size=8,
        )
        value2 = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_SDIV",
            operands=[
                Expression(ExpressionType.PARAMETER, name="y", size=8),
                shifted2,
            ],
            size=8,
        )

        analysis1 = FunctionReturnAnalysis(
            function_name="func1",
            entry_point="0x00401000",
            parameters=[
                {"name": "x", "size": 8, "index": 0, "is_signed": True},
                {"name": "shift", "size": 4, "index": 1, "is_signed": True},
            ],
            returns=[ReturnInfo(address="0x00401000", conditions=[], value=value1)],
        )
        analysis2 = FunctionReturnAnalysis(
            function_name="func2",
            entry_point="0x00402000",
            parameters=[
                {"name": "y", "size": 8, "index": 0, "is_signed": True},
                {"name": "shift", "size": 4, "index": 1, "is_signed": True},
            ],
            returns=[ReturnInfo(address="0x00402000", conditions=[], value=value2)],
        )

        formula = builder.build_equivalence_formula_extended(analysis1, analysis2, input_correspondence=build_input_correspondence_set(analysis1, analysis2)).formula

        assert "signed left shift overflow requires shift < 63" in formula
        assert "(assert (bvult shift_1 (_ bv63 32)))" in formula
        assert "(assert (bvult shift_2 (_ bv63 32)))" in formula

        print("\n[TEST] signed left shift overflow constraints emitted for signed context")

    def test_signed_left_shift_overflow_constraints_are_not_emitted_for_unsigned_context(self):
        """unsigned 文脈では追加の signed overflow 制約を入れないことを確認"""
        builder = FormulaBuilder(debug=False, exclude_ub=True)

        shift1 = Expression(ExpressionType.PARAMETER, name="shift", size=4)
        shift2 = Expression(ExpressionType.PARAMETER, name="shift", size=4)
        shifted1 = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_LEFT",
            operands=[Expression(ExpressionType.CONSTANT, value=1, size=8), shift1],
            size=8,
        )
        shifted2 = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_LEFT",
            operands=[Expression(ExpressionType.CONSTANT, value=1, size=8), shift2],
            size=8,
        )

        value1 = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_DIV",
            operands=[
                Expression(ExpressionType.PARAMETER, name="x", size=8),
                shifted1,
            ],
            size=8,
        )
        value2 = Expression(
            ExpressionType.BINARY_OP,
            operator="INT_DIV",
            operands=[
                Expression(ExpressionType.PARAMETER, name="y", size=8),
                shifted2,
            ],
            size=8,
        )

        analysis1 = FunctionReturnAnalysis(
            function_name="func1",
            entry_point="0x00401000",
            parameters=[
                {"name": "x", "size": 8, "index": 0, "is_signed": False},
                {"name": "shift", "size": 4, "index": 1, "is_signed": True},
            ],
            returns=[ReturnInfo(address="0x00401000", conditions=[], value=value1)],
        )
        analysis2 = FunctionReturnAnalysis(
            function_name="func2",
            entry_point="0x00402000",
            parameters=[
                {"name": "y", "size": 8, "index": 0, "is_signed": False},
                {"name": "shift", "size": 4, "index": 1, "is_signed": True},
            ],
            returns=[ReturnInfo(address="0x00402000", conditions=[], value=value2)],
        )

        formula = builder.build_equivalence_formula_extended(analysis1, analysis2, input_correspondence=build_input_correspondence_set(analysis1, analysis2)).formula

        assert "signed left shift overflow requires shift < 63" not in formula
        assert "(assert (bvult shift_1 (_ bv64 32)))" in formula
        assert "(assert (bvult shift_2 (_ bv64 32)))" in formula

        print("\n[TEST] no signed overflow constraints emitted for unsigned context")



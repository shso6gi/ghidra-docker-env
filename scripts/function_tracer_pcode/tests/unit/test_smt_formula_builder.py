# -*- coding: utf-8 -*-
"""FormulaBuilder のユニットテスト（統合系・リトライ連携中心）。"""

import pytest
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.model import (
    FunctionReturnAnalysis,
    ReturnInfo,
    Expression,
    ExpressionType,
    Condition,
)


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
            extra_assertions=extra_assertions
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

        result = builder.build_equivalence_formula_extended(analysis1, analysis2)
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

        formula = builder.build_equivalence_formula_extended(analysis1, analysis2).formula

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

        formula = builder.build_equivalence_formula_extended(analysis1, analysis2).formula

        assert "signed left shift overflow requires shift < 63" not in formula
        assert "(assert (bvult shift_1 (_ bv64 32)))" in formula
        assert "(assert (bvult shift_2 (_ bv64 32)))" in formula

        print("\n[TEST] no signed overflow constraints emitted for unsigned context")


class TestCheckerABIRetryIntegration:
    """checker._retry_with_abi_constraints() 経由の integration test"""

    @staticmethod
    def _phase_context(analysis1, analysis2):
        from scripts.function_tracer_pcode.equivalence.phases.handler import (
            PhaseContext,
        )
        from scripts.function_tracer_pcode.equivalence.typing.fixer import (
            TypeFixResult,
        )
        from unittest.mock import Mock

        return PhaseContext(
            program1=Mock(),
            program2=Mock(),
            function_name1=analysis1.function_name,
            function_name2=analysis2.function_name,
            binary1_name="mips64-bin",
            binary2_name="comparison-bin",
            decompile_timeout=60,
            save_formula=True,
            type_fix_result=TypeFixResult(),
            original_signature1=None,
            original_signature2=None,
            analysis1=analysis1,
            analysis2=analysis2,
        )
    
    def test_retry_with_abi_constraints_integration(self):
        """_retry_with_abi_constraints が FormulaBuilder の正しい経路を使うことを確認"""
        from scripts.function_tracer_pcode.equivalence.checker import EquivalenceChecker
        from scripts.function_tracer_pcode.equivalence.phases.handler import PhaseContext
        from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixResult
        from unittest.mock import Mock, patch, call
        
        # ★ 修正: debug=False にして run_parallel() のみを patch
        checker = EquivalenceChecker(debug=False)
        
        analysis1 = FunctionReturnAnalysis(
            function_name="func1",
            entry_point="0x00401000",
            parameters=[{"name": "x", "size": 8, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression(ExpressionType.PARAMETER, name="x", size=8)
                )
            ]
        )
        
        analysis2 = FunctionReturnAnalysis(
            function_name="func2",
            entry_point="0x00402000",
            parameters=[{"name": "x", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=Expression(ExpressionType.PARAMETER, name="x", size=4)
                )
            ]
        )
        
        ctx = PhaseContext(
            program1=Mock(),
            program2=Mock(),
            function_name1="func1",
            function_name2="func2",
            binary1_name="binary1",
            binary2_name="binary2",
            decompile_timeout=60,
            save_formula=True,
            type_fix_result=TypeFixResult(),
            original_signature1=None,
            original_signature2=None,
            analysis1=analysis1,
            analysis2=analysis2
        )
        
        abi_constraints = {
            "x_1": ("signed", 32),
        }
        
        # FormulaBuilder のメソッド呼び出しを spy
        with patch.object(checker.formula_builder, 'build_abi_assertion_section', 
                         wraps=checker.formula_builder.build_abi_assertion_section) as spy_section, \
             patch.object(checker.formula_builder, 'build_equivalence_formula_extended',
                         wraps=checker.formula_builder.build_equivalence_formula_extended) as spy_extended, \
             patch.object(checker.solver_runner, 'run_parallel') as mock_solver:
            
            from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
            
            solver_result = SolverResult(
                solver_name="mock",
                status=SolverStatus.UNSAT,
                elapsed_time=0.1,
            )

            mock_solver.return_value = ParallelResult(
                results=[solver_result],
                first_definitive=solver_result,
                is_equivalent=True,
            )

            
            result = checker._retry_with_abi_constraints(ctx, abi_constraints, retry_count=1)
            
            # build_abi_assertion_section が呼ばれたことを確認
            assert spy_section.called, "build_abi_assertion_section should be called"
            spy_section.assert_called_once_with(abi_constraints, "_1", "_2")
            
            # build_equivalence_formula_extended が extra_assertions 付きで呼ばれたことを確認
            assert spy_extended.called, "build_equivalence_formula_extended should be called"
            
            # extra_assertions 引数を検証
            call_kwargs = spy_extended.call_args.kwargs
            assert 'extra_assertions' in call_kwargs, "extra_assertions should be passed"
            extra_assertions_arg = call_kwargs['extra_assertions']
            
            # extra_assertions が空でないことを確認
            assert extra_assertions_arg is not None, "extra_assertions should not be None"
            assert len(extra_assertions_arg) > 0, "extra_assertions should not be empty"
            
            # ABI セクションヘッダが含まれることを確認
            extra_text = '\n'.join(extra_assertions_arg)
            assert "MIPS64 ABI constraints" in extra_text, \
                "extra_assertions should contain ABI section header"
            
            # return width bridge proof がない ABI 制約だけでは solver へ進まない。
            assert not mock_solver.called, "run_parallel should not be called without a return-width bridge proof"
        
        # 結果検証
        assert result.is_equivalent is None
        assert result.error_message is None
        assert result.smt_formula is None
        assert result.pairwise_debug_stats == {"return_width_bridge_missing": 1}
        assert result.mips64_abi_constraints == abi_constraints
        
        print("\n[TEST] _retry_with_abi_constraints uses correct FormulaBuilder path")
        print(f"  - build_abi_assertion_section called: {spy_section.call_count} time(s)")
        print(f"  - build_equivalence_formula_extended called with extra_assertions")
        print(f"  - run_parallel blocked until a return-width bridge proof exists")

    def test_retry_with_abi_constraints_unknown_extension_width_is_unknown(self):
        from scripts.function_tracer_pcode.equivalence.checker import (
            EquivalenceChecker,
        )

        unknown = Expression.unknown("phi_no_valid_branch")
        unknown.size = 4
        extended = Expression.unary_op("INT_ZEXT", unknown)
        extended.size = 0
        analysis = FunctionReturnAnalysis(
            function_name="abi_retry_unknown_extension",
            entry_point="0x00401000",
            parameters=[],
            returns=[ReturnInfo("0x00401010", extended, [])],
            return_type="long",
        )
        checker = EquivalenceChecker(debug=False)
        constraints = {}

        result = checker._retry_with_abi_constraints(
            self._phase_context(analysis, analysis),
            constraints,
            retry_count=1,
        )

        assert result.is_equivalent is None
        assert result.error_message is None
        assert result.counterexample_raw is None
        assert result.mips64_abi_constraints == constraints
        assert result.pairwise_debug_stats == {
            "unknown_smt_extension_width": 1,
        }
        assert any(
            reason.reason_id == "expression_semantics_unsupported"
            and reason.stage == "ABI_RETRY"
            and "unknown_smt_extension_width" in tuple(
                reason.evidence_refs or ()
            )
            for reason in result.unknown_reasons
        )

    def test_retry_with_abi_constraints_unsat_has_no_counterexample_raw(self):
        from scripts.function_tracer_pcode.equivalence.checker import (
            EquivalenceChecker,
        )
        from scripts.function_tracer_pcode.smt import (
            ParallelResult,
            SolverResult,
            SolverStatus,
        )
        from unittest.mock import patch

        analysis1 = FunctionReturnAnalysis(
            function_name="abi_retry_unsat_left",
            entry_point="0x00401000",
            parameters=[],
            returns=[
                ReturnInfo(
                    "0x00401010",
                    Expression(ExpressionType.CONSTANT, value=7, size=4),
                    [],
                )
            ],
            return_type="int",
        )
        analysis2 = FunctionReturnAnalysis(
            function_name="abi_retry_unsat_right",
            entry_point="0x00402000",
            parameters=[],
            returns=[
                ReturnInfo(
                    "0x00402010",
                    Expression(ExpressionType.CONSTANT, value=7, size=4),
                    [],
                )
            ],
            return_type="int",
        )
        checker = EquivalenceChecker(debug=False)
        solver_result = SolverResult(
            solver_name="mock",
            status=SolverStatus.UNSAT,
            elapsed_time=0.1,
        )
        parallel_result = ParallelResult(
            results=[solver_result],
            first_definitive=solver_result,
            is_equivalent=True,
        )

        with patch.object(
            checker.solver_runner,
            "run_parallel",
            return_value=parallel_result,
        ):
            result = checker._retry_with_abi_constraints(
                self._phase_context(analysis1, analysis2),
                {},
                retry_count=1,
            )

        assert result.is_equivalent is True
        assert result.error_message is None
        assert result.counterexample is None
        assert result.counterexample_raw is None

# -*- coding: utf-8 -*-
"""FormulaBuilder のユニットテスト（SMT編集の一元化）"""

import pytest
from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.model import FunctionReturnAnalysis, ReturnInfo, Expression, ExpressionType


class TestExtraAssertions:
    """extra_assertions 機能のテスト"""
    
    def test_extra_assertions_placement(self):
        """extra_assertions が (check-sat) の直前に配置されることを確認"""
        builder = FormulaBuilder(debug=False)
        
        analysis1 = FunctionReturnAnalysis(
            function_name="func1",
            entry_point="0x00401000",
            parameters=[{"name": "x", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression(ExpressionType.PARAMETER, name="x", size=4)
                )
            ]
        )
        
        analysis2 = FunctionReturnAnalysis(
            function_name="func2",
            entry_point="0x00402000",
            parameters=[{"name": "y", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=Expression(ExpressionType.PARAMETER, name="y", size=4)
                )
            ]
        )
        
        extra_assertions = [
            "; Custom constraint section",
            "(assert (bvugt x_1 (_ bv0 32)))",
            "(assert (bvugt y_2 (_ bv0 32)))"
        ]
        
        result = builder.build_equivalence_formula_extended(
            analysis1, analysis2,
            extra_assertions=extra_assertions
        )
        
        formula = result.formula
        lines = formula.split('\n')
        
        check_sat_index = -1
        for i, line in enumerate(lines):
            if '(check-sat)' in line:
                check_sat_index = i
                break
        
        assert check_sat_index >= 0, "(check-sat) not found in formula"
        
        custom_section_found = False
        for i in range(check_sat_index):
            if "Custom constraint section" in lines[i]:
                custom_section_found = True
                assert "(assert (bvugt x_1" in lines[i + 1]
                assert "(assert (bvugt y_2" in lines[i + 2]
                break
        
        assert custom_section_found, "Extra assertions not found before (check-sat)"
        
        print("\n[TEST] extra_assertions correctly placed before (check-sat)")


class TestABIConstraints:
    """ABI制約生成のテスト"""
    
    def test_abi_constraint_generation(self):
        """ABI制約が正しい形式（wide = extend(narrow)）で生成されることを確認"""
        builder = FormulaBuilder(debug=False)
        
        abi_constraints = {
            "param0_1": ("signed", 32),
            "param1_2": ("unsigned", 32),
        }
        
        constraint_lines = builder.build_abi_constraints(abi_constraints, "_1", "_2")
        constraints_text = '\n'.join(constraint_lines)
        
        assert "param0_1" in constraints_text
        assert "sign_extend" in constraints_text
        assert "param0_2" in constraints_text
        assert "(= param0_1 ((_ sign_extend 32) param0_2))" in constraints_text
        
        assert "param1_2" in constraints_text
        assert "zero_extend" in constraints_text
        assert "param1_1" in constraints_text
        assert "(= param1_2 ((_ zero_extend 32) param1_1))" in constraints_text
        
        print("\n[TEST] ABI constraints correctly generated with opposite-suffix narrow params")
    
    def test_build_with_abi_constraints_uses_new_api(self):
        """build_with_abi_constraints が新APIを使うことを確認"""
        builder = FormulaBuilder(debug=False)
        
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
            parameters=[{"name": "y", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=Expression(ExpressionType.PARAMETER, name="y", size=4)
                )
            ]
        )
        
        abi_constraints = {
            "x_1": ("signed", 32),
        }
        
        formula = builder.build_with_abi_constraints(
            analysis1, analysis2, abi_constraints
        )
        
        assert "MIPS64 ABI constraints" in formula
        assert "sign_extend" in formula
        assert "x_1" in formula
        assert "y_2" in formula
        
        lines = formula.split('\n')
        check_sat_index = -1
        abi_constraint_index = -1
        
        for i, line in enumerate(lines):
            if '(check-sat)' in line:
                check_sat_index = i
            if 'MIPS64 ABI constraints' in line:
                abi_constraint_index = i
        
        assert check_sat_index >= 0
        assert abi_constraint_index >= 0
        assert abi_constraint_index < check_sat_index
        
        print("\n[TEST] build_with_abi_constraints uses new API")
    
    def test_build_abi_assertion_section(self):
        """build_abi_assertion_section がヘッダ付きセクション全体を生成することを確認"""
        builder = FormulaBuilder(debug=False)
        
        abi_constraints = {
            "param0_1": ("signed", 32),
        }
        
        section_lines = builder.build_abi_assertion_section(abi_constraints, "_1", "_2")
        
        assert any("MIPS64 ABI constraints" in line for line in section_lines), \
            "Section should include header"
        
        section_text = '\n'.join(section_lines)
        assert "param0_1" in section_text
        assert "param0_2" in section_text
        assert "sign_extend" in section_text
        
        print("\n[TEST] build_abi_assertion_section generates complete section with header")
    
    def test_build_abi_assertion_section_empty(self):
        """空のABI制約マップでは空リストを返すことを確認"""
        builder = FormulaBuilder(debug=False)
        
        section_lines = builder.build_abi_assertion_section({}, "_1", "_2")
        
        assert section_lines == [], "Empty constraints should return empty list"
        
        print("\n[TEST] build_abi_assertion_section returns empty list for empty constraints")
    
    def test_suffix_resolution_in_abi_constraints(self):
        """ABI制約の suffix 解決が正しく動作することを確認"""
        builder = FormulaBuilder(debug=False)
        
        abi_constraints_1to2 = {
            "x_1": ("signed", 32),
        }
        
        lines_1to2 = builder.build_abi_constraints(abi_constraints_1to2, "_1", "_2")
        text_1to2 = '\n'.join(lines_1to2)
        
        assert "x_1" in text_1to2
        assert "x_2" in text_1to2
        assert "(= x_1" in text_1to2
        assert "x_2))" in text_1to2
        
        abi_constraints_2to1 = {
            "y_2": ("unsigned", 32),
        }
        
        lines_2to1 = builder.build_abi_constraints(abi_constraints_2to1, "_1", "_2")
        text_2to1 = '\n'.join(lines_2to1)
        
        assert "y_2" in text_2to1
        assert "y_1" in text_2to1
        assert "(= y_2" in text_2to1
        assert "y_1))" in text_2to1
        assert "zero_extend" in text_2to1
        
        print("\n[TEST] Suffix resolution works correctly for both directions")

    def test_suffix_resolution_only_rewrites_trailing_suffix(self):
        """パラメータ名中の `_1` / `_2` を壊さず、末尾サフィックスだけを反転することを確認"""
        builder = FormulaBuilder(debug=False)

        abi_constraints = {
            "param_1_1": ("signed", 32),
            "param_2_2": ("unsigned", 32),
        }

        text = "\n".join(builder.build_abi_constraints(abi_constraints, "_1", "_2"))

        assert "param_1_2" in text
        assert "param_2_1" in text
        assert "param_2_2 ((_ sign_extend 32) param_1_1)" not in text
        assert "param_1_1 ((_ zero_extend 32) param_2_2)" not in text
        assert "(= param_1_1 ((_ sign_extend 32) param_1_2))" in text
        assert "(= param_2_2 ((_ zero_extend 32) param_2_1))" in text

        print("\n[TEST] Trailing suffix rewrite does not corrupt numbered parameter names")
    
    def test_build_with_abi_constraints_wrapper_consistency(self):
        """build_with_abi_constraints が build_abi_assertion_section を経由することを確認"""
        builder = FormulaBuilder(debug=False)
        
        analysis1 = FunctionReturnAnalysis(
            function_name="func1",
            entry_point="0x00401000",
            parameters=[{"name": "param0", "size": 8, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression(ExpressionType.PARAMETER, name="param0", size=8)
                )
            ]
        )
        
        analysis2 = FunctionReturnAnalysis(
            function_name="func2",
            entry_point="0x00402000",
            parameters=[{"name": "param0", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=Expression(ExpressionType.PARAMETER, name="param0", size=4)
                )
            ]
        )
        
        abi_constraints = {
            "param0_1": ("signed", 32),
        }
        
        # build_with_abi_constraints 経由
        formula_wrapper = builder.build_with_abi_constraints(
            analysis1, analysis2, abi_constraints
        )
        
        # build_abi_assertion_section + build_equivalence_formula_extended 経由（直接）
        section = builder.build_abi_assertion_section(abi_constraints, "_1", "_2")
        result_direct = builder.build_equivalence_formula_extended(
            analysis1, analysis2,
            extra_assertions=section
        )
        formula_direct = result_direct.formula
        
        # 両方が同じ SMT 式を生成することを確認
        assert formula_wrapper == formula_direct, \
            "Wrapper should produce the same formula as direct call"
        
        print("\n[TEST] build_with_abi_constraints wrapper is consistent with direct API")


class TestNoRsplit:
    """rsplit削除の検証テスト"""
    
    def test_no_rsplit_in_builder(self):
        """FormulaBuilder の ABI 関連メソッドに rsplit が使われていないことを確認"""
        from scripts.function_tracer_pcode.equivalence.formula.builder import FormulaBuilder
        
        builder = FormulaBuilder(debug=False)
        
        assert 'rsplit' not in builder.build_abi_constraints.__code__.co_names, \
            "build_abi_constraints should not call rsplit"
        
        assert 'rsplit' not in builder.build_with_abi_constraints.__code__.co_names, \
            "build_with_abi_constraints should not call rsplit"
        
        assert 'rsplit' not in builder.build_equivalence_formula_extended.__code__.co_names, \
            "build_equivalence_formula_extended should not call rsplit"
        
        assert 'rsplit' not in builder.build_abi_assertion_section.__code__.co_names, \
            "build_abi_assertion_section should not call rsplit"
        
        print("\n[TEST] No rsplit calls found in FormulaBuilder methods (bytecode check)")


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


class TestCheckerABIRetryIntegration:
    """checker._retry_with_abi_constraints() 経由の integration test"""
    
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
            
            # ★ 追加: run_parallel() が呼ばれたことを確認
            assert mock_solver.called, "run_parallel should be called (debug=False)"
        
        # 結果検証
        assert result.is_equivalent is True
        assert result.smt_formula is not None
        
        # 生成された SMT 式に ABI 制約が含まれることを確認
        assert "MIPS64 ABI constraints" in result.smt_formula
        assert "x_1" in result.smt_formula
        assert "x_2" in result.smt_formula
        assert "sign_extend" in result.smt_formula
        
        # (check-sat) の前にABI制約があることを確認
        lines = result.smt_formula.split('\n')
        check_sat_index = -1
        abi_section_index = -1
        
        for i, line in enumerate(lines):
            if '(check-sat)' in line:
                check_sat_index = i
            if 'MIPS64 ABI constraints' in line:
                abi_section_index = i
        
        assert check_sat_index >= 0
        assert abi_section_index >= 0
        assert abi_section_index < check_sat_index, \
            "ABI constraints should be before (check-sat)"
        
        print("\n[TEST] _retry_with_abi_constraints uses correct FormulaBuilder path")
        print(f"  - build_abi_assertion_section called: {spy_section.call_count} time(s)")
        print(f"  - build_equivalence_formula_extended called with extra_assertions")
        print(f"  - run_parallel called (debug=False mode)")


class TestPublicAPIWrappers:
    """公開 API wrapper の一貫性テスト"""
    
    def test_build_equivalence_formula_with_extra_assertions(self):
        """build_equivalence_formula が extra_assertions をサポートすることを確認"""
        builder = FormulaBuilder(debug=False)
        
        analysis1 = FunctionReturnAnalysis(
            function_name="func1",
            entry_point="0x00401000",
            parameters=[{"name": "x", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression(ExpressionType.PARAMETER, name="x", size=4)
                )
            ]
        )
        
        analysis2 = FunctionReturnAnalysis(
            function_name="func2",
            entry_point="0x00402000",
            parameters=[{"name": "y", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=Expression(ExpressionType.PARAMETER, name="y", size=4)
                )
            ]
        )
        
        extra_assertions = [
            "; Test constraint",
            "(assert (bvult x_1 (_ bv100 32)))"
        ]
        
        # build_equivalence_formula 経由（タプル戻り値）
        formula, return_var1, return_var2 = builder.build_equivalence_formula(
            analysis1, analysis2,
            extra_assertions=extra_assertions
        )
        
        # 戻り値の型を確認
        assert isinstance(formula, str), "formula should be str"
        assert isinstance(return_var1, str), "return_var1 should be str"
        assert isinstance(return_var2, str), "return_var2 should be str"
        
        # 戻り値の内容を確認
        assert return_var1 == "return_1"
        assert return_var2 == "return_2"
        
        # extra_assertions が含まれることを確認
        assert "Test constraint" in formula
        assert "(assert (bvult x_1 (_ bv100 32)))" in formula
        
        # (check-sat) の前にあることを確認
        lines = formula.split('\n')
        check_sat_index = -1
        constraint_index = -1
        
        for i, line in enumerate(lines):
            if '(check-sat)' in line:
                check_sat_index = i
            if 'Test constraint' in line:
                constraint_index = i
        
        assert check_sat_index >= 0
        assert constraint_index >= 0
        assert constraint_index < check_sat_index
        
        print("\n[TEST] build_equivalence_formula wrapper supports extra_assertions")
    
    def test_build_equivalence_formula_wrapper_consistency(self):
        """build_equivalence_formula が build_equivalence_formula_extended と一貫性があることを確認"""
        from unittest.mock import patch
        
        builder = FormulaBuilder(debug=False)
        
        analysis1 = FunctionReturnAnalysis(
            function_name="func1",
            entry_point="0x00401000",
            parameters=[{"name": "p", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression(ExpressionType.PARAMETER, name="p", size=4)
                )
            ]
        )
        
        analysis2 = FunctionReturnAnalysis(
            function_name="func2",
            entry_point="0x00402000",
            parameters=[{"name": "q", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=Expression(ExpressionType.PARAMETER, name="q", size=4)
                )
            ]
        )
        
        extra_assertions = [
            "; Wrapper test",
            "(assert (= p_1 q_2))"
        ]
        
        # build_equivalence_formula_extended を spy
        with patch.object(builder, 'build_equivalence_formula_extended',
                         wraps=builder.build_equivalence_formula_extended) as spy_extended:
            
            formula, return_var1, return_var2 = builder.build_equivalence_formula(
                analysis1, analysis2,
                func1_suffix="_1",
                func2_suffix="_2",
                extra_assertions=extra_assertions
            )
            
            # build_equivalence_formula_extended が呼ばれたことを確認
            assert spy_extended.called, "build_equivalence_formula_extended should be called"
            
            # ★ 修正: 位置引数として渡されることを確認
            call_args = spy_extended.call_args
            assert call_args.args[0] is analysis1, "First arg should be analysis1"
            assert call_args.args[1] is analysis2, "Second arg should be analysis2"
            assert call_args.args[2] == "_1", "Third arg should be func1_suffix='_1'"
            assert call_args.args[3] == "_2", "Fourth arg should be func2_suffix='_2'"
            assert call_args.kwargs.get("extra_assertions") == extra_assertions, \
                "extra_assertions should be passed as keyword argument"
        
        # 戻り値が正しいことを確認
        assert formula is not None
        assert return_var1 == "return_1"
        assert return_var2 == "return_2"
        
        # extended 版を直接呼んだ結果と一貫性があることを確認
        result_extended = builder.build_equivalence_formula_extended(
            analysis1, analysis2,
            func1_suffix="_1",
            func2_suffix="_2",
            extra_assertions=extra_assertions
        )
        
        assert formula == result_extended.formula, \
            "Wrapper should produce the same formula as direct extended call"
        assert return_var1 == result_extended.return_var1
        assert return_var2 == result_extended.return_var2
        
        print("\n[TEST] build_equivalence_formula wrapper is consistent with extended version")
        print(f"  - Verified positional args: analysis1, analysis2, '_1', '_2'")
        print(f"  - Verified keyword arg: extra_assertions")


class TestSharedFormulaContext:
    """FormulaBuilder 内の共有 context/header 構築の回帰テスト"""

    @staticmethod
    def _build_simple_analyses():
        analysis1 = FunctionReturnAnalysis(
            function_name="func1",
            entry_point="0x00401000",
            parameters=[{"name": "x", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression(ExpressionType.PARAMETER, name="x", size=4)
                )
            ]
        )

        analysis2 = FunctionReturnAnalysis(
            function_name="func2",
            entry_point="0x00402000",
            parameters=[{"name": "y", "size": 4, "index": 0, "is_signed": True}],
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=Expression(ExpressionType.PARAMETER, name="y", size=4)
                )
            ]
        )

        return analysis1, analysis2

    def test_build_base_context_reuses_extended_header_context(self):
        """build_base_context と extended 版が同じ header/context を共有することを確認"""
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

        print("\n[TEST] build_base_context shares the same header/context as extended builder")

    def test_build_base_context_preserves_debug_silence(self):
        """build_base_context では debug 情報を増やさず、extended 版のみ詳細出力することを確認"""
        from unittest.mock import patch

        builder = FormulaBuilder(debug=True, exclude_ub=False)
        analysis1, analysis2 = self._build_simple_analyses()

        with patch.object(builder, "_print_debug_info") as spy_debug:
            builder.build_base_context(analysis1, analysis2)
            spy_debug.assert_not_called()

            builder.build_equivalence_formula_extended(analysis1, analysis2)
            spy_debug.assert_called_once()

        print("\n[TEST] shared context helper preserves previous debug behavior")

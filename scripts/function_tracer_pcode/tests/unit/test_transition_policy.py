# -*- coding: utf-8 -*-
"""Phase遷移ポリシーの回帰テスト"""

import pytest
from unittest.mock import Mock

from scripts.function_tracer_pcode.equivalence.phases.handler import PhaseHandler, PhaseContext
from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixerConfig, TypeFixResult
from scripts.function_tracer_pcode.model import Expression, ReturnInfo
from scripts.function_tracer_pcode.smt import SolverStatus

# ★ [P3] sys.path操作はconftest.pyで一元化されているため不要
from conftest import create_mock_result, create_mock_analysis


class TestPhaseTransitionPolicy:
    """Phase遷移ルールのテスト"""
    
    def test_phase0_equivalent_stops_immediately(self):
        """Phase 0でEQUIVALENT → 即終了（リトライなし）"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        result = create_mock_result(is_equivalent=True, solver_status=SolverStatus.UNSAT)
        
        should_retry = handler.should_retry(result)
        assert should_retry is False, "UNSAT result should not trigger retry"
        
        reason = handler.get_retry_reason(result)
        assert "EQUIVALENT" in reason or reason == "EQUIVALENT (no retry needed)"
    
    def test_phase0_sat_stops_immediately(self):
        """★ [P1] Phase 0でSAT → 即終了（仕様に準拠）"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        result = create_mock_result(is_equivalent=False, solver_status=SolverStatus.SAT)
        
        # ★ 修正: SAT時は原則リトライ禁止（仕様に準拠）
        should_retry = handler.should_retry(result)
        assert should_retry is False, "SAT should stop retry immediately (spec compliance)"
        
        reason = handler.get_retry_reason(result)
        assert "NOT EQUIVALENT" in reason or reason == "NOT EQUIVALENT"
    
    def test_phase0_unknown_allows_retry(self):
        """Phase 0でUNKNOWN → リトライ許可"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        result = create_mock_result(is_equivalent=None, solver_status=SolverStatus.UNKNOWN)
        
        should_retry = handler.should_retry(result)
        assert should_retry is True, "UNKNOWN should trigger retry"
        
        reason = handler.get_retry_reason(result)
        assert reason == "UNKNOWN"
    
    def test_phase0_timeout_allows_retry(self):
        """Phase 0でTIMEOUT → リトライ許可"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        result = create_mock_result(is_equivalent=None, solver_status=SolverStatus.TIMEOUT)
        
        should_retry = handler.should_retry(result)
        assert should_retry is True, "TIMEOUT should trigger retry"
        
        assert result.is_timeout() is True
    
    def test_critical_error_stops_retry(self):
        """致命的エラー → リトライ禁止"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        result = create_mock_result(
            is_equivalent=None,
            error_message="Function 'test_func' not found in binary"
        )
        
        has_error = result.has_critical_error()
        assert has_error is True, "Function not found should be critical"
        
        should_retry = handler.should_retry(result)
        assert should_retry is False, "Critical error should stop retry"
    
    def test_phase1_signedness_fix_execution(self, mock_program_x86):
        """Phase 1: 符号性修正の実行条件"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        # ★ [P1修正] unsigned型 + signed証拠 の組み合わせ
        # should_fix_return_to_signed() は unsigned型のみを対象とする
        analysis = create_mock_analysis(
            function_name="test_func",
            return_type="unsigned int",  # ★ "undefined" から "unsigned int" に変更
            signedness="signed"
        )
        
        # Phase 1が実行されるかチェック
        assert analysis.should_fix_return_to_signed() is True, (
            f"Expected True for unsigned type with signed evidence, "
            f"got return_type={analysis.return_type}, "
            f"signedness={analysis.signedness_result.signedness if analysis.signedness_result else None}"
        )
        
        # TypeFixerをモック化
        type_fixer = Mock()
        type_fixer.fix_function_signature_by_name = Mock(return_value=(True, False))
        
        ctx = PhaseContext(
            program1=mock_program_x86,
            program2=mock_program_x86,
            function_name1="test_func",
            function_name2="test_func",
            binary1_name="binary1",
            binary2_name="binary2",
            decompile_timeout=60,
            save_formula=False,
            type_fix_result=TypeFixResult(),
            original_signature1=None,
            original_signature2=None,
            analysis1=analysis,
            analysis2=None
        )
        
        # ★ 修正: タプルアンパッキング + changed1/changed2 の検証
        applied, changed1, changed2 = handler.run_phase1_signedness_fix(ctx, type_fixer, type_fixer)
        assert applied is True, "Signedness fix should be applied"
        assert changed1 is True, "binary1 should be changed"
        assert changed2 is False, "binary2 should NOT be changed (analysis2 is None)"
        assert ctx.type_fix_result.signedness_fixed_binary1 is True
    
    def test_phase1_skipped_if_no_signedness_info(self, mock_program_x86):
        """Phase 1: 符号性情報なし → スキップ"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        analysis = create_mock_analysis(
            function_name="test_func",
            return_type="int"
        )
        
        assert analysis.should_fix_return_to_signed() is False
        
        type_fixer = Mock()
        
        ctx = PhaseContext(
            program1=mock_program_x86,
            program2=mock_program_x86,
            function_name1="test_func",
            function_name2="test_func",
            binary1_name="binary1",
            binary2_name="binary2",
            decompile_timeout=60,
            save_formula=False,
            type_fix_result=TypeFixResult(),
            original_signature1=None,
            original_signature2=None,
            analysis1=analysis,
            analysis2=None
        )
        
        # ★ 修正: タプルアンパッキング + changed1/changed2 の検証
        applied, changed1, changed2 = handler.run_phase1_signedness_fix(ctx, type_fixer, type_fixer)
        assert applied is False, "Phase 1 should be skipped"
        assert changed1 is False, "binary1 should NOT be changed"
        assert changed2 is False, "binary2 should NOT be changed"
    
    def test_phase2_pattern_match_execution(self, mock_program_x86):
        """Phase 2: パターンマッチ型修正の実行条件"""
        config = TypeFixerConfig()
        handler = PhaseHandler(config, debug=True)
        
        analysis = create_mock_analysis(
            function_name="test_func",
            return_type="undefined4"
        )
        
        should_fix = handler.should_fix_return_type(analysis)
        assert should_fix is True, "Pattern match should trigger fix"
        
        type_fixer = Mock()
        type_fixer.fix_function_signature_by_name = Mock(return_value=(True, False))
        
        ctx = PhaseContext(
            program1=mock_program_x86,
            program2=mock_program_x86,
            function_name1="test_func",
            function_name2="test_func",
            binary1_name="binary1",
            binary2_name="binary2",
            decompile_timeout=60,
            save_formula=False,
            type_fix_result=TypeFixResult(),
            original_signature1=None,
            original_signature2=None,
            analysis1=analysis,
            analysis2=None
        )
        
        # ★ 修正: タプルアンパッキング + changed1/changed2 の検証
        applied, changed1, changed2 = handler.run_phase2_return_type_fix(ctx, type_fixer, type_fixer)
        assert applied is True, "Pattern fix should be applied"
        assert changed1 is True, "binary1 should be changed"
        assert changed2 is False, "binary2 should NOT be changed (analysis2 is None)"
        assert ctx.type_fix_result.return_type_fixed_binary1 is True

    def test_phase2_force_fixes_suspicious_void_return_when_counterpart_is_concrete(self, mock_program_x86):
        """片側が suspicious な void return に潰れた場合は、相手側の concrete return を根拠に戻り値型修正を試す"""
        config = TypeFixerConfig()
        handler = PhaseHandler(config, debug=True)

        concrete_analysis = create_mock_analysis(
            function_name="test_func",
            return_type="int",
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression.constant(1, 4),
                )
            ],
        )

        void_analysis = create_mock_analysis(
            function_name="test_func",
            return_type="void",
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=Expression.unknown("void"),
                )
            ],
        )
        void_analysis.unknown_event_count = 1
        void_analysis.unknown_event_reasons = ["call_out_of_scope"]

        assert handler.should_fix_return_type(void_analysis, concrete_analysis) is True

        type_fixer1 = Mock()
        type_fixer1.fix_function_signature_by_name = Mock(return_value=(False, False))
        type_fixer2 = Mock()
        type_fixer2.fix_function_signature_by_name = Mock(return_value=(True, False))

        ctx = PhaseContext(
            program1=mock_program_x86,
            program2=mock_program_x86,
            function_name1="test_func",
            function_name2="test_func",
            binary1_name="binary1",
            binary2_name="binary2",
            decompile_timeout=60,
            save_formula=False,
            type_fix_result=TypeFixResult(),
            original_signature1=None,
            original_signature2=None,
            analysis1=concrete_analysis,
            analysis2=void_analysis,
        )

        applied, changed1, changed2 = handler.run_phase2_return_type_fix(
            ctx,
            type_fixer1,
            type_fixer2,
        )

        assert applied is True
        assert changed1 is False
        assert changed2 is True
        assert ctx.type_fix_result.return_type_fixed_binary2 is True
        type_fixer2.fix_function_signature_by_name.assert_called_once()
        assert type_fixer2.fix_function_signature_by_name.call_args.kwargs["override_return_type_name"] == "int"

    def test_phase2_forces_nonvoid_artifact_return_to_counterpart_void(self, mock_program_x86):
        config = TypeFixerConfig()
        handler = PhaseHandler(config, debug=True)

        void_analysis = create_mock_analysis(
            function_name="sphbes",
            return_type="void",
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression.unknown("void"),
                )
            ],
        )
        nonvoid_artifact = create_mock_analysis(
            function_name="sphbes",
            return_type="ulong",
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=Expression.parameter("param_2", index=1, size=8),
                )
            ],
        )

        assert handler.should_fix_return_type(nonvoid_artifact, void_analysis) is True

        type_fixer1 = Mock()
        type_fixer1.fix_function_signature_by_name = Mock(return_value=(False, False))
        type_fixer2 = Mock()
        type_fixer2.fix_function_signature_by_name = Mock(return_value=(True, False))

        ctx = PhaseContext(
            program1=mock_program_x86,
            program2=mock_program_x86,
            function_name1="sphbes",
            function_name2="sphbes",
            binary1_name="binary1",
            binary2_name="binary2",
            decompile_timeout=60,
            save_formula=False,
            type_fix_result=TypeFixResult(),
            original_signature1=None,
            original_signature2=None,
            analysis1=void_analysis,
            analysis2=nonvoid_artifact,
        )

        applied, changed1, changed2 = handler.run_phase2_return_type_fix(
            ctx,
            type_fixer1,
            type_fixer2,
        )

        assert applied is True
        assert changed1 is False
        assert changed2 is True
        type_fixer2.fix_function_signature_by_name.assert_called_once()
        assert type_fixer2.fix_function_signature_by_name.call_args.kwargs["override_return_type_name"] == "void"

    def test_phase2_does_not_force_nonvoid_to_suspicious_counterpart_void(self, mock_program_x86):
        config = TypeFixerConfig()
        handler = PhaseHandler(config, debug=True)

        suspicious_void = create_mock_analysis(
            function_name="sphbes",
            return_type="void",
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression.unknown("void"),
                )
            ],
        )
        suspicious_void.unknown_event_count = 1
        suspicious_void.unknown_event_reasons = ["call_out_of_scope"]

        concrete_analysis = create_mock_analysis(
            function_name="sphbes",
            return_type="int",
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=Expression.constant(1, 4),
                )
            ],
        )

        assert handler.should_fix_return_type(concrete_analysis, suspicious_void, program=mock_program_x86) is False
        assert handler.should_fix_return_type(suspicious_void, concrete_analysis, program=mock_program_x86) is True

        type_fixer1 = Mock()
        type_fixer1.fix_function_signature_by_name = Mock(return_value=(True, False))
        type_fixer2 = Mock()
        type_fixer2.fix_function_signature_by_name = Mock(return_value=(True, False))

        ctx = PhaseContext(
            program1=mock_program_x86,
            program2=mock_program_x86,
            function_name1="sphbes",
            function_name2="sphbes",
            binary1_name="binary1",
            binary2_name="binary2",
            decompile_timeout=60,
            save_formula=False,
            type_fix_result=TypeFixResult(),
            original_signature1=None,
            original_signature2=None,
            analysis1=suspicious_void,
            analysis2=concrete_analysis,
        )

        applied, changed1, changed2 = handler.run_phase2_return_type_fix(
            ctx,
            type_fixer1,
            type_fixer2,
        )

        assert applied is True
        assert changed1 is True
        assert changed2 is False
        type_fixer1.fix_function_signature_by_name.assert_called_once()
        assert type_fixer1.fix_function_signature_by_name.call_args.kwargs["override_return_type_name"] == "int"
        type_fixer2.fix_function_signature_by_name.assert_not_called()

    def test_phase2_does_not_force_counterpart_void_across_different_function_names(self, mock_program_x86):
        config = TypeFixerConfig()
        handler = PhaseHandler(config, debug=True)

        void_analysis = create_mock_analysis(
            function_name="void_func",
            return_type="void",
            returns=[
                ReturnInfo(
                    address="0x00401000",
                    conditions=[],
                    value=Expression.unknown("void"),
                )
            ],
        )
        nonvoid_analysis = create_mock_analysis(
            function_name="returns_value",
            return_type="ulong",
            returns=[
                ReturnInfo(
                    address="0x00402000",
                    conditions=[],
                    value=Expression.parameter("param_1", index=0, size=8),
                )
            ],
        )

        assert handler.should_fix_return_type(nonvoid_analysis, void_analysis, program=mock_program_x86) is False
    
    def test_phase4a_mips64_condition(self, mock_program_mips64, mock_program_x86):
        """Phase 4-A: MIPS64バイナリが含まれる場合のみ実行"""
        handler = PhaseHandler(TypeFixerConfig(), debug=True)
        
        analysis_mips = create_mock_analysis(
            function_name="test_func",
            parameters=[{"name": "param_1", "data_type": "long"}]
        )
        
        analysis_x86 = create_mock_analysis(
            function_name="test_func",
            parameters=[{"name": "param_1", "data_type": "int"}]
        )
        
        should_apply = handler.mips64_handler.should_apply_fix(
            True, False, analysis_mips, analysis_x86
        )
        
        assert should_apply is not None

# -*- coding: utf-8 -*-
"""CLI の --no-retry-phases オプションのテスト"""

import pytest
from unittest.mock import Mock, patch, MagicMock
import argparse
import sys
import io


def test_default_retry_phases_enabled():
    """デフォルトでは recovery phases が有効"""
    from function_tracer_pcode.cli.main import parse_arguments
    
    # 最小限の引数でパース
    test_args = ['--equiv', 'binary1', 'binary2', '-f', 'test_func']
    
    with patch.object(sys, 'argv', ['main.py'] + test_args):
        args = parse_arguments()
        
        # --no-retry-phases が指定されていない → False
        assert getattr(args, 'no_retry_phases', False) == False
        
        # retry_with_type_fix のロジックを検証
        retry_with_type_fix = not getattr(args, 'no_retry_phases', False)
        assert retry_with_type_fix == True


def test_no_retry_phases_option():
    """--no-retry-phases が指定されたときは recovery phases が無効"""
    from function_tracer_pcode.cli.main import parse_arguments
    
    test_args = ['--equiv', 'binary1', 'binary2', '-f', 'test_func', '--no-retry-phases']
    
    with patch.object(sys, 'argv', ['main.py'] + test_args):
        args = parse_arguments()
        
        # --no-retry-phases が指定されている → True
        assert args.no_retry_phases == True
        
        # retry_with_type_fix のロジックを検証
        retry_with_type_fix = not getattr(args, 'no_retry_phases', False)
        assert retry_with_type_fix == False


def test_help_does_not_contain_retry_with_int():
    """help メッセージに --retry-with-int が含まれていないことを確認"""
    from function_tracer_pcode.cli.main import parse_arguments
    
    # ヘルプメッセージをキャプチャ
    test_args = ['--help']
    
    with patch.object(sys, 'argv', ['main.py'] + test_args):
        with patch('sys.stdout', new_callable=io.StringIO) as mock_stdout:
            try:
                parse_arguments()
            except SystemExit:
                pass  # --help は SystemExit を投げるので正常
            
            help_output = mock_stdout.getvalue()
            
            # --retry-with-int が含まれていないことを確認
            assert '--retry-with-int' not in help_output, \
                "Old --retry-with-int option found in help message"
            
            # --no-retry-phases が含まれていることを確認
            assert '--no-retry-phases' in help_output, \
                "--no-retry-phases option not found in help message"
            
            # Recovery phases の説明が含まれていることを確認
            assert 'Recovery phases' in help_output or 'recovery phases' in help_output, \
                "Recovery phases description not found in help message"
            
            print("\n[HELP CHECK] Verified: --retry-with-int removed, --no-retry-phases present")


def test_equiv_check_propagates_retry_flag():
    """run_equivalence_check() が retry_with_type_fix を正しく伝播することを確認"""
    from function_tracer_pcode.cli.main import run_equivalence_check
    from function_tracer_pcode.equivalence import EquivalenceChecker
    
    # Mock args
    mock_args = Mock()
    mock_args.equiv = ('binary1', 'binary2')
    mock_args.functions = ['test_func']
    mock_args.no_retry_phases = False  # デフォルト: recovery phases 有効
    mock_args.equiv_timeout = 10
    mock_args.timeout = 60
    mock_args.save_formula = False
    mock_args.debug = False
    mock_args.quiet = True
    mock_args.verbose = False
    mock_args.output = None
    mock_args.no_rewrite = False
    mock_args.rewrite_direction = 'to_modulo'
    mock_args.strategy = 'pairwise'
    mock_args.pairwise_timeout = 5
    mock_args.pairwise_timeout_hard = 30
    mock_args.pairwise_save_unknown = False
    
    # pyghidra を sys.modules に差し込む
    mock_pyghidra = MagicMock()
    mock_pyghidra.start = Mock()
    
    mock_program1 = MagicMock()
    mock_program2 = MagicMock()
    
    mock_result1 = MagicMock()
    mock_result1.getPrimaryDomainObject.return_value = mock_program1
    
    mock_result2 = MagicMock()
    mock_result2.getPrimaryDomainObject.return_value = mock_program2
    
    mock_loader1 = MagicMock()
    mock_loader1.load.return_value.__enter__.return_value = mock_result1
    mock_loader1.load.return_value.__exit__ = Mock(return_value=False)
    
    mock_loader2 = MagicMock()
    mock_loader2.load.return_value.__enter__.return_value = mock_result2
    mock_loader2.load.return_value.__exit__ = Mock(return_value=False)
    
    mock_program_loader = MagicMock()
    mock_program_loader.project.return_value.source.side_effect = [
        mock_loader1, mock_loader2
    ]
    mock_pyghidra.program_loader.return_value = mock_program_loader
    
    mock_project = MagicMock()
    mock_pyghidra.open_project.return_value.__enter__.return_value = mock_project
    mock_pyghidra.open_project.return_value.__exit__ = Mock(return_value=False)
    
    mock_pyghidra.analyze = Mock()
    
    # sys.modules に差し込む
    with patch.dict('sys.modules', {'pyghidra': mock_pyghidra}):
        with patch.object(EquivalenceChecker, 'check_from_binaries') as mock_check:
            # check_from_binaries が返す Mock 結果
            mock_equiv_result = Mock()
            mock_equiv_result.is_equivalent = True
            mock_equiv_result.to_string.return_value = "EQUIVALENT"
            mock_equiv_result.smt_formula = None
            mock_check.return_value = mock_equiv_result
            
            # run_equivalence_check を実行
            try:
                run_equivalence_check(mock_args)
            except SystemExit:
                pass  # sys.exit(0) が呼ばれる
            
            # check_from_binaries が retry_with_type_fix=True で呼ばれたことを確認
            mock_check.assert_called_once()
            call_kwargs = mock_check.call_args[1]
            assert call_kwargs['retry_with_type_fix'] == True
            
            print("\n[RETRY ENABLED] Verified: retry_with_type_fix=True propagated correctly")


def test_equiv_check_propagates_no_retry_flag():
    """run_equivalence_check() が --no-retry-phases を正しく伝播することを確認"""
    from function_tracer_pcode.cli.main import run_equivalence_check
    from function_tracer_pcode.equivalence import EquivalenceChecker
    
    # Mock args
    mock_args = Mock()
    mock_args.equiv = ('binary1', 'binary2')
    mock_args.functions = ['test_func']
    mock_args.no_retry_phases = True  # recovery phases 無効
    mock_args.equiv_timeout = 10
    mock_args.timeout = 60
    mock_args.save_formula = False
    mock_args.debug = False
    mock_args.quiet = True
    mock_args.verbose = False
    mock_args.output = None
    mock_args.no_rewrite = False
    mock_args.rewrite_direction = 'to_modulo'
    mock_args.strategy = 'pairwise'
    mock_args.pairwise_timeout = 5
    mock_args.pairwise_timeout_hard = 30
    mock_args.pairwise_save_unknown = False
    
    # pyghidra を sys.modules に差し込む
    mock_pyghidra = MagicMock()
    mock_pyghidra.start = Mock()
    
    mock_program1 = MagicMock()
    mock_program2 = MagicMock()
    
    mock_result1 = MagicMock()
    mock_result1.getPrimaryDomainObject.return_value = mock_program1
    
    mock_result2 = MagicMock()
    mock_result2.getPrimaryDomainObject.return_value = mock_program2
    
    mock_loader1 = MagicMock()
    mock_loader1.load.return_value.__enter__.return_value = mock_result1
    mock_loader1.load.return_value.__exit__ = Mock(return_value=False)
    
    mock_loader2 = MagicMock()
    mock_loader2.load.return_value.__enter__.return_value = mock_result2
    mock_loader2.load.return_value.__exit__ = Mock(return_value=False)
    
    mock_program_loader = MagicMock()
    mock_program_loader.project.return_value.source.side_effect = [
        mock_loader1, mock_loader2
    ]
    mock_pyghidra.program_loader.return_value = mock_program_loader
    
    mock_project = MagicMock()
    mock_pyghidra.open_project.return_value.__enter__.return_value = mock_project
    mock_pyghidra.open_project.return_value.__exit__ = Mock(return_value=False)
    
    mock_pyghidra.analyze = Mock()
    
    with patch.dict('sys.modules', {'pyghidra': mock_pyghidra}):
        with patch.object(EquivalenceChecker, 'check_from_binaries') as mock_check:
            mock_equiv_result = Mock()
            mock_equiv_result.is_equivalent = False
            mock_equiv_result.to_string.return_value = "NOT EQUIVALENT"
            mock_equiv_result.smt_formula = None
            mock_check.return_value = mock_equiv_result
            
            try:
                run_equivalence_check(mock_args)
            except SystemExit:
                pass
            
            # check_from_binaries が retry_with_type_fix=False で呼ばれたことを確認
            mock_check.assert_called_once()
            call_kwargs = mock_check.call_args[1]
            assert call_kwargs['retry_with_type_fix'] == False
            
            print("\n[RETRY DISABLED] Verified: retry_with_type_fix=False propagated correctly")


def test_cli_output_shows_retry_phases_status():
    """★ [最終修正] CLI 出力に recovery phases の状態が表示されることを確認"""
    from function_tracer_pcode.cli.main import run_equivalence_check
    
    mock_args = Mock()
    mock_args.equiv = ('binary1', 'binary2')
    mock_args.functions = ['test_func']
    mock_args.no_retry_phases = False  # 有効
    mock_args.equiv_timeout = 10
    mock_args.timeout = 60
    mock_args.save_formula = False
    mock_args.debug = False
    mock_args.quiet = False  # quiet を False にして出力をキャプチャ
    mock_args.verbose = False
    mock_args.output = None
    mock_args.no_rewrite = False
    mock_args.rewrite_direction = 'to_modulo'
    mock_args.strategy = 'pairwise'
    mock_args.pairwise_timeout = 5
    mock_args.pairwise_timeout_hard = 30
    mock_args.pairwise_save_unknown = False
    
    mock_pyghidra = MagicMock()
    mock_pyghidra.start = Mock()
    
    mock_program1 = MagicMock()
    mock_program2 = MagicMock()
    
    mock_result1 = MagicMock()
    mock_result1.getPrimaryDomainObject.return_value = mock_program1
    
    mock_result2 = MagicMock()
    mock_result2.getPrimaryDomainObject.return_value = mock_program2
    
    mock_loader1 = MagicMock()
    mock_loader1.load.return_value.__enter__.return_value = mock_result1
    mock_loader1.load.return_value.__exit__ = Mock(return_value=False)
    
    mock_loader2 = MagicMock()
    mock_loader2.load.return_value.__enter__.return_value = mock_result2
    mock_loader2.load.return_value.__exit__ = Mock(return_value=False)
    
    mock_program_loader = MagicMock()
    mock_program_loader.project.return_value.source.side_effect = [
        mock_loader1, mock_loader2
    ]
    mock_pyghidra.program_loader.return_value = mock_program_loader
    
    mock_project = MagicMock()
    mock_pyghidra.open_project.return_value.__enter__.return_value = mock_project
    mock_pyghidra.open_project.return_value.__exit__ = Mock(return_value=False)
    
    mock_pyghidra.analyze = Mock()
    
    with patch.dict('sys.modules', {'pyghidra': mock_pyghidra}):
        # ★ [修正] 正しいpatch先: function_tracer_pcode.equivalence.EquivalenceChecker
        with patch('function_tracer_pcode.equivalence.EquivalenceChecker') as MockEquivChecker:
            # EquivalenceChecker のインスタンスをモック化
            mock_checker = Mock()
            mock_checker.solver_runner = Mock()
            mock_checker.solver_runner.get_available_solvers.return_value = ['z3']
            
            mock_equiv_result = Mock()
            mock_equiv_result.is_equivalent = True
            mock_equiv_result.to_string.return_value = "EQUIVALENT"
            mock_equiv_result.smt_formula = None
            mock_checker.check_from_binaries = Mock(return_value=mock_equiv_result)
            
            MockEquivChecker.return_value = mock_checker
            
            with patch('sys.stdout', new_callable=io.StringIO) as mock_stdout:
                try:
                    run_equivalence_check(mock_args)
                except SystemExit:
                    pass
                
                output = mock_stdout.getvalue()
                
                # "Recovery phases: enabled" が出力されていることを確認
                assert 'Recovery phases: enabled' in output, \
                    f"Expected 'Recovery phases: enabled' in output, got:\n{output}"
                
                print("\n[OUTPUT CHECK] Verified: 'Recovery phases: enabled' displayed")


def test_cli_output_shows_retry_phases_disabled():
    """★ [最終修正] CLI 出力に recovery phases が無効であることが表示されることを確認"""
    from function_tracer_pcode.cli.main import run_equivalence_check
    
    mock_args = Mock()
    mock_args.equiv = ('binary1', 'binary2')
    mock_args.functions = ['test_func']
    mock_args.no_retry_phases = True  # 無効
    mock_args.equiv_timeout = 10
    mock_args.timeout = 60
    mock_args.save_formula = False
    mock_args.debug = False
    mock_args.quiet = False
    mock_args.verbose = False
    mock_args.output = None
    mock_args.no_rewrite = False
    mock_args.rewrite_direction = 'to_modulo'
    mock_args.strategy = 'pairwise'
    mock_args.pairwise_timeout = 5
    mock_args.pairwise_timeout_hard = 30
    mock_args.pairwise_save_unknown = False
    
    mock_pyghidra = MagicMock()
    mock_pyghidra.start = Mock()
    
    mock_program1 = MagicMock()
    mock_program2 = MagicMock()
    
    mock_result1 = MagicMock()
    mock_result1.getPrimaryDomainObject.return_value = mock_program1
    
    mock_result2 = MagicMock()
    mock_result2.getPrimaryDomainObject.return_value = mock_program2
    
    mock_loader1 = MagicMock()
    mock_loader1.load.return_value.__enter__.return_value = mock_result1
    mock_loader1.load.return_value.__exit__ = Mock(return_value=False)
    
    mock_loader2 = MagicMock()
    mock_loader2.load.return_value.__enter__.return_value = mock_result2
    mock_loader2.load.return_value.__exit__ = Mock(return_value=False)
    
    mock_program_loader = MagicMock()
    mock_program_loader.project.return_value.source.side_effect = [
        mock_loader1, mock_loader2
    ]
    mock_pyghidra.program_loader.return_value = mock_program_loader
    
    mock_project = MagicMock()
    mock_pyghidra.open_project.return_value.__enter__.return_value = mock_project
    mock_pyghidra.open_project.return_value.__exit__ = Mock(return_value=False)
    
    mock_pyghidra.analyze = Mock()
    
    with patch.dict('sys.modules', {'pyghidra': mock_pyghidra}):
        # ★ [修正] 正しいpatch先: function_tracer_pcode.equivalence.EquivalenceChecker
        with patch('function_tracer_pcode.equivalence.EquivalenceChecker') as MockEquivChecker:
            mock_checker = Mock()
            mock_checker.solver_runner = Mock()
            mock_checker.solver_runner.get_available_solvers.return_value = ['z3']
            
            mock_equiv_result = Mock()
            mock_equiv_result.is_equivalent = False
            mock_equiv_result.to_string.return_value = "NOT EQUIVALENT"
            mock_equiv_result.smt_formula = None
            mock_checker.check_from_binaries = Mock(return_value=mock_equiv_result)
            
            MockEquivChecker.return_value = mock_checker
            
            with patch('sys.stdout', new_callable=io.StringIO) as mock_stdout:
                try:
                    run_equivalence_check(mock_args)
                except SystemExit:
                    pass
                
                output = mock_stdout.getvalue()
                
                # "Recovery phases: disabled" が出力されていることを確認
                assert 'Recovery phases: disabled' in output, \
                    f"Expected 'Recovery phases: disabled' in output, got:\n{output}"
                
                print("\n[OUTPUT CHECK] Verified: 'Recovery phases: disabled' displayed")
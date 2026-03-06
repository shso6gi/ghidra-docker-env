# -*- coding: utf-8 -*-
"""pytest共通設定・フィクスチャ"""

import sys
from pathlib import Path

# ★ [P3] sys.path操作を一元化：conftest.pyで一度だけ設定
workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

import pytest
import yaml
from typing import Dict, Any, List, Optional
from dataclasses import dataclass
from unittest.mock import Mock

# 完全なパッケージパスでインポート
from scripts.function_tracer_pcode.equivalence.result import EquivalenceResult
from scripts.function_tracer_pcode.equivalence.typing.fixer import TypeFixResult
from scripts.function_tracer_pcode.smt import ParallelResult, SolverResult, SolverStatus
from scripts.function_tracer_pcode.model import (
    FunctionReturnAnalysis, 
    ReturnInfo, 
    Expression, 
    ExpressionType,
)
from scripts.function_tracer_pcode.model.analysis import SignednessResult

# ★ 追加: フィクスチャではない通常の関数として定義
def load_golden_cases() -> List[Dict[str, Any]]:
    """ゴールデンケースをYAMLから読み込み（通常の関数）"""
    yaml_path = Path(__file__).parent / "fixtures" / "cases.yml"
    with open(yaml_path, 'r', encoding='utf-8') as f:
        data = yaml.safe_load(f)
    return data['test_cases']

@pytest.fixture(scope="session")
def golden_cases():
    """ゴールデンケースをYAMLから読み込み（セッション全体で1回のみ）"""
    return load_golden_cases()  # 通常の関数を呼び出す


@pytest.fixture(scope="session")
def golden_cases_by_id(golden_cases):
    """★ [P3] ID検索用の辞書を提供（高速化）"""
    return {case['id']: case for case in golden_cases}


@dataclass
class MockProgram:
    """モックバイナリプログラム（ArchitectureDetectorと整合性を保つ）"""
    name: str
    architecture: str = "x86:LE:64:default"
    
    def getName(self):
        return self.name
    
    def getLanguage(self):
        """★ [P1] ArchitectureDetectorが参照する形式に完全一致"""
        arch = self.architecture
        
        class MockLanguageID:
            def getIdAsString(self):
                return arch
            
            def __str__(self):
                return arch
        
        class MockProcessor:
            def toString(self):
                # "MIPS:BE:64:64-32addr" -> "MIPS"
                return arch.split(':')[0]
            
            def __str__(self):
                return arch.split(':')[0]
        
        class MockLanguage:
            def getProcessor(self):
                return MockProcessor()
            
            def getLanguageID(self):
                return MockLanguageID()
        
        return MockLanguage()


def create_mock_analysis(
    function_name: str,
    return_type: str = "int",
    parameters: Optional[List[Dict[str, Any]]] = None,
    returns: Optional[List[ReturnInfo]] = None,
    signedness: Optional[str] = None
) -> FunctionReturnAnalysis:
    """モック解析結果を作成"""
    if parameters is None:
        parameters = []
    
    if returns is None:
        returns = [
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.PARAMETER, name="param_1")
            )
        ]
    
    analysis = FunctionReturnAnalysis(
        function_name=function_name,
        entry_point="0x00401000",
        parameters=parameters,
        returns=returns
    )
    
    analysis.return_type = return_type
    
    if signedness:
        analysis.signedness_result = SignednessResult(signedness=signedness)
    
    return analysis


def create_mock_result(
    is_equivalent: Optional[bool],
    solver_status: Optional[SolverStatus] = None,
    elapsed_time: float = 0.1,
    counterexample: Optional[Dict] = None,
    error_message: Optional[str] = None
) -> EquivalenceResult:
    """モック判定結果を作成"""
    if solver_status is None:
        if is_equivalent is True:
            solver_status = SolverStatus.UNSAT
        elif is_equivalent is False:
            solver_status = SolverStatus.SAT
        else:
            solver_status = SolverStatus.UNKNOWN
    
    solver_result = SolverResult(
        solver_name="mock_solver",
        status=solver_status,
        elapsed_time=elapsed_time,
        model=counterexample
    )
    
    parallel_result = ParallelResult(results=[solver_result])
    
    result = EquivalenceResult(
        is_equivalent=is_equivalent,
        function1_name="func1",
        function2_name="func2",
        binary1_name="binary1",
        binary2_name="binary2",
        solver_results=parallel_result,
        type_fix_result=TypeFixResult()
    )
    
    if error_message:
        result.error_message = error_message
    
    return result


@pytest.fixture
def mock_program_x86():
    """x86バイナリのモック"""
    return MockProgram(name="test_x86.exe", architecture="x86:LE:64:default")


@pytest.fixture
def mock_program_mips64():
    """★ [P1] MIPS64バイナリのモック（ArchitectureDetectorで確実に検出される）"""
    return MockProgram(name="test_mips64.elf", architecture="MIPS:BE:64:64-32addr")


@pytest.fixture
def solver_status_map():
    """★ YAML用のステータスマッピング"""
    return {
        "SAT": SolverStatus.SAT,
        "UNSAT": SolverStatus.UNSAT,
        "UNKNOWN": SolverStatus.UNKNOWN,
        "TIMEOUT": SolverStatus.TIMEOUT,
    }


@pytest.fixture
def is_equiv_map():
    """★ YAML用の等価性マッピング"""
    return {
        "SAT": False,
        "UNSAT": True,
        "UNKNOWN": None,
        "TIMEOUT": None,
    }
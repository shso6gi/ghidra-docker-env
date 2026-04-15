# -*- coding: utf-8 -*-
"""pytest共通設定・フィクスチャ"""

import sys
import importlib
from pathlib import Path
from typing import Any, Dict, List, Optional, cast

# ★ [P3] sys.path操作を一元化：conftest.pyで一度だけ設定
workspace_root = Path(__file__).parent.parent.parent.parent
if str(workspace_root) not in sys.path:
    sys.path.insert(0, str(workspace_root))

pytest = cast(Any, importlib.import_module("pytest"))
yaml = cast(Any, importlib.import_module("yaml"))
from dataclasses import dataclass, field
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


# ============================================================================
# ★ [P3] Helper Functions (not fixtures) - IDE安全・再利用性向上
# ============================================================================

def load_golden_cases() -> List[Dict[str, Any]]:
    """ゴールデンケースをYAMLから読み込み（通常の関数）"""
    yaml_path = Path(__file__).parent / "fixtures" / "cases.yml"
    with open(yaml_path, 'r', encoding='utf-8') as f:
        data = yaml.safe_load(f)
    return data['test_cases']


class MockDataOrganization:
    def __init__(self, *, int_size=4, long_size=8, long_long_size=8, short_size=2, char_size=1, pointer_size=8):
        self._int_size = int_size
        self._long_size = long_size
        self._long_long_size = long_long_size
        self._short_size = short_size
        self._char_size = char_size
        self._pointer_size = pointer_size

    def getIntegerSize(self):
        return self._int_size

    def getLongSize(self):
        return self._long_size

    def getLongLongSize(self):
        return self._long_long_size

    def getShortSize(self):
        return self._short_size

    def getCharSize(self):
        return self._char_size

    def getPointerSize(self):
        return self._pointer_size


class MockDataType:
    def __init__(self, name: str, length: int, is_signed: bool, path: Optional[str] = None):
        self._name = name
        self._length = length
        self._is_signed = is_signed
        self._path = path or f"/builtin/{name}"
        self._data_type_manager = None
        self._opposite = None

    def getName(self):
        return self._name

    def getLength(self):
        return self._length

    def isSigned(self):
        return self._is_signed

    def getDataTypePath(self):
        return self._path

    def getDataTypeManager(self):
        return self._data_type_manager

    def setDataTypeManager(self, data_type_manager):
        self._data_type_manager = data_type_manager

    def getOppositeSignednessDataType(self):
        return self._opposite

    def setOppositeSignednessDataType(self, opposite):
        self._opposite = opposite

    def isEquivalent(self, other):
        return str(self.getDataTypePath()) == str(other.getDataTypePath())

    def isUndefined(self):
        return self._name.startswith("undefined")

    def __str__(self):
        return self._name


class MockVoidDataType(MockDataType):
    def __init__(self):
        super().__init__("void", 0, False, "/builtin/void")


class MockDataTypeManager:
    def __init__(self, architecture: str = "x86:LE:64:default"):
        pointer_size = 8 if ":64:" in architecture else 4
        self._data_organization = MockDataOrganization(pointer_size=pointer_size)
        self._data_types = {}
        self._register_builtins()

    def _add(self, data_type: MockDataType):
        data_type.setDataTypeManager(self)
        self._data_types[data_type.getName()] = data_type
        self._data_types[f"/{data_type.getName()}"] = data_type
        self._data_types[data_type.getDataTypePath()] = data_type
        return data_type

    def _add_signed_pair(self, signed_name: str, unsigned_name: str, size: int):
        signed_dt = self._add(MockDataType(signed_name, size, True))
        unsigned_dt = self._add(MockDataType(unsigned_name, size, False))
        signed_dt.setOppositeSignednessDataType(unsigned_dt)
        unsigned_dt.setOppositeSignednessDataType(signed_dt)

    def _register_builtins(self):
        self._add(MockVoidDataType())
        self._add_signed_pair("char", "unsigned char", 1)
        self._add_signed_pair("short", "unsigned short", 2)
        self._add_signed_pair("int", "unsigned int", 4)
        self._add_signed_pair("long", "unsigned long", 8)
        self._add_signed_pair("long long", "unsigned long long", 8)
        self._add_signed_pair("int8_t", "uint8_t", 1)
        self._add_signed_pair("int16_t", "uint16_t", 2)
        self._add_signed_pair("int32_t", "uint32_t", 4)
        self._add_signed_pair("int64_t", "uint64_t", 8)
        self._add(MockDataType("undefined1", 1, False, "/builtin/undefined1"))
        self._add(MockDataType("undefined2", 2, False, "/builtin/undefined2"))
        self._add(MockDataType("undefined4", 4, False, "/builtin/undefined4"))
        self._add(MockDataType("undefined8", 8, False, "/builtin/undefined8"))
        self._alias("uchar", "unsigned char")
        self._alias("ushort", "unsigned short")
        self._alias("uint", "unsigned int")
        self._alias("ulong", "unsigned long")
        self._alias("ulonglong", "unsigned long long")
        self._alias("longlong", "long long")
        self._alias("bool", "unsigned char")

    def _alias(self, alias_name: str, canonical_name: str):
        target = self._data_types.get(canonical_name)
        if target is None:
            return
        self._data_types[alias_name] = target
        self._data_types[f"/{alias_name}"] = target

    def getDataType(self, name):
        return self._data_types.get(name)

    def findDataType(self, name):
        return self._data_types.get(name)

    def getDataOrganization(self):
        return self._data_organization


def create_mock_data_type_manager(architecture: str = "x86:LE:64:default") -> MockDataTypeManager:
    return MockDataTypeManager(architecture=architecture)


def resolve_mock_data_type(type_name: Optional[str], data_type_manager: Optional[MockDataTypeManager] = None):
    if not type_name:
        return None
    dtm = data_type_manager or create_mock_data_type_manager()
    return dtm.getDataType(type_name) or dtm.findDataType(type_name) or dtm.getDataType(f"/{type_name}")


@dataclass
class MockProgram:
    """モックバイナリプログラム（ArchitectureDetectorと整合性を保つ）"""
    name: str
    architecture: str = "x86:LE:64:default"
    data_type_manager: Optional[MockDataTypeManager] = None

    def __post_init__(self):
        self.data_type_manager = self.data_type_manager or create_mock_data_type_manager(self.architecture)
    
    def getName(self):
        return self.name

    def getDataTypeManager(self):
        return self.data_type_manager
    
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
    """モック解析結果を作成
    
    ★ [P1] 修正: パラメータ情報を正しく設定してP4B検証を可能にする
    """
    if parameters is None:
        parameters = []
    dtm = create_mock_data_type_manager()
    
    if returns is None:
        returns = [
            ReturnInfo(
                address="0x00401000",
                conditions=[],
                value=Expression(ExpressionType.PARAMETER, name="param_1")
            )
        ]
    
    normalized_parameters: List[Dict[str, Any]] = []
    for index, param in enumerate(parameters):
        normalized = dict(param)
        data_type_name = normalized.get("data_type")
        data_type_obj = normalized.get("data_type_obj") or resolve_mock_data_type(data_type_name, dtm)
        normalized["data_type_obj"] = data_type_obj
        normalized.setdefault("index", index)
        if data_type_obj is not None:
            normalized.setdefault("size", int(data_type_obj.getLength()))
            normalized.setdefault("is_signed", bool(data_type_obj.isSigned()))
        normalized_parameters.append(normalized)

    analysis = FunctionReturnAnalysis(
        function_name=function_name,
        entry_point="0x00401000",
        parameters=normalized_parameters,
        returns=returns,
    )
    
    analysis.return_type = return_type
    analysis.return_type_obj = resolve_mock_data_type(return_type, dtm)
    
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
    
    # ★ [P1] 追加: counterexampleがあればFormattedCounterexampleも設定
    if counterexample:
        from scripts.function_tracer_pcode.equivalence.counterexample import FormattedCounterexample
        result.counterexample = FormattedCounterexample(
            parameters={k: hex(v) if isinstance(v, int) else str(v) for k, v in counterexample.items()},
            return_value1=None,
            return_value2=None,
            raw_model=counterexample
        )
    
    return result


# ============================================================================
# ★ Pytest Fixtures
# ============================================================================

@pytest.fixture(scope="session")
def golden_cases():
    """ゴールデンケースをYAMLから読み込み（セッション全体で1回のみ）"""
    return load_golden_cases()


@pytest.fixture(scope="session")
def golden_cases_by_id(golden_cases):
    """★ [P3] ID検索用の辞書を提供（高速化）"""
    return {case['id']: case for case in golden_cases}


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

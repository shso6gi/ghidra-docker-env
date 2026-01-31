# -*- coding: utf-8 -*-
"""型修正モジュール - 等価性判定のリトライ時に使用"""

from typing import List, Set, Optional, Tuple, Dict, Any
from dataclasses import dataclass, field
from contextlib import contextmanager


@dataclass
class TypeFixerConfig:
    """
    型修正の設定
    
    Attributes:
        target_patterns: 修正対象とする型名のパターン（小文字で比較）
        replacement_type_name: 置換先の型名（ログ用）
    """
    target_patterns: Set[str] = field(default_factory=lambda: {
        "longlong",
        "long long", 
        "undefined",
        "undefined1",
        "undefined2",
        "undefined4",
        "undefined8",
        "ulong",
    })
    replacement_type_name: str = "int"
    
    def add_pattern(self, pattern: str) -> None:
        """修正対象パターンを追加"""
        self.target_patterns.add(pattern.lower())
    
    def remove_pattern(self, pattern: str) -> None:
        """修正対象パターンを削除"""
        self.target_patterns.discard(pattern.lower())
    
    def set_patterns(self, patterns: Set[str]) -> None:
        """修正対象パターンを置き換え"""
        self.target_patterns = {p.lower() for p in patterns}


class TypeFixer:
    """
    関数の型を修正するクラス
    """
    
    def __init__(
        self,
        program,
        config: Optional[TypeFixerConfig] = None,
        debug: bool = False
    ):
        self.program = program
        self.config = config or TypeFixerConfig()
        self.debug = debug
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[TypeFixer] {msg}")
    
    @contextmanager
    def _transaction(self, description: str):
        """Ghidraトランザクションのコンテキストマネージャ"""
        tx_id = self.program.startTransaction(description)
        self._debug_print(f"Started transaction: {description} (id={tx_id})")
        try:
            yield tx_id
            self.program.endTransaction(tx_id, True)
            self._debug_print(f"Committed transaction: {tx_id}")
        except Exception as e:
            self.program.endTransaction(tx_id, False)
            self._debug_print(f"Rolled back transaction: {tx_id} due to {e}")
            raise
    
    def _should_fix_type(self, type_str: Optional[str]) -> bool:
        """型を修正すべきか判定"""
        if type_str is None:
            return False
        
        type_lower = type_str.lower().strip()
        
        for pattern in self.config.target_patterns:
            if pattern in type_lower:
                self._debug_print(f"Type '{type_str}' matches pattern '{pattern}'")
                return True
        
        return False
    
    def _get_replacement_data_type(self):
        """置換先のデータ型を取得"""
        from ghidra.program.model.data import IntegerDataType # type: ignore[import]
        return IntegerDataType.dataType
    
    def _resolve_data_type(self, type_str: Optional[str]):
        """型名からGhidraのDataTypeを解決"""
        from ghidra.program.model.data import ( # type: ignore[import]
            IntegerDataType,
            UnsignedIntegerDataType,
            LongDataType,
            UnsignedLongDataType,
            ShortDataType,
            CharDataType,
            VoidDataType,
        )
        
        if type_str is None:
            return IntegerDataType.dataType
        
        type_lower = type_str.lower().strip()
        
        # 修正対象のパターンにマッチする場合はintに置換
        if self._should_fix_type(type_str):
            self._debug_print(f"Resolving '{type_str}' -> int (pattern match)")
            return IntegerDataType.dataType
        
        # 通常の型マッピング
        if "unsigned int" in type_lower or "uint" in type_lower:
            return UnsignedIntegerDataType.dataType
        if "unsigned long" in type_lower:
            return UnsignedLongDataType.dataType
        if "long" in type_lower:
            return LongDataType.dataType
        if "short" in type_lower:
            return ShortDataType.dataType
        if "char" in type_lower:
            return CharDataType.dataType
        if "void" in type_lower:
            return VoidDataType.dataType
        if "int" in type_lower:
            return IntegerDataType.dataType
        
        # デフォルトはint
        self._debug_print(f"Unknown type '{type_str}', defaulting to int")
        return IntegerDataType.dataType
    
    def _find_function_by_name(self, function_name: str):
        """関数名から関数オブジェクトを取得"""
        function_manager = self.program.getFunctionManager()
        functions = function_manager.getFunctions(True)
        
        for func in functions:
            if func.getName() == function_name:
                return func
        return None
    
    def check_return_type_needs_fix(self, function) -> bool:
        """戻り値の型が修正対象かチェック"""
        return_type = function.getReturnType()
        type_str = str(return_type) if return_type else ""
        
        needs_fix = self._should_fix_type(type_str)
        self._debug_print(
            f"Return type of '{function.getName()}': '{type_str}' "
            f"-> needs_fix={needs_fix}"
        )
        return needs_fix
    
    def check_param_types_need_fix(self, function) -> List[int]:
        """修正対象の引数インデックスのリストを返す"""
        indices = []
        
        for i, param in enumerate(function.getParameters()):
            type_str = str(param.getDataType()) if param.getDataType() else ""
            
            if self._should_fix_type(type_str):
                self._debug_print(
                    f"Param {i} '{param.getName()}' of '{function.getName()}': "
                    f"'{type_str}' -> needs_fix=True"
                )
                indices.append(i)
        
        return indices
    
    def check_needs_fix(self, function_name: str) -> Tuple[bool, bool]:
        """関数の型修正が必要かどうかを事前チェック"""
        function = self._find_function_by_name(function_name)
        if function is None:
            self._debug_print(f"Function '{function_name}' not found")
            return (False, False)
        
        return_needs_fix = self.check_return_type_needs_fix(function)
        param_indices = self.check_param_types_need_fix(function)
        
        return (return_needs_fix, len(param_indices) > 0)
    
    def check_needs_fix_with_params(
        self,
        function_name: str,
        param_info: List[Dict[str, Any]]
    ) -> Tuple[bool, bool]:
        """
        関数の型修正が必要かどうかを事前チェック（引数情報付き）
        
        Args:
            function_name: 関数名
            param_info: デコンパイル結果から取得した引数情報
        """
        function = self._find_function_by_name(function_name)
        if function is None:
            self._debug_print(f"Function '{function_name}' not found")
            return (False, False)
        
        return_needs_fix = self.check_return_type_needs_fix(function)
        
        # 引数情報から修正が必要かチェック
        param_needs_fix = False
        for i, info in enumerate(param_info):
            type_str = info.get("data_type", "")
            if self._should_fix_type(type_str):
                self._debug_print(
                    f"Param {i} '{info.get('name', 'unknown')}': "
                    f"'{type_str}' -> needs_fix=True"
                )
                param_needs_fix = True
        
        return (return_needs_fix, param_needs_fix)
    
    def fix_function_signature(
        self,
        function,
        param_info: List[Dict[str, Any]],
        fix_return_type: bool = True,
        fix_param_types: bool = True
    ) -> Tuple[bool, bool]:
        """
        関数のシグネチャを修正（戻り値と引数）
        
        Args:
            function: Ghidra Function オブジェクト
            param_info: 引数情報のリスト
                [{"name": str, "data_type": str, "size": int}, ...]
            fix_return_type: 戻り値の型を修正するか
            fix_param_types: 引数の型を修正するか
        
        Returns:
            (戻り値を修正したか, 引数を修正したか) のタプル
        """
        from ghidra.program.model.symbol import SourceType # type: ignore[import]
        from ghidra.program.model.listing import ( # type: ignore[import]
            ParameterImpl,
            ReturnParameterImpl,
            Function as GhidraFunction
        )
        from java.util import ArrayList # type: ignore[import]
        
        function_name = function.getName()
        return_fixed = False
        params_fixed = False
        
        # 現在の呼び出し規約を取得
        calling_convention = function.getCallingConventionName()
        self._debug_print(f"Current calling convention: {calling_convention}")
        
        # 戻り値の型を決定
        current_return_type = function.getReturnType()
        current_return_type_str = str(current_return_type) if current_return_type else ""
        
        if fix_return_type and self._should_fix_type(current_return_type_str):
            new_return_type = self._get_replacement_data_type()
            return_fixed = True
            self._debug_print(f"Will fix return type: '{current_return_type_str}' -> 'int'")
        else:
            new_return_type = current_return_type
        
        return_param = ReturnParameterImpl(new_return_type, self.program)
        
        # パラメータを構築
        new_params = ArrayList()
        
        self._debug_print(f"Building params from {len(param_info)} param info entries")
        
        for i, info in enumerate(param_info):
            param_name = info.get("name", f"param_{i}")
            param_type_str = info.get("data_type", "int")
            
            # 引数の型を決定
            if fix_param_types and self._should_fix_type(param_type_str):
                param_type = self._get_replacement_data_type()
                self._debug_print(
                    f"Param {i} '{param_name}': '{param_type_str}' -> 'int' (fixed)"
                )
                params_fixed = True
            else:
                param_type = self._resolve_data_type(param_type_str)
                self._debug_print(
                    f"Param {i} '{param_name}': '{param_type_str}' -> '{param_type}' (resolved)"
                )
            
            param_impl = ParameterImpl(
                param_name,
                param_type,
                self.program
            )
            new_params.add(param_impl)
        
        self._debug_print(f"Total params to set: {new_params.size()}")
        
        # 変更がある場合のみ更新
        if return_fixed or params_fixed or new_params.size() > 0:
            with self._transaction(f"Fix function signature of {function_name}"):
                self._debug_print("Calling updateFunction...")
                function.updateFunction(
                    calling_convention,
                    return_param,
                    new_params,
                    GhidraFunction.FunctionUpdateType.DYNAMIC_STORAGE_FORMAL_PARAMS,
                    True,
                    SourceType.USER_DEFINED
                )
            
            self._debug_print(
                f"Fixed function signature of '{function_name}': "
                f"return_fixed={return_fixed}, params_fixed={params_fixed}"
            )
        else:
            self._debug_print(f"No changes needed for '{function_name}'")
        
        return (return_fixed, params_fixed)
    
    def fix_function_signature_by_name(
        self,
        function_name: str,
        param_info: List[Dict[str, Any]],
        fix_return_type: bool = True,
        fix_param_types: bool = True
    ) -> Tuple[bool, bool]:
        """
        関数名を指定してシグネチャを修正
        
        Args:
            function_name: 関数名
            param_info: 引数情報のリスト
            fix_return_type: 戻り値の型を修正するか
            fix_param_types: 引数の型を修正するか
        
        Returns:
            (戻り値を修正したか, 引数を修正したか) のタプル
        """
        function = self._find_function_by_name(function_name)
        if function is None:
            self._debug_print(f"Function '{function_name}' not found")
            return (False, False)
        
        return self.fix_function_signature(
            function, param_info, fix_return_type, fix_param_types
        )
    
    # 以下は後方互換性のために残す
    def fix_return_type(self, function) -> bool:
        """戻り値の型をint型に修正（引数情報なし）"""
        # 既存のパラメータを取得（空の可能性あり）
        params = []
        for param in function.getParameters():
            params.append({
                "name": param.getName(),
                "data_type": str(param.getDataType()) if param.getDataType() else "int",
                "size": param.getSize()
            })
        
        return_fixed, _ = self.fix_function_signature(
            function, params, fix_return_type=True, fix_param_types=False
        )
        return return_fixed
    
    def fix_param_types(self, function) -> bool:
        """引数の型をint型に修正（引数情報なし）"""
        params = []
        for param in function.getParameters():
            params.append({
                "name": param.getName(),
                "data_type": str(param.getDataType()) if param.getDataType() else "int",
                "size": param.getSize()
            })
        
        _, params_fixed = self.fix_function_signature(
            function, params, fix_return_type=False, fix_param_types=True
        )
        return params_fixed
    
    def fix_return_type_by_name(self, function_name: str) -> bool:
        function = self._find_function_by_name(function_name)
        if function is None:
            return False
        return self.fix_return_type(function)
    
    def fix_param_types_by_name(self, function_name: str) -> bool:
        function = self._find_function_by_name(function_name)
        if function is None:
            return False
        return self.fix_param_types(function)


class TypeFixResult:
    """型修正の結果を保持するクラス"""
    
    def __init__(self):
        self.return_type_fixed_binary1: bool = False
        self.return_type_fixed_binary2: bool = False
        self.param_types_fixed_binary1: bool = False
        self.param_types_fixed_binary2: bool = False
        self.retry_phase: str = "none"
    
    def any_fix_applied(self) -> bool:
        return (
            self.return_type_fixed_binary1 or
            self.return_type_fixed_binary2 or
            self.param_types_fixed_binary1 or
            self.param_types_fixed_binary2
        )
    
    def to_dict(self) -> dict:
        return {
            "return_type_fixed_binary1": self.return_type_fixed_binary1,
            "return_type_fixed_binary2": self.return_type_fixed_binary2,
            "param_types_fixed_binary1": self.param_types_fixed_binary1,
            "param_types_fixed_binary2": self.param_types_fixed_binary2,
            "retry_phase": self.retry_phase,
        }
    
    def __str__(self) -> str:
        parts = []
        if self.return_type_fixed_binary1:
            parts.append("return_type_fixed(binary1)")
        if self.return_type_fixed_binary2:
            parts.append("return_type_fixed(binary2)")
        if self.param_types_fixed_binary1:
            parts.append("param_types_fixed(binary1)")
        if self.param_types_fixed_binary2:
            parts.append("param_types_fixed(binary2)")
        
        if not parts:
            return "No type fixes applied"
        return f"Type fixes: {', '.join(parts)} (phase: {self.retry_phase})"
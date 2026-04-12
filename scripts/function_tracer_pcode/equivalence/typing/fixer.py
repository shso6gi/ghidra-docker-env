# -*- coding: utf-8 -*-
"""型修正モジュール - 等価性判定のリトライ時に使用（統合版 + MIPS64 ABI対応）"""

from typing import List, Set, Optional, Tuple, Dict, Any, TYPE_CHECKING
from dataclasses import dataclass, field
from contextlib import contextmanager

# Pylance等の静的解析用スタブ
if TYPE_CHECKING:
    from ghidra.program.model.listing import Program, Function, Parameter # type: ignore[import]
    from ghidra.program.model.data import DataType, DataTypeManager # type: ignore[import]


@dataclass
class TypeFixerConfig:
    """
    型修正の設定
    
    Attributes:
        target_patterns: 修正対象とする型名のパターン（小文字で比較）
        replacement_type_name: 置換先の型名（ログ用）
        unsigned_to_signed_map: unsigned型からsigned型へのマッピング
    """
    target_patterns: Set[str] = field(default_factory=lambda: {
        "undefined",
        "undefined1",
        "undefined2",
        "undefined4",
        "undefined8",
    })
    replacement_type_name: str = "int"
    
    # 符号性修正用: unsigned型 → signed型 のマッピング
    unsigned_to_signed_map: Dict[str, str] = field(default_factory=lambda: {
        "ulong": "long",
        "ulonglong": "longlong",
        "unsigned long": "long",
        "unsigned long long": "long long",
        "uint": "int",
        "unsigned int": "int",
        "ushort": "short",
        "unsigned short": "short",
        "uchar": "char",
        "unsigned char": "char",
    })
    
    def add_pattern(self, pattern: str) -> None:
        """修正対象パターンを追加"""
        self.target_patterns.add(pattern.lower())
    
    def remove_pattern(self, pattern: str) -> None:
        """修正対象パターンを削除"""
        self.target_patterns.discard(pattern.lower())
    
    def set_patterns(self, patterns: Set[str]) -> None:
        """修正対象パターンを置き換え"""
        self.target_patterns = {p.lower() for p in patterns}
    
    def get_signed_type_for(self, unsigned_type: str) -> Optional[str]:
        """unsigned型に対応するsigned型を取得"""
        if unsigned_type is None:
            return None
        
        type_lower = unsigned_type.lower().strip()
        
        # 完全一致を優先
        if type_lower in self.unsigned_to_signed_map:
            return self.unsigned_to_signed_map[type_lower]
        
        # 部分一致
        for unsigned_pattern, signed_type in self.unsigned_to_signed_map.items():
            if unsigned_pattern in type_lower:
                return signed_type
        
        return None


class TypeFixer:
    """
    関数の型を修正するクラス
    
    機能:
    1. パターンマッチによる型修正（undefined → int, longlong → int 等）
    2. 符号性推定に基づく型修正（ulong → long 等）
    3. MIPS64 ABI修正（long → int への強制ダウンキャスト）
    
    全て updateFunction() を使用してアトミックに更新します。
    """
    
    def __init__(
        self,
        program,  # type: Program
        config: Optional[TypeFixerConfig] = None,
        debug: bool = False
    ):
        self.program = program
        self.config = config or TypeFixerConfig()
        self.debug = debug
        # プログラム固有のint型をキャッシュ
        self._cached_int_type = None
        # 型キャッシュ
        self._type_cache: Dict[str, Any] = {}
    
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
    
    def _resolve_program_int_type(self):
        """
        現在のプログラムアーキテクチャに適したint型を取得する。
        DataTypeManagerから '/int' を検索し、なければ汎用のIntegerDataTypeを使用。
        """
        from ghidra.program.model.data import IntegerDataType  # type: ignore[import]
        
        dtm = self.program.getDataTypeManager()
        # アーキテクチャ固有のint（サイズが正しく定義されているもの）を探す
        int_type = dtm.getDataType("/int")
        
        if int_type is None:
            # 見つからない場合は汎用シングルトンを使用
            self._debug_print("Program-specific '/int' not found. Using generic IntegerDataType.")
            return IntegerDataType.dataType
        
        self._debug_print(f"Using program-specific int type: {int_type}")
        return int_type
    
    def _resolve_program_type_by_name(self, type_name: str):
        """
        型名からGhidraのDataTypeを解決（キャッシュ付き）
        
        Args:
            type_name: 型名（"long", "int", "short", "uint" 等）
        
        Returns:
            DataTypeオブジェクト、見つからなければNone
        """
        if type_name is None:
            return None
        
        if type_name in self._type_cache:
            return self._type_cache[type_name]
        
        from ghidra.program.model.data import (  # type: ignore[import]
            IntegerDataType,
            UnsignedIntegerDataType,
            LongDataType,
            UnsignedLongDataType,
            ShortDataType,
            UnsignedShortDataType,
            CharDataType,
            UnsignedCharDataType,
            LongLongDataType,
            UnsignedLongLongDataType,
        )
        
        dtm = self.program.getDataTypeManager()
        
        # まずプログラム固有の型を検索
        program_type = dtm.getDataType(f"/{type_name}")
        if program_type is not None:
            self._type_cache[type_name] = program_type
            self._debug_print(f"Found program-specific type: {type_name} -> {program_type}")
            return program_type
        
        # ビルトイン型にフォールバック
        builtin_map = {
            "int": IntegerDataType.dataType,
            "uint": UnsignedIntegerDataType.dataType,
            "unsigned int": UnsignedIntegerDataType.dataType,
            "long": LongDataType.dataType,
            "ulong": UnsignedLongDataType.dataType,
            "unsigned long": UnsignedLongDataType.dataType,
            "short": ShortDataType.dataType,
            "ushort": UnsignedShortDataType.dataType,
            "unsigned short": UnsignedShortDataType.dataType,
            "char": CharDataType.dataType,
            "uchar": UnsignedCharDataType.dataType,
            "unsigned char": UnsignedCharDataType.dataType,
            "longlong": LongLongDataType.dataType,
            "long long": LongLongDataType.dataType,
            "ulonglong": UnsignedLongLongDataType.dataType,
            "unsigned long long": UnsignedLongLongDataType.dataType,
        }
        
        type_lower = type_name.lower().strip()
        if type_lower in builtin_map:
            result = builtin_map[type_lower]
            self._type_cache[type_name] = result
            self._debug_print(f"Using builtin type for '{type_name}': {result}")
            return result
        
        self._debug_print(f"Type '{type_name}' not found")
        return None
    
    def _should_fix_type(self, type_str: Optional[str]) -> bool:
        """型を修正すべきか判定（パターンマッチ）"""
        if type_str is None:
            return False
        
        type_lower = type_str.lower().strip()
        if "*" in type_lower or "ptr" in type_lower:
            return False
        
        for pattern in self.config.target_patterns:
            if pattern in type_lower:
                self._debug_print(f"Type '{type_str}' matches pattern '{pattern}'")
                return True
        
        return False
    
    def _is_unsigned_type(self, type_str: Optional[str]) -> bool:
        """型がunsigned型かどうかを判定"""
        if type_str is None:
            return False
        
        type_lower = type_str.lower().strip()
        
        # 明示的なunsignedパターン
        unsigned_indicators = [
            "unsigned",
            "ulong",
            "uint",
            "ushort",
            "uchar",
            "ubyte",
        ]
        
        for indicator in unsigned_indicators:
            if indicator in type_lower:
                return True
        
        # "u" で始まる型名（ulong, uint等）- ただし "undefined" は除外
        if type_lower.startswith("u") and len(type_lower) > 1:
            if not type_lower.startswith("undefined"):
                return True
        
        return False
    
    def _get_replacement_data_type(self):
        """置換先のデータ型を取得（キャッシュ済み）"""
        if self._cached_int_type is None:
            self._cached_int_type = self._resolve_program_int_type()
        return self._cached_int_type
    
    def _resolve_data_type(self, type_str: Optional[str]):
        """型名からGhidraのDataTypeを解決"""
        from ghidra.program.model.data import (  # type: ignore[import]
            IntegerDataType,
            UnsignedIntegerDataType,
            LongDataType,
            UnsignedLongDataType,
            ShortDataType,
            CharDataType,
            VoidDataType,
        )
        
        if type_str is None:
            return self._get_replacement_data_type()
        
        type_lower = type_str.lower().strip()
        
        # 修正対象のパターンにマッチする場合はintに置換
        if self._should_fix_type(type_str):
            self._debug_print(f"Resolving '{type_str}' -> int (pattern match)")
            return self._get_replacement_data_type()
        
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
            return self._get_replacement_data_type()
        
        # デフォルトはint
        self._debug_print(f"Unknown type '{type_str}', defaulting to int")
        return self._get_replacement_data_type()
    
    def _find_function_by_name(self, function_name: str):
        """関数名から関数オブジェクトを取得"""
        function_manager = self.program.getFunctionManager()
        for func in function_manager.getFunctions(True):
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
    
    def check_return_type_needs_signedness_fix(
        self,
        return_type_str: Optional[str],
        signedness_result: Optional['SignednessResult'] = None
    ) -> Tuple[bool, Optional[str]]:
        """
        戻り値の型が符号性修正を必要とするかチェック
        
        Args:
            return_type_str: 戻り値の型名
            signedness_result: 符号性推定結果
        
        Returns:
            (修正が必要か, 修正後の型名)
        """
        if signedness_result is None:
            return False, None
        
        # 推定がsignedでない場合は修正不要
        if not signedness_result.is_signed():
            return False, None
        
        if return_type_str is None:
            return False, None
        
        # unsigned型でない場合は修正不要
        if not self._is_unsigned_type(return_type_str):
            return False, None
        
        # 対応するsigned型を取得
        signed_type = self.config.get_signed_type_for(return_type_str)
        if signed_type is None:
            self._debug_print(f"No signed type mapping for '{return_type_str}'")
            return False, None
        
        self._debug_print(
            f"Return type '{return_type_str}' needs signedness fix -> '{signed_type}' "
            f"(evidence: {signedness_result.opcode_counts})"
        )
        return True, signed_type
    
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
            # DataTypeオブジェクトがある場合はそちらを優先
            raw_dt = info.get("data_type_obj")
            if raw_dt is not None and hasattr(raw_dt, 'getName'):
                type_str = str(raw_dt)
            else:
                type_str = info.get("data_type", "")
            
            if self._should_fix_type(type_str):
                self._debug_print(
                    f"Param {i} '{info.get('name', 'unknown')}': "
                    f"'{type_str}' -> needs_fix=True"
                )
                param_needs_fix = True
        
        return (return_needs_fix, param_needs_fix)
    
    def _is_type_equivalent(self, type1, type2) -> bool:
        """2つの型が等価かどうかを安全に判定"""
        if type1 is None or type2 is None:
            return type1 is type2
        
        try:
            return type1.isEquivalent(type2)
        except Exception:
            # isEquivalentが失敗した場合は文字列比較にフォールバック
            return str(type1) == str(type2)
    
    def fix_function_signature(
        self,
        function,
        param_info: List[Dict[str, Any]],
        fix_return_type: bool = True,
        fix_param_types: bool = True,
        override_return_type_name: Optional[str] = None,
        override_param_type_names: Optional[Dict[int, str]] = None
    ) -> Tuple[bool, bool]:
        """
        関数のシグネチャをupdateFunction()でアトミックに修正（戻り値と引数）
        
        ★重要: 全ての型修正（undefined修正、符号性修正、MIPS64 ABI修正）で
        updateFunction()を使用した一括アトミック更新を行います。
        
        Args:
            function: Ghidra Function オブジェクト
            param_info: 引数情報のリスト
                [{"name": str, "data_type": str, "data_type_obj": DataType, "size": int}, ...]
                ※ "data_type_obj" にDataTypeオブジェクトを渡すことを推奨
            fix_return_type: 戻り値の型を修正するか（パターンマッチ）
            fix_param_types: 引数の型を修正するか（パターンマッチ）
            override_return_type_name: 戻り値の型を指定した型名で上書き（符号性修正用）
            override_param_type_names: 引数の型を index -> 型名 で強制上書き（MIPS64 ABI修正用）
        
        Returns:
            (戻り値を修正したか, 引数を修正したか) のタプル
        """
        from ghidra.program.model.symbol import SourceType  # type: ignore[import]
        from ghidra.program.model.listing import (  # type: ignore[import]
            ParameterImpl,
            ReturnParameterImpl,
            Function as GhidraFunction
        )
        from java.util import ArrayList  # type: ignore[import]
        
        function_name = function.getName()
        return_fixed = False
        params_fixed = False
        
        # 現在の呼び出し規約を取得
        calling_convention = function.getCallingConventionName()
        self._debug_print(f"Current calling convention: {calling_convention}")
        
        # ============================================
        # 戻り値の型を決定
        # ============================================
        current_return_type = function.getReturnType()
        current_return_type_str = str(current_return_type) if current_return_type else ""
        new_return_type = current_return_type
        
        # 1. override_return_type_name が指定されている場合（符号性修正）
        if override_return_type_name is not None:
            override_type = self._resolve_program_type_by_name(override_return_type_name)
            if override_type is not None:
                if not self._is_type_equivalent(current_return_type, override_type):
                    new_return_type = override_type
                    return_fixed = True
                    self._debug_print(
                        f"Will fix return type (override): "
                        f"'{current_return_type_str}' -> '{override_return_type_name}'"
                    )
                else:
                    self._debug_print(
                        f"Return type already matches override type '{override_return_type_name}'"
                    )
            else:
                self._debug_print(f"Could not resolve override type '{override_return_type_name}'")
        
        # 2. パターンマッチによる修正（overrideが指定されていない場合のみ）
        elif fix_return_type and self._should_fix_type(current_return_type_str):
            replacement_type = self._get_replacement_data_type()
            if not self._is_type_equivalent(current_return_type, replacement_type):
                new_return_type = replacement_type
                return_fixed = True
                self._debug_print(
                    f"Will fix return type (pattern): "
                    f"'{current_return_type_str}' -> 'int'"
                )
        
        return_param = ReturnParameterImpl(new_return_type, self.program)
        
        # ============================================
        # パラメータを構築
        # ============================================
        new_params = ArrayList()
        
        self._debug_print(f"Building params from {len(param_info)} param info entries")
        
        for i, info in enumerate(param_info):
            param_name = info.get("name", f"param_{i}")
            
            # DataTypeオブジェクトが渡されている場合はそれを優先使用（重要）
            # これにより、ポインタ型や構造体が文字列変換で失われるのを防ぐ
            raw_dt = info.get("data_type_obj")
            if raw_dt is None:
                # 後方互換性：オブジェクトがない場合はキー "data_type" の文字列を見る
                raw_dt = info.get("data_type")
            
            # 現在の型を文字列で取得（デバッグログ用）
            if raw_dt is not None and hasattr(raw_dt, 'getName'):
                current_type_str = str(raw_dt)
            else:
                current_type_str = str(raw_dt) if raw_dt else "undefined"
            
            # 型修復判定
            final_dt = None
            param_was_fixed = False
            
            # ============================================
            # 優先度1: override_param_type_names による強制上書き（MIPS64 ABI修正等）
            # ============================================
            if override_param_type_names is not None and i in override_param_type_names:
                override_type_name = override_param_type_names[i]
                override_type = self._resolve_program_type_by_name(override_type_name)
                
                if override_type is not None:
                    final_dt = override_type
                    
                    # 型が異なる場合のみ「修正した」とマーク
                    if not self._is_type_equivalent(
                        raw_dt if hasattr(raw_dt, 'getName') else None, 
                        override_type
                    ):
                        param_was_fixed = True
                        self._debug_print(
                            f"Param {i} '{param_name}': '{current_type_str}' -> '{override_type_name}' "
                            f"(override - MIPS64 ABI fix)"
                        )
                    else:
                        self._debug_print(
                            f"Param {i} '{param_name}': already '{override_type_name}' (no change)"
                        )
                else:
                    self._debug_print(
                        f"Param {i} '{param_name}': could not resolve override type '{override_type_name}'"
                    )
                    # フォールバック: 元の型を使用
                    if raw_dt is not None and hasattr(raw_dt, 'getName'):
                        final_dt = raw_dt
                    else:
                        final_dt = self._resolve_data_type(str(raw_dt) if raw_dt else "int")
            
            # ============================================
            # 優先度2: パターンマッチによる修正（undefined修正等）
            # ============================================
            elif raw_dt is not None and hasattr(raw_dt, 'getName'):
                # DataTypeオブジェクトの場合
                type_str = str(raw_dt)
                if fix_param_types and self._should_fix_type(type_str):
                    new_dt = self._get_replacement_data_type()
                    if not self._is_type_equivalent(raw_dt, new_dt):
                        final_dt = new_dt
                        param_was_fixed = True
                        self._debug_print(
                            f"Param {i} '{param_name}': '{type_str}' -> 'int' (pattern match)"
                        )
                    else:
                        final_dt = raw_dt
                else:
                    final_dt = raw_dt  # 既存の型を維持
                    self._debug_print(
                        f"Param {i} '{param_name}': '{type_str}' (preserved)"
                    )
            
            # ============================================
            # 優先度3: 文字列からの型解決（フォールバック）
            # ============================================
            else:
                type_str = str(raw_dt) if raw_dt else "undefined"
                if fix_param_types and self._should_fix_type(type_str):
                    final_dt = self._get_replacement_data_type()
                    param_was_fixed = True
                    self._debug_print(
                        f"Param {i} '{param_name}': '{type_str}' -> 'int' (pattern match from string)"
                    )
                else:
                    final_dt = self._resolve_data_type(type_str)
                    self._debug_print(
                        f"Param {i} '{param_name}': '{type_str}' -> '{final_dt}' (resolved)"
                    )
            
            # パラメータが修正された場合はフラグをセット
            if param_was_fixed:
                params_fixed = True
            
            # ParameterImplを作成してリストに追加
            param_impl = ParameterImpl(
                param_name,
                final_dt,
                self.program
            )
            new_params.add(param_impl)
        
        self._debug_print(f"Total params to set: {new_params.size()}")
        
        # ============================================
        # updateFunction() でアトミックに更新
        # ============================================
        # 変更がある場合、または強制的に更新する必要がある場合
        needs_update = (
            return_fixed or 
            params_fixed or 
            new_params.size() > 0 or
            override_param_type_names is not None  # override指定時は必ず更新
        )
        
        if needs_update:
            with self._transaction(f"Fix function signature of {function_name}"):
                self._debug_print("Calling updateFunction (Atomic Update)...")
                try:
                    function.updateFunction(
                        calling_convention,
                        return_param,
                        new_params,
                        GhidraFunction.FunctionUpdateType.DYNAMIC_STORAGE_FORMAL_PARAMS,
                        True,  # force: 競合があっても強制適用
                        SourceType.USER_DEFINED
                    )
                    self._debug_print(
                        f"Successfully updated function '{function_name}' via updateFunction(): "
                        f"return_fixed={return_fixed}, params_fixed={params_fixed}"
                    )
                except Exception as e:
                    self._debug_print(f"Error updating function {function_name}: {e}")
                    raise
        else:
            self._debug_print(f"No changes needed for '{function_name}'")
        
        return (return_fixed, params_fixed)
    
    def fix_function_signature_by_name(
        self,
        function_name: str,
        param_info: List[Dict[str, Any]],
        fix_return_type: bool = True,
        fix_param_types: bool = True,
        override_return_type_name: Optional[str] = None,
        override_param_type_names: Optional[Dict[int, str]] = None
    ) -> Tuple[bool, bool]:
        """
        関数名を指定してシグネチャを修正
        
        内部で updateFunction() を使用してアトミックに更新します。
        
        Args:
            function_name: 関数名
            param_info: 引数情報のリスト
            fix_return_type: 戻り値の型を修正するか（パターンマッチ）
            fix_param_types: 引数の型を修正するか（パターンマッチ）
            override_return_type_name: 戻り値の型を指定した型名で上書き（符号性修正用）
            override_param_type_names: 引数の型を index -> 型名 で強制上書き（MIPS64 ABI修正用）
        
        Returns:
            (戻り値を修正したか, 引数を修正したか) のタプル
        """
        function = self._find_function_by_name(function_name)
        if function is None:
            self._debug_print(f"Function '{function_name}' not found")
            return (False, False)
        
        return self.fix_function_signature(
            function, param_info, fix_return_type, fix_param_types,
            override_return_type_name=override_return_type_name,
            override_param_type_names=override_param_type_names
        )
    
    # 以下は後方互換性のために残す
    def fix_return_type(self, function) -> bool:
        """戻り値の型をint型に修正（引数情報なし）"""
        # 既存のパラメータをDataTypeオブジェクトとして取得（重要）
        params = []
        for param in function.getParameters():
            params.append({
                "name": param.getName(),
                "data_type": str(param.getDataType()) if param.getDataType() else "int",
                "data_type_obj": param.getDataType(),  # DataTypeオブジェクトを維持
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
                "data_type_obj": param.getDataType(),  # DataTypeオブジェクトを維持
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
        # パターンマッチによる修正
        self.return_type_fixed_binary1: bool = False
        self.return_type_fixed_binary2: bool = False
        self.param_types_fixed_binary1: bool = False
        self.param_types_fixed_binary2: bool = False
        self.retry_phase: str = "none"
        
        # 符号性に基づく修正（戻り値）
        self.signedness_fixed_binary1: bool = False
        self.signedness_fixed_binary2: bool = False
        self.inferred_signedness_binary1: Optional[str] = None
        self.inferred_signedness_binary2: Optional[str] = None
        self.original_type_binary1: Optional[str] = None
        self.original_type_binary2: Optional[str] = None
        self.fixed_type_binary1: Optional[str] = None
        self.fixed_type_binary2: Optional[str] = None
        
        # Phase 1.5: 引数の符号性修正
        self.param_signedness_fixed_binary1: bool = False
        self.param_signedness_fixed_binary2: bool = False
        self.param_signedness_override_map_binary1: Optional[Dict[int, str]] = None
        self.param_signedness_override_map_binary2: Optional[Dict[int, str]] = None
        
        # MIPS64 ABI修正
        self.mips64_abi_fixed_binary1: bool = False
        self.mips64_abi_fixed_binary2: bool = False
        self.mips64_abi_override_map_binary1: Optional[Dict[int, str]] = None
        self.mips64_abi_override_map_binary2: Optional[Dict[int, str]] = None
    
    def any_fix_applied(self) -> bool:
        """何らかの修正が適用されたか"""
        return (
            self.return_type_fixed_binary1 or
            self.return_type_fixed_binary2 or
            self.param_types_fixed_binary1 or
            self.param_types_fixed_binary2 or
            self.signedness_fixed_binary1 or
            self.signedness_fixed_binary2 or
            self.param_signedness_fixed_binary1 or
            self.param_signedness_fixed_binary2 or
            self.mips64_abi_fixed_binary1 or
            self.mips64_abi_fixed_binary2
        )
    
    def any_signedness_fix_applied(self) -> bool:
        """符号性修正が適用されたか（戻り値）"""
        return (
            self.signedness_fixed_binary1 or
            self.signedness_fixed_binary2
        )
    
    def any_param_signedness_fix_applied(self) -> bool:
        """引数の符号性修正が適用されたか（NEW）"""
        return (
            self.param_signedness_fixed_binary1 or
            self.param_signedness_fixed_binary2
        )
    
    def any_mips64_abi_fix_applied(self) -> bool:
        """MIPS64 ABI修正が適用されたか"""
        return (
            self.mips64_abi_fixed_binary1 or
            self.mips64_abi_fixed_binary2
        )
    
    def to_dict(self) -> dict:
        result = {
            "return_type_fixed_binary1": self.return_type_fixed_binary1,
            "return_type_fixed_binary2": self.return_type_fixed_binary2,
            "param_types_fixed_binary1": self.param_types_fixed_binary1,
            "param_types_fixed_binary2": self.param_types_fixed_binary2,
            "retry_phase": self.retry_phase,
            "signedness_fixed_binary1": self.signedness_fixed_binary1,
            "signedness_fixed_binary2": self.signedness_fixed_binary2,
            "inferred_signedness_binary1": self.inferred_signedness_binary1,
            "inferred_signedness_binary2": self.inferred_signedness_binary2,
            "original_type_binary1": self.original_type_binary1,
            "original_type_binary2": self.original_type_binary2,
            "fixed_type_binary1": self.fixed_type_binary1,
            "fixed_type_binary2": self.fixed_type_binary2,
            "param_signedness_fixed_binary1": self.param_signedness_fixed_binary1,
            "param_signedness_fixed_binary2": self.param_signedness_fixed_binary2,
            "mips64_abi_fixed_binary1": self.mips64_abi_fixed_binary1,
            "mips64_abi_fixed_binary2": self.mips64_abi_fixed_binary2,
        }
        
        if self.param_signedness_override_map_binary1:
            result["param_signedness_override_map_binary1"] = self.param_signedness_override_map_binary1
        if self.param_signedness_override_map_binary2:
            result["param_signedness_override_map_binary2"] = self.param_signedness_override_map_binary2
        if self.mips64_abi_override_map_binary1:
            result["mips64_abi_override_map_binary1"] = self.mips64_abi_override_map_binary1
        if self.mips64_abi_override_map_binary2:
            result["mips64_abi_override_map_binary2"] = self.mips64_abi_override_map_binary2
        
        return result
    
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
        if self.signedness_fixed_binary1:
            orig = self.original_type_binary1 or "?"
            fixed = self.fixed_type_binary1 or "?"
            parts.append(f"signedness_fixed(binary1: {orig} -> {fixed})")
        if self.signedness_fixed_binary2:
            orig = self.original_type_binary2 or "?"
            fixed = self.fixed_type_binary2 or "?"
            parts.append(f"signedness_fixed(binary2: {orig} -> {fixed})")
        if self.param_signedness_fixed_binary1:
            parts.append(f"param_signedness_fixed(binary1: {self.param_signedness_override_map_binary1})")
        if self.param_signedness_fixed_binary2:
            parts.append(f"param_signedness_fixed(binary2: {self.param_signedness_override_map_binary2})")
        if self.mips64_abi_fixed_binary1:
            parts.append(f"mips64_abi_fixed(binary1: {self.mips64_abi_override_map_binary1})")
        if self.mips64_abi_fixed_binary2:
            parts.append(f"mips64_abi_fixed(binary2: {self.mips64_abi_override_map_binary2})")
        
        if not parts:
            return "No type fixes applied"
        return f"Type fixes: {', '.join(parts)} (phase: {self.retry_phase})"


# 型ヒント用のインポート（循環参照を避けるため末尾に配置）
if TYPE_CHECKING:
    from ...model.analysis import SignednessResult

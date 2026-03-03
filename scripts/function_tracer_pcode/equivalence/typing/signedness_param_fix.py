# -*- coding: utf-8 -*-
"""引数の符号性推定・修正モジュール（Phase 1.5用）"""

from typing import Dict
from ...model import FunctionReturnAnalysis
from .fixer import TypeFixerConfig


class ParamSignednessFixer:
    """引数の符号性推定・修正を行うクラス"""
    
    def __init__(self, config: TypeFixerConfig, debug: bool = False):
        self.config = config
        self.debug = debug
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[ParamSignednessFixer] {msg}")
    
    def detect_param_signedness_mismatch(
        self,
        analysis: FunctionReturnAnalysis
    ) -> Dict[int, str]:
        """
        引数の型が誤ってunsignedになっているかを検出
        
        検出条件：
        1. 関数の符号性推定結果が"signed"（return-chain由来）
        2. パラメータの型がunsigned系（ulong, uint等）
        
        Args:
            analysis: 関数解析結果
        
        Returns:
            修正すべきparamのインデックス→型名のマップ
            例: {0: "long", 1: "int"}
        """
        override_map = {}
        
        # 符号性推定結果がない、またはsignedでない場合はスキップ
        if analysis.signedness_result is None:
            return override_map
        
        if not analysis.signedness_result.is_signed():
            return override_map
        
        # パラメータがない場合はスキップ
        if not analysis.parameters:
            return override_map
        
        self._debug_print(
            f"Function '{analysis.function_name}' inferred as signed, "
            f"checking {len(analysis.parameters)} parameters..."
        )
        
        for i, param in enumerate(analysis.parameters):
            # DataTypeオブジェクトがある場合はそれを優先
            raw_dt = param.get("data_type_obj")
            if raw_dt is not None and hasattr(raw_dt, 'getName'):
                type_str = str(raw_dt)
            else:
                type_str = param.get("data_type", "")
            
            if not type_str:
                continue
            
            # unsigned型かどうかをチェック
            if not self._is_unsigned_type(type_str):
                continue
            
            # 対応するsigned型を取得
            signed_type = self.config.get_signed_type_for(type_str)
            if signed_type is None:
                self._debug_print(
                    f"  Param {i} '{param.get('name', 'unknown')}': "
                    f"'{type_str}' is unsigned but no signed mapping found"
                )
                continue
            
            # 修正対象として登録
            override_map[i] = signed_type
            self._debug_print(
                f"  Param {i} '{param.get('name', 'unknown')}': "
                f"'{type_str}' -> '{signed_type}' (signedness mismatch detected)"
            )
        
        if override_map:
            self._debug_print(
                f"Detected {len(override_map)} param(s) needing signedness fix"
            )
        else:
            self._debug_print("No param signedness mismatches detected")
        
        return override_map
    
    def _is_unsigned_type(self, type_str: str) -> bool:
        """型がunsigned型かどうかを判定"""
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
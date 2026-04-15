# -*- coding: utf-8 -*-
"""引数の符号性推定・修正モジュール（Phase 1.5用）"""

from typing import Any, Dict
from ...model import FunctionReturnAnalysis
from ...model.signature import (
    ResolvedTypeSpec,
    get_data_type_display_name,
    is_unsigned_data_type,
)
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
        analysis: FunctionReturnAnalysis,
        *,
        program: Any = None,
    ) -> Dict[int, ResolvedTypeSpec]:
        """
        引数の型が誤ってunsignedになっているかを検出
        
        検出条件：
        1. 関数の符号性推定結果が"signed"（return-chain由来）
        2. パラメータの型がunsigned系（ulong, uint等）
        
        Args:
            analysis: 関数解析結果
        
        Returns:
            修正すべきparamのインデックス→型specのマップ
        """
        override_map: Dict[int, ResolvedTypeSpec] = {}
        
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
            type_str = get_data_type_display_name(raw_dt, param.get("data_type", ""))
            
            if not type_str:
                continue
            
            # unsigned型かどうかをチェック
            if not self._is_unsigned_type(raw_dt, type_str):
                continue
            
            # 対応するsigned型を取得
            signed_spec = self.config.resolve_signed_type_spec(
                type_str,
                data_type_obj=raw_dt,
                program=program,
                fallback_size=param.get("size"),
            )
            if signed_spec is None:
                self._debug_print(
                    f"  Param {i} '{param.get('name', 'unknown')}': "
                    f"'{type_str}' is unsigned but no signed mapping found"
                )
                continue
            
            # 修正対象として登録
            override_map[i] = signed_spec
            self._debug_print(
                f"  Param {i} '{param.get('name', 'unknown')}': "
                f"'{type_str}' -> '{signed_spec.type_name}' "
                f"(signedness mismatch detected via {signed_spec.source})"
            )
        
        if override_map:
            self._debug_print(
                f"Detected {len(override_map)} param(s) needing signedness fix"
            )
        else:
            self._debug_print("No param signedness mismatches detected")
        
        return override_map
    
    def _is_unsigned_type(self, data_type_obj, type_str: str) -> bool:
        """型がunsigned型かどうかを判定"""
        return is_unsigned_data_type(data_type_obj, type_str)

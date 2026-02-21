# -*- coding: utf-8 -*-
"""MIPS64 ABI型修正処理"""

from typing import Optional, Dict, List, Any

from ..model import FunctionReturnAnalysis
from .type_helpers import is_long_type, is_int_type, is_unsigned_type, get_type_name_from_param


class MIPS64Handler:
    """MIPS64 ABI関連の型修正処理"""
    
    def __init__(self, debug: bool = False):
        self.debug = debug
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[MIPS64Handler] {msg}")
    
    def detect_param_type_mismatch(
        self,
        mips_analysis: FunctionReturnAnalysis,
        other_analysis: FunctionReturnAnalysis
    ) -> Optional[Dict[int, str]]:
        """
        MIPS64側のパラメータ型修正マップを生成
        
        MIPS64 ABIでは、32bit int型の引数も64bitレジスタに
        符号拡張/ゼロ拡張されて渡される。このため、Ghidraが
        long/ulongと誤認識することがある。
        
        Args:
            mips_analysis: MIPS64 側の解析結果
            other_analysis: 比較相手側の解析結果
        
        Returns:
            修正が必要な場合: {param_index: new_type_name} の辞書
            不要な場合: None
        """
        override_map = {}
        
        max_params = max(
            len(mips_analysis.parameters),
            len(other_analysis.parameters)
        )
        
        for i in range(max_params):
            mips_param = (
                mips_analysis.parameters[i]
                if i < len(mips_analysis.parameters) else None
            )
            other_param = (
                other_analysis.parameters[i]
                if i < len(other_analysis.parameters) else None
            )
            
            if mips_param is None or other_param is None:
                continue
            
            mips_type = get_type_name_from_param(mips_param)
            other_type = get_type_name_from_param(other_param)
            
            # MIPS側が long/ulong、相手側が int/uint の場合
            if is_long_type(mips_type) and is_int_type(other_type):
                # signed/unsigned を判定
                target_type = "uint" if is_unsigned_type(mips_type) else "int"
                override_map[i] = target_type
                self._debug_print(
                    f"Param {i}: MIPS64 has '{mips_type}', other has '{other_type}' "
                    f"-> will fix to '{target_type}'"
                )
        
        return override_map if override_map else None
    
    def should_apply_fix(
        self,
        is_mips64_1: bool,
        is_mips64_2: bool,
        analysis1: Optional[FunctionReturnAnalysis],
        analysis2: Optional[FunctionReturnAnalysis]
    ) -> bool:
        """MIPS64 ABI修正を適用すべきかどうかを判定"""
        if not (is_mips64_1 or is_mips64_2):
            return False
        
        if analysis1 is None or analysis2 is None:
            return False
        
        return True
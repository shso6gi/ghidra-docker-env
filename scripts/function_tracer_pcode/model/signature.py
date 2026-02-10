# -*- coding: utf-8 -*-
"""関数シグネチャのデータモデル"""

from typing import Optional, List, Dict, Any, TYPE_CHECKING
from dataclasses import dataclass

if TYPE_CHECKING:
    from .analysis import FunctionReturnAnalysis


@dataclass
class FunctionSignature:
    """関数シグネチャ情報"""
    return_type: Optional[str] = None
    parameters: Optional[List[Dict[str, Any]]] = None
    
    def format_return_type(self) -> str:
        """戻り値の型をフォーマット"""
        return self.return_type if self.return_type else "unknown"
    
    def format_parameters(self) -> str:
        """引数リストをフォーマット（例: (int a, long b)）"""
        if not self.parameters:
            return "(void)"
        
        param_strs = []
        for p in self.parameters:
            dtype = p.get("data_type", "unknown")
            name = p.get("name", "")
            if name:
                param_strs.append(f"{dtype} {name}")
            else:
                param_strs.append(dtype)
        
        return f"({', '.join(param_strs)})"
    
    def format_full(self, func_name: str) -> str:
        """完全なシグネチャをフォーマット（例: int func(int a, long b)）"""
        return f"{self.format_return_type()} {func_name}{self.format_parameters()}"
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "return_type": self.return_type,
            "parameters": self.parameters
        }
    
    @classmethod
    def from_analysis(cls, analysis: 'FunctionReturnAnalysis') -> 'FunctionSignature':
        """FunctionReturnAnalysisからシグネチャを抽出"""
        return cls(
            return_type=analysis.return_type,
            parameters=analysis.parameters.copy() if analysis.parameters else None
        )

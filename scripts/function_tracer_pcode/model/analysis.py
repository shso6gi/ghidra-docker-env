# -*- coding: utf-8 -*-
"""関数解析結果のデータモデル"""

from typing import List, Dict, Optional, Any, TYPE_CHECKING

if TYPE_CHECKING:
    from .expression import Expression, Condition


class ReturnInfo:
    """Return情報"""
    
    def __init__(
        self,
        address: str,
        value: 'Expression',
        conditions: Optional[List['Condition']] = None,
        branch_index: Optional[int] = None
    ):
        self.address = address
        self.value = value
        self.conditions = conditions or []
        self.branch_index = branch_index
    
    def to_dict(self) -> Dict:
        return {
            "address": self.address,
            "value": self.value.to_dict(),
            "value_string": self.value.to_string(),
            "value_smt": self.value.to_smt(),
            "conditions": [c.to_string() for c in self.conditions],
            "conditions_smt": [c.to_smt() for c in self.conditions],
            "branch_index": self.branch_index,
        }


class FunctionReturnAnalysis:
    """関数のReturn解析結果"""
    
    def __init__(
        self,
        function_name: str,
        entry_point: str,
        parameters: List[Dict],
        returns: List[ReturnInfo],
        return_type: Optional[str] = None
    ):
        self.function_name = function_name
        self.entry_point = entry_point
        self.parameters = parameters
        self.returns = returns
        self.return_type = return_type
    
    def get_signature_string(self) -> str:
        """関数シグネチャを文字列で取得（例: int func(int a, long b)）"""
        ret_type = self.return_type or "unknown"
        
        if not self.parameters:
            params_str = "void"
        else:
            param_strs = []
            for p in self.parameters:
                dtype = p.get("data_type", "unknown")
                name = p.get("name", "")
                if name:
                    param_strs.append(f"{dtype} {name}")
                else:
                    param_strs.append(dtype)
            params_str = ", ".join(param_strs)
        
        return f"{ret_type} {self.function_name}({params_str})"
    
    def to_dict(self) -> Dict:
        return {
            "function_name": self.function_name,
            "entry_point": self.entry_point,
            "return_type": self.return_type,
            "parameters": self.parameters,
            "returns": [r.to_dict() for r in self.returns],
            "signature": self.get_signature_string(),
        }

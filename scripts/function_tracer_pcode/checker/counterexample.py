# -*- coding: utf-8 -*-
"""反例フォーマットモジュール"""

from typing import Dict, Any, Optional, List
from dataclasses import dataclass
from scripts.function_tracer_pcode.core.json_encoding import materialize


@dataclass
class FormattedCounterexample:
    """フォーマットされた反例"""
    parameters: Dict[str, str]   # パラメータ名 -> 値
    return_value1: Optional[str]  # 関数1のreturn値
    return_value2: Optional[str]  # 関数2のreturn値
    raw_model: Dict[str, Any]    # 生のモデル
    
    def json_items(self):
        yield "parameters", self.parameters
        yield "return_value1", self.return_value1
        yield "return_value2", self.return_value2
        # raw_modelは巨大になる可能性があるため除外（必要なら含める）

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)
    
    def to_string(self, format_type: str = "text") -> str:
        if format_type == "json":
            import json
            return json.dumps(self.to_dict(), indent=2)
        
        lines = []
        lines.append("Counterexample found:")
        lines.append("  Parameters:")
        for name, value in self.parameters.items():
            lines.append(f"    {name} = {value}")
        
        if self.return_value1:
            lines.append(f"  Return value 1: {self.return_value1}")
        if self.return_value2:
            lines.append(f"  Return value 2: {self.return_value2}")
        
        return "\n".join(lines)


class CounterexampleFormatter:
    """反例のフォーマッタ"""
    
    @staticmethod
    def format(
        model: Dict[str, Any],
        param_names: List[str],
        return_var1: str,
        return_var2: str,
        hex_format: bool = True
    ) -> FormattedCounterexample:
        """
        モデルをフォーマット
        
        Args:
            model: SMTソルバーから得られたモデル
            param_names: パラメータ名のリスト
            return_var1: return変数名1
            return_var2: return変数名2
            hex_format: 16進数で表示するか
        """
        parameters = {}
        return_value1 = None
        return_value2 = None
        
        for name, value in model.items():
            formatted_value = CounterexampleFormatter._format_value(value, hex_format)
            
            if name in param_names or name.startswith("param_"):
                parameters[name] = formatted_value
            elif name == return_var1:
                return_value1 = formatted_value
            elif name == return_var2:
                return_value2 = formatted_value
            else:
                # その他の変数もパラメータとして記録
                parameters[name] = formatted_value
        
        return FormattedCounterexample(
            parameters=parameters,
            return_value1=return_value1,
            return_value2=return_value2,
            raw_model=model
        )
    
    @staticmethod
    def _format_value(value: Any, hex_format: bool) -> str:
        """値をフォーマット"""
        if isinstance(value, int):
            if hex_format:
                return f"0x{value:x}"
            return str(value)
        return str(value)
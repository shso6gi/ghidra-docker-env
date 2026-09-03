# -*- coding: utf-8 -*-
"""出力フォーマッタ（SMT修正版 v2）"""

import json
from typing import List, Optional
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis


class OutputFormatter:
    """出力フォーマットを担当するクラス"""
    
    @staticmethod
    def format_header(program_name: str, format_type: str = "text") -> str:
        """ファイル名をヘッダーとして出力"""
        if format_type == "json":
            return json.dumps({
                "program": program_name,
                "analysis_results": []
            }, indent=2, ensure_ascii=False).split('"analysis_results"')[0].rstrip() + '"analysis_results": ['
        
        elif format_type == "smt":
            lines = [
                ";" + "=" * 68,
                f"; Program: {program_name}",
                ";" + "=" * 68,
                "",
                "; SMT-LIB v2.6 compatible output",
                "(set-logic QF_BV)",
                ""
            ]
            return "\n".join(lines)
        
        elif format_type == "detailed":
            lines = [
                "#" * 70,
                "# BINARY ANALYSIS REPORT",
                f"# Program: {program_name}",
                "#" * 70,
                ""
            ]
            return "\n".join(lines)
        
        else:  # text
            lines = [
                "=" * 70,
                f"Binary: {program_name}",
                "=" * 70,
                ""
            ]
            return "\n".join(lines)
    
    @classmethod
    def format_text(cls, analysis: 'FunctionReturnAnalysis') -> str:
        """テキスト形式でフォーマット"""
        from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier
        
        lines = []
        lines.append("-" * 70)
        lines.append(f"\nFunction: {analysis.function_name}")
        lines.append(f"Entry Point: {analysis.entry_point}")
        
        lines.append("\n[Parameters]")
        if analysis.parameters:
            for param in analysis.parameters:
                dtype = param.get("data_type", "unknown")
                name = param.get("name", "unknown")
                lines.append(f"  {dtype} {name}")
        else:
            lines.append("  (none)")

        lines.append("\n[Return Type]")
        return_type = analysis.return_type if analysis.return_type else "unknown"
        lines.append(f"  {return_type}")
        
        lines.append("\n[Return Values]")
        if analysis.returns:
            for i, ret in enumerate(analysis.returns):
                branch_idx = ret.branch_index if ret.branch_index is not None else i
                lines.append(f"\n  Return #{i + 1} at {ret.address} (branch {branch_idx + 1}):")
                lines.append(f"    Value: {ret.value.to_string()}")
                
                if ret.conditions:
                    lines.append("    Conditions:")
                    for cond in ret.conditions:
                        simplified = ConditionSimplifier.get_simplified_condition_string(cond)
                        lines.append(f"      - {simplified}")
                else:
                    lines.append("    Conditions: (unconditional)")
        else:
            lines.append("  (no return values found)")
        
        return "\n".join(lines)
    
    @staticmethod
    def format_json(analysis: FunctionReturnAnalysis, indent: int = 2) -> str:
        """JSON形式でフォーマット"""
        return json.dumps(analysis.to_dict(), indent=indent, ensure_ascii=False)
    
    @staticmethod
    def format_smt(analysis: FunctionReturnAnalysis) -> str:
        """
        SMTソルバー用形式でフォーマット（Z3互換・修正版）
        
        修正点:
        1. 引数なし関数の参照で括弧を使用しない
        2. 条件を適切なSMT形式で出力
        3. ite式で統合されたreturn値を定義
        """
        lines = []
        func_name = analysis.function_name
        
        lines.append(f"; Function: {func_name}")
        lines.append(f"; Entry Point: {analysis.entry_point}")
        lines.append("")
        
        # パラメータの宣言
        lines.append("; " + "=" * 50)
        lines.append("; Parameter declarations")
        lines.append("; " + "=" * 50)
        param_info = []
        for param in analysis.parameters:
            name = param.get("name", "param")
            size = param.get("size", 4) * 8  # バイト→ビット
            lines.append(f"(declare-const {name} (_ BitVec {size}))")
            param_info.append({"name": name, "size": size})
        
        lines.append("")
        
        # 戻り値のサイズを決定
        return_size = 32  # デフォルト
        if analysis.returns:
            first_ret = analysis.returns[0]
            if hasattr(first_ret.value, 'size') and first_ret.value.size:
                return_size = first_ret.value.size * 8
        
        # 各return値の条件と値を収集
        lines.append("; " + "=" * 50)
        lines.append("; Return value analysis")
        lines.append("; " + "=" * 50)
        
        return_defs = []
        for i, ret in enumerate(analysis.returns):
            lines.append("")
            lines.append(f"; Return #{i + 1} at {ret.address}")
            
            # 条件をSMT形式で取得
            if ret.conditions:
                cond_parts = []
                for c in ret.conditions:
                    cond_smt = c.to_smt()
                    cond_parts.append(cond_smt)
                
                if len(cond_parts) == 1:
                    cond_str = cond_parts[0]
                else:
                    cond_str = f"(and {' '.join(cond_parts)})"
                
                lines.append(f"; Condition: {cond_str}")
            else:
                cond_str = "true"
                lines.append("; Condition: true (unconditional)")
            
            # 戻り値のSMT式
            value_smt = ret.value.to_smt()
            lines.append(f"; Value: {value_smt}")
            
            return_defs.append({
                "index": i,
                "condition": cond_str,
                "value": value_smt
            })
        
        lines.append("")
        
        # 統合されたreturn値の定義（ite式を使用）
        lines.append("; " + "=" * 50)
        lines.append("; Unified return value definition")
        lines.append("; " + "=" * 50)
        
        if return_defs:
            unified_return = OutputFormatter._build_ite_expression(return_defs)
            # define-funで定義
            lines.append(f"(define-fun return_{func_name} () (_ BitVec {return_size})")
            lines.append(f"  {unified_return})")
        else:
            # return値がない場合
            lines.append(f"(define-fun return_{func_name} () (_ BitVec {return_size})")
            lines.append(f"  (_ bv0 {return_size}))")
        
        lines.append("")
        
        # 充足可能性チェック用のテンプレート
        lines.append("; " + "=" * 50)
        lines.append("; Verification commands")
        lines.append("; " + "=" * 50)
        lines.append("")
        lines.append("; Basic satisfiability check")
        lines.append(f"; (assert (= return_{func_name} (_ bv0 {return_size})))")
        lines.append("; (check-sat)")
        lines.append("; (get-model)")
        lines.append("")
        
        # 等価性検証のテンプレート（コメントとして）
        lines.append("; " + "=" * 50)
        lines.append("; Equivalence check template (for comparison with another binary)")
        lines.append("; " + "=" * 50)
        lines.append("; To compare, define another function and assert non-equivalence:")
        lines.append(f"; (define-fun return_{func_name}_other () (_ BitVec {return_size}) ...)")
        # 括弧なしで関数を参照
        lines.append(f"; (assert (not (= return_{func_name} return_{func_name}_other)))")
        lines.append("; (check-sat)")
        lines.append("; If result is 'unsat', the functions are equivalent.")
        lines.append("; If result is 'sat', (get-model) shows a counterexample.")
        
        return "\n".join(lines)
    
    @staticmethod
    def _build_ite_expression(return_defs: List[dict]) -> str:
        """
        複数の条件付きreturn値からite式を構築
        
        Args:
            return_defs: [{"condition": str, "value": str}, ...]
        
        Returns:
            ite式の文字列
        """
        if not return_defs:
            return "(_ bv0 32)"
        
        if len(return_defs) == 1:
            return return_defs[0]["value"]
        
        # 最後の要素をデフォルト値として使用
        result = return_defs[-1]["value"]
        
        # 逆順にite式を構築
        for i in range(len(return_defs) - 2, -1, -1):
            ret_def = return_defs[i]
            cond = ret_def["condition"]
            value = ret_def["value"]
            
            if cond == "true":
                # 無条件の場合はその値を使用
                result = value
            else:
                result = f"(ite {cond} {value} {result})"
        
        return result
    
    @staticmethod
    def format_detailed(analysis: FunctionReturnAnalysis) -> str:
        """詳細形式でフォーマット"""
        lines = []
        lines.append("#" * 70)
        lines.append("# DETAILED RETURN ANALYSIS")
        lines.append(f"# Function: {analysis.function_name}")
        lines.append("#" * 70)
        
        lines.append("\n## Parameters")
        lines.append("-" * 40)
        for param in analysis.parameters:
            lines.append(f"  Name: {param.get('name', 'unnamed')}")
            lines.append(f"  Type: {param.get('data_type', 'unknown')}")
            lines.append(f"  Size: {param.get('size', 0)} bytes")
            lines.append(f"  Index: {param.get('index', -1)}")
            lines.append("")
        
        lines.append("\n## Return Values")
        lines.append("-" * 40)
        
        for i, ret in enumerate(analysis.returns):
            lines.append(f"\n### Return #{i + 1}")
            lines.append(f"Address: {ret.address}")
            lines.append("")
            lines.append("Expression (readable):")
            lines.append(f"  {ret.value.to_string()}")
            lines.append("")
            lines.append("Expression (SMT):")
            lines.append(f"  {ret.value.to_smt()}")
            lines.append("")
            lines.append("Expression (AST):")
            lines.append(f"  {json.dumps(ret.value.to_dict(), indent=4)}")
            lines.append("")
            
            if ret.conditions:
                lines.append("Conditions:")
                for j, cond in enumerate(ret.conditions):
                    lines.append(f"  [{j + 1}] {cond.to_string()}")
                    lines.append(f"      SMT: {cond.to_smt()}")
            else:
                lines.append("Conditions: (unconditional)")
            
            lines.append("-" * 40)
        
        return "\n".join(lines)
    
    @staticmethod
    def format(
        analysis: FunctionReturnAnalysis,
        format_type: str = "text"
    ) -> str:
        """指定された形式でフォーマット"""
        formatters = {
            "text": OutputFormatter.format_text,
            "json": OutputFormatter.format_json,
            "smt": OutputFormatter.format_smt,
            "detailed": OutputFormatter.format_detailed,
        }
        
        formatter = formatters.get(format_type, OutputFormatter.format_text)
        return formatter(analysis)


def write_to_file(content: str, filepath: str):
    """ファイルに書き込み"""
    try:
        with open(filepath, "a", encoding="utf-8") as f:
            f.write(content + "\n")
    except Exception as e:
        print(f"ファイル書き込みエラー: {e}")


def output_result(content: str, output_file: Optional[str] = None, quiet: bool = False):
    """結果を出力（標準出力とファイルの両方）"""
    if not quiet:
        print(content)
    
    if output_file:
        write_to_file(content, output_file)
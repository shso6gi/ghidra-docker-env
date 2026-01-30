# -*- coding: utf-8 -*-
"""SMT式構築モジュール（ビット幅制約モード対応版）"""

from typing import List, Dict, Optional, Tuple
from dataclasses import dataclass
import re

from ..return_analyzer import FunctionReturnAnalysis, ReturnInfo


@dataclass
class ParameterInfo:
    """パラメータ情報"""
    original_name: str
    smt_name: str
    bit_width: int
    index: int


@dataclass
class ParameterPair:
    """パラメータペア（2つの関数間のマッピング）"""
    index: int
    param1: Optional[ParameterInfo]
    param2: Optional[ParameterInfo]
    
    def has_width_mismatch(self) -> bool:
        """ビット幅の不一致があるか"""
        if self.param1 is None or self.param2 is None:
            return True
        return self.param1.bit_width != self.param2.bit_width
    
    def get_overlapping_width(self) -> int:
        """重複するビット幅を取得（小さい方）"""
        if self.param1 is None or self.param2 is None:
            return 0
        return min(self.param1.bit_width, self.param2.bit_width)
    
    def get_larger_width(self) -> int:
        """大きい方のビット幅を取得"""
        w1 = self.param1.bit_width if self.param1 else 0
        w2 = self.param2.bit_width if self.param2 else 0
        return max(w1, w2)


class FormulaBuilder:
    """2つの関数解析結果からSMT式を構築"""
    
    def __init__(self, debug: bool = False, upper_bits_zero: bool = False):
        """
        Args:
            debug: デバッグモード
            upper_bits_zero: ビット幅が異なる場合に上位ビットを0に制約するか
                             False（デフォルト）: 上位ビットは自由（ランダム）
                             True: 上位ビットは0に制約
        """
        self.debug = debug
        self.upper_bits_zero = upper_bits_zero
    
    def build_equivalence_formula(
        self,
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        func1_suffix: str = "_1",
        func2_suffix: str = "_2"
    ) -> Tuple[str, str, str]:
        """
        2つの関数の等価性検証用SMT式を構築
        
        ビット幅が異なる場合:
        - 重複するビット（下位ビット）は同一にする
        - upper_bits_zero=False: 上位ビットは自由（任意の値）
        - upper_bits_zero=True: 上位ビットは0に制約
        """
        lines = []
        
        # 上位ビットモードの説明を追加
        upper_bits_mode_desc = "zero (constrained)" if self.upper_bits_zero else "free (any value)"
        
        # ヘッダー
        lines.append("; " + "=" * 60)
        lines.append("; Equivalence Check")
        lines.append(f"; Function 1: {analysis1.function_name}")
        lines.append(f"; Function 2: {analysis2.function_name}")
        lines.append(f"; Upper bits mode: {upper_bits_mode_desc}")
        lines.append("; " + "=" * 60)
        lines.append("")
        lines.append("(set-logic QF_BV)")
        lines.append("")
        
        # 各関数のパラメータ情報を収集
        params1 = self._collect_param_info(analysis1.parameters, func1_suffix)
        params2 = self._collect_param_info(analysis2.parameters, func2_suffix)
        
        if self.debug:
            print(f"[FormulaBuilder] Function 1 parameters:")
            for p in params1:
                print(f"  {p.original_name} -> {p.smt_name} ({p.bit_width}bit)")
            print(f"[FormulaBuilder] Function 2 parameters:")
            for p in params2:
                print(f"  {p.original_name} -> {p.smt_name} ({p.bit_width}bit)")
            print(f"[FormulaBuilder] Upper bits mode: {upper_bits_mode_desc}")
        
        # パラメータペアを構築
        param_pairs = self._build_parameter_pairs(params1, params2)
        
        # 関数1のパラメータを宣言
        lines.append("; " + "-" * 40)
        lines.append(f"; Parameters for {analysis1.function_name}")
        lines.append("; (Bit widths from Ghidra analysis)")
        lines.append("; " + "-" * 40)
        for p in params1:
            lines.append(f"(declare-const {p.smt_name} (_ BitVec {p.bit_width}))")
        lines.append("")
        
        # 関数2のパラメータを宣言
        lines.append("; " + "-" * 40)
        lines.append(f"; Parameters for {analysis2.function_name}")
        lines.append("; (Bit widths from Ghidra analysis)")
        lines.append("; " + "-" * 40)
        for p in params2:
            lines.append(f"(declare-const {p.smt_name} (_ BitVec {p.bit_width}))")
        lines.append("")
        
        # パラメータ間の等価制約
        lines.append("; " + "-" * 40)
        lines.append("; Parameter equality constraints")
        lines.append("; For matching bit widths: direct equality")
        if self.upper_bits_zero:
            lines.append("; For different bit widths: overlapping bits equal, upper bits = 0")
        else:
            lines.append("; For different bit widths: overlapping bits equal, upper bits free")
        lines.append("; " + "-" * 40)
        
        for pair in param_pairs:
            constraint_lines = self._build_parameter_constraint(pair)
            lines.extend(constraint_lines)
        
        lines.append("")
        
        # 関数1のreturn値を定義
        lines.append("; " + "-" * 40)
        lines.append(f"; Return value for {analysis1.function_name}")
        lines.append("; " + "-" * 40)
        return_var1 = f"return{func1_suffix}"
        return_def1 = self._build_return_definition(
            analysis1, return_var1, params1
        )
        lines.extend(return_def1)
        lines.append("")
        
        # 関数2のreturn値を定義
        lines.append("; " + "-" * 40)
        lines.append(f"; Return value for {analysis2.function_name}")
        lines.append("; " + "-" * 40)
        return_var2 = f"return{func2_suffix}"
        return_def2 = self._build_return_definition(
            analysis2, return_var2, params2
        )
        lines.extend(return_def2)
        lines.append("")
        
        # return値のビット幅を取得
        return_size1 = self._get_return_size(analysis1)
        return_size2 = self._get_return_size(analysis2)
        
        # 等価性の否定をアサート
        lines.append("; " + "-" * 40)
        lines.append("; Equivalence assertion (negated)")
        lines.append("; If SAT: functions are NOT equivalent")
        lines.append("; If UNSAT: functions ARE equivalent")
        lines.append("; " + "-" * 40)
        
        if return_size1 == return_size2:
            lines.append(f"(assert (not (= {return_var1} {return_var2})))")
        else:
            # return値のビット幅が異なる場合も重複ビットで比較
            overlap_size = min(return_size1, return_size2)
            lines.append(f"; Return sizes differ: {return_size1} vs {return_size2}")
            lines.append(f"; Comparing overlapping {overlap_size} bits")
            if return_size1 < return_size2:
                lines.append(f"(assert (not (= {return_var1} ((_ extract {overlap_size - 1} 0) {return_var2}))))")
            else:
                lines.append(f"(assert (not (= ((_ extract {overlap_size - 1} 0) {return_var1}) {return_var2})))")
        
        lines.append("")
        lines.append("(check-sat)")
        lines.append("(get-model)")
        
        return "\n".join(lines), return_var1, return_var2
    
    def _collect_param_info(
        self,
        params: List[Dict],
        suffix: str
    ) -> List[ParameterInfo]:
        """パラメータ情報を収集"""
        result = []
        for param in params:
            name = param.get('name', f"param_{param.get('index', 0)}")
            size = param.get('size', 4) * 8
            index = param.get('index', 0)
            smt_name = f"{name}{suffix}"
            
            result.append(ParameterInfo(
                original_name=name,
                smt_name=smt_name,
                bit_width=size,
                index=index
            ))
        
        result.sort(key=lambda x: x.index)
        return result
    
    def _build_parameter_pairs(
        self,
        params1: List[ParameterInfo],
        params2: List[ParameterInfo]
    ) -> List[ParameterPair]:
        """パラメータペアを構築"""
        pairs = []
        
        all_indices = set()
        p1_by_index = {}
        p2_by_index = {}
        
        for p in params1:
            p1_by_index[p.index] = p
            all_indices.add(p.index)
        
        for p in params2:
            p2_by_index[p.index] = p
            all_indices.add(p.index)
        
        for idx in sorted(all_indices):
            pairs.append(ParameterPair(
                index=idx,
                param1=p1_by_index.get(idx),
                param2=p2_by_index.get(idx)
            ))
        
        return pairs
    
    def _build_parameter_constraint(self, pair: ParameterPair) -> List[str]:
        """
        パラメータ間の制約を構築
        
        - 同じビット幅: 直接等価
        - 異なるビット幅: 重複するビット（下位ビット）のみ等価
          - upper_bits_zero=False: 上位ビットは自由（ランダム）
          - upper_bits_zero=True: 上位ビットは0に制約
        """
        lines = []
        
        if pair.param1 is None or pair.param2 is None:
            lines.append(f"; Parameter index {pair.index}: missing in one function")
            return lines
        
        p1 = pair.param1
        p2 = pair.param2
        
        if not pair.has_width_mismatch():
            # 同じビット幅：直接比較
            lines.append(f"; {p1.smt_name} and {p2.smt_name}: same width ({p1.bit_width}bit)")
            lines.append(f"(assert (= {p1.smt_name} {p2.smt_name}))")
        else:
            # 異なるビット幅：重複ビットのみ等価
            overlap_bits = pair.get_overlapping_width()
            
            lines.append(f"; {p1.smt_name} ({p1.bit_width}bit) vs {p2.smt_name} ({p2.bit_width}bit)")
            lines.append(f"; Overlapping bits: {overlap_bits}")
            lines.append(f"; Constraint: lower {overlap_bits} bits are equal")
            
            if p1.bit_width < p2.bit_width:
                # p1が小さい: p1全体 = p2の下位ビット
                lines.append(f"(assert (= {p1.smt_name} ((_ extract {overlap_bits - 1} 0) {p2.smt_name})))")
                
                if self.upper_bits_zero:
                    # 上位ビットを0に制約
                    upper_bits_width = p2.bit_width - overlap_bits
                    lines.append(f"; Upper bits of {p2.smt_name} [{p2.bit_width - 1}:{overlap_bits}] constrained to 0")
                    lines.append(f"(assert (= ((_ extract {p2.bit_width - 1} {overlap_bits}) {p2.smt_name}) (_ bv0 {upper_bits_width})))")
                else:
                    lines.append(f"; Upper bits of {p2.smt_name} [{p2.bit_width - 1}:{overlap_bits}] are free")
            else:
                # p2が小さい: p1の下位ビット = p2全体
                lines.append(f"(assert (= ((_ extract {overlap_bits - 1} 0) {p1.smt_name}) {p2.smt_name}))")
                
                if self.upper_bits_zero:
                    # 上位ビットを0に制約
                    upper_bits_width = p1.bit_width - overlap_bits
                    lines.append(f"; Upper bits of {p1.smt_name} [{p1.bit_width - 1}:{overlap_bits}] constrained to 0")
                    lines.append(f"(assert (= ((_ extract {p1.bit_width - 1} {overlap_bits}) {p1.smt_name}) (_ bv0 {upper_bits_width})))")
                else:
                    lines.append(f"; Upper bits of {p1.smt_name} [{p1.bit_width - 1}:{overlap_bits}] are free")
        
        return lines
    
    def _get_return_size(self, analysis: FunctionReturnAnalysis) -> int:
        """return値のビット幅を取得"""
        if analysis.returns:
            first_ret = analysis.returns[0]
            if hasattr(first_ret.value, 'size') and first_ret.value.size:
                return first_ret.value.size * 8
        return 32
    
    def _build_return_definition(
        self,
        analysis: FunctionReturnAnalysis,
        return_var_name: str,
        param_infos: List[ParameterInfo]
    ) -> List[str]:
        """return値の定義を構築"""
        lines = []
        
        return_size = self._get_return_size(analysis)
        
        return_defs = []
        for i, ret in enumerate(analysis.returns):
            if ret.conditions:
                cond_parts = []
                for c in ret.conditions:
                    cond_smt = c.to_smt()
                    cond_smt = self._replace_param_names(cond_smt, param_infos)
                    cond_parts.append(cond_smt)
                
                if len(cond_parts) == 1:
                    cond_str = cond_parts[0]
                else:
                    cond_str = f"(and {' '.join(cond_parts)})"
            else:
                cond_str = "true"
            
            value_smt = ret.value.to_smt()
            value_smt = self._replace_param_names(value_smt, param_infos)
            
            return_defs.append({
                "condition": cond_str,
                "value": value_smt
            })
        
        if return_defs:
            unified_return = self._build_ite_expression(return_defs)
        else:
            unified_return = f"(_ bv0 {return_size})"
        
        lines.append(f"(define-fun {return_var_name} () (_ BitVec {return_size})")
        lines.append(f"  {unified_return})")
        
        return lines
    
    def _replace_param_names(
        self,
        smt_expr: str,
        param_infos: List[ParameterInfo]
    ) -> str:
        """SMT式内のパラメータ名を置換"""
        result = smt_expr
        sorted_params = sorted(param_infos, key=lambda p: -len(p.original_name))
        
        for param in sorted_params:
            pattern = r'\b' + re.escape(param.original_name) + r'\b'
            result = re.sub(pattern, param.smt_name, result)
        
        return result
    
    def _build_ite_expression(self, return_defs: List[dict]) -> str:
        """ite式を構築"""
        if not return_defs:
            return "(_ bv0 32)"
        
        if len(return_defs) == 1:
            return return_defs[0]["value"]
        
        result = return_defs[-1]["value"]
        
        for i in range(len(return_defs) - 2, -1, -1):
            ret_def = return_defs[i]
            cond = ret_def["condition"]
            value = ret_def["value"]
            
            if cond == "true":
                result = value
            else:
                result = f"(ite {cond} {value} {result})"
        
        return result
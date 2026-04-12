# -*- coding: utf-8 -*-
"""追加変数の分析モジュール

パラメータ以外の変数（in_a1_hi等）を検出・分析し、
ストレージ情報に基づいてパラメータ断片かどうかを判定する。

パラメータ断片と判定された場合は、0固定ではなく
sign/zero extension から導かれる値として拘束する。
"""

from typing import List, Dict, Set, Optional, Tuple
from dataclasses import dataclass
from enum import Enum, auto

from ...model import Expression, ExpressionType, Condition, StorageInfo, FunctionReturnAnalysis


class VariableClassification(Enum):
    """変数の分類"""
    PARAMETER = auto()              # パラメータ本体
    PARAMETER_FRAGMENT = auto()     # パラメータの上位ビット断片（sign/zero ext制約が必要）
    INDEPENDENT_INPUT = auto()      # 独立した入力変数
    UNKNOWN = auto()                # 分類不明


class ExtensionType(Enum):
    """拡張タイプ"""
    SIGN_EXTEND = auto()   # 符号拡張
    ZERO_EXTEND = auto()   # ゼロ拡張


@dataclass
class ParameterFragmentInfo:
    """パラメータ断片の情報"""
    fragment_name: str
    fragment_bit_width: int
    parent_param_name: str
    parent_param_index: int
    parent_param_bit_width: int
    extension_type: ExtensionType
    bit_offset_in_base: int      # 断片のビットオフセット（親レジスタ内）
    bit_length: int              # 断片のビット長
    base_register_name: str
    base_register_size_bits: int
    
    def get_smt_constraint(self, fragment_smt_name: str, param_smt_name: str) -> str:
        """
        SMT制約を生成
        
        断片 = extract(extend(param), high_bit, low_bit)
        
        符号拡張/ゼロ拡張後の上位ビットを抽出する。
        メモリ配置（エンディアン）に関係なく、値としての上位ビットを取得。
        
        例: in_a1_hi (32bit) = extract(sign_extend(param_2, 64), 63, 32)
        """
        extend_bits = self.base_register_size_bits - self.parent_param_bit_width
        
        if extend_bits <= 0:
            # 拡張不要の場合（通常は発生しない）
            extended = param_smt_name
        elif self.extension_type == ExtensionType.SIGN_EXTEND:
            extended = f"((_ sign_extend {extend_bits}) {param_smt_name})"
        else:
            extended = f"((_ zero_extend {extend_bits}) {param_smt_name})"
        
        # 上位ビットを抽出（値としての上位、メモリ配置ではない）
        # sign_extend/zero_extend は常に上位ビットに拡張される
        high_bit = self.base_register_size_bits - 1
        low_bit = self.parent_param_bit_width
        
        return f"(assert (= {fragment_smt_name} ((_ extract {high_bit} {low_bit}) {extended})))"
    
    def get_reason_string(self) -> str:
        """制約の理由を説明する文字列"""
        ext_str = "sign_extend" if self.extension_type == ExtensionType.SIGN_EXTEND else "zero_extend"
        return (f"Upper bits of {self.parent_param_name} in {self.base_register_name} "
                f"(constrained via {ext_str})")
    
    def to_dict(self) -> Dict:
        return {
            "fragment_name": self.fragment_name,
            "fragment_bit_width": self.fragment_bit_width,
            "parent_param_name": self.parent_param_name,
            "parent_param_index": self.parent_param_index,
            "parent_param_bit_width": self.parent_param_bit_width,
            "extension_type": self.extension_type.name,
            "bit_offset_in_base": self.bit_offset_in_base,
            "bit_length": self.bit_length,
            "base_register_name": self.base_register_name,
            "base_register_size_bits": self.base_register_size_bits,
        }


@dataclass
class ExtraVariableAnalysis:
    """追加変数の分析結果"""
    name: str
    bit_width: int
    classification: VariableClassification
    fragment_info: Optional[ParameterFragmentInfo] = None
    reason: str = ""
    
    def is_parameter_fragment(self) -> bool:
        """パラメータ断片かどうか"""
        return self.classification == VariableClassification.PARAMETER_FRAGMENT
    
    def can_safely_constrain(self) -> bool:
        """安全に制約できるか（パラメータ断片の場合）"""
        return self.is_parameter_fragment() and self.fragment_info is not None
    
    def get_smt_constraint(self, fragment_smt_name: str, param_smt_name: str) -> Optional[str]:
        """SMT制約を取得"""
        if self.fragment_info:
            return self.fragment_info.get_smt_constraint(fragment_smt_name, param_smt_name)
        return None
    
    def to_dict(self) -> Dict:
        result = {
            "name": self.name,
            "bit_width": self.bit_width,
            "classification": self.classification.name,
            "reason": self.reason,
        }
        if self.fragment_info:
            result["fragment_info"] = self.fragment_info.to_dict()
        return result


class VariableAnalyzer:
    """追加変数を分析するクラス（ストレージベース判定）"""
    
    def __init__(self, debug: bool = False):
        self.debug = debug
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[VariableAnalyzer] {msg}")
    
    def classify_variable_by_storage(
        self,
        var_name: str,
        var_storage: Optional[StorageInfo],
        var_bit_width: int,
        parameters: List[Dict]
    ) -> ExtraVariableAnalysis:
        """
        ストレージ情報を使用して変数を分類する
        """
        self._debug_print(f"Classifying variable '{var_name}' ({var_bit_width}bit) by storage")
        
        if var_storage is None:
            self._debug_print(f"  -> UNKNOWN: No storage info available")
            return ExtraVariableAnalysis(
                name=var_name,
                bit_width=var_bit_width,
                classification=VariableClassification.UNKNOWN,
                reason="No storage information available"
            )
        
        if not var_storage.is_register:
            self._debug_print(f"  -> INDEPENDENT_INPUT: Not a register")
            return ExtraVariableAnalysis(
                name=var_name,
                bit_width=var_bit_width,
                classification=VariableClassification.INDEPENDENT_INPUT,
                reason="Not a register-based variable"
            )
        
        self._debug_print(f"  Variable storage: reg={var_storage.register_name}, "
                        f"base={var_storage.base_register_name}, "
                        f"offset={var_storage.bit_offset_in_base}bit, "
                        f"size={var_storage.size_bits}bit, "
                        f"base_size={var_storage.base_register_size_bits}bit")
        
        for param in parameters:
            param_storage_dict = param.get("storage")
            if param_storage_dict is None:
                continue
            
            param_storage_info = self._dict_to_storage_info(param_storage_dict)
            if param_storage_info is None or not param_storage_info.is_register:
                continue
            
            param_name = param.get('name', 'unknown')
            self._debug_print(f"  Checking against param '{param_name}': "
                            f"reg={param_storage_info.register_name}, "
                            f"base={param_storage_info.base_register_name}, "
                            f"offset={param_storage_info.bit_offset_in_base}bit, "
                            f"size={param_storage_info.size_bits}bit")
            
            # 同一の親レジスタを共有するかチェック
            if not var_storage.shares_base_register_with(param_storage_info):
                self._debug_print(f"    -> Different base register")
                continue
            
            # パラメータの型幅が親レジスタ幅より小さいかチェック
            if param_storage_info.size_bits >= param_storage_info.base_register_size_bits:
                self._debug_print(f"    -> Parameter occupies full register")
                continue
            
            # 変数がパラメータの補完部分（上位ビット）かチェック
            if var_storage.is_upper_bits_of(param_storage_info):
                is_signed = param.get("is_signed", True)
                ext_type = ExtensionType.SIGN_EXTEND if is_signed else ExtensionType.ZERO_EXTEND
                
                fragment_info = ParameterFragmentInfo(
                    fragment_name=var_name,
                    fragment_bit_width=var_bit_width,
                    parent_param_name=param_name,
                    parent_param_index=param.get("index", -1),
                    parent_param_bit_width=param_storage_info.size_bits,
                    extension_type=ext_type,
                    bit_offset_in_base=var_storage.bit_offset_in_base,
                    bit_length=var_storage.size_bits,
                    base_register_name=var_storage.base_register_name or "",
                    base_register_size_bits=var_storage.base_register_size_bits
                )
                
                self._debug_print(f"  -> PARAMETER_FRAGMENT: parent={param_name}, "
                                f"ext_type={ext_type.name}, "
                                f"constraint: extract({var_storage.base_register_size_bits-1}, "
                                f"{param_storage_info.size_bits})")
                
                return ExtraVariableAnalysis(
                    name=var_name,
                    bit_width=var_bit_width,
                    classification=VariableClassification.PARAMETER_FRAGMENT,
                    fragment_info=fragment_info,
                    reason=fragment_info.get_reason_string()
                )
            else:
                self._debug_print(f"    -> Not a complement (overlapping or non-adjacent)")
        
        self._debug_print(f"  -> INDEPENDENT_INPUT: No matching parameter found")
        return ExtraVariableAnalysis(
            name=var_name,
            bit_width=var_bit_width,
            classification=VariableClassification.INDEPENDENT_INPUT,
            reason="Register-based but no matching parameter fragment"
        )
    
    def _dict_to_storage_info(self, storage_dict: Dict) -> Optional[StorageInfo]:
        """辞書からStorageInfoを作成"""
        if not storage_dict:
            return None
        
        return StorageInfo(
            is_register=storage_dict.get("is_register", False),
            space_name=storage_dict.get("space_name", ""),
            offset=storage_dict.get("offset", 0),
            size=storage_dict.get("size", 0),
            size_bits=storage_dict.get("size_bits", 0),
            register_name=storage_dict.get("register_name"),
            base_register_name=storage_dict.get("base_register_name"),
            base_register_offset=storage_dict.get("base_register_offset", 0),
            base_register_size=storage_dict.get("base_register_size", 0),
            base_register_size_bits=storage_dict.get("base_register_size_bits", 0),
            bit_offset_in_base=storage_dict.get("bit_offset_in_base", 0)
        )
    
    def analyze_all_extra_variables(
        self,
        analysis: FunctionReturnAnalysis,
        param_names: Set[str],
        return_bit_width: int
    ) -> Dict[str, ExtraVariableAnalysis]:
        """
        全ての追加変数を分析
        
        Args:
            analysis: 関数解析結果
            param_names: パラメータ名のセット
            return_bit_width: 戻り値のビット幅
        
        Returns:
            変数名 -> 分析結果 のマッピング
        """
        # 全変数とストレージ情報を収集
        all_vars_with_storage: Dict[str, Optional[StorageInfo]] = {}
        var_sizes: Dict[str, int] = {}
        
        for ret in analysis.returns:
            if hasattr(ret.value, 'get_all_variables_with_storage'):
                vars_in_expr = ret.value.get_all_variables_with_storage()
                for name, storage in vars_in_expr.items():
                    if name not in all_vars_with_storage:
                        all_vars_with_storage[name] = storage
                self._collect_variable_sizes(ret.value, var_sizes)
            
            for cond in ret.conditions:
                if hasattr(cond, 'get_all_variables_with_storage'):
                    vars_in_cond = cond.get_all_variables_with_storage()
                    for name, storage in vars_in_cond.items():
                        if name not in all_vars_with_storage:
                            all_vars_with_storage[name] = storage
                    if hasattr(cond, 'expression'):
                        self._collect_variable_sizes(cond.expression, var_sizes)
        
        # パラメータ以外の変数を抽出
        extra_var_names = {
            name
            for name in (set(all_vars_with_storage.keys()) - param_names)
            if not str(name).startswith("__locread__")
        }
        
        self._debug_print(f"Found {len(extra_var_names)} extra variables: {extra_var_names}")

        # === デバッグ: ストレージ情報の確認 ===
        if self.debug:
            print("\n" + "=" * 60)
            print("[DEBUG] Variable Storage Information")
            print("=" * 60)
            for name in extra_var_names:
                storage = all_vars_with_storage.get(name)
                print(f"  Variable: {name}")
                if storage is None:
                    print(f"    -> StorageInfo: None (NOT COLLECTED)")
                else:
                    print(f"    -> is_register: {storage.is_register}")
                    print(f"    -> register_name: {storage.register_name}")
                    print(f"    -> base_register_name: {storage.base_register_name}")
                    print(f"    -> bit_offset_in_base: {storage.bit_offset_in_base}")
                    print(f"    -> size_bits: {storage.size_bits}")
                    print(f"    -> base_register_size_bits: {storage.base_register_size_bits}")
            
            print("\n[DEBUG] Parameter Storage Information")
            for param in analysis.parameters:
                print(f"  Parameter: {param.get('name')}")
                storage = param.get('storage')
                if storage is None:
                    print(f"    -> storage: None")
                else:
                    print(f"    -> is_register: {storage.get('is_register')}")
                    print(f"    -> register_name: {storage.get('register_name')}")
                    print(f"    -> base_register_name: {storage.get('base_register_name')}")
                    print(f"    -> bit_offset_in_base: {storage.get('bit_offset_in_base')}")
                    print(f"    -> size_bits: {storage.get('size_bits')}")
                    print(f"    -> base_register_size_bits: {storage.get('base_register_size_bits')}")
            print("=" * 60 + "\n")
        
        # 各変数を分析
        results = {}
        for var_name in sorted(extra_var_names):
            var_storage = all_vars_with_storage.get(var_name)
            bit_width = var_sizes.get(var_name, 32)
            
            results[var_name] = self.classify_variable_by_storage(
                var_name, var_storage, bit_width, analysis.parameters
            )
        
        return results
    
    def _collect_variable_sizes(
        self,
        expr: Expression,
        var_sizes: Dict[str, int]
    ) -> None:
        """式から変数のサイズを収集"""
        if expr.expr_type in (ExpressionType.VARIABLE, ExpressionType.PARAMETER):
            if expr.name and expr.name not in var_sizes:
                if expr.size and expr.size > 0:
                    var_sizes[expr.name] = expr.size * 8
                else:
                    var_sizes[expr.name] = expr.get_bit_width()
        
        for operand in expr.operands:
            self._collect_variable_sizes(operand, var_sizes)
        
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, val in expr.value:
                if hasattr(val, 'expr_type'):
                    self._collect_variable_sizes(val, var_sizes)


def get_parameter_fragment_constraints(
    analyses: Dict[str, ExtraVariableAnalysis],
    suffix: str
) -> Tuple[List[str], List[str]]:
    """
    パラメータ断片のSMT制約を生成
    
    Args:
        analyses: 変数名 -> 分析結果 のマッピング
        suffix: SMT変数名のサフィックス（"_1" or "_2"）
    
    Returns:
        (制約行のリスト, 制約された変数名のリスト)
    """
    lines = []
    constrained_vars = []
    
    for name, analysis in analyses.items():
        if analysis.is_parameter_fragment() and analysis.fragment_info:
            fragment_smt = f"{name}{suffix}"
            param_smt = f"{analysis.fragment_info.parent_param_name}{suffix}"
            
            constraint = analysis.get_smt_constraint(fragment_smt, param_smt)
            if constraint:
                lines.append(f"; {name}: {analysis.reason}")
                lines.append(constraint)
                constrained_vars.append(fragment_smt)
    
    return lines, constrained_vars

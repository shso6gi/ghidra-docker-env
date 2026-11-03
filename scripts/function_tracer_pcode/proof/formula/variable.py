# -*- coding: utf-8 -*-
"""追加変数の分析モジュール

パラメータ以外の変数（in_a1_hi等）を検出・分析し、
ストレージ情報に基づいてパラメータ断片かどうかを判定する。

パラメータ断片と判定しても SMT 上では拘束しない（自由な入力のまま）。
「上位 bit は ext(param) に等しい」は入力 extension 仮定であり、その根拠は
Ghidra の ``is_signed`` ではなく最終 ``InputCorrespondence``
（``proof/formula/input_correspondence``）だけが持てる（Issue #167）。
断片の有無は raw closure 走査が register alias として扱う。
"""

from typing import List, Dict, Set, Optional, Tuple
from dataclasses import dataclass
from enum import Enum, auto

from scripts.function_tracer_pcode.core import (
    AddressValueRef,
    Expression,
    ExpressionType,
    StorageInfo,
    FunctionReturnAnalysis,
    CanonicalLocation,
)


from scripts.function_tracer_pcode.core.observation_index import is_observation_index  # noqa: E402


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
    
    def get_reason_string(self) -> str:
        """診断用の説明（``extension_type`` は Ghidra の型ラベル由来で、制約には使わない）"""
        ext_str = "sign_extend" if self.extension_type == ExtensionType.SIGN_EXTEND else "zero_extend"
        return (f"Upper bits of {self.parent_param_name} in {self.base_register_name} "
                f"(declared-type label {ext_str}; unconstrained)")
    
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

    def _is_symbolic_location_read_expr(self, expr: Optional[Expression]) -> bool:
        runtime_ref = getattr(expr, "runtime_ref", None)
        if isinstance(runtime_ref, CanonicalLocation):
            return True
        return isinstance(getattr(runtime_ref, "location", None), CanonicalLocation)

    def _is_concrete_address_expr(self, expr: Optional[Expression]) -> bool:
        runtime_ref = getattr(expr, "runtime_ref", None)
        return isinstance(runtime_ref, AddressValueRef) and runtime_ref.has_concrete_address()

    def _describe_expression_origin(self, expr: Optional[Expression]) -> str:
        if expr is None:
            return "origin=missing_expr"

        parts = []
        runtime_ref = getattr(expr, "runtime_ref", None)
        if isinstance(runtime_ref, AddressValueRef):
            parts.append(
                "runtime_ref="
                f"AddressValueRef(offset=0x{int(runtime_ref.address_offset):x},"
                f"source={runtime_ref.source},space={runtime_ref.space_name},"
                f"symbol={runtime_ref.symbol_name},block={runtime_ref.block_name},"
                f"readonly={runtime_ref.is_readonly_memory()})"
            )
        elif runtime_ref is None:
            parts.append("runtime_ref=None")
        else:
            parts.append(f"runtime_ref={type(runtime_ref).__name__}")

        storage = getattr(expr, "storage_info", None)
        if storage is None:
            parts.append("storage=None")
        else:
            parts.append(
                "storage="
                f"{storage.space_name}:off=0x{int(storage.offset or 0):x}:"
                f"size={int(storage.size or 0)}:reg={storage.register_name}:"
                f"base={storage.base_register_name}"
            )

        parts.append(f"expr_type={expr.expr_type.name}")
        parts.append(f"size={int(expr.size or 0)}")
        return ", ".join(parts)

    def _collect_variable_exprs(
        self,
        expr: Optional[Expression],
        collected: Dict[str, Expression],
    ) -> None:
        if expr is None:
            return
        if expr.expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
            if expr.name and expr.name not in collected:
                collected[expr.name] = expr
            return
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None:
                    self._collect_variable_exprs(cond.expression, collected)
                self._collect_variable_exprs(value, collected)
            return
        for operand in getattr(expr, "operands", []) or []:
            self._collect_variable_exprs(operand, collected)

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
            self._debug_print("  -> UNKNOWN: No storage info available")
            return ExtraVariableAnalysis(
                name=var_name,
                bit_width=var_bit_width,
                classification=VariableClassification.UNKNOWN,
                reason="No storage information available"
            )
        
        if not var_storage.is_register:
            self._debug_print("  -> INDEPENDENT_INPUT: Not a register")
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
                self._debug_print("    -> Different base register")
                continue
            
            # パラメータの型幅が親レジスタ幅より小さいかチェック
            if param_storage_info.size_bits >= param_storage_info.base_register_size_bits:
                self._debug_print("    -> Parameter occupies full register")
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
                self._debug_print("    -> Not a complement (overlapping or non-adjacent)")
        
        self._debug_print("  -> INDEPENDENT_INPUT: No matching parameter found")
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
        all_var_exprs: Dict[str, Expression] = {}
        var_sizes: Dict[str, int] = {}
        inferred_fragments: Dict[str, ParameterFragmentInfo] = {}

        for ret in analysis.returns:
            if ret.value is not None:
                self._collect_variable_exprs(ret.value, all_var_exprs)
                self._collect_variable_sizes(ret.value, var_sizes)
                self._collect_expression_fragment_bindings(ret.value, analysis.parameters, inferred_fragments)
            
            for cond in ret.conditions:
                if hasattr(cond, 'expression'):
                    self._collect_variable_exprs(cond.expression, all_var_exprs)
                    self._collect_variable_sizes(cond.expression, var_sizes)
                    self._collect_expression_fragment_bindings(
                        cond.expression,
                        analysis.parameters,
                        inferred_fragments,
                    )

        for name, expr in all_var_exprs.items():
            if name not in all_vars_with_storage:
                all_vars_with_storage[name] = expr.storage_info

        # パラメータ以外の変数を抽出
        extra_var_names = {
            name
            for name, expr in all_var_exprs.items()
            if (
                name not in param_names
                and not self._is_symbolic_location_read_expr(expr)
                and not self._is_concrete_address_expr(expr)
                # store の観測の番地は入力ではなく、左右で同じ記号（Issue #282: `core.observation_index`）
                and not is_observation_index(expr)
            )
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
                    print("    -> StorageInfo: None (NOT COLLECTED)")
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
                    print("    -> storage: None")
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
            expr = all_var_exprs.get(var_name)

            storage_result = self.classify_variable_by_storage(
                var_name, var_storage, bit_width, analysis.parameters
            )
            inferred_fragment = inferred_fragments.get(var_name)
            if (
                inferred_fragment is not None
                and storage_result.classification in {
                    VariableClassification.UNKNOWN,
                    VariableClassification.INDEPENDENT_INPUT,
                }
            ):
                results[var_name] = ExtraVariableAnalysis(
                    name=var_name,
                    bit_width=bit_width,
                    classification=VariableClassification.PARAMETER_FRAGMENT,
                    fragment_info=inferred_fragment,
                    reason=inferred_fragment.get_reason_string(),
                )
                continue
            origin_details = self._describe_expression_origin(expr)
            base_reason = storage_result.reason or "No classification reason"
            storage_result.reason = f"{base_reason}; {origin_details}"
            results[var_name] = storage_result
        
        return results

    def _collect_expression_fragment_bindings(
        self,
        expr: Optional[Expression],
        parameters: List[Dict],
        inferred_fragments: Dict[str, ParameterFragmentInfo],
    ) -> None:
        if expr is None:
            return
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None:
                    self._collect_expression_fragment_bindings(
                        cond.expression,
                        parameters,
                        inferred_fragments,
                    )
                self._collect_expression_fragment_bindings(
                    value,
                    parameters,
                    inferred_fragments,
                )
            return

        fragment_info = self._infer_fragment_from_expression(expr, parameters)
        if fragment_info is not None:
            inferred_fragments.setdefault(fragment_info.fragment_name, fragment_info)

        for operand in expr.operands:
            self._collect_expression_fragment_bindings(operand, parameters, inferred_fragments)

    def _infer_fragment_from_expression(
        self,
        expr: Expression,
        parameters: List[Dict],
    ) -> Optional[ParameterFragmentInfo]:
        if expr.expr_type != ExpressionType.BINARY_OP or len(expr.operands) != 2:
            return None

        high_expr: Optional[Expression] = None
        low_expr: Optional[Expression] = None
        total_bits: Optional[int] = None

        if expr.operator == "PIECE":
            high_expr, low_expr = expr.operands
            total_bits = high_expr.get_bit_width() + low_expr.get_bit_width()
        elif expr.operator == "INT_OR":
            high_expr, low_expr, total_bits = self._match_shift_or_fragment(expr)
        else:
            return None

        if high_expr is None or low_expr is None or total_bits is None:
            return None
        if high_expr.expr_type != ExpressionType.VARIABLE or not high_expr.name:
            return None
        if low_expr.expr_type != ExpressionType.PARAMETER or not low_expr.name:
            return None

        param = next((item for item in parameters if item.get("name") == low_expr.name), None)
        if param is None:
            return None

        parent_bits = max(1, int(param.get("size", low_expr.size or 4) or 4) * 8)
        fragment_bits = high_expr.get_bit_width()
        if parent_bits <= 0 or fragment_bits <= 0 or total_bits != parent_bits + fragment_bits:
            return None

        high_storage = high_expr.storage_info
        low_storage = self._dict_to_storage_info(param.get("storage")) or low_expr.storage_info
        if high_storage is not None and low_storage is not None:
            try:
                if not (
                    high_storage.is_register
                    and low_storage.is_register
                    and high_storage.shares_base_register_with(low_storage)
                    and high_storage.is_upper_bits_of(low_storage)
                ):
                    return None
            except Exception:
                return None
            bit_offset_in_base = int(high_storage.bit_offset_in_base)
            bit_length = int(high_storage.size_bits or fragment_bits)
            base_register_name = (
                high_storage.base_register_name
                or high_storage.register_name
                or high_expr.name
            )
            base_register_size_bits = int(high_storage.base_register_size_bits or total_bits)
        else:
            bit_offset_in_base = parent_bits
            bit_length = fragment_bits
            base_register_name = high_expr.name
            base_register_size_bits = total_bits

        is_signed = bool(param.get("is_signed", True))
        return ParameterFragmentInfo(
            fragment_name=high_expr.name,
            fragment_bit_width=fragment_bits,
            parent_param_name=low_expr.name,
            parent_param_index=int(param.get("index", -1)),
            parent_param_bit_width=parent_bits,
            extension_type=ExtensionType.SIGN_EXTEND if is_signed else ExtensionType.ZERO_EXTEND,
            bit_offset_in_base=bit_offset_in_base,
            bit_length=bit_length,
            base_register_name=base_register_name,
            base_register_size_bits=base_register_size_bits,
        )

    def _match_shift_or_fragment(
        self,
        expr: Expression,
    ) -> Tuple[Optional[Expression], Optional[Expression], Optional[int]]:
        left_expr, right_expr = expr.operands
        matched = self._match_shift_or_operands(left_expr, right_expr, expr.get_bit_width())
        if matched is not None:
            return matched
        matched = self._match_shift_or_operands(right_expr, left_expr, expr.get_bit_width())
        if matched is not None:
            return matched
        return None, None, None

    def _match_shift_or_operands(
        self,
        shifted_expr: Expression,
        low_expr: Expression,
        total_bits: int,
    ) -> Optional[Tuple[Expression, Expression, int]]:
        if (
            shifted_expr.expr_type != ExpressionType.BINARY_OP
            or shifted_expr.operator != "INT_LEFT"
            or len(shifted_expr.operands) != 2
        ):
            return None
        shift_amount = shifted_expr.operands[1]
        if shift_amount.expr_type != ExpressionType.CONSTANT:
            return None
        if low_expr.expr_type != ExpressionType.PARAMETER or not low_expr.name:
            return None
        low_bits = low_expr.get_bit_width()
        if int(shift_amount.value) != low_bits:
            return None
        high_expr = shifted_expr.operands[0]
        if high_expr.expr_type != ExpressionType.VARIABLE or not high_expr.name:
            return None
        return high_expr, low_expr, total_bits
    
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

# -*- coding: utf-8 -*-
"""MIPS64 ABI処理モジュール"""

from typing import Dict, List, Optional, Tuple, Any
from ..model import FunctionReturnAnalysis, Expression, ExpressionType


class MIPS64Handler:
    """MIPS64 ABI処理"""
    
    def __init__(self, debug: bool = False):
        self.debug = debug
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[MIPS64Handler] {msg}")
    
    def should_apply_fix(
        self,
        is_mips64_1: bool,
        is_mips64_2: bool,
        analysis1: Optional[FunctionReturnAnalysis],
        analysis2: Optional[FunctionReturnAnalysis]
    ) -> bool:
        """MIPS64 ABIパラメータ型修正を適用すべきか判定（Phase 4-A用）"""
        if not (is_mips64_1 or is_mips64_2):
            return False
        if analysis1 is None or analysis2 is None:
            return False
        if not analysis1.parameters or not analysis2.parameters:
            return False
        return True
    
    def detect_param_type_mismatch(
        self,
        mips64_analysis: FunctionReturnAnalysis,
        other_analysis: FunctionReturnAnalysis
    ) -> Dict[int, str]:
        """
        MIPS64側とother側でパラメータ型が不一致（long vs int）の場合、
        MIPS64側をintに上書きするマップを返す（Phase 4-A用）
        
        保守的な戦略: 片側がint/uint確定、もう片側がlong/ulongの場合のみ修正
        """
        override_map: Dict[int, str] = {}
        
        for i, (mips_param, other_param) in enumerate(
            zip(mips64_analysis.parameters, other_analysis.parameters)
        ):
            mips_type = self._get_param_type_string(mips_param)
            other_type = self._get_param_type_string(other_param)
            
            if self._is_long_vs_int(mips_type, other_type):
                # other側がintならintに、uintならuintに
                if "unsigned" in other_type or "uint" in other_type:
                    override_map[i] = "unsigned int"
                else:
                    override_map[i] = "int"
                
                self._debug_print(
                    f"Param {i}: {mips_type} (MIPS64) vs {other_type} (other) "
                    f"-> override to {override_map[i]}"
                )
        
        return override_map
    
    def _get_param_type_string(self, param: Dict[str, Any]) -> str:
        """パラメータの型文字列を取得"""
        raw_dt = param.get("data_type_obj")
        if raw_dt is not None and hasattr(raw_dt, 'getName'):
            return str(raw_dt).lower().strip()
        return param.get("data_type", "").lower().strip()
    
    def _is_long_vs_int(self, type1: str, type2: str) -> bool:
        """片方がlong、もう片方がintかを判定"""
        long_keywords = ["long", "int8", "qword"]
        int_keywords = ["int", "int4", "dword"]
        
        is_long_1 = any(kw in type1 for kw in long_keywords)
        is_int_1 = any(kw in type1 for kw in int_keywords) and not is_long_1
        
        is_long_2 = any(kw in type2 for kw in long_keywords)
        is_int_2 = any(kw in type2 for kw in int_keywords) and not is_long_2
        
        return (is_long_1 and is_int_2) or (is_int_1 and is_long_2)
    
    def _get_param_size(self, param: Dict[str, Any]) -> int:
        """パラメータのサイズ（バイト数）を取得"""
        raw_dt = param.get("data_type_obj")
        if raw_dt is not None and hasattr(raw_dt, 'getLength'):
            return raw_dt.getLength()
        
        type_str = self._get_param_type_string(param)
        if any(kw in type_str for kw in ["long", "int8", "qword"]):
            return 8
        elif any(kw in type_str for kw in ["int", "int4", "dword"]):
            return 4
        elif any(kw in type_str for kw in ["short", "int2", "word"]):
            return 2
        elif any(kw in type_str for kw in ["char", "int1", "byte"]):
            return 1
        
        return 4
    
    # ===== Phase 4-B：偽反例検出（拡張版） =====
    
    def detect_spurious_counterexample(
        self,
        counterexample: Dict[str, Any],
        analysis1: FunctionReturnAnalysis,
        analysis2: FunctionReturnAnalysis,
        is_mips64_1: bool,
        is_mips64_2: bool
    ) -> Dict[str, Tuple[str, int]]:
        """
        偽反例を検出し、ABI整合制約マップを返す（拡張版）
        
        1. 幅不一致（32bit vs 64bit）のパラメータをチェック（既存）
        2. 同一幅（64bit vs 64bit）でも拡張パターンがあればチェック（新規）
        
        Args:
            counterexample: SATモデル（変数名→値のマップ）
            analysis1, analysis2: 各バイナリの関数解析結果
            is_mips64_1, is_mips64_2: MIPS64フラグ
        
        Returns:
            param名 -> (signedness, narrow_bits) のマップ
            例: {"param_1_1": ("signed", 32), "param_2_2": ("unsigned", 32)}
        """
        constraints: Dict[str, Tuple[str, int]] = {}
        
        if not (is_mips64_1 or is_mips64_2):
            return constraints
        
        min_params = min(len(analysis1.parameters), len(analysis2.parameters))
        
        # 各関数のパラメータ使用パターンを分析
        self._debug_print("Analyzing parameter usage patterns...")
        usage1 = self._analyze_parameter_usage(analysis1)
        usage2 = self._analyze_parameter_usage(analysis2)
        
        if usage1:
            self._debug_print(f"Function 1 extension patterns: {usage1}")
        if usage2:
            self._debug_print(f"Function 2 extension patterns: {usage2}")
        
        for i in range(min_params):
            p1 = analysis1.parameters[i]
            p2 = analysis2.parameters[i]
            
            size1 = self._get_param_size(p1)
            size2 = self._get_param_size(p2)
            
            param_name_1 = p1.get('name', f'param{i}')
            param_name_2 = p2.get('name', f'param{i}')
            param_key_1 = f"{param_name_1}_1"
            param_key_2 = f"{param_name_2}_2"
            
            # ケース1: 幅不一致（32bit vs 64bit）
            if {size1, size2} == {4, 8}:
                constraint = self._check_width_mismatch(
                    i, p1, p2, size1, size2,
                    param_key_1, param_key_2,
                    is_mips64_1, is_mips64_2,
                    counterexample
                )
                if constraint:
                    param_wide, signedness, narrow_bits = constraint
                    constraints[param_wide] = (signedness, narrow_bits)
            
            # ケース2: 同一幅（64bit vs 64bit）でも拡張パターンあり
            elif size1 == 8 and size2 == 8:
                pattern1 = usage1.get(param_name_1)
                pattern2 = usage2.get(param_name_2)
                
                if pattern1 and not pattern2:
                    # function1が拡張、function2が直接使用 → function2に制約
                    constraint = self._check_extension_pattern_violation(
                        param_key_2, pattern1, counterexample
                    )
                    if constraint:
                        constraints[param_key_2] = constraint
                
                elif pattern2 and not pattern1:
                    # function2が拡張、function1が直接使用 → function1に制約
                    constraint = self._check_extension_pattern_violation(
                        param_key_1, pattern2, counterexample
                    )
                    if constraint:
                        constraints[param_key_1] = constraint
                
                elif pattern1 and pattern2 and pattern1[0] != pattern2[0]:
                    # 両側とも拡張だが符号性が異なる
                    c1 = self._check_extension_pattern_violation(
                        param_key_1, pattern1, counterexample
                    )
                    c2 = self._check_extension_pattern_violation(
                        param_key_2, pattern2, counterexample
                    )
                    if c1:
                        constraints[param_key_1] = c1
                    if c2:
                        constraints[param_key_2] = c2
        
        return constraints
    
    def _check_width_mismatch(
        self,
        param_index: int,
        p1: Dict[str, Any],
        p2: Dict[str, Any],
        size1: int,
        size2: int,
        param_key_1: str,
        param_key_2: str,
        is_mips64_1: bool,
        is_mips64_2: bool,
        counterexample: Dict[str, Any]
    ) -> Optional[Tuple[str, str, int]]:
        """幅不一致のパラメータについて偽反例をチェック"""
        if is_mips64_1 and size1 == 8 and size2 == 4:
            param_wide = param_key_1
            param_narrow = param_key_2
            narrow_bits = 32
            narrow_param = p2
        elif is_mips64_2 and size2 == 8 and size1 == 4:
            param_wide = param_key_2
            param_narrow = param_key_1
            narrow_bits = 32
            narrow_param = p1
        else:
            return None
        
        if param_wide not in counterexample or param_narrow not in counterexample:
            self._debug_print(
                f"Parameter {param_index}: keys not found in counterexample "
                f"(expected '{param_wide}', '{param_narrow}')"
            )
            return None
        
        val_wide = counterexample[param_wide]
        val_narrow = counterexample[param_narrow]
        signedness = self._infer_signedness(narrow_param)
        
        is_spurious = self._check_spurious_upper_bits(
            val_wide, val_narrow, narrow_bits, signedness
        )
        
        if is_spurious:
            self._debug_print(
                f"Spurious counterexample detected (width mismatch): "
                f"{param_wide}=0x{val_wide:x}, {param_narrow}=0x{val_narrow:x} "
                f"-> {signedness} extension needed"
            )
            return (param_wide, signedness, narrow_bits)
        
        return None
    
    def _analyze_parameter_usage(
        self,
        analysis: FunctionReturnAnalysis
    ) -> Dict[str, Tuple[str, int]]:
        """
        関数の式からパラメータの使用パターンを分析
        
        Returns:
            param_name -> (signedness, narrow_bits) のマップ
        """
        usage: Dict[str, Tuple[str, int]] = {}
        
        for ret_info in analysis.returns:
            if ret_info.value:
                patterns = self._detect_extension_patterns(ret_info.value)
                for param_name, (signedness, bits) in patterns.items():
                    if param_name not in usage:
                        usage[param_name] = (signedness, bits)
            
            for cond in ret_info.conditions:
                if cond.expression:
                    patterns = self._detect_extension_patterns(cond.expression)
                    for param_name, (signedness, bits) in patterns.items():
                        if param_name not in usage:
                            usage[param_name] = (signedness, bits)
        
        return usage
    
    def _detect_extension_patterns(
        self,
        expr: Expression
    ) -> Dict[str, Tuple[str, int]]:
        """
        式から拡張パターンを検出
        
        検出パターン：
        1. INT_SEXT(SUBPIECE(PARAM, 0)) → signed
        2. INT_ZEXT(SUBPIECE(PARAM, 0)) → unsigned
        3. INT_AND(PARAM, 0xffffffff) → unsigned, 32bit
        4. SUBPIECE(PARAM, 0) (size=4) → unsigned, 32bit
        """
        patterns: Dict[str, Tuple[str, int]] = {}
        self._detect_extension_patterns_recursive(expr, patterns)
        return patterns
    
    def _detect_extension_patterns_recursive(
        self,
        expr: Expression,
        patterns: Dict[str, Tuple[str, int]]
    ) -> None:
        """式を再帰的に走査"""
        
        # パターン1: INT_SEXT(SUBPIECE(PARAM, 0))
        if expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "INT_SEXT":
            if expr.operands:
                inner = expr.operands[0]
                param_name = self._extract_subpiece_param(inner, 0)
                if param_name:
                    narrow_bits = inner.get_bit_width()
                    if narrow_bits == 32:
                        patterns[param_name] = ("signed", 32)
                        self._debug_print(
                            f"  Detected INT_SEXT(SUBPIECE({param_name}, 0)) -> signed 32bit"
                        )
        
        # パターン2: INT_ZEXT(SUBPIECE(PARAM, 0))
        elif expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "INT_ZEXT":
            if expr.operands:
                inner = expr.operands[0]
                param_name = self._extract_subpiece_param(inner, 0)
                if param_name:
                    narrow_bits = inner.get_bit_width()
                    if narrow_bits == 32:
                        patterns[param_name] = ("unsigned", 32)
                        self._debug_print(
                            f"  Detected INT_ZEXT(SUBPIECE({param_name}, 0)) -> unsigned 32bit"
                        )
        
        # パターン3: INT_AND(PARAM, 0xffffffff)
        elif expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "INT_AND":
            if len(expr.operands) == 2:
                left, right = expr.operands
                if left.expr_type == ExpressionType.PARAMETER and \
                   right.expr_type == ExpressionType.CONSTANT and \
                   right.value == 0xffffffff:
                    if left.name:
                        patterns[left.name] = ("unsigned", 32)
                        self._debug_print(
                            f"  Detected {left.name} & 0xffffffff -> unsigned 32bit"
                        )
                elif right.expr_type == ExpressionType.PARAMETER and \
                     left.expr_type == ExpressionType.CONSTANT and \
                     left.value == 0xffffffff:
                    if right.name:
                        patterns[right.name] = ("unsigned", 32)
                        self._debug_print(
                            f"  Detected 0xffffffff & {right.name} -> unsigned 32bit"
                        )
        
        # パターン4: SUBPIECE(PARAM, 0) で出力が32bit
        elif expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "SUBPIECE":
            param_name = self._extract_subpiece_param(expr, 0)
            if param_name and expr.size == 4:
                if param_name not in patterns:
                    patterns[param_name] = ("unsigned", 32)
                    self._debug_print(
                        f"  Detected SUBPIECE({param_name}, 0) [32bit] -> unsigned 32bit"
                    )
        
        # 再帰
        if expr.operands:
            for operand in expr.operands:
                self._detect_extension_patterns_recursive(operand, patterns)
        
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, val in expr.value:
                if hasattr(val, 'expr_type'):
                    self._detect_extension_patterns_recursive(val, patterns)
                if cond and hasattr(cond, 'expression'):
                    self._detect_extension_patterns_recursive(cond.expression, patterns)
    
    def _extract_subpiece_param(
        self,
        expr: Expression,
        expected_offset: int
    ) -> Optional[str]:
        """SUBPIECE(PARAM, offset) からパラメータ名を抽出"""
        if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "SUBPIECE":
            return None
        
        if len(expr.operands) != 2:
            return None
        
        source, offset = expr.operands
        
        if offset.expr_type == ExpressionType.CONSTANT:
            if offset.value != expected_offset:
                return None
        
        if source.expr_type == ExpressionType.PARAMETER:
            return source.name
        
        return None
    
    def _check_extension_pattern_violation(
        self,
        param_key: str,
        pattern: Tuple[str, int],
        counterexample: Dict[str, Any]
    ) -> Optional[Tuple[str, int]]:
        """拡張パターンに基づいてSATモデルの値が違反しているかチェック"""
        if param_key not in counterexample:
            return None
        
        val = counterexample[param_key]
        signedness, narrow_bits = pattern
        
        mask = (1 << narrow_bits) - 1
        lower = val & mask
        upper = (val >> narrow_bits)
        
        if signedness == "signed":
            sign_bit = lower & (1 << (narrow_bits - 1))
            expected_upper = (1 << (64 - narrow_bits)) - 1 if sign_bit else 0
        else:
            expected_upper = 0
        
        upper_mask = (1 << (64 - narrow_bits)) - 1
        actual_upper = upper & upper_mask
        
        if actual_upper != expected_upper:
            self._debug_print(
                f"Spurious counterexample detected (extension pattern): "
                f"{param_key}=0x{val:x}, expected {signedness} extension from {narrow_bits}bit "
                f"(upper: expected=0x{expected_upper:x}, actual=0x{actual_upper:x})"
            )
            return (signedness, narrow_bits)
        
        return None
    
    def _infer_signedness(self, param: Dict[str, Any]) -> str:
        """パラメータの符号性を推定"""
        type_str = self._get_param_type_string(param)
        
        if "unsigned" in type_str or "uint" in type_str:
            return "unsigned"
        
        return "signed"
    
    def _check_spurious_upper_bits(
        self,
        val_wide: int,
        val_narrow: int,
        narrow_bits: int,
        expected_signedness: str
    ) -> bool:
        """上位ビット自由による偽反例かをチェック"""
        mask = (1 << narrow_bits) - 1
        lower = val_wide & mask
        
        if lower != (val_narrow & mask):
            return False
        
        upper_shift = 64 - narrow_bits
        if expected_signedness == "signed":
            sign_bit = lower & (1 << (narrow_bits - 1))
            expected_upper = (1 << upper_shift) - 1 if sign_bit else 0
        else:
            expected_upper = 0
        
        actual_upper = (val_wide >> narrow_bits) & ((1 << upper_shift) - 1)
        
        if actual_upper != expected_upper:
            if self.debug:
                print(
                    f"    Upper mismatch: expected=0x{expected_upper:x}, "
                    f"actual=0x{actual_upper:x} ({expected_signedness})"
                )
            return True
        
        return False
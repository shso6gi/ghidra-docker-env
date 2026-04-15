# -*- coding: utf-8 -*-
"""MIPS64 ABI処理モジュール"""

from typing import Dict, List, Optional, Tuple, Any
from ...model import FunctionReturnAnalysis, Expression, ExpressionType
from ...model.signature import (
    ResolvedTypeSpec,
    get_data_type_display_name,
    get_declared_type_size_bytes,
    is_unsigned_data_type,
    resolve_integer_type_spec,
)
from ..param_semantics import ParameterSemanticHint, hint_objects_by_name


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
        other_analysis: FunctionReturnAnalysis,
        *,
        program: Any = None,
    ) -> Dict[int, ResolvedTypeSpec]:
        """
        MIPS64側とother側でパラメータ型/意味幅が不一致の場合、
        MIPS64側を narrower な C 整数型に上書きするマップを返す（Phase 4-A用）

        保守的な戦略:
        - 片側がint/uint確定、もう片側がlong/ulongの場合のみ修正
        - または other 側に explicit な semantic-width 証拠があり、
          MIPS64側だけが 64bit のまま残っている場合に修正
        """
        override_map: Dict[int, ResolvedTypeSpec] = {}
        other_hints = hint_objects_by_name(other_analysis)
        
        for i, (mips_param, other_param) in enumerate(
            zip(mips64_analysis.parameters, other_analysis.parameters)
        ):
            mips_type = self._get_param_type_string(mips_param)
            other_type = self._get_param_type_string(other_param)
            mips_size = self._get_param_size(mips_param)
            other_size = self._get_param_size(other_param)

            if mips_size > 4 and other_size == 4:
                signed = not is_unsigned_data_type(
                    other_param.get("data_type_obj"),
                    other_param.get("data_type"),
                )
                override_spec = resolve_integer_type_spec(
                    size_bytes=4,
                    signed=signed,
                    program=program,
                    data_type_manager=getattr(mips_param.get("data_type_obj"), "getDataTypeManager", lambda: None)(),
                    source="mips64_width_alignment",
                )
                if override_spec is None:
                    continue
                override_map[i] = override_spec
                
                self._debug_print(
                    f"Param {i}: {mips_type} (MIPS64) vs {other_type} (other) "
                    f"-> override to {override_spec.type_name}"
                )
                continue

            semantic_override = self._detect_semantic_width_override(
                index=i,
                mips_param=mips_param,
                other_param=other_param,
                other_hints=other_hints,
                program=program,
            )
            if semantic_override is not None:
                override_map[i] = semantic_override
                self._debug_print(
                    f"Param {i}: {mips_type} (MIPS64) vs semantic hint "
                    f"{other_hints.get(other_param.get('name', f'param_{i}'))} (other) "
                    f"-> override to {semantic_override.type_name}"
                )
        
        return override_map

    def _detect_semantic_width_override(
        self,
        index: int,
        mips_param: Dict[str, Any],
        other_param: Dict[str, Any],
        other_hints: Dict[str, ParameterSemanticHint],
        *,
        program: Any = None,
    ) -> Optional[ResolvedTypeSpec]:
        """Use explicit cross-binary semantic-width evidence to narrow a MIPS64 param."""
        mips_bits = self._get_param_size(mips_param) * 8
        if mips_bits <= 32:
            return None

        other_name = other_param.get("name", f"param_{index}")
        hint = other_hints.get(other_name)
        if hint is None:
            return None
        if hint.narrow_bits >= mips_bits:
            return None

        mips_type = self._get_param_type_string(mips_param)
        if not any(kw in mips_type for kw in ["long", "int8", "qword"]):
            return None

        return self._type_spec_for_semantic_hint(
            hint,
            program=program,
            data_type_manager=getattr(mips_param.get("data_type_obj"), "getDataTypeManager", lambda: None)(),
        )

    def _type_spec_for_semantic_hint(
        self,
        hint: ParameterSemanticHint,
        *,
        program: Any = None,
        data_type_manager: Any = None,
    ) -> Optional[ResolvedTypeSpec]:
        if hint.narrow_bits not in {8, 16, 32}:
            return None
        return resolve_integer_type_spec(
            size_bytes=hint.narrow_bits // 8,
            signed=(hint.signedness == "signed"),
            program=program,
            data_type_manager=data_type_manager,
            source="mips64_semantic_hint",
        )
    
    def _get_param_type_string(self, param: Dict[str, Any]) -> str:
        """パラメータの型文字列を取得"""
        return (get_data_type_display_name(
            param.get("data_type_obj"),
            param.get("data_type", ""),
        ) or "").lower().strip()
    
    def _get_param_size(self, param: Dict[str, Any]) -> int:
        """パラメータのサイズ（バイト数）を取得"""
        size = get_declared_type_size_bytes(
            param.get("data_type_obj"),
            param.get("data_type"),
            fallback_size=int(param.get("size", 4) or 4),
        )
        return int(size or 4)
    
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
                    param_name_1, param_name_2,
                    param_key_1, param_key_2,
                    is_mips64_1, is_mips64_2,
                    counterexample,
                    usage1,
                    usage2,
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
                
                elif pattern1 and pattern2:
                    # 両側とも拡張証拠あり。signedness が同じでも、
                    # 上位ビットが ABI 拡張規則を破っていれば偽反例。
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
        param_name_1: str,
        param_name_2: str,
        param_key_1: str,
        param_key_2: str,
        is_mips64_1: bool,
        is_mips64_2: bool,
        counterexample: Dict[str, Any],
        usage1: Dict[str, ParameterSemanticHint],
        usage2: Dict[str, ParameterSemanticHint],
    ) -> Optional[Tuple[str, str, int]]:
        """幅不一致のパラメータについて偽反例をチェック"""
        if size1 == 8 and size2 == 4:
            param_wide = param_key_1
            param_narrow = param_key_2
            narrow_bits = 32
            narrow_param = p2
        elif size2 == 8 and size1 == 4:
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
        signedness = self._resolve_width_mismatch_signedness(
            param_name_1,
            param_name_2,
            p1,
            p2,
            narrow_param,
            usage1,
            usage2,
        )
        
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
    ) -> Dict[str, ParameterSemanticHint]:
        """
        関数の式からパラメータの使用パターンを分析
        
        Returns:
            param_name -> semantic hint のマップ
        """
        return hint_objects_by_name(analysis)
    
    def _detect_extension_patterns(
        self,
        expr: Expression,
        evidence: Dict[str, Dict[str, Any]],
    ) -> None:
        """
        式からパラメータの width/signedness 証拠を収集

        検出パターン:
        1. INT_SEXT(SUBPIECE(PARAM, 0)) → signed 32bit
        2. INT_ZEXT(SUBPIECE(PARAM, 0)) → unsigned 32bit
        3. INT_AND(PARAM, 0xffffffff) → 32bit 利用 + unsigned 寄り
        4. SUBPIECE(PARAM, 0) (size=4) → 32bit 利用の証拠
        5. INT_SLESS / INT_SLESSEQUAL with 0/-1 → signed 利用の証拠
        """
        self._detect_extension_patterns_recursive(expr, evidence)
    
    def _detect_extension_patterns_recursive(
        self,
        expr: Expression,
        evidence: Dict[str, Dict[str, Any]]
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
                        self._record_param_evidence(
                            evidence,
                            param_name,
                            narrow_bits=32,
                            signed_score=3,
                        )
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
                        self._record_param_evidence(
                            evidence,
                            param_name,
                            narrow_bits=32,
                            unsigned_score=3,
                        )
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
                        self._record_param_evidence(
                            evidence,
                            left.name,
                            narrow_bits=32,
                            unsigned_score=1,
                        )
                        self._debug_print(
                            f"  Detected {left.name} & 0xffffffff -> unsigned 32bit"
                        )
                elif right.expr_type == ExpressionType.PARAMETER and \
                     left.expr_type == ExpressionType.CONSTANT and \
                     left.value == 0xffffffff:
                    if right.name:
                        self._record_param_evidence(
                            evidence,
                            right.name,
                            narrow_bits=32,
                            unsigned_score=1,
                        )
                        self._debug_print(
                            f"  Detected 0xffffffff & {right.name} -> unsigned 32bit"
                        )
        
        # パターン4: SUBPIECE(PARAM, 0) で出力が32bit
        elif expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "SUBPIECE":
            param_name = self._extract_subpiece_param(expr, 0)
            if param_name and expr.size == 4:
                self._record_param_evidence(
                    evidence,
                    param_name,
                    narrow_bits=32,
                )
                self._debug_print(
                    f"  Detected SUBPIECE({param_name}, 0) [32bit] -> width evidence"
                )

        # パターン5: signed 比較 with 0/-1 は signed 利用の証拠
        elif expr.expr_type == ExpressionType.BINARY_OP and expr.operator in {
            "INT_SLESS", "INT_SLESSEQUAL"
        }:
            self._record_signed_comparison_evidence(expr, evidence)
        
        # 再帰
        if expr.operands:
            for operand in expr.operands:
                self._detect_extension_patterns_recursive(operand, evidence)
        
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, val in expr.value:
                if hasattr(val, 'expr_type'):
                    self._detect_extension_patterns_recursive(val, evidence)
                if cond and hasattr(cond, 'expression'):
                    self._detect_extension_patterns_recursive(cond.expression, evidence)
    
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
        pattern: Any,
        counterexample: Dict[str, Any]
    ) -> Optional[Tuple[str, int]]:
        """拡張パターンに基づいてSATモデルの値が違反しているかチェック"""
        if param_key not in counterexample:
            return None
        
        val = counterexample[param_key]
        hint = self._coerce_semantic_hint(pattern)
        if hint is None:
            return None

        signedness = hint.signedness
        narrow_bits = hint.narrow_bits
        
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

    def _resolve_width_mismatch_signedness(
        self,
        param_name_1: str,
        param_name_2: str,
        p1: Dict[str, Any],
        p2: Dict[str, Any],
        narrow_param: Dict[str, Any],
        usage1: Dict[str, ParameterSemanticHint],
        usage2: Dict[str, ParameterSemanticHint],
    ) -> str:
        """幅不一致時に使う signedness を、明示的な usage 証拠優先で決める。"""
        usage_signedness = []

        pattern1 = self._coerce_semantic_hint(usage1.get(param_name_1))
        if pattern1 is not None and pattern1.signedness_source == "explicit":
            usage_signedness.append(pattern1.signedness)

        pattern2 = self._coerce_semantic_hint(usage2.get(param_name_2))
        if pattern2 is not None and pattern2.signedness_source == "explicit":
            usage_signedness.append(pattern2.signedness)

        unique = set(usage_signedness)
        if len(unique) == 1:
            return usage_signedness[0]

        if "signed" in unique and "unsigned" not in unique:
            return "signed"
        if "unsigned" in unique and "signed" not in unique:
            return "unsigned"

        if (
            pattern1 is not None
            and pattern2 is None
            and pattern1.signedness_source == "explicit"
        ):
            return pattern1.signedness
        if (
            pattern2 is not None
            and pattern1 is None
            and pattern2.signedness_source == "explicit"
        ):
            return pattern2.signedness

        if (
            pattern1 is not None
            and pattern2 is not None
            and pattern1.signedness_source == "explicit"
            and pattern2.signedness_source == "explicit"
            and pattern1.signedness == pattern2.signedness
        ):
            return pattern1.signedness

        fallback_candidates = [self._infer_signedness(p1), self._infer_signedness(p2)]
        if "signed" in fallback_candidates and "unsigned" not in fallback_candidates:
            return "signed"
        if "unsigned" in fallback_candidates and "signed" not in fallback_candidates:
            return "unsigned"

        return self._infer_signedness(narrow_param)

    def _coerce_semantic_hint(self, pattern: Any) -> Optional[ParameterSemanticHint]:
        """Accept both new hint objects and legacy tuple hints used in tests."""
        if isinstance(pattern, ParameterSemanticHint):
            return pattern

        if (
            isinstance(pattern, tuple)
            and len(pattern) == 2
            and isinstance(pattern[0], str)
            and isinstance(pattern[1], int)
        ):
            return ParameterSemanticHint(
                signedness=pattern[0],
                narrow_bits=pattern[1],
                signedness_source="explicit",
            )

        return None

    def _record_param_evidence(
        self,
        evidence: Dict[str, Dict[str, Any]],
        param_name: str,
        narrow_bits: Optional[int] = None,
        signed_score: int = 0,
        unsigned_score: int = 0,
    ) -> None:
        """パラメータ usage 証拠を累積する。"""
        entry = evidence.setdefault(
            param_name,
            {
                "narrow_bits": set(),
                "signed_score": 0,
                "unsigned_score": 0,
            },
        )
        if narrow_bits is not None:
            entry["narrow_bits"].add(narrow_bits)
        entry["signed_score"] += signed_score
        entry["unsigned_score"] += unsigned_score

    def _resolve_narrow_bits(self, param_evidence: Dict[str, Any]) -> Optional[int]:
        """証拠から narrow bit 幅を決める。"""
        narrow_bits = sorted(param_evidence.get("narrow_bits", ()))
        if not narrow_bits:
            return None
        return narrow_bits[0]

    def _resolve_usage_signedness(
        self,
        param_evidence: Dict[str, Any],
        param: Optional[Dict[str, Any]],
    ) -> Optional[str]:
        """証拠スコアから signedness を決める。"""
        signed_score = param_evidence.get("signed_score", 0)
        unsigned_score = param_evidence.get("unsigned_score", 0)

        if signed_score > unsigned_score:
            return "signed"
        if unsigned_score > signed_score:
            return "unsigned"
        if signed_score == 0 and unsigned_score == 0:
            return None

        return self._infer_signedness(param) if param is not None else None

    def _record_signed_comparison_evidence(
        self,
        expr: Expression,
        evidence: Dict[str, Dict[str, Any]],
    ) -> None:
        """signed 比較から signedness の証拠を収集する。"""
        if len(expr.operands) != 2:
            return

        left, right = expr.operands
        recorded = False

        if self._is_zero_or_minus_one_constant(right):
            recorded = self._record_signed_operand_evidence(left, evidence)
        if self._is_zero_or_minus_one_constant(left):
            recorded = self._record_signed_operand_evidence(right, evidence) or recorded

        if recorded and self.debug:
            self._debug_print(
                f"  Detected signed comparison evidence in {expr.to_string()}"
            )

    def _record_signed_operand_evidence(
        self,
        expr: Expression,
        evidence: Dict[str, Dict[str, Any]],
    ) -> bool:
        """operand から signed 利用の証拠を記録する。"""
        extracted = self._extract_param_reference(expr)
        if extracted is None:
            return False

        param_name, narrow_bits = extracted
        self._record_param_evidence(
            evidence,
            param_name,
            narrow_bits=narrow_bits,
            signed_score=3,
        )
        return True

    def _extract_param_reference(
        self,
        expr: Expression,
    ) -> Optional[Tuple[str, Optional[int]]]:
        """式から対応するパラメータ名と width ヒントを抽出する。"""
        if expr.expr_type == ExpressionType.PARAMETER and expr.name:
            return expr.name, None

        if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
            if expr.operator in {"INT_SEXT", "INT_ZEXT"}:
                inner = self._extract_param_reference(expr.operands[0])
                if inner is not None:
                    return inner

        if expr.expr_type == ExpressionType.BINARY_OP:
            if expr.operator == "SUBPIECE":
                param_name = self._extract_subpiece_param(expr, 0)
                if param_name:
                    return param_name, expr.get_bit_width()

            if expr.operator == "INT_AND" and len(expr.operands) == 2:
                left, right = expr.operands
                if left.expr_type == ExpressionType.PARAMETER and \
                   right.expr_type == ExpressionType.CONSTANT and \
                   right.value == 0xffffffff:
                    if left.name:
                        return left.name, 32
                if right.expr_type == ExpressionType.PARAMETER and \
                   left.expr_type == ExpressionType.CONSTANT and \
                   left.value == 0xffffffff:
                    if right.name:
                        return right.name, 32

        return None

    def _is_zero_or_minus_one_constant(self, expr: Expression) -> bool:
        """0 または -1 比較かどうかを判定。"""
        return (
            expr.expr_type == ExpressionType.CONSTANT and
            expr.value in {0, -1, 0xffffffff, 0xffffffffffffffff}
        )
    
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

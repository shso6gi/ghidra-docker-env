# -*- coding: utf-8 -*-
"""等価性判定のPhase管理モジュール"""

from typing import Optional, Tuple, List, Dict, Any, Callable
from dataclasses import dataclass
from enum import Enum
import time

from ...model import FunctionReturnAnalysis, FunctionSignature
from ..result import EquivalenceResult
from ..typing.fixer import TypeFixer, TypeFixerConfig, TypeFixResult
from ..typing.signedness_param_fix import ParamSignednessFixer
from ..arch.detector import ArchitectureDetector
from ..arch.mips64 import MIPS64Handler


# ============================================================================
# Phase 定義（新フロー骨格）
# ============================================================================

class PhaseID(Enum):
    """Phase識別子"""
    P0_BASE = "P0_BASE"
    P1_SIGNEDNESS = "P1_SIGNEDNESS"  # Phase 1 + Phase 1.5 の複合
    P2_PATTERN_INT = "P2_PATTERN_INT"  # Phase 2 + Phase 3 の複合
    P4A_MIPS64_ABI = "P4A_MIPS64_ABI"  # Phase 4-A (conservative、主経路外)


@dataclass
class PhaseSpec:
    """Phase仕様"""
    phase_id: PhaseID
    description: str


@dataclass
class PhaseResult:
    """Phase実行結果"""
    phase_id: PhaseID
    applied: bool  # Phase が適用されたか
    retry_name: str  # type_fix_result.retry_phase に設定する名前
    changed_binary1: bool = False  # ★ NEW: binary1 に変更があったか
    changed_binary2: bool = False  # ★ NEW: binary2 に変更があったか


# デフォルトの Phase plan（主経路）
DEFAULT_PHASE_PLAN: List[PhaseSpec] = [
    PhaseSpec(PhaseID.P0_BASE, "Initial check without type fix"),
    PhaseSpec(PhaseID.P1_SIGNEDNESS, "Signedness-based type fix (return + params)"),
    PhaseSpec(PhaseID.P2_PATTERN_INT, "Pattern-based type fix (return + params)"),
]


@dataclass
class PhaseContext:
    """Phase実行のコンテキスト"""
    program1: Any
    program2: Any
    function_name1: str
    function_name2: str
    binary1_name: str
    binary2_name: str
    decompile_timeout: int
    save_formula: bool
    type_fix_result: TypeFixResult
    original_signature1: Optional[FunctionSignature]
    original_signature2: Optional[FunctionSignature]
    analysis1: Optional[FunctionReturnAnalysis] = None
    analysis2: Optional[FunctionReturnAnalysis] = None


class PhaseHandler:
    """型修正Phaseを管理するクラス"""
    
    def __init__(
        self,
        type_fixer_config: TypeFixerConfig,
        debug: bool = False
    ):
        self.type_fixer_config = type_fixer_config
        self.debug = debug
        self.arch_detector = ArchitectureDetector(debug=debug)
        self.mips64_handler = MIPS64Handler(debug=debug)
        self.param_signedness_fixer = ParamSignednessFixer(type_fixer_config, debug=debug)
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[PhaseHandler] {msg}")
    
    # ============================================================================
    # Phase 実行（新フロー骨格）
    # ============================================================================
    
    def execute_phase(
        self,
        phase_spec: PhaseSpec,
        ctx: PhaseContext,
        type_fixer1: TypeFixer,
        type_fixer2: TypeFixer,
        get_params_func: Callable
    ) -> PhaseResult:
        """
        指定された Phase を実行
        
        Returns:
            PhaseResult（適用されたか、retry_name、changed sides など）
        """
        phase_id = phase_spec.phase_id
        
        if phase_id == PhaseID.P0_BASE:
            # P0 は型修正なしなので何もしない
            return PhaseResult(
                phase_id, applied=False, retry_name="initial",
                changed_binary1=False, changed_binary2=False
            )
        
        elif phase_id == PhaseID.P1_SIGNEDNESS:
            # Phase 1 + Phase 1.5 を統合
            retry_name = "signedness_fix"
            changed_binary1 = False
            changed_binary2 = False
            
            # Phase 1: 符号性に基づく型修正（戻り値）
            applied1, ch1_1, ch1_2 = self.run_phase1_signedness_fix(ctx, type_fixer1, type_fixer2)
            changed_binary1 = changed_binary1 or ch1_1
            changed_binary2 = changed_binary2 or ch1_2
            
            # Phase 1.5: 引数の符号性に基づく型修正
            applied15, ch15_1, ch15_2 = self.run_phase1_5_param_signedness_fix(
                ctx, type_fixer1, type_fixer2, get_params_func
            )
            changed_binary1 = changed_binary1 or ch15_1
            changed_binary2 = changed_binary2 or ch15_2
            
            if applied15:
                retry_name = "param_signedness_fix"
            
            applied = applied1 or applied15
            
            return PhaseResult(
                phase_id, applied=applied, retry_name=retry_name,
                changed_binary1=changed_binary1, changed_binary2=changed_binary2
            )
        
        elif phase_id == PhaseID.P2_PATTERN_INT:
            # Phase 2 + Phase 3 を統合
            retry_name = "pattern_int_fix"
            changed_binary1 = False
            changed_binary2 = False
            
            # Phase 2: パターンマッチに基づく戻り値の型修正
            applied2, ch2_1, ch2_2 = self.run_phase2_return_type_fix(ctx, type_fixer1, type_fixer2)
            changed_binary1 = changed_binary1 or ch2_1
            changed_binary2 = changed_binary2 or ch2_2
            
            if applied2:
                retry_name = "return_type_fix"
            
            # Phase 3: 引数の型修正
            applied3, ch3_1, ch3_2 = self.run_phase3_param_type_fix(
                ctx, type_fixer1, type_fixer2, get_params_func
            )
            changed_binary1 = changed_binary1 or ch3_1
            changed_binary2 = changed_binary2 or ch3_2
            
            if applied3:
                retry_name = "param_type_fix"
            
            applied = applied2 or applied3
            
            return PhaseResult(
                phase_id, applied=applied, retry_name=retry_name,
                changed_binary1=changed_binary1, changed_binary2=changed_binary2
            )
        
        elif phase_id == PhaseID.P4A_MIPS64_ABI:
            # Phase 4-A: MIPS64 ABI param fix (主経路外)
            applied, ch1, ch2 = self.run_phase4_mips64_fix(
                ctx, type_fixer1, type_fixer2, get_params_func
            )
            return PhaseResult(
                phase_id, applied=applied, retry_name="mips64_abi_fix",
                changed_binary1=ch1, changed_binary2=ch2
            )
        
        else:
            raise ValueError(f"Unknown phase_id: {phase_id}")
    
    # ============================================================================
    # 遷移判定（ゲート）
    # ============================================================================
    
    def should_retry(self, result: EquivalenceResult) -> bool:
        """通常recovery継続可否を判定（UNKNOWN/TIMEOUTのみ許可）
        
        Returns:
            True: UNKNOWN/TIMEOUT → 通常recovery phases (P1, P2) を試行可能
            False: UNSAT/SAT/critical error → 通常recovery phases へ進まない
        
        Note:
            SAT時の Phase 4-B (MIPS64 spurious) は should_run_phase4_retry() で別途判定
        """
        if result.is_equivalent is True:  # UNSAT
            return False
        if result.is_equivalent is False:  # SAT
            return False  # ★ SAT時は通常recoveryブロック（P4Bは別ゲート）
        if result.has_critical_error():
            return False
        # UNKNOWN/TIMEOUT のみ True
        return True
    
    def get_retry_reason(self, result: EquivalenceResult) -> str:
        """リトライの理由を取得"""
        if result.is_equivalent is False:
            return "NOT EQUIVALENT"
        elif result.is_timeout():
            return "TIMEOUT"
        elif result.is_equivalent is None:
            return "UNKNOWN"
        else:
            return "EQUIVALENT (no retry needed)"
    
    # ============================================================================
    # 個別 Phase 実行メソッド（戻り値を (applied, changed1, changed2) に拡張）
    # ============================================================================
    
    def should_fix_return_type(
        self,
        analysis: Optional[FunctionReturnAnalysis]
    ) -> bool:
        """戻り値の型が修正対象かチェック（パターンマッチ）"""
        if analysis is None or analysis.return_type is None:
            return False
        
        # 既に符号性修正が適用されている場合はスキップ
        if analysis.should_fix_return_to_signed():
            return False
        
        type_str = analysis.return_type.lower().strip()
        
        for pattern in self.type_fixer_config.target_patterns:
            if pattern in type_str:
                self._debug_print(
                    f"Return type '{analysis.return_type}' matches pattern '{pattern}'"
                )
                return True
        
        return False
    
    def should_fix_params(
        self,
        analysis: Optional[FunctionReturnAnalysis]
    ) -> bool:
        """パラメータ型が修正対象かチェック"""
        if analysis is None or not analysis.parameters:
            return False
        
        for param in analysis.parameters:
            raw_dt = param.get("data_type_obj")
            if raw_dt is not None and hasattr(raw_dt, 'getName'):
                type_str = str(raw_dt).lower().strip()
            else:
                type_str = param.get("data_type", "").lower().strip()
            
            for pattern in self.type_fixer_config.target_patterns:
                if pattern in type_str:
                    self._debug_print(f"Param type '{type_str}' matches pattern '{pattern}'")
                    return True
        
        return False
    
    def run_phase1_signedness_fix(
        self,
        ctx: PhaseContext,
        type_fixer1: TypeFixer,
        type_fixer2: TypeFixer
    ) -> Tuple[bool, bool, bool]:
        """
        Phase 1: 符号性に基づく型修正
        
        Returns:
            (applied, changed_binary1, changed_binary2)
        """
        changed_binary1 = False
        changed_binary2 = False
        
        if ctx.analysis1 and ctx.analysis1.signedness_result:
            ctx.type_fix_result.inferred_signedness_binary1 = (
                ctx.analysis1.signedness_result.signedness
            )
            
            if ctx.analysis1.should_fix_return_to_signed():
                self._debug_print("=" * 60)
                self._debug_print("Phase 1: Signedness-based type fix for Binary 1")
                self._debug_print("=" * 60)
                
                original_type = ctx.analysis1.return_type
                signed_type = self.type_fixer_config.get_signed_type_for(original_type or "")
                
                if signed_type:
                    params1 = ctx.analysis1.parameters if ctx.analysis1 else []
                    ret_fixed, _ = type_fixer1.fix_function_signature_by_name(
                        ctx.function_name1,
                        params1,
                        fix_return_type=False,
                        fix_param_types=False,
                        override_return_type_name=signed_type
                    )
                    if ret_fixed:
                        ctx.type_fix_result.signedness_fixed_binary1 = True
                        ctx.type_fix_result.original_type_binary1 = original_type
                        ctx.type_fix_result.fixed_type_binary1 = signed_type
                        changed_binary1 = True
                        self._debug_print(
                            f"Binary 1: {original_type} -> {signed_type} (signedness fix)"
                        )
        
        if ctx.analysis2 and ctx.analysis2.signedness_result:
            ctx.type_fix_result.inferred_signedness_binary2 = (
                ctx.analysis2.signedness_result.signedness
            )
            
            if ctx.analysis2.should_fix_return_to_signed():
                self._debug_print("=" * 60)
                self._debug_print("Phase 1: Signedness-based type fix for Binary 2")
                self._debug_print("=" * 60)
                
                original_type = ctx.analysis2.return_type
                signed_type = self.type_fixer_config.get_signed_type_for(original_type or "")
                
                if signed_type:
                    params2 = ctx.analysis2.parameters if ctx.analysis2 else []
                    ret_fixed, _ = type_fixer2.fix_function_signature_by_name(
                        ctx.function_name2,
                        params2,
                        fix_return_type=False,
                        fix_param_types=False,
                        override_return_type_name=signed_type
                    )
                    if ret_fixed:
                        ctx.type_fix_result.signedness_fixed_binary2 = True
                        ctx.type_fix_result.original_type_binary2 = original_type
                        ctx.type_fix_result.fixed_type_binary2 = signed_type
                        changed_binary2 = True
                        self._debug_print(
                            f"Binary 2: {original_type} -> {signed_type} (signedness fix)"
                        )
        
        applied = changed_binary1 or changed_binary2
        return (applied, changed_binary1, changed_binary2)
    
    def run_phase1_5_param_signedness_fix(
        self,
        ctx: PhaseContext,
        type_fixer1: TypeFixer,
        type_fixer2: TypeFixer,
        get_params_func: Callable
    ) -> Tuple[bool, bool, bool]:
        """
        Phase 1.5: 引数の符号性に基づく型修正
        
        Returns:
            (applied, changed_binary1, changed_binary2)
        """
        changed_binary1 = False
        changed_binary2 = False
        
        # Binary 1の引数符号性チェック
        if ctx.analysis1:
            override_map1 = self.param_signedness_fixer.detect_param_signedness_mismatch(
                ctx.analysis1
            )
            
            if override_map1:
                self._debug_print("=" * 60)
                self._debug_print("Phase 1.5: Param signedness fix for Binary 1")
                self._debug_print("=" * 60)
                
                # 最新のparam情報を取得
                params1_updated = get_params_func(
                    ctx.program1, ctx.function_name1, ctx.decompile_timeout
                )
                
                # 型修正を適用
                _, param_fixed = type_fixer1.fix_function_signature_by_name(
                    ctx.function_name1,
                    params1_updated,
                    fix_return_type=False,
                    fix_param_types=False,
                    override_param_type_names=override_map1
                )
                
                if param_fixed:
                    ctx.type_fix_result.param_signedness_fixed_binary1 = True
                    ctx.type_fix_result.param_signedness_override_map_binary1 = override_map1
                    changed_binary1 = True
                    
                    # 修正内容をログ出力
                    for param_idx, new_type in override_map1.items():
                        param_info = params1_updated[param_idx] if param_idx < len(params1_updated) else {}
                        param_name = param_info.get("name", f"param_{param_idx}")
                        
                        # 元の型を取得
                        raw_dt = param_info.get("data_type_obj")
                        if raw_dt is not None and hasattr(raw_dt, 'getName'):
                            old_type = str(raw_dt)
                        else:
                            old_type = param_info.get("data_type", "?")
                        
                        self._debug_print(
                            f"Binary 1: param[{param_idx}] '{param_name}': "
                            f"{old_type} -> {new_type} (param signedness fix)"
                        )
        
        # Binary 2の引数符号性チェック
        if ctx.analysis2:
            override_map2 = self.param_signedness_fixer.detect_param_signedness_mismatch(
                ctx.analysis2
            )
            
            if override_map2:
                self._debug_print("=" * 60)
                self._debug_print("Phase 1.5: Param signedness fix for Binary 2")
                self._debug_print("=" * 60)
                
                # 最新のparam情報を取得
                params2_updated = get_params_func(
                    ctx.program2, ctx.function_name2, ctx.decompile_timeout
                )
                
                # 型修正を適用
                _, param_fixed = type_fixer2.fix_function_signature_by_name(
                    ctx.function_name2,
                    params2_updated,
                    fix_return_type=False,
                    fix_param_types=False,
                    override_param_type_names=override_map2
                )
                
                if param_fixed:
                    ctx.type_fix_result.param_signedness_fixed_binary2 = True
                    ctx.type_fix_result.param_signedness_override_map_binary2 = override_map2
                    changed_binary2 = True
                    
                    # 修正内容をログ出力
                    for param_idx, new_type in override_map2.items():
                        param_info = params2_updated[param_idx] if param_idx < len(params2_updated) else {}
                        param_name = param_info.get("name", f"param_{param_idx}")
                        
                        # 元の型を取得
                        raw_dt = param_info.get("data_type_obj")
                        if raw_dt is not None and hasattr(raw_dt, 'getName'):
                            old_type = str(raw_dt)
                        else:
                            old_type = param_info.get("data_type", "?")
                        
                        self._debug_print(
                            f"Binary 2: param[{param_idx}] '{param_name}': "
                            f"{old_type} -> {new_type} (param signedness fix)"
                        )
        
        applied = changed_binary1 or changed_binary2
        return (applied, changed_binary1, changed_binary2)

    def run_phase2_return_type_fix(
        self,
        ctx: PhaseContext,
        type_fixer1: TypeFixer,
        type_fixer2: TypeFixer
    ) -> Tuple[bool, bool, bool]:
        """
        Phase 2: パターンマッチに基づく戻り値の型修正
        
        Returns:
            (applied, changed_binary1, changed_binary2)
        """
        ret_needs_fix1 = self.should_fix_return_type(ctx.analysis1)
        ret_needs_fix2 = self.should_fix_return_type(ctx.analysis2)
        
        if not (ret_needs_fix1 or ret_needs_fix2):
            return (False, False, False)
        
        self._debug_print("=" * 60)
        self._debug_print("Phase 2: Pattern-based return type fix")
        self._debug_print("=" * 60)
        
        params1 = ctx.analysis1.parameters if ctx.analysis1 else []
        params2 = ctx.analysis2.parameters if ctx.analysis2 else []
        
        changed_binary1 = False
        changed_binary2 = False
        
        if ret_needs_fix1:
            ret_fixed1, _ = type_fixer1.fix_function_signature_by_name(
                ctx.function_name1,
                params1,
                fix_return_type=True,
                fix_param_types=False
            )
            ctx.type_fix_result.return_type_fixed_binary1 = ret_fixed1
            changed_binary1 = ret_fixed1
            self._debug_print(f"Binary 1 return type fixed: {ret_fixed1}")
        
        if ret_needs_fix2:
            ret_fixed2, _ = type_fixer2.fix_function_signature_by_name(
                ctx.function_name2,
                params2,
                fix_return_type=True,
                fix_param_types=False
            )
            ctx.type_fix_result.return_type_fixed_binary2 = ret_fixed2
            changed_binary2 = ret_fixed2
            self._debug_print(f"Binary 2 return type fixed: {ret_fixed2}")
        
        applied = changed_binary1 or changed_binary2
        return (applied, changed_binary1, changed_binary2)
    
    def run_phase3_param_type_fix(
        self,
        ctx: PhaseContext,
        type_fixer1: TypeFixer,
        type_fixer2: TypeFixer,
        get_params_func: Callable
    ) -> Tuple[bool, bool, bool]:
        """
        Phase 3: 引数の型修正
        
        Returns:
            (applied, changed_binary1, changed_binary2)
        """
        param_needs_fix1 = self.should_fix_params(ctx.analysis1)
        param_needs_fix2 = self.should_fix_params(ctx.analysis2)
        
        if not (param_needs_fix1 or param_needs_fix2):
            return (False, False, False)
        
        self._debug_print("=" * 60)
        self._debug_print("Phase 3: Parameter type fix")
        self._debug_print("=" * 60)
        
        changed_binary1 = False
        changed_binary2 = False
        
        if param_needs_fix1:
            params1_updated = get_params_func(
                ctx.program1, ctx.function_name1, ctx.decompile_timeout
            )
            _, param_fixed1 = type_fixer1.fix_function_signature_by_name(
                ctx.function_name1,
                params1_updated,
                fix_return_type=False,
                fix_param_types=True
            )
            ctx.type_fix_result.param_types_fixed_binary1 = param_fixed1
            changed_binary1 = param_fixed1
            self._debug_print(f"Binary 1 param types fixed: {param_fixed1}")
        
        if param_needs_fix2:
            params2_updated = get_params_func(
                ctx.program2, ctx.function_name2, ctx.decompile_timeout
            )
            _, param_fixed2 = type_fixer2.fix_function_signature_by_name(
                ctx.function_name2,
                params2_updated,
                fix_return_type=False,
                fix_param_types=True
            )
            ctx.type_fix_result.param_types_fixed_binary2 = param_fixed2
            changed_binary2 = param_fixed2
            self._debug_print(f"Binary 2 param types fixed: {param_fixed2}")
        
        applied = changed_binary1 or changed_binary2
        return (applied, changed_binary1, changed_binary2)
    
    def run_phase4_mips64_fix(
        self,
        ctx: PhaseContext,
        type_fixer1: TypeFixer,
        type_fixer2: TypeFixer,
        get_params_func: Callable
    ) -> Tuple[bool, bool, bool]:
        """
        Phase 4-A: MIPS64 ABI param fix (long → int)
        片側がint/uint確定、もう片側がlong/ulongの場合のみ型修正を適用
        
        Returns:
            (applied, changed_binary1, changed_binary2)
        """
        is_mips64_1 = self.arch_detector.is_mips64(ctx.program1)
        is_mips64_2 = self.arch_detector.is_mips64(ctx.program2)
        
        self._debug_print(
            f"Architecture detection: Binary1 MIPS64={is_mips64_1}, "
            f"Binary2 MIPS64={is_mips64_2}"
        )
        
        if not self.mips64_handler.should_apply_fix(
            is_mips64_1, is_mips64_2, ctx.analysis1, ctx.analysis2
        ):
            return (False, False, False)
        
        self._debug_print("=" * 60)
        self._debug_print("Phase 4-A: MIPS64 ABI param fix (conservative)")
        self._debug_print("=" * 60)
        
        changed_binary1 = False
        changed_binary2 = False
        
        if is_mips64_1 and ctx.analysis1 and ctx.analysis2:
            override_map1 = self.mips64_handler.detect_param_type_mismatch(
                ctx.analysis1, ctx.analysis2
            )
            if override_map1:
                params1_updated = get_params_func(
                    ctx.program1, ctx.function_name1, ctx.decompile_timeout
                )
                _, param_fixed = type_fixer1.fix_function_signature_by_name(
                    ctx.function_name1,
                    params1_updated,
                    fix_return_type=False,
                    fix_param_types=False,
                    override_param_type_names=override_map1
                )
                
                if param_fixed:
                    ctx.type_fix_result.mips64_abi_fixed_binary1 = True
                    ctx.type_fix_result.mips64_abi_override_map_binary1 = override_map1
                    changed_binary1 = True
                    self._debug_print(
                        f"Binary 1 (MIPS64): Applied param type fix {override_map1}"
                    )
        
        if is_mips64_2 and ctx.analysis1 and ctx.analysis2:
            override_map2 = self.mips64_handler.detect_param_type_mismatch(
                ctx.analysis2, ctx.analysis1
            )
            if override_map2:
                params2_updated = get_params_func(
                    ctx.program2, ctx.function_name2, ctx.decompile_timeout
                )
                _, param_fixed = type_fixer2.fix_function_signature_by_name(
                    ctx.function_name2,
                    params2_updated,
                    fix_return_type=False,
                    fix_param_types=False,
                    override_param_type_names=override_map2
                )
                
                if param_fixed:
                    ctx.type_fix_result.mips64_abi_fixed_binary2 = True
                    ctx.type_fix_result.mips64_abi_override_map_binary2 = override_map2
                    changed_binary2 = True
                    self._debug_print(
                        f"Binary 2 (MIPS64): Applied param type fix {override_map2}"
                    )
        
        applied = changed_binary1 or changed_binary2
        return (applied, changed_binary1, changed_binary2)
    
    # ===== Phase 4-B: MIPS64 ABI Retry (spurious counterexample detection) =====
    
    def should_run_phase4_retry(
        self,
        previous_result: EquivalenceResult,
        ctx: PhaseContext
    ) -> bool:
        """Phase 4-B Retryを実行すべきかを判定
        
        SAT時の特別ゲート: MIPS64偽反例検出に限定
        
        Returns:
            True: MIPS64 + SAT + counterexample + analysis揃い
            False: 上記条件を満たさない
        """
        # NOT EQUIVALENT (SAT) の場合のみ
        if previous_result.is_equivalent is not False:
            return False
        
        # counterexampleが取得できている
        if previous_result.solver_results is None:
            return False
        counterexample = previous_result.solver_results.get_counterexample()
        if not counterexample:
            return False
        
        # MIPS64バイナリが含まれている
        is_mips64_1 = self.arch_detector.is_mips64(ctx.program1)
        is_mips64_2 = self.arch_detector.is_mips64(ctx.program2)
        if not (is_mips64_1 or is_mips64_2):
            return False
        
        # 解析結果が揃っている
        if ctx.analysis1 is None or ctx.analysis2 is None:
            return False
        
        return True
    
    def run_phase4_mips64_retry(
        self,
        previous_result: EquivalenceResult,
        ctx: PhaseContext
    ) -> Optional[Dict[str, Tuple[str, int]]]:
        """
        Phase 4-B: MIPS64 ABI Retry
        偽反例を検出し、ABI整合制約マップを返す
        
        Args:
            previous_result: 前回の判定結果（NOT EQUIVALENT）
            ctx: Phaseコンテキスト
        
        Returns:
            ABI整合制約マップ
            - key: 64bitパラメータ名（例: "param_1_1"）
            - value: (signedness, narrow_bits) タプル
            空の場合は偽反例なし → リトライ不要
        """
        if not self.should_run_phase4_retry(previous_result, ctx):
            return None
        
        counterexample = previous_result.solver_results.get_counterexample()
        if not counterexample:
            return None
        
        if ctx.analysis1 is None or ctx.analysis2 is None:
            self._debug_print("Phase 4-B: Analysis not available, skipping")
            return None
        
        is_mips64_1 = self.arch_detector.is_mips64(ctx.program1)
        is_mips64_2 = self.arch_detector.is_mips64(ctx.program2)
        
        self._debug_print("=" * 60)
        self._debug_print("Phase 4-B: MIPS64 ABI Retry (spurious counterexample detection)")
        self._debug_print("=" * 60)
        
        # 偽反例検出
        abi_constraints = self.mips64_handler.detect_spurious_counterexample(
            counterexample,
            ctx.analysis1,
            ctx.analysis2,
            is_mips64_1,
            is_mips64_2
        )
        
        if abi_constraints:
            self._debug_print(f"Spurious counterexample detected, constraints: {abi_constraints}")
            return abi_constraints
        else:
            self._debug_print("No spurious counterexample detected (genuine NOT EQUIVALENT)")
            return None
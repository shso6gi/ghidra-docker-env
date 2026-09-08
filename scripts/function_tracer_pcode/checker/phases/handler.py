# -*- coding: utf-8 -*-
"""等価性判定のPhase管理モジュール"""

from typing import Optional, Tuple, List, Dict, Any, Callable
from dataclasses import dataclass
from enum import Enum

from scripts.function_tracer_pcode.core import FunctionReturnAnalysis, FunctionSignature
from scripts.function_tracer_pcode.core.signature import (
    ResolvedTypeSpec,
    get_data_type_display_name,
    get_declared_type_size_bytes,
    is_unsigned_data_type,
    is_void_data_type,
    resolve_integer_type_spec,
    resolve_type_spec,
)
from scripts.function_tracer_pcode.semantics.typing.fixer import (
    TypeFixer,
    TypeFixerConfig,
    TypeFixResult,
)
from scripts.function_tracer_pcode.semantics.typing.signedness_param_fix import ParamSignednessFixer
from scripts.function_tracer_pcode.checker.arch.detector import ArchitectureDetector
from scripts.function_tracer_pcode.checker.arch.mips64 import MIPS64Handler


# Re-exports kept for callers that import these names from this module.
from scripts.function_tracer_pcode.checker.result import EquivalenceResult


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
    changed_binary1: bool = False  # effective analysis1 に変更があったか
    changed_binary2: bool = False  # effective analysis2 に変更があったか


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
    binary1_id: Optional[str] = None
    binary2_id: Optional[str] = None
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

    def _apply_analysis_fix(
        self,
        type_fixer: TypeFixer,
        analysis: Optional[FunctionReturnAnalysis],
        *,
        fix_return_type: bool,
        fix_param_types: bool,
        override_return_type_name: Optional[str] = None,
        override_param_type_names: Optional[Dict[int, str]] = None,
        override_return_type_spec: Optional[ResolvedTypeSpec] = None,
        override_param_type_specs: Optional[Dict[int, ResolvedTypeSpec]] = None,
        phase_name: str = "",
        reason: str = "",
        evidence: Optional[Dict[str, Any]] = None,
    ) -> Tuple[Optional[FunctionReturnAnalysis], bool, bool]:
        """新旧 TypeFixer API 互換で解析ビュー更新を試みる。"""
        if analysis is None:
            return None, False, False

        apply_method = getattr(type_fixer, "apply_analysis_signature_fix", None)
        if callable(apply_method):
            result = apply_method(
                analysis,
                fix_return_type=fix_return_type,
                fix_param_types=fix_param_types,
                override_return_type_name=override_return_type_name,
                override_param_type_names=override_param_type_names,
                override_return_type_spec=override_return_type_spec,
                override_param_type_specs=override_param_type_specs,
                phase_name=phase_name,
                reason=reason,
                evidence=evidence,
            )
            if (
                isinstance(result, tuple)
                and len(result) == 3
            ):
                return result

        compat_method = getattr(type_fixer, "fix_function_signature_by_name", None)
        if not callable(compat_method):
            return analysis, False, False

        return_fixed, param_fixed = compat_method(
            analysis.function_name,
            analysis.parameters or [],
            fix_return_type=fix_return_type,
            fix_param_types=fix_param_types,
            override_return_type_name=override_return_type_name,
            override_param_type_names=override_param_type_names,
        )
        return analysis, bool(return_fixed), bool(param_fixed)
    
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
        analysis: Optional[FunctionReturnAnalysis],
        counterpart_analysis: Optional[FunctionReturnAnalysis] = None,
        program: Any = None,
    ) -> bool:
        """戻り値の型が修正対象かチェック（パターンマッチ）"""
        if analysis is None:
            return False
        
        # 既に符号性修正が適用されている場合はスキップ
        if analysis.should_fix_return_to_signed():
            return False
        
        type_str = get_data_type_display_name(
            getattr(analysis, "return_type_obj", None),
            analysis.return_type,
        )
        if self.type_fixer_config.is_suspicious_data_type(
            getattr(analysis, "return_type_obj", None)
        ):
            self._debug_print(
                f"Return type '{type_str}' is suspicious undefined data"
            )
            return True

        suspicious_override = self._get_suspicious_void_return_override_spec(
            analysis,
            program,
            counterpart_analysis,
        )
        if suspicious_override is not None:
            self._debug_print(
                f"Return type '{type_str}' looks suspicious; "
                f"will force '{suspicious_override.type_name}'"
            )
            return True

        counterpart_void_override = self._get_counterpart_void_return_override_spec(
            analysis,
            program,
            counterpart_analysis,
        )
        if counterpart_void_override is not None:
            self._debug_print(
                f"Return type '{type_str}' conflicts with counterpart void "
                f"surface; will force '{counterpart_void_override.type_name}'"
            )
            return True
        
        return False

    def _get_suspicious_void_return_override_spec(
        self,
        analysis: Optional[FunctionReturnAnalysis],
        program: Any,
        counterpart_analysis: Optional[FunctionReturnAnalysis],
    ) -> Optional[ResolvedTypeSpec]:
        if analysis is None:
            return None

        type_str = get_data_type_display_name(
            getattr(analysis, "return_type_obj", None),
            analysis.return_type,
        )
        if not is_void_data_type(getattr(analysis, "return_type_obj", None), type_str):
            return None

        if len(analysis.returns) != 1:
            return None

        ret = analysis.returns[0]
        expr_type = getattr(ret.value, "expr_type", None)
        expr_type_name = getattr(expr_type, "name", None)
        if expr_type_name != "UNKNOWN" or getattr(ret.value, "name", None) != "void":
            return None

        if analysis.unknown_event_count <= 0 and not analysis.unknown_event_reasons:
            return None

        if counterpart_analysis is None:
            return None

        counterpart_type = get_data_type_display_name(
            getattr(counterpart_analysis, "return_type_obj", None),
            counterpart_analysis.return_type,
        )
        if (
            not counterpart_type
            or is_void_data_type(getattr(counterpart_analysis, "return_type_obj", None), counterpart_type)
        ):
            return None

        if counterpart_analysis.has_unresolved_return_value():
            return None

        explicit_counterpart_type = self._infer_explicit_integral_return_type_spec(
            counterpart_analysis.return_type,
            getattr(counterpart_analysis, "return_type_obj", None),
            program=program,
        )
        if explicit_counterpart_type is not None:
            return explicit_counterpart_type

        value_sizes = {
            int(getattr(other_ret.value, "size", 0) or 0)
            for other_ret in counterpart_analysis.returns
            if getattr(getattr(other_ret.value, "expr_type", None), "name", None) != "UNKNOWN"
            and int(getattr(other_ret.value, "size", 0) or 0) > 0
        }
        if len(value_sizes) == 1:
            size = next(iter(value_sizes))
            return resolve_integer_type_spec(
                size_bytes=int(size),
                signed=True,
                program=program,
                source="counterpart_value_width",
            )

        return self.type_fixer_config.resolve_default_integral_type_spec(
            program=program,
            fallback_size=self.type_fixer_config.default_integral_size_bytes,
            signed=True,
        )

    def _get_counterpart_void_return_override_spec(
        self,
        analysis: Optional[FunctionReturnAnalysis],
        program: Any,
        counterpart_analysis: Optional[FunctionReturnAnalysis],
    ) -> Optional[ResolvedTypeSpec]:
        if analysis is None or counterpart_analysis is None:
            return None

        type_str = get_data_type_display_name(
            getattr(analysis, "return_type_obj", None),
            analysis.return_type,
        )
        if (
            not type_str
            or is_void_data_type(getattr(analysis, "return_type_obj", None), type_str)
            or self.type_fixer_config.is_suspicious_data_type(
                getattr(analysis, "return_type_obj", None)
            )
        ):
            return None

        counterpart_type = get_data_type_display_name(
            getattr(counterpart_analysis, "return_type_obj", None),
            counterpart_analysis.return_type,
        )
        if not is_void_data_type(
            getattr(counterpart_analysis, "return_type_obj", None),
            counterpart_type,
        ):
            return None
        if self._analysis_has_unknown_events(counterpart_analysis):
            return None

        if (
            analysis.function_name
            and counterpart_analysis.function_name
            and analysis.function_name != counterpart_analysis.function_name
        ):
            return None

        if not counterpart_analysis.returns or any(
            not self._return_info_is_void_placeholder(ret)
            for ret in counterpart_analysis.returns
        ):
            return None

        if not analysis.returns:
            return None

        resolved = resolve_type_spec("void", program=program, fallback_signed=True)
        if resolved is not None:
            return resolved
        return ResolvedTypeSpec(
            type_name="void",
            size_bytes=0,
            source="counterpart_void_return_surface",
        )

    @staticmethod
    def _analysis_has_unknown_events(analysis: Optional[FunctionReturnAnalysis]) -> bool:
        if analysis is None:
            return False
        try:
            unknown_event_count = int(getattr(analysis, "unknown_event_count", 0) or 0)
        except (TypeError, ValueError):
            unknown_event_count = 0
        return unknown_event_count > 0 or bool(
            getattr(analysis, "unknown_event_reasons", None)
        )

    @staticmethod
    def _return_info_is_void_placeholder(ret) -> bool:
        value = getattr(ret, "value", None)
        expr_type = getattr(value, "expr_type", None)
        return (
            getattr(expr_type, "name", None) == "UNKNOWN"
            and str(getattr(value, "name", "") or "").lower() == "void"
        )

    def _infer_explicit_integral_return_type_spec(
        self,
        type_name: Optional[str],
        type_obj: Any = None,
        *,
        program: Any = None,
    ) -> Optional[ResolvedTypeSpec]:
        display_name = get_data_type_display_name(type_obj, type_name)
        if not display_name:
            return None

        normalized = display_name.lower().strip()
        if not normalized or is_void_data_type(type_obj, display_name):
            return None

        if self.type_fixer_config.is_suspicious_data_type(type_obj):
            return None

        if type_obj is not None:
            resolved = resolve_type_spec(
                display_name,
                data_type_obj=type_obj,
                program=program,
            )
            if resolved is not None and resolved.data_type_obj is not None:
                return resolved

        size = get_declared_type_size_bytes(type_obj, display_name, program=program)
        if size not in {1, 2, 4, 8}:
            return None
        signed = not is_unsigned_data_type(type_obj, display_name)
        return resolve_integer_type_spec(
            size_bytes=int(size),
            signed=signed,
            program=program,
            source="counterpart_declared_type",
        )
    
    def should_fix_params(
        self,
        analysis: Optional[FunctionReturnAnalysis]
    ) -> bool:
        """パラメータ型が修正対象かチェック"""
        if analysis is None or not analysis.parameters:
            return False
        
        for param in analysis.parameters:
            raw_dt = param.get("data_type_obj")
            type_str = get_data_type_display_name(raw_dt, param.get("data_type"))
            if self.type_fixer_config.is_suspicious_data_type(raw_dt):
                self._debug_print(f"Param type '{type_str}' is suspicious undefined data")
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
                
                original_type = get_data_type_display_name(
                    getattr(ctx.analysis1, "return_type_obj", None),
                    ctx.analysis1.return_type,
                )
                signed_spec = self.type_fixer_config.resolve_signed_type_spec(
                    original_type,
                    data_type_obj=getattr(ctx.analysis1, "return_type_obj", None),
                    program=ctx.program1,
                )
                
                if signed_spec is not None:
                    updated_analysis1, ret_fixed, _ = self._apply_analysis_fix(
                        type_fixer1,
                        ctx.analysis1,
                        fix_return_type=False,
                        fix_param_types=False,
                        override_return_type_name=signed_spec.type_name,
                        override_return_type_spec=signed_spec,
                        phase_name=PhaseID.P1_SIGNEDNESS.value,
                        reason="signedness-based return type hypothesis",
                        evidence={
                            "original_type": original_type,
                            "signed_type": signed_spec.type_name,
                            "resolved_signed_type": signed_spec.to_dict(),
                            "opcode_counts": dict(ctx.analysis1.signedness_result.opcode_counts),
                        },
                    )
                    if ret_fixed:
                        ctx.analysis1 = updated_analysis1
                        ctx.type_fix_result.signedness_fixed_binary1 = True
                        ctx.type_fix_result.original_type_binary1 = original_type
                        ctx.type_fix_result.fixed_type_binary1 = signed_spec.type_name
                        changed_binary1 = True
                        self._debug_print(
                            f"Binary 1: {original_type} -> {signed_spec.type_name} "
                            f"(signedness fix via {signed_spec.source})"
                        )
        
        if ctx.analysis2 and ctx.analysis2.signedness_result:
            ctx.type_fix_result.inferred_signedness_binary2 = (
                ctx.analysis2.signedness_result.signedness
            )
            
            if ctx.analysis2.should_fix_return_to_signed():
                self._debug_print("=" * 60)
                self._debug_print("Phase 1: Signedness-based type fix for Binary 2")
                self._debug_print("=" * 60)
                
                original_type = get_data_type_display_name(
                    getattr(ctx.analysis2, "return_type_obj", None),
                    ctx.analysis2.return_type,
                )
                signed_spec = self.type_fixer_config.resolve_signed_type_spec(
                    original_type,
                    data_type_obj=getattr(ctx.analysis2, "return_type_obj", None),
                    program=ctx.program2,
                )
                
                if signed_spec is not None:
                    updated_analysis2, ret_fixed, _ = self._apply_analysis_fix(
                        type_fixer2,
                        ctx.analysis2,
                        fix_return_type=False,
                        fix_param_types=False,
                        override_return_type_name=signed_spec.type_name,
                        override_return_type_spec=signed_spec,
                        phase_name=PhaseID.P1_SIGNEDNESS.value,
                        reason="signedness-based return type hypothesis",
                        evidence={
                            "original_type": original_type,
                            "signed_type": signed_spec.type_name,
                            "resolved_signed_type": signed_spec.to_dict(),
                            "opcode_counts": dict(ctx.analysis2.signedness_result.opcode_counts),
                        },
                    )
                    if ret_fixed:
                        ctx.analysis2 = updated_analysis2
                        ctx.type_fix_result.signedness_fixed_binary2 = True
                        ctx.type_fix_result.original_type_binary2 = original_type
                        ctx.type_fix_result.fixed_type_binary2 = signed_spec.type_name
                        changed_binary2 = True
                        self._debug_print(
                            f"Binary 2: {original_type} -> {signed_spec.type_name} "
                            f"(signedness fix via {signed_spec.source})"
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
            override_specs1 = self.param_signedness_fixer.detect_param_signedness_mismatch(
                ctx.analysis1,
                program=ctx.program1,
            )
            override_map1 = {
                index: spec.type_name
                for index, spec in override_specs1.items()
            }
            
            if override_map1:
                self._debug_print("=" * 60)
                self._debug_print("Phase 1.5: Param signedness fix for Binary 1")
                self._debug_print("=" * 60)
                
                params1_before = list(ctx.analysis1.parameters or [])
                updated_analysis1, _, param_fixed = self._apply_analysis_fix(
                    type_fixer1,
                    ctx.analysis1,
                    fix_return_type=False,
                    fix_param_types=False,
                    override_param_type_names=override_map1,
                    override_param_type_specs=override_specs1,
                    phase_name=PhaseID.P1_SIGNEDNESS.value,
                    reason="signedness-based parameter hypothesis",
                    evidence={
                        "override_map": dict(override_map1),
                        "resolved_override_map": {
                            index: spec.to_dict()
                            for index, spec in override_specs1.items()
                        },
                    },
                )
                
                if param_fixed:
                    ctx.analysis1 = updated_analysis1
                    ctx.type_fix_result.param_signedness_fixed_binary1 = True
                    ctx.type_fix_result.param_signedness_override_map_binary1 = override_map1
                    changed_binary1 = True
                    
                    # 修正内容をログ出力
                    for param_idx, new_type in override_map1.items():
                        param_info = params1_before[param_idx] if param_idx < len(params1_before) else {}
                        param_name = param_info.get("name", f"param_{param_idx}")
                        
                        # 元の型を取得
                        old_type = get_data_type_display_name(
                            param_info.get("data_type_obj"),
                            param_info.get("data_type", "?"),
                        ) or "?"
                        
                        self._debug_print(
                            f"Binary 1: param[{param_idx}] '{param_name}': "
                            f"{old_type} -> {new_type} "
                            f"(param signedness fix via {override_specs1[param_idx].source})"
                        )
        
        # Binary 2の引数符号性チェック
        if ctx.analysis2:
            override_specs2 = self.param_signedness_fixer.detect_param_signedness_mismatch(
                ctx.analysis2,
                program=ctx.program2,
            )
            override_map2 = {
                index: spec.type_name
                for index, spec in override_specs2.items()
            }
            
            if override_map2:
                self._debug_print("=" * 60)
                self._debug_print("Phase 1.5: Param signedness fix for Binary 2")
                self._debug_print("=" * 60)
                
                params2_before = list(ctx.analysis2.parameters or [])
                updated_analysis2, _, param_fixed = self._apply_analysis_fix(
                    type_fixer2,
                    ctx.analysis2,
                    fix_return_type=False,
                    fix_param_types=False,
                    override_param_type_names=override_map2,
                    override_param_type_specs=override_specs2,
                    phase_name=PhaseID.P1_SIGNEDNESS.value,
                    reason="signedness-based parameter hypothesis",
                    evidence={
                        "override_map": dict(override_map2),
                        "resolved_override_map": {
                            index: spec.to_dict()
                            for index, spec in override_specs2.items()
                        },
                    },
                )
                
                if param_fixed:
                    ctx.analysis2 = updated_analysis2
                    ctx.type_fix_result.param_signedness_fixed_binary2 = True
                    ctx.type_fix_result.param_signedness_override_map_binary2 = override_map2
                    changed_binary2 = True
                    
                    # 修正内容をログ出力
                    for param_idx, new_type in override_map2.items():
                        param_info = params2_before[param_idx] if param_idx < len(params2_before) else {}
                        param_name = param_info.get("name", f"param_{param_idx}")
                        
                        # 元の型を取得
                        old_type = get_data_type_display_name(
                            param_info.get("data_type_obj"),
                            param_info.get("data_type", "?"),
                        ) or "?"
                        
                        self._debug_print(
                            f"Binary 2: param[{param_idx}] '{param_name}': "
                            f"{old_type} -> {new_type} "
                            f"(param signedness fix via {override_specs2[param_idx].source})"
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
        override_return_type1 = self._get_suspicious_void_return_override_spec(
            ctx.analysis1,
            ctx.program1,
            ctx.analysis2,
        )
        if override_return_type1 is None:
            override_return_type1 = self._get_counterpart_void_return_override_spec(
                ctx.analysis1,
                ctx.program1,
                ctx.analysis2,
            )
        override_return_type2 = self._get_suspicious_void_return_override_spec(
            ctx.analysis2,
            ctx.program2,
            ctx.analysis1,
        )
        if override_return_type2 is None:
            override_return_type2 = self._get_counterpart_void_return_override_spec(
                ctx.analysis2,
                ctx.program2,
                ctx.analysis1,
            )

        ret_needs_fix1 = self.should_fix_return_type(ctx.analysis1, ctx.analysis2, program=ctx.program1)
        ret_needs_fix2 = self.should_fix_return_type(ctx.analysis2, ctx.analysis1, program=ctx.program2)
        
        if not (ret_needs_fix1 or ret_needs_fix2):
            return (False, False, False)
        
        self._debug_print("=" * 60)
        self._debug_print("Phase 2: Pattern-based return type fix")
        self._debug_print("=" * 60)
        
        
        changed_binary1 = False
        changed_binary2 = False
        
        if ret_needs_fix1:
            updated_analysis1, ret_fixed1, _ = self._apply_analysis_fix(
                type_fixer1,
                ctx.analysis1,
                fix_return_type=True,
                fix_param_types=False,
                override_return_type_name=override_return_type1.type_name if override_return_type1 else None,
                override_return_type_spec=override_return_type1,
                phase_name=PhaseID.P2_PATTERN_INT.value,
                reason="pattern/counterpart-based return type hypothesis",
                evidence={"counterpart_return_type": ctx.analysis2.return_type if ctx.analysis2 else None},
            )
            if ret_fixed1:
                ctx.analysis1 = updated_analysis1
            ctx.type_fix_result.return_type_fixed_binary1 = ret_fixed1
            changed_binary1 = ret_fixed1
            self._debug_print(f"Binary 1 return type fixed: {ret_fixed1}")
        
        if ret_needs_fix2:
            updated_analysis2, ret_fixed2, _ = self._apply_analysis_fix(
                type_fixer2,
                ctx.analysis2,
                fix_return_type=True,
                fix_param_types=False,
                override_return_type_name=override_return_type2.type_name if override_return_type2 else None,
                override_return_type_spec=override_return_type2,
                phase_name=PhaseID.P2_PATTERN_INT.value,
                reason="pattern/counterpart-based return type hypothesis",
                evidence={"counterpart_return_type": ctx.analysis1.return_type if ctx.analysis1 else None},
            )
            if ret_fixed2:
                ctx.analysis2 = updated_analysis2
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
            updated_analysis1, _, param_fixed1 = self._apply_analysis_fix(
                type_fixer1,
                ctx.analysis1,
                fix_return_type=False,
                fix_param_types=True,
                phase_name=PhaseID.P2_PATTERN_INT.value,
                reason="pattern-based parameter type hypothesis",
            )
            if param_fixed1:
                ctx.analysis1 = updated_analysis1
            ctx.type_fix_result.param_types_fixed_binary1 = param_fixed1
            changed_binary1 = param_fixed1
            self._debug_print(f"Binary 1 param types fixed: {param_fixed1}")
        
        if param_needs_fix2:
            updated_analysis2, _, param_fixed2 = self._apply_analysis_fix(
                type_fixer2,
                ctx.analysis2,
                fix_return_type=False,
                fix_param_types=True,
                phase_name=PhaseID.P2_PATTERN_INT.value,
                reason="pattern-based parameter type hypothesis",
            )
            if param_fixed2:
                ctx.analysis2 = updated_analysis2
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
            override_specs1 = self.mips64_handler.detect_param_type_mismatch(
                ctx.analysis1,
                ctx.analysis2,
                program=ctx.program1,
            )
            override_map1 = {
                index: spec.type_name
                for index, spec in override_specs1.items()
            }
            if override_map1:
                updated_analysis1, _, param_fixed = self._apply_analysis_fix(
                    type_fixer1,
                    ctx.analysis1,
                    fix_return_type=False,
                    fix_param_types=False,
                    override_param_type_names=override_map1,
                    override_param_type_specs=override_specs1,
                    phase_name=PhaseID.P4A_MIPS64_ABI.value,
                    reason="MIPS64 ABI parameter-width hypothesis",
                    evidence={
                        "override_map": dict(override_map1),
                        "resolved_override_map": {
                            index: spec.to_dict()
                            for index, spec in override_specs1.items()
                        },
                    },
                )
                
                if param_fixed:
                    ctx.analysis1 = updated_analysis1
                    ctx.type_fix_result.mips64_abi_fixed_binary1 = True
                    ctx.type_fix_result.mips64_abi_override_map_binary1 = override_map1
                    changed_binary1 = True
                    self._debug_print(
                        f"Binary 1 (MIPS64): Applied param type fix {override_map1}"
                    )
        
        if is_mips64_2 and ctx.analysis1 and ctx.analysis2:
            override_specs2 = self.mips64_handler.detect_param_type_mismatch(
                ctx.analysis2,
                ctx.analysis1,
                program=ctx.program2,
            )
            override_map2 = {
                index: spec.type_name
                for index, spec in override_specs2.items()
            }
            if override_map2:
                updated_analysis2, _, param_fixed = self._apply_analysis_fix(
                    type_fixer2,
                    ctx.analysis2,
                    fix_return_type=False,
                    fix_param_types=False,
                    override_param_type_names=override_map2,
                    override_param_type_specs=override_specs2,
                    phase_name=PhaseID.P4A_MIPS64_ABI.value,
                    reason="MIPS64 ABI parameter-width hypothesis",
                    evidence={
                        "override_map": dict(override_map2),
                        "resolved_override_map": {
                            index: spec.to_dict()
                            for index, spec in override_specs2.items()
                        },
                    },
                )
                
                if param_fixed:
                    ctx.analysis2 = updated_analysis2
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

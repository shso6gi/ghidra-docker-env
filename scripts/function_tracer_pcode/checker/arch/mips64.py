# -*- coding: utf-8 -*-
"""MIPS64 ABI処理モジュール"""

from typing import Dict, Optional, Any
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.signature import (
    ResolvedTypeSpec,
    get_data_type_display_name,
    get_declared_type_size_bytes,
    is_integral_data_type,
    is_unsigned_data_type,
    resolve_integer_type_spec,
)
from scripts.function_tracer_pcode.semantics.param_semantics import (
    ParameterIdentityKey,
    ParameterSemanticHint,
    hint_objects_by_identity,
    parameter_identity_key_from_descriptor,
)


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
        other_hints = hint_objects_by_identity(other_analysis)
        
        for i, (mips_param, other_param) in enumerate(
            zip(mips64_analysis.parameters, other_analysis.parameters)
        ):
            mips_type = self._get_param_type_string(mips_param)
            other_type = self._get_param_type_string(other_param)
            mips_size = self._get_param_size(mips_param)
            other_size = self._get_param_size(other_param)

            if (
                mips_size > 4
                and other_size == 4
                and is_integral_data_type(
                    mips_param.get("data_type_obj"),
                    mips_param.get("data_type"),
                    program=program,
                )
                and is_integral_data_type(
                    other_param.get("data_type_obj"),
                    other_param.get("data_type"),
                    program=program,
                )
            ):
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
                    f"{other_hints.get(parameter_identity_key_from_descriptor(other_param))} (other) "
                    f"-> override to {semantic_override.type_name}"
                )
        
        return override_map

    def _detect_semantic_width_override(
        self,
        index: int,
        mips_param: Dict[str, Any],
        other_param: Dict[str, Any],
        other_hints: Dict[ParameterIdentityKey, ParameterSemanticHint],
        *,
        program: Any = None,
    ) -> Optional[ResolvedTypeSpec]:
        """Use explicit cross-binary semantic-width evidence to narrow a MIPS64 param."""
        mips_bits = self._get_param_size(mips_param) * 8
        if mips_bits <= 32:
            return None

        other_identity = parameter_identity_key_from_descriptor(other_param)
        if other_identity is None:
            return None
        hint = other_hints.get(other_identity)
        if hint is None:
            return None
        if hint.narrow_bits >= mips_bits:
            return None

        if not is_integral_data_type(
            mips_param.get("data_type_obj"),
            mips_param.get("data_type"),
            program=program,
        ):
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

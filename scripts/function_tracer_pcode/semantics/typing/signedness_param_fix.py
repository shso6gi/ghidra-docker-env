# -*- coding: utf-8 -*-
"""引数の符号性推定・修正モジュール（Phase 1.5用）"""

from typing import Any, Dict
from scripts.function_tracer_pcode.semantics.param_semantics import infer_parameter_semantics
from scripts.function_tracer_pcode.core import FunctionReturnAnalysis
from scripts.function_tracer_pcode.core.signature import (
    ResolvedTypeSpec,
    get_data_type_display_name,
    get_declared_type_signedness,
    get_declared_type_size_bytes,
    is_void_data_type,
    is_pointer_data_type,
    resolve_integer_type_spec,
)
from scripts.function_tracer_pcode.semantics.typing.fixer import TypeFixerConfig


class ParamSignednessFixer:
    """引数の符号性推定・修正を行うクラス"""
    
    def __init__(self, config: TypeFixerConfig, debug: bool = False):
        self.config = config
        self.debug = debug
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[ParamSignednessFixer] {msg}")
    
    def detect_param_signedness_mismatch(
        self,
        analysis: FunctionReturnAnalysis,
        *,
        program: Any = None,
    ) -> Dict[int, ResolvedTypeSpec]:
        """局所的な parameter semantic hint に基づいて型仮説を解決する。"""
        override_map: Dict[int, ResolvedTypeSpec] = {}

        parameters = list(analysis.parameters or [])
        if not parameters:
            return override_map

        hints = infer_parameter_semantics(analysis)
        if not hints:
            self._debug_print(
                f"Function '{analysis.function_name}' has no semantic parameter hints"
            )
            return override_map

        self._debug_print(
            f"Function '{analysis.function_name}' has semantic hints for "
            f"{len(hints)} parameter(s); checking {len(parameters)} parameter(s)..."
        )

        for i, param in enumerate(parameters):
            index = param.get("index", i)
            hint = hints.get(index)
            if hint is None:
                continue

            raw_dt = param.get("data_type_obj")
            type_str = get_data_type_display_name(raw_dt, param.get("data_type", ""))
            if not type_str:
                continue

            if is_void_data_type(raw_dt, type_str):
                continue
            if is_pointer_data_type(raw_dt, type_str):
                continue

            resolved_spec = self._resolve_param_semantic_hint(
                param,
                hint_narrow_bits=hint.narrow_bits,
                hint_signedness=hint.signedness,
                hint_signedness_source=hint.signedness_source,
                program=program,
            )
            if resolved_spec is None:
                self._debug_print(
                    f"  Param {index} '{param.get('name', 'unknown')}': "
                    f"no type mapping for semantic hint {hint.signedness}:{hint.narrow_bits}"
                )
                continue

            if not self._param_needs_override(param, resolved_spec, program=program):
                continue

            override_map[index] = resolved_spec
            self._debug_print(
                f"  Param {index} '{param.get('name', 'unknown')}': "
                f"'{type_str}' -> '{resolved_spec.type_name}' "
                f"(semantic hint {hint.signedness}:{hint.narrow_bits}, source={resolved_spec.source})"
            )

        if override_map:
            self._debug_print(
                f"Detected {len(override_map)} param(s) needing semantic parameter fix"
            )
        else:
            self._debug_print("No semantic parameter overrides detected")

        return override_map

    def _resolve_param_semantic_hint(
        self,
        param: Dict[str, Any],
        *,
        hint_narrow_bits: int,
        hint_signedness: str,
        hint_signedness_source: str,
        program: Any = None,
    ) -> ResolvedTypeSpec | None:
        if hint_narrow_bits <= 0 or hint_narrow_bits % 8 != 0:
            return None

        raw_dt = param.get("data_type_obj")
        type_str = get_data_type_display_name(raw_dt, param.get("data_type", ""))
        declared_size = get_declared_type_size_bytes(
            raw_dt,
            type_str,
            fallback_size=param.get("size"),
            program=program,
        )
        declared_signed = get_declared_type_signedness(
            raw_dt,
            type_str,
            fallback_signed=bool(param.get("is_signed", True)),
            program=program,
        )

        target_size_bytes = hint_narrow_bits // 8
        effective_signedness = (
            hint_signedness
            if hint_signedness in {"signed", "unsigned"}
            else ("signed" if declared_signed else "unsigned")
            if declared_signed is not None
            else None
        )
        if effective_signedness not in {"signed", "unsigned"}:
            return None
        if (
            hint_signedness_source == "explicit"
            and effective_signedness == "signed"
            and declared_size is not None
            and int(declared_size) == int(target_size_bytes)
            and declared_signed is False
        ):
            counterpart = self.config.resolve_signed_type_spec(
                type_str,
                data_type_obj=raw_dt,
                program=program,
                fallback_size=declared_size,
            )
            if counterpart is not None:
                return counterpart
            fallback = self._fallback_integer_type_spec(
                size_bytes=target_size_bytes,
                signed=True,
                source="param_semantic_hint",
            )
            if fallback is not None:
                return fallback

        resolved = resolve_integer_type_spec(
            size_bytes=target_size_bytes,
            signed=(effective_signedness == "signed"),
            program=program,
            source="param_semantic_hint",
        )
        if resolved is not None:
            return resolved
        return self._fallback_integer_type_spec(
            size_bytes=target_size_bytes,
            signed=(effective_signedness == "signed"),
            source="param_semantic_hint",
        )

    @staticmethod
    def _fallback_integer_type_spec(
        *,
        size_bytes: int,
        signed: bool,
        source: str,
    ) -> ResolvedTypeSpec | None:
        names = {
            (True, 1): "char",
            (False, 1): "unsigned char",
            (True, 2): "short",
            (False, 2): "unsigned short",
            (True, 4): "int",
            (False, 4): "unsigned int",
            (True, 8): "long",
            (False, 8): "unsigned long",
        }
        type_name = names.get((bool(signed), int(size_bytes)))
        if type_name is None:
            return None
        return ResolvedTypeSpec(
            type_name=type_name,
            data_type_obj=None,
            size_bytes=int(size_bytes),
            is_signed=bool(signed),
            source=source,
        )

    def _param_needs_override(
        self,
        param: Dict[str, Any],
        resolved_spec: ResolvedTypeSpec,
        *,
        program: Any = None,
    ) -> bool:
        raw_dt = param.get("data_type_obj")
        type_str = get_data_type_display_name(raw_dt, param.get("data_type", ""))
        declared_size = get_declared_type_size_bytes(
            raw_dt,
            type_str,
            fallback_size=param.get("size"),
            program=program,
        )
        declared_signed = get_declared_type_signedness(
            raw_dt,
            type_str,
            fallback_signed=bool(param.get("is_signed", True)),
            program=program,
        )
        resolved_size = resolved_spec.size_bytes
        resolved_signed = resolved_spec.is_signed

        if declared_size is not None and resolved_size is not None and int(declared_size) != int(resolved_size):
            return True
        if declared_signed is not None and resolved_signed is not None and bool(declared_signed) != bool(resolved_signed):
            return True
        if type_str and resolved_spec.type_name and type_str != resolved_spec.type_name:
            return True
        return False

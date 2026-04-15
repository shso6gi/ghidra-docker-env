# -*- coding: utf-8 -*-
"""型仮説オーバーレイ生成モジュール。

Ghidra Program へ永続的な updateFunction() を行わず、解析結果上に
仮説シグネチャを重ねるためのユーティリティを提供する。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple, TYPE_CHECKING

from ...model import FunctionReturnAnalysis, FunctionSignature, SignatureHypothesis
from ...model.signature import (
    ResolvedTypeSpec,
    are_types_equivalent,
    get_data_type_display_name,
    is_unsigned_data_type,
    normalize_type_name,
    resolve_type_spec,
    resolve_signed_counterpart_spec,
    type_matches_patterns,
)

if TYPE_CHECKING:
    from ...model.analysis import SignednessResult


@dataclass
class TypeFixerConfig:
    """
    型修正ヒューリスティクスの設定。

    Attributes:
        target_patterns: 修正対象とする型名のパターン（小文字で比較）
        replacement_type_name: 置換先の型名
        unsigned_to_signed_map: unsigned型からsigned型へのレガシーfallbackマッピング
    """

    target_patterns: Set[str] = field(default_factory=lambda: {
        "undefined",
        "undefined1",
        "undefined2",
        "undefined4",
        "undefined8",
    })
    replacement_type_name: str = "int"
    unsigned_to_signed_map: Dict[str, str] = field(default_factory=lambda: {
        "ulong": "long",
        "ulonglong": "longlong",
        "unsigned long": "long",
        "unsigned long long": "long long",
        "uint": "int",
        "unsigned int": "int",
        "ushort": "short",
        "unsigned short": "short",
        "uchar": "char",
        "unsigned char": "char",
    })

    def add_pattern(self, pattern: str) -> None:
        self.target_patterns.add(pattern.lower())

    def remove_pattern(self, pattern: str) -> None:
        self.target_patterns.discard(pattern.lower())

    def set_patterns(self, patterns: Set[str]) -> None:
        self.target_patterns = {p.lower() for p in patterns}

    def resolve_signed_type_spec(
        self,
        unsigned_type: Optional[str],
        *,
        data_type_obj: Any = None,
        program: Any = None,
        fallback_size: Optional[int] = None,
    ) -> Optional[ResolvedTypeSpec]:
        ghidra_spec = resolve_signed_counterpart_spec(
            unsigned_type,
            data_type_obj=data_type_obj,
            program=program,
            fallback_size=fallback_size,
        )
        if ghidra_spec is not None:
            return ghidra_spec

        if unsigned_type is None:
            return None

        normalized = normalize_type_name(unsigned_type)
        if normalized in self.unsigned_to_signed_map:
            signed_name = self.unsigned_to_signed_map[normalized]
            resolved = resolve_type_spec(
                signed_name,
                program=program,
                fallback_size=fallback_size,
                fallback_signed=True,
            )
            if resolved is not None:
                return ResolvedTypeSpec(
                    type_name=resolved.type_name,
                    data_type_obj=resolved.data_type_obj,
                    size_bytes=resolved.size_bytes,
                    is_signed=resolved.is_signed,
                    source="legacy_string_map",
                    data_type_path=resolved.data_type_path,
                )
            return ResolvedTypeSpec(
                type_name=signed_name,
                size_bytes=fallback_size,
                is_signed=True,
                source="legacy_string_map",
            )

        for unsigned_pattern, signed_type in self.unsigned_to_signed_map.items():
            if unsigned_pattern in normalized:
                resolved = resolve_type_spec(
                    signed_type,
                    program=program,
                    fallback_size=fallback_size,
                    fallback_signed=True,
                )
                if resolved is not None:
                    return ResolvedTypeSpec(
                        type_name=resolved.type_name,
                        data_type_obj=resolved.data_type_obj,
                        size_bytes=resolved.size_bytes,
                        is_signed=resolved.is_signed,
                        source="legacy_string_map",
                        data_type_path=resolved.data_type_path,
                    )
                return ResolvedTypeSpec(
                    type_name=signed_type,
                    size_bytes=fallback_size,
                    is_signed=True,
                    source="legacy_string_map",
                )

        return None

    def get_signed_type_for(
        self,
        unsigned_type: Optional[str],
        *,
        data_type_obj: Any = None,
        program: Any = None,
        fallback_size: Optional[int] = None,
    ) -> Optional[str]:
        spec = self.resolve_signed_type_spec(
            unsigned_type,
            data_type_obj=data_type_obj,
            program=program,
            fallback_size=fallback_size,
        )
        if spec is None:
            return None
        return spec.type_name


class TypeFixer:
    """FunctionReturnAnalysis 上に型仮説を適用するクラス。"""

    def __init__(
        self,
        program,
        config: Optional[TypeFixerConfig] = None,
        debug: bool = False,
    ):
        self.program = program
        self.config = config or TypeFixerConfig()
        self.debug = debug

    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[TypeFixer] {msg}")

    def _find_function_by_name(self, function_name: str):
        """後方互換性のため Program 上の関数検索は残す。"""
        function_manager = getattr(self.program, "getFunctionManager", lambda: None)()
        if function_manager is None:
            return None
        for func in function_manager.getFunctions(True):
            if func.getName() == function_name:
                return func
        return None

    def _should_fix_type(self, type_obj: Any = None, type_str: Optional[str] = None) -> bool:
        if type_str is None and type_obj is None:
            return False
        display_name = get_data_type_display_name(type_obj, type_str)
        type_lower = normalize_type_name(display_name)
        if "*" in type_lower or "ptr" in type_lower:
            return False
        return type_matches_patterns(
            type_obj,
            display_name,
            patterns=list(self.config.target_patterns),
        )
        
    def _is_unsigned_type(self, type_obj: Any = None, type_str: Optional[str] = None) -> bool:
        return is_unsigned_data_type(type_obj, type_str)

    def check_return_type_needs_fix(self, function) -> bool:
        return_type = function.getReturnType() if hasattr(function, "getReturnType") else None
        type_str = str(return_type) if return_type else ""
        needs_fix = self._should_fix_type(return_type, type_str)
        self._debug_print(
            f"Return type of '{function.getName()}': '{type_str}' -> needs_fix={needs_fix}"
        )
        return needs_fix

    def check_return_type_needs_signedness_fix(
        self,
        return_type_str: Optional[str],
        return_type_obj: Any = None,
        signedness_result: Optional["SignednessResult"] = None,
    ) -> Tuple[bool, Optional[ResolvedTypeSpec]]:
        if signedness_result is None or not signedness_result.is_signed():
            return False, None
        if (return_type_str is None and return_type_obj is None) or not self._is_unsigned_type(
            return_type_obj,
            return_type_str,
        ):
            return False, None

        signed_spec = self.config.resolve_signed_type_spec(
            return_type_str,
            data_type_obj=return_type_obj,
            program=self.program,
        )
        if signed_spec is None:
            self._debug_print(f"No signed type mapping for '{return_type_str}'")
            return False, None

        self._debug_print(
            f"Return type '{return_type_str}' needs signedness fix -> '{signed_spec.type_name}' "
            f"(evidence: {signedness_result.opcode_counts})"
        )
        return True, signed_spec

    def check_param_types_need_fix(self, function) -> List[int]:
        indices = []
        for i, param in enumerate(function.getParameters()):
            data_type = param.getDataType() if hasattr(param, "getDataType") else None
            type_str = str(data_type) if data_type else ""
            if self._should_fix_type(data_type, type_str):
                indices.append(i)
        return indices

    def check_needs_fix(self, function_name: str) -> Tuple[bool, bool]:
        function = self._find_function_by_name(function_name)
        if function is None:
            self._debug_print(f"Function '{function_name}' not found")
            return (False, False)

        return_needs_fix = self.check_return_type_needs_fix(function)
        param_indices = self.check_param_types_need_fix(function)
        return (return_needs_fix, len(param_indices) > 0)

    def check_needs_fix_with_params(
        self,
        function_name: str,
        param_info: List[Dict[str, Any]],
    ) -> Tuple[bool, bool]:
        function = self._find_function_by_name(function_name)
        if function is None:
            self._debug_print(f"Function '{function_name}' not found")
            return (False, False)

        return_needs_fix = self.check_return_type_needs_fix(function)
        param_needs_fix = False
        for info in param_info:
            type_str = info.get("data_type", "")
            if self._should_fix_type(info.get("data_type_obj"), type_str):
                param_needs_fix = True
                break

        return (return_needs_fix, param_needs_fix)

    def build_signature_hypothesis(
        self,
        signature: FunctionSignature,
        *,
        fix_return_type: bool = True,
        fix_param_types: bool = True,
        override_return_type_name: Optional[str] = None,
        override_param_type_names: Optional[Dict[int, str]] = None,
        override_return_type_spec: Optional[ResolvedTypeSpec] = None,
        override_param_type_specs: Optional[Dict[int, ResolvedTypeSpec]] = None,
        phase_name: str = "",
        reason: str = "",
        evidence: Optional[Dict[str, Any]] = None,
    ) -> Tuple[SignatureHypothesis, bool, bool]:
        """現在シグネチャから適用可能な仮説を構築する。"""
        return_override: Optional[str] = None
        param_overrides: Dict[int, str] = {}
        resolved_return_override = None
        resolved_param_overrides: Dict[int, Any] = {}

        current_return = signature.return_type
        current_return_obj = signature.return_type_obj
        if override_return_type_spec is not None:
            resolved_override = override_return_type_spec
            resolved_return_override = override_return_type_spec
            if not are_types_equivalent(
                current_return_obj,
                current_return,
                resolved_override.data_type_obj if resolved_override else None,
                resolved_override.type_name,
            ):
                return_override = resolved_override.type_name
        elif override_return_type_name is not None:
            resolved_override = resolve_type_spec(
                override_return_type_name,
                program=self.program,
                fallback_signed=True,
            )
            if not are_types_equivalent(
                current_return_obj,
                current_return,
                resolved_override.data_type_obj if resolved_override else None,
                override_return_type_name,
            ):
                return_override = override_return_type_name
        elif fix_return_type and self._should_fix_type(current_return_obj, current_return):
            replacement = self.config.replacement_type_name
            replacement_spec = resolve_type_spec(
                replacement,
                program=self.program,
                fallback_signed=True,
            )
            if not are_types_equivalent(
                current_return_obj,
                current_return,
                replacement_spec.data_type_obj if replacement_spec else None,
                replacement,
            ):
                return_override = replacement

        parameters = signature.parameters or []
        override_param_type_specs = dict(override_param_type_specs or {})
        merged_param_overrides: Dict[int, Tuple[str, Optional[ResolvedTypeSpec]]] = {}
        for index, spec in override_param_type_specs.items():
            if spec is None:
                continue
            merged_param_overrides[index] = (spec.type_name, spec)
        for index, override_name in sorted((override_param_type_names or {}).items()):
            if index not in merged_param_overrides:
                merged_param_overrides[index] = (override_name, None)

        if merged_param_overrides:
            for index, (override_name, override_spec) in sorted(merged_param_overrides.items()):
                if index < 0 or index >= len(parameters):
                    continue
                current_name = parameters[index].get("data_type")
                current_obj = parameters[index].get("data_type_obj")
                if override_spec is None:
                    override_spec = resolve_type_spec(
                        override_name,
                        program=self.program,
                        fallback_size=parameters[index].get("size"),
                        fallback_signed=bool(parameters[index].get("is_signed", True)),
                    )
                if are_types_equivalent(
                    current_obj,
                    current_name,
                    override_spec.data_type_obj if override_spec else None,
                    override_name,
                ):
                    continue
                param_overrides[index] = override_name
                if override_spec is not None:
                    resolved_param_overrides[index] = override_spec
        elif fix_param_types:
            for index, param in enumerate(parameters):
                type_name = param.get("data_type")
                type_obj = param.get("data_type_obj")
                if not self._should_fix_type(type_obj, type_name):
                    continue
                replacement = self.config.replacement_type_name
                replacement_spec = resolve_type_spec(
                    replacement,
                    program=self.program,
                    fallback_size=param.get("size"),
                    fallback_signed=bool(param.get("is_signed", True)),
                )
                if are_types_equivalent(
                    type_obj,
                    type_name,
                    replacement_spec.data_type_obj if replacement_spec else None,
                    replacement,
                ):
                    continue
                param_overrides[index] = replacement

        if return_override is not None and resolved_return_override is None:
            resolved_return_override = resolve_type_spec(
                return_override,
                program=self.program,
                fallback_signed=True,
            )

        for index, override_name in param_overrides.items():
            if index in resolved_param_overrides:
                continue
            param = parameters[index]
            resolved_spec = resolve_type_spec(
                override_name,
                program=self.program,
                fallback_size=param.get("size"),
                fallback_signed=bool(param.get("is_signed", True)),
            )
            if resolved_spec is not None:
                resolved_param_overrides[index] = resolved_spec

        hypothesis = SignatureHypothesis(
            return_type_override=return_override,
            parameter_type_overrides=param_overrides,
            return_type_override_obj=resolved_return_override.data_type_obj if resolved_return_override else None,
            parameter_type_override_objs={
                index: spec.data_type_obj
                for index, spec in resolved_param_overrides.items()
            },
            resolved_return_override=resolved_return_override,
            resolved_parameter_overrides=resolved_param_overrides,
            phase=phase_name,
            reason=reason,
            evidence=dict(evidence or {}),
        )
        _, return_changed, param_changed = signature.apply_hypothesis(hypothesis)
        return hypothesis, return_changed, param_changed

    def apply_analysis_signature_fix(
        self,
        analysis: Optional[FunctionReturnAnalysis],
        *,
        fix_return_type: bool = True,
        fix_param_types: bool = True,
        override_return_type_name: Optional[str] = None,
        override_param_type_names: Optional[Dict[int, str]] = None,
        override_return_type_spec: Optional[ResolvedTypeSpec] = None,
        override_param_type_specs: Optional[Dict[int, ResolvedTypeSpec]] = None,
        phase_name: str = "",
        reason: str = "",
        evidence: Optional[Dict[str, Any]] = None,
    ) -> Tuple[Optional[FunctionReturnAnalysis], bool, bool]:
        """解析結果へ仮説シグネチャを適用した新しい解析ビューを返す。"""
        if analysis is None:
            return None, False, False

        signature = FunctionSignature.from_analysis(analysis)
        hypothesis, return_changed, param_changed = self.build_signature_hypothesis(
            signature,
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
        if not (return_changed or param_changed):
            self._debug_print(f"No signature hypothesis applied for '{analysis.function_name}'")
            return analysis, False, False

        updated_analysis = analysis.with_signature_hypothesis(hypothesis)
        self._debug_print(
            f"Applied signature hypothesis to '{analysis.function_name}': "
            f"return_changed={return_changed}, param_changed={param_changed}, "
            f"hypothesis={hypothesis.to_dict()}"
        )
        return updated_analysis, return_changed, param_changed

    def fix_function_signature(
        self,
        function,
        param_info: List[Dict[str, Any]],
        fix_return_type: bool = True,
        fix_param_types: bool = True,
        override_return_type_name: Optional[str] = None,
        override_param_type_names: Optional[Dict[int, str]] = None,
    ) -> Tuple[bool, bool]:
        """後方互換API: 永続更新せず、適用可能な変更有無だけ返す。"""
        current_return_type = None
        current_return_type_obj = None
        if hasattr(function, "getReturnType"):
            ret_type = function.getReturnType()
            current_return_type_obj = ret_type
            current_return_type = str(ret_type) if ret_type else None

        signature = FunctionSignature(
            return_type=current_return_type,
            return_type_obj=current_return_type_obj,
            parameters=[
                {
                    "name": info.get("name", f"param_{index}"),
                    "data_type": info.get("data_type"),
                    "size": info.get("size"),
                    "is_signed": info.get("is_signed", True),
                    "index": info.get("index", index),
                    "storage": dict(info.get("storage", {})) if info.get("storage") else None,
                }
                for index, info in enumerate(param_info)
            ],
        )
        _, return_changed, param_changed = self.build_signature_hypothesis(
            signature,
            fix_return_type=fix_return_type,
            fix_param_types=fix_param_types,
            override_return_type_name=override_return_type_name,
            override_param_type_names=override_param_type_names,
        )
        return return_changed, param_changed

    def fix_function_signature_by_name(
        self,
        function_name: str,
        param_info: List[Dict[str, Any]],
        fix_return_type: bool = True,
        fix_param_types: bool = True,
        override_return_type_name: Optional[str] = None,
        override_param_type_names: Optional[Dict[int, str]] = None,
    ) -> Tuple[bool, bool]:
        function = self._find_function_by_name(function_name)
        if function is None:
            self._debug_print(f"Function '{function_name}' not found")
            return (False, False)

        return self.fix_function_signature(
            function,
            param_info,
            fix_return_type=fix_return_type,
            fix_param_types=fix_param_types,
            override_return_type_name=override_return_type_name,
            override_param_type_names=override_param_type_names,
        )


class TypeFixResult:
    """型仮説適用の結果を保持するクラス。"""

    def __init__(self):
        self.return_type_fixed_binary1: bool = False
        self.return_type_fixed_binary2: bool = False
        self.param_types_fixed_binary1: bool = False
        self.param_types_fixed_binary2: bool = False
        self.retry_phase: str = "none"

        self.signedness_fixed_binary1: bool = False
        self.signedness_fixed_binary2: bool = False
        self.inferred_signedness_binary1: Optional[str] = None
        self.inferred_signedness_binary2: Optional[str] = None
        self.original_type_binary1: Optional[str] = None
        self.original_type_binary2: Optional[str] = None
        self.fixed_type_binary1: Optional[str] = None
        self.fixed_type_binary2: Optional[str] = None

        self.param_signedness_fixed_binary1: bool = False
        self.param_signedness_fixed_binary2: bool = False
        self.param_signedness_override_map_binary1: Optional[Dict[int, str]] = None
        self.param_signedness_override_map_binary2: Optional[Dict[int, str]] = None

        self.mips64_abi_fixed_binary1: bool = False
        self.mips64_abi_fixed_binary2: bool = False
        self.mips64_abi_override_map_binary1: Optional[Dict[int, str]] = None
        self.mips64_abi_override_map_binary2: Optional[Dict[int, str]] = None

    def any_fix_applied(self) -> bool:
        return (
            self.return_type_fixed_binary1
            or self.return_type_fixed_binary2
            or self.param_types_fixed_binary1
            or self.param_types_fixed_binary2
            or self.signedness_fixed_binary1
            or self.signedness_fixed_binary2
            or self.param_signedness_fixed_binary1
            or self.param_signedness_fixed_binary2
            or self.mips64_abi_fixed_binary1
            or self.mips64_abi_fixed_binary2
        )

    def any_signedness_fix_applied(self) -> bool:
        return self.signedness_fixed_binary1 or self.signedness_fixed_binary2

    def any_param_signedness_fix_applied(self) -> bool:
        return self.param_signedness_fixed_binary1 or self.param_signedness_fixed_binary2

    def any_mips64_abi_fix_applied(self) -> bool:
        return self.mips64_abi_fixed_binary1 or self.mips64_abi_fixed_binary2

    def to_dict(self) -> dict:
        result = {
            "return_type_fixed_binary1": self.return_type_fixed_binary1,
            "return_type_fixed_binary2": self.return_type_fixed_binary2,
            "param_types_fixed_binary1": self.param_types_fixed_binary1,
            "param_types_fixed_binary2": self.param_types_fixed_binary2,
            "retry_phase": self.retry_phase,
            "signedness_fixed_binary1": self.signedness_fixed_binary1,
            "signedness_fixed_binary2": self.signedness_fixed_binary2,
            "inferred_signedness_binary1": self.inferred_signedness_binary1,
            "inferred_signedness_binary2": self.inferred_signedness_binary2,
            "original_type_binary1": self.original_type_binary1,
            "original_type_binary2": self.original_type_binary2,
            "fixed_type_binary1": self.fixed_type_binary1,
            "fixed_type_binary2": self.fixed_type_binary2,
            "param_signedness_fixed_binary1": self.param_signedness_fixed_binary1,
            "param_signedness_fixed_binary2": self.param_signedness_fixed_binary2,
            "mips64_abi_fixed_binary1": self.mips64_abi_fixed_binary1,
            "mips64_abi_fixed_binary2": self.mips64_abi_fixed_binary2,
        }

        if self.param_signedness_override_map_binary1:
            result["param_signedness_override_map_binary1"] = self.param_signedness_override_map_binary1
        if self.param_signedness_override_map_binary2:
            result["param_signedness_override_map_binary2"] = self.param_signedness_override_map_binary2
        if self.mips64_abi_override_map_binary1:
            result["mips64_abi_override_map_binary1"] = self.mips64_abi_override_map_binary1
        if self.mips64_abi_override_map_binary2:
            result["mips64_abi_override_map_binary2"] = self.mips64_abi_override_map_binary2

        return result

    def __str__(self) -> str:
        parts = []
        if self.return_type_fixed_binary1:
            parts.append("return_type_fixed(binary1)")
        if self.return_type_fixed_binary2:
            parts.append("return_type_fixed(binary2)")
        if self.param_types_fixed_binary1:
            parts.append("param_types_fixed(binary1)")
        if self.param_types_fixed_binary2:
            parts.append("param_types_fixed(binary2)")
        if self.signedness_fixed_binary1:
            orig = self.original_type_binary1 or "?"
            fixed = self.fixed_type_binary1 or "?"
            parts.append(f"signedness_fixed(binary1: {orig} -> {fixed})")
        if self.signedness_fixed_binary2:
            orig = self.original_type_binary2 or "?"
            fixed = self.fixed_type_binary2 or "?"
            parts.append(f"signedness_fixed(binary2: {orig} -> {fixed})")
        if self.param_signedness_fixed_binary1:
            parts.append(f"param_signedness_fixed(binary1: {self.param_signedness_override_map_binary1})")
        if self.param_signedness_fixed_binary2:
            parts.append(f"param_signedness_fixed(binary2: {self.param_signedness_override_map_binary2})")
        if self.mips64_abi_fixed_binary1:
            parts.append(f"mips64_abi_fixed(binary1: {self.mips64_abi_override_map_binary1})")
        if self.mips64_abi_fixed_binary2:
            parts.append(f"mips64_abi_fixed(binary2: {self.mips64_abi_override_map_binary2})")

        if not parts:
            return "No type fixes applied"
        return f"Type fixes: {', '.join(parts)} (phase: {self.retry_phase})"

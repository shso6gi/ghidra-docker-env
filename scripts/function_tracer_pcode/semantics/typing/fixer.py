# -*- coding: utf-8 -*-
"""型仮説オーバーレイ生成モジュール。

Ghidra Program へ永続的な updateFunction() を行わず、解析結果上に
仮説シグネチャを重ねるためのユーティリティを提供する。
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple, TYPE_CHECKING

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.json_encoding import as_dict, materialize
from scripts.function_tracer_pcode.core import (
    FunctionReturnAnalysis,
    FunctionSignature,
    SignatureHypothesis,
)
from scripts.function_tracer_pcode.core.signature import (
    ResolvedTypeSpec,
    are_types_equivalent,
    get_declared_type_size_bytes,
    is_suspicious_undefined_data_type,
    is_unsigned_data_type,
    resolve_integer_type_spec,
    resolve_type_spec,
    resolve_signed_counterpart_spec,
)

if TYPE_CHECKING:
    pass


@dataclass
class TypeFixerConfig:
    """
    型修正ヒューリスティクスの設定。

    Attributes:
        suspicious_undefined_sizes: 修正候補とみなす Undefined 型のサイズ集合
        default_integral_size_bytes: Undefined を置換する既定の整数幅
        debug_unsigned_to_signed_map: デバッグ表示用の旧マッピング
    """

    suspicious_undefined_sizes: Set[int] = field(default_factory=lambda: {1, 2, 4, 8})
    default_integral_size_bytes: int = 4
    debug_unsigned_to_signed_map: Dict[str, str] = field(default_factory=lambda: {
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

    def is_suspicious_data_type(self, data_type_obj: Any = None) -> bool:
        return is_suspicious_undefined_data_type(
            data_type_obj,
            expected_sizes=sorted(self.suspicious_undefined_sizes),
        )

    def resolve_default_integral_type_spec(
        self,
        *,
        program: Any = None,
        fallback_size: Optional[int] = None,
        signed: bool = True,
    ) -> Optional[ResolvedTypeSpec]:
        size_bytes = int(fallback_size or self.default_integral_size_bytes)
        return resolve_integer_type_spec(
            size_bytes=size_bytes,
            signed=signed,
            program=program,
            source="default_integral_replacement",
        )

    def resolve_signed_type_spec(
        self,
        unsigned_type: Optional[str],
        *,
        data_type_obj: Any = None,
        program: Any = None,
        fallback_size: Optional[int] = None,
    ) -> Optional[ResolvedTypeSpec]:
        return resolve_signed_counterpart_spec(
            unsigned_type,
            data_type_obj=data_type_obj,
            program=program,
            fallback_size=fallback_size,
        )

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
        if isinstance(type_obj, str) and type_str is None:
            type_str = type_obj
            resolved = resolve_type_spec(type_str, program=getattr(self, "program", None))
            type_obj = resolved.data_type_obj if resolved is not None else None
        return self.config.is_suspicious_data_type(type_obj)
        
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
            if resolved_override is None or resolved_override.data_type_obj is None:
                resolved_override = None
            if not are_types_equivalent(
                current_return_obj,
                current_return,
                resolved_override.data_type_obj if resolved_override else None,
                override_return_type_name,
            ):
                if resolved_override is not None:
                    return_override = resolved_override.type_name
                    resolved_return_override = resolved_override
        elif fix_return_type and self._should_fix_type(current_return_obj, current_return):
            replacement_spec = self.config.resolve_default_integral_type_spec(
                program=self.program,
                fallback_size=get_declared_type_size_bytes(
                    current_return_obj,
                    current_return,
                    fallback_size=self.config.default_integral_size_bytes,
                    program=self.program,
                ),
                signed=True,
            )
            replacement = replacement_spec.type_name if replacement_spec is not None else None
            if not are_types_equivalent(
                current_return_obj,
                current_return,
                replacement_spec.data_type_obj if replacement_spec else None,
                replacement,
            ):
                if replacement is not None:
                    return_override = replacement
                    resolved_return_override = replacement_spec

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
                if override_spec is None or override_spec.data_type_obj is None:
                    continue
                if are_types_equivalent(
                    current_obj,
                    current_name,
                    override_spec.data_type_obj if override_spec else None,
                    override_name,
                ):
                    continue
                param_overrides[index] = override_spec.type_name
                if override_spec is not None:
                    resolved_param_overrides[index] = override_spec
        elif fix_param_types:
            for index, param in enumerate(parameters):
                type_name = param.get("data_type")
                type_obj = param.get("data_type_obj")
                if not self._should_fix_type(type_obj, type_name):
                    continue
                replacement_spec = self.config.resolve_default_integral_type_spec(
                    program=self.program,
                    fallback_size=param.get("size"),
                    signed=bool(param.get("is_signed", True)),
                )
                if replacement_spec is None:
                    continue
                replacement = replacement_spec.type_name
                if are_types_equivalent(
                    type_obj,
                    type_name,
                    replacement_spec.data_type_obj if replacement_spec else None,
                    replacement,
                ):
                    continue
                param_overrides[index] = replacement
                resolved_param_overrides[index] = replacement_spec

        if return_override is not None and resolved_return_override is None:
            resolved_return_override = resolve_type_spec(
                return_override,
                program=self.program,
                fallback_signed=True,
            )
            if resolved_return_override is None or resolved_return_override.data_type_obj is None:
                return_override = None
                resolved_return_override = None

        for index, override_name in list(param_overrides.items()):
            if index in resolved_param_overrides:
                continue
            param = parameters[index]
            resolved_spec = resolve_type_spec(
                override_name,
                program=self.program,
                fallback_size=param.get("size"),
                fallback_signed=bool(param.get("is_signed", True)),
            )
            if resolved_spec is not None and resolved_spec.data_type_obj is not None:
                resolved_param_overrides[index] = resolved_spec
                param_overrides[index] = resolved_spec.type_name
            else:
                param_overrides.pop(index, None)

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

    def json_items(self):
        yield "return_type_fixed_binary1", self.return_type_fixed_binary1
        yield "return_type_fixed_binary2", self.return_type_fixed_binary2
        yield "param_types_fixed_binary1", self.param_types_fixed_binary1
        yield "param_types_fixed_binary2", self.param_types_fixed_binary2
        yield "retry_phase", self.retry_phase
        yield "signedness_fixed_binary1", self.signedness_fixed_binary1
        yield "signedness_fixed_binary2", self.signedness_fixed_binary2
        yield "inferred_signedness_binary1", self.inferred_signedness_binary1
        yield "inferred_signedness_binary2", self.inferred_signedness_binary2
        yield "original_type_binary1", self.original_type_binary1
        yield "original_type_binary2", self.original_type_binary2
        yield "fixed_type_binary1", self.fixed_type_binary1
        yield "fixed_type_binary2", self.fixed_type_binary2
        yield "param_signedness_fixed_binary1", self.param_signedness_fixed_binary1
        yield "param_signedness_fixed_binary2", self.param_signedness_fixed_binary2
        yield "mips64_abi_fixed_binary1", self.mips64_abi_fixed_binary1
        yield "mips64_abi_fixed_binary2", self.mips64_abi_fixed_binary2
        if live_values.as_bool(self.param_signedness_override_map_binary1):
            yield "param_signedness_override_map_binary1", self.param_signedness_override_map_binary1
        if live_values.as_bool(self.param_signedness_override_map_binary2):
            yield "param_signedness_override_map_binary2", self.param_signedness_override_map_binary2
        if live_values.as_bool(self.mips64_abi_override_map_binary1):
            yield "mips64_abi_override_map_binary1", self.mips64_abi_override_map_binary1
        if live_values.as_bool(self.mips64_abi_override_map_binary2):
            yield "mips64_abi_override_map_binary2", self.mips64_abi_override_map_binary2

    def to_dict(self) -> dict:
        return materialize(self)

    def __str__(self) -> str:
        return describe_type_fix(self.to_dict())


def type_fix_applied(payload: Any) -> bool:
    """`TypeFixResult.any_fix_applied()` と同じ判定を、表現（出力の `type_fix_result`）から。"""

    payload = payload or {}
    return any(bool(payload.get(name)) for name in (
        "return_type_fixed_binary1", "return_type_fixed_binary2",
        "param_types_fixed_binary1", "param_types_fixed_binary2",
        "signedness_fixed_binary1", "signedness_fixed_binary2",
        "param_signedness_fixed_binary1", "param_signedness_fixed_binary2",
        "mips64_abi_fixed_binary1", "mips64_abi_fixed_binary2",
    ))


def describe_type_fix(payload: Any) -> str:
    """型修正の人間向けの説明（`TypeFixResult` の表現から作る）。"""

    payload = payload or {}
    parts = []
    if payload.get("return_type_fixed_binary1"):
        parts.append("return_type_fixed(binary1)")
    if payload.get("return_type_fixed_binary2"):
        parts.append("return_type_fixed(binary2)")
    if payload.get("param_types_fixed_binary1"):
        parts.append("param_types_fixed(binary1)")
    if payload.get("param_types_fixed_binary2"):
        parts.append("param_types_fixed(binary2)")
    for side in ("1", "2"):
        if payload.get(f"signedness_fixed_binary{side}"):
            orig = payload.get(f"original_type_binary{side}") or "?"
            fixed = payload.get(f"fixed_type_binary{side}") or "?"
            parts.append(f"signedness_fixed(binary{side}: {orig} -> {fixed})")
    for side in ("1", "2"):
        if payload.get(f"param_signedness_fixed_binary{side}"):
            parts.append(
                f"param_signedness_fixed(binary{side}: "
                f"{payload.get(f'param_signedness_override_map_binary{side}')})"
            )
    for side in ("1", "2"):
        if payload.get(f"mips64_abi_fixed_binary{side}"):
            parts.append(
                f"mips64_abi_fixed(binary{side}: {payload.get(f'mips64_abi_override_map_binary{side}')})"
            )

    if not parts:
        return "No type fixes applied"
    return f"Type fixes: {', '.join(parts)} (phase: {payload.get('retry_phase')})"

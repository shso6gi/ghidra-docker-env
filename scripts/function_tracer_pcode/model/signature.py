# -*- coding: utf-8 -*-
"""関数シグネチャと型仮説のデータモデル"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Optional, List, Dict, Any, TYPE_CHECKING, Tuple

if TYPE_CHECKING:
    from .analysis import FunctionReturnAnalysis


def normalize_type_name(type_name: Optional[str]) -> str:
    """型名を比較しやすい形に正規化する。"""
    return (type_name or "").strip().lower()


def clone_parameter_descriptor(
    param: Dict[str, Any],
    *,
    include_data_type_obj: bool = False,
) -> Dict[str, Any]:
    """パラメータ記述子を安全に複製する。"""
    cloned: Dict[str, Any] = {}
    for key, value in (param or {}).items():
        if key == "data_type_obj" and not include_data_type_obj:
            continue
        if isinstance(value, dict):
            cloned[key] = dict(value)
        elif isinstance(value, list):
            cloned[key] = list(value)
        else:
            cloned[key] = value
    return cloned


def _call_zero_arg(obj: Any, method_name: str) -> Any:
    """0 引数メソッドを安全に呼び出す。"""
    method = getattr(obj, method_name, None)
    if not callable(method):
        return None
    try:
        return method()
    except Exception:
        return None


def _call_one_arg(obj: Any, method_name: str, arg: Any) -> Any:
    """1 引数メソッドを安全に呼び出す。"""
    method = getattr(obj, method_name, None)
    if not callable(method):
        return None
    try:
        return method(arg)
    except Exception:
        return None


def infer_type_size_bytes(
    type_name: Optional[str],
    fallback_size: Optional[int] = None,
) -> Optional[int]:
    """C整数型名からサイズを推定する。"""
    normalized = normalize_type_name(type_name)
    if not normalized:
        return fallback_size
    if normalized == "void":
        return 0

    undefined_match = re.fullmatch(r"undefined(\d+)", normalized)
    if undefined_match:
        return int(undefined_match.group(1))

    if "bool" in normalized:
        return 1
    if any(token in normalized for token in ("char", "byte")):
        return 1
    if "short" in normalized or "int2" in normalized:
        return 2
    if (
        "long long" in normalized
        or "longlong" in normalized
        or "int8" in normalized
        or "qword" in normalized
    ):
        return 8
    if "long" in normalized:
        return 8
    if "int" in normalized or "int4" in normalized or "dword" in normalized:
        return 4
    if "word" in normalized:
        return 2
    return fallback_size


def infer_type_signedness(
    type_name: Optional[str],
    fallback_signed: bool = True,
) -> bool:
    """型名から signed/unsigned を推定する。"""
    normalized = normalize_type_name(type_name)
    if not normalized:
        return fallback_signed
    if "unsigned" in normalized:
        return False
    if normalized.startswith("u") and not normalized.startswith("undefined"):
        return False
    if "*" in normalized or "ptr" in normalized:
        return False
    return True


def _resolve_size_from_data_organization(
    type_name: Optional[str],
    data_organization: Any,
    fallback_size: Optional[int] = None,
) -> Optional[int]:
    """DataOrganization から C 基本型のサイズを引く。"""
    normalized = normalize_type_name(type_name)
    if not normalized:
        return fallback_size
    if normalized == "void":
        return 0

    undefined_match = re.fullmatch(r"undefined(\d+)", normalized)
    if undefined_match:
        return int(undefined_match.group(1))

    if "*" in normalized or "ptr" in normalized:
        pointer_size = _call_zero_arg(data_organization, "getPointerSize")
        return int(pointer_size) if pointer_size is not None else fallback_size

    if "bool" in normalized:
        return 1
    if any(token in normalized for token in ("char", "byte")):
        char_size = _call_zero_arg(data_organization, "getCharSize")
        return int(char_size) if char_size is not None else 1
    if "short" in normalized or "int2" in normalized:
        short_size = _call_zero_arg(data_organization, "getShortSize")
        return int(short_size) if short_size is not None else 2
    if (
        "long long" in normalized
        or "longlong" in normalized
        or "int8" in normalized
        or "qword" in normalized
    ):
        long_long_size = _call_zero_arg(data_organization, "getLongLongSize")
        return int(long_long_size) if long_long_size is not None else 8
    if "long" in normalized:
        long_size = _call_zero_arg(data_organization, "getLongSize")
        return int(long_size) if long_size is not None else 8
    if "int" in normalized or "int4" in normalized or "dword" in normalized:
        int_size = _call_zero_arg(data_organization, "getIntegerSize")
        return int(int_size) if int_size is not None else 4
    if "word" in normalized:
        short_size = _call_zero_arg(data_organization, "getShortSize")
        return int(short_size) if short_size is not None else 2
    return fallback_size


@dataclass(frozen=True)
class ResolvedTypeSpec:
    """Program/ABI 文脈で具体化した型情報。"""

    type_name: str
    size_bytes: Optional[int] = None
    is_signed: Optional[bool] = None
    source: str = "heuristic"
    data_type_path: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        result: Dict[str, Any] = {
            "type_name": self.type_name,
            "source": self.source,
        }
        if self.size_bytes is not None:
            result["size_bytes"] = self.size_bytes
        if self.is_signed is not None:
            result["is_signed"] = self.is_signed
        if self.data_type_path:
            result["data_type_path"] = self.data_type_path
        return result


def _resolved_type_spec_from_data_type(
    type_name: str,
    data_type: Any,
    fallback_signed: bool,
) -> ResolvedTypeSpec:
    """Ghidra DataType から overlay 用の型情報を抽出する。"""
    normalized = normalize_type_name(type_name)
    resolved_name = str(_call_zero_arg(data_type, "getName") or type_name)
    size = _call_zero_arg(data_type, "getLength")
    if size is not None:
        try:
            size = int(size)
        except Exception:
            size = None
    if normalized == "void":
        size = 0
    elif size is not None and size < 0:
        size = None

    is_signed = None
    signed_value = _call_zero_arg(data_type, "isSigned")
    if signed_value is not None:
        is_signed = bool(signed_value)
    elif normalized == "void":
        is_signed = False
    elif size == 0:
        is_signed = False
    elif "*" in normalized or "ptr" in normalized:
        is_signed = False
    else:
        is_signed = infer_type_signedness(type_name, fallback_signed=fallback_signed)

    data_type_path = None
    path_obj = _call_zero_arg(data_type, "getDataTypePath")
    if path_obj is not None:
        data_type_path = str(path_obj)

    return ResolvedTypeSpec(
        type_name=resolved_name or type_name,
        size_bytes=size,
        is_signed=is_signed,
        source="ghidra_datatype",
        data_type_path=data_type_path,
    )


def _parse_data_type_with_ghidra(
    data_type_manager: Any,
    type_name: str,
) -> Any:
    """Ghidra DataTypeParser を使って型名を解決する。"""
    try:
        from ghidra.util.data import DataTypeParser  # type: ignore[import]
    except Exception:
        return None

    allowed_types = getattr(DataTypeParser.AllowedDataTypes, "ALL", None)
    try:
        parser = DataTypeParser(data_type_manager, data_type_manager, None, allowed_types)
        return parser.parse(type_name)
    except Exception:
        return None


def _lookup_data_type_directly(
    data_type_manager: Any,
    type_name: str,
) -> Any:
    """DataTypeManager から直接型名を引く。"""
    candidates = [type_name]
    stripped = type_name.strip()
    if stripped and stripped not in candidates:
        candidates.append(stripped)
    if stripped and not stripped.startswith("/"):
        candidates.append(f"/{stripped}")

    for candidate in candidates:
        data_type = _call_one_arg(data_type_manager, "getDataType", candidate)
        if data_type is not None:
            return data_type
        data_type = _call_one_arg(data_type_manager, "findDataType", candidate)
        if data_type is not None:
            return data_type
    return None


def resolve_type_spec(
    type_name: Optional[str],
    *,
    program: Any = None,
    fallback_size: Optional[int] = None,
    fallback_signed: bool = True,
) -> Optional[ResolvedTypeSpec]:
    """型名を Program/ABI 文脈で具体化する。"""
    normalized = normalize_type_name(type_name)
    if not normalized:
        return None

    data_type_manager = None
    if program is not None:
        data_type_manager = _call_zero_arg(program, "getDataTypeManager")

    if data_type_manager is not None:
        data_type = _parse_data_type_with_ghidra(data_type_manager, type_name or normalized)
        if data_type is None:
            data_type = _lookup_data_type_directly(data_type_manager, type_name or normalized)
        if data_type is not None:
            return _resolved_type_spec_from_data_type(
                type_name or normalized,
                data_type,
                fallback_signed=fallback_signed,
            )

        data_organization = _call_zero_arg(data_type_manager, "getDataOrganization")
        if data_organization is not None:
            size = _resolve_size_from_data_organization(
                type_name,
                data_organization,
                fallback_size=fallback_size,
            )
            return ResolvedTypeSpec(
                type_name=type_name or normalized,
                size_bytes=size,
                is_signed=infer_type_signedness(
                    type_name,
                    fallback_signed=fallback_signed,
                ),
                source="data_organization",
            )

    return ResolvedTypeSpec(
        type_name=type_name or normalized,
        size_bytes=infer_type_size_bytes(type_name, fallback_size=fallback_size),
        is_signed=infer_type_signedness(type_name, fallback_signed=fallback_signed),
        source="heuristic",
    )


def apply_type_name_to_parameter(
    param: Dict[str, Any],
    type_name: str,
    resolved_spec: Optional[ResolvedTypeSpec] = None,
) -> Dict[str, Any]:
    """パラメータ記述子へ型オーバーライドを適用する。"""
    updated = clone_parameter_descriptor(param, include_data_type_obj=False)
    updated["data_type"] = type_name
    updated["data_type_obj"] = None

    fallback_size = updated.get("size")
    inferred_size = (
        resolved_spec.size_bytes
        if resolved_spec is not None and resolved_spec.size_bytes is not None
        else infer_type_size_bytes(type_name, fallback_size=fallback_size)
    )
    if inferred_size is not None and inferred_size >= 0:
        updated["size"] = inferred_size
        storage = updated.get("storage")
        if isinstance(storage, dict):
            storage = dict(storage)
            storage["size"] = inferred_size
            storage["size_bits"] = inferred_size * 8
            updated["storage"] = storage

    if resolved_spec is not None and resolved_spec.is_signed is not None:
        updated["is_signed"] = resolved_spec.is_signed
    else:
        updated["is_signed"] = infer_type_signedness(
            type_name,
            fallback_signed=bool(updated.get("is_signed", True)),
        )
    return updated


def parameters_without_runtime_objects(
    parameters: Optional[List[Dict[str, Any]]],
) -> Optional[List[Dict[str, Any]]]:
    """シリアライズ可能なパラメータ一覧へ正規化する。"""
    if parameters is None:
        return None
    return [
        clone_parameter_descriptor(param, include_data_type_obj=False)
        for param in parameters
    ]


@dataclass(frozen=True)
class SignatureHypothesis:
    """関数シグネチャへ重ねる仮説的オーバーライド。"""

    return_type_override: Optional[str] = None
    parameter_type_overrides: Dict[int, str] = field(default_factory=dict)
    resolved_return_override: Optional[ResolvedTypeSpec] = None
    resolved_parameter_overrides: Dict[int, ResolvedTypeSpec] = field(default_factory=dict)
    phase: str = ""
    reason: str = ""
    evidence: Dict[str, Any] = field(default_factory=dict)

    def has_changes(self) -> bool:
        return (
            self.return_type_override is not None
            or bool(self.parameter_type_overrides)
        )

    def to_dict(self) -> Dict[str, Any]:
        result = {
            "return_type_override": self.return_type_override,
            "parameter_type_overrides": dict(self.parameter_type_overrides),
        }
        if self.resolved_return_override is not None:
            result["resolved_return_override"] = self.resolved_return_override.to_dict()
        if self.resolved_parameter_overrides:
            result["resolved_parameter_overrides"] = {
                index: spec.to_dict()
                for index, spec in self.resolved_parameter_overrides.items()
            }
        if self.phase:
            result["phase"] = self.phase
        if self.reason:
            result["reason"] = self.reason
        if self.evidence:
            result["evidence"] = dict(self.evidence)
        return result

    def describe(self) -> str:
        parts: List[str] = []
        if self.return_type_override is not None:
            parts.append(f"return={self.return_type_override}")
        if self.parameter_type_overrides:
            parts.append(f"params={self.parameter_type_overrides}")
        payload = ", ".join(parts) if parts else "no-op"
        prefix = self.phase or "signature_hypothesis"
        if self.reason:
            return f"{prefix}: {self.reason} ({payload})"
        return f"{prefix}: {payload}"


@dataclass
class FunctionSignature:
    """関数シグネチャ情報"""

    return_type: Optional[str] = None
    parameters: Optional[List[Dict[str, Any]]] = None

    def format_return_type(self) -> str:
        """戻り値の型をフォーマット"""
        return self.return_type if self.return_type else "unknown"

    def format_parameters(self) -> str:
        """引数リストをフォーマット（例: (int a, long b)）"""
        if not self.parameters:
            return "(void)"

        param_strs = []
        for p in self.parameters:
            dtype = p.get("data_type", "unknown")
            name = p.get("name", "")
            if name:
                param_strs.append(f"{dtype} {name}")
            else:
                param_strs.append(dtype)

        return f"({', '.join(param_strs)})"

    def format_full(self, func_name: str) -> str:
        """完全なシグネチャをフォーマット（例: int func(int a, long b)）"""
        return f"{self.format_return_type()} {func_name}{self.format_parameters()}"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "return_type": self.return_type,
            "parameters": parameters_without_runtime_objects(self.parameters),
        }

    def clone(self) -> "FunctionSignature":
        return FunctionSignature(
            return_type=self.return_type,
            parameters=parameters_without_runtime_objects(self.parameters),
        )

    def apply_hypothesis(
        self,
        hypothesis: SignatureHypothesis,
    ) -> Tuple["FunctionSignature", bool, bool]:
        """仮説オーバーライドを適用した新しいシグネチャを返す。"""
        updated_return_type = self.return_type
        return_changed = False
        param_changed = False

        if hypothesis.return_type_override is not None:
            if normalize_type_name(updated_return_type) != normalize_type_name(
                hypothesis.return_type_override
            ):
                updated_return_type = hypothesis.return_type_override
                return_changed = True

        updated_params = parameters_without_runtime_objects(self.parameters) or []
        if updated_params and hypothesis.parameter_type_overrides:
            for index, new_type in sorted(hypothesis.parameter_type_overrides.items()):
                if index < 0 or index >= len(updated_params):
                    continue
                current_type = updated_params[index].get("data_type")
                if normalize_type_name(current_type) == normalize_type_name(new_type):
                    continue
                resolved_spec = hypothesis.resolved_parameter_overrides.get(index)
                updated_params[index] = apply_type_name_to_parameter(
                    updated_params[index],
                    new_type,
                    resolved_spec=resolved_spec,
                )
                param_changed = True

        return (
            FunctionSignature(
                return_type=updated_return_type,
                parameters=updated_params,
            ),
            return_changed,
            param_changed,
        )

    @classmethod
    def from_analysis(cls, analysis: "FunctionReturnAnalysis") -> "FunctionSignature":
        """FunctionReturnAnalysisからシグネチャを抽出"""
        return cls(
            return_type=analysis.return_type,
            parameters=parameters_without_runtime_objects(analysis.parameters),
        )

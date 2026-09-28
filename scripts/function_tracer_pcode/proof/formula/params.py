# -*- coding: utf-8 -*-
"""FormulaBuilder のパラメータ関連ヘルパー。"""

from __future__ import annotations

import re
from typing import Dict, List, Optional, Mapping, Tuple

from scripts.function_tracer_pcode.core.parameter_domain import (
    parameter_descriptor_bits,
    parameter_descriptor_index,
    parameter_descriptor_signed,
    synthetic_parameter_kind,
)
from scripts.function_tracer_pcode.core.signature import (
    get_data_type_display_name,
    is_pointer_data_type,
    normalize_type_name,
)

from scripts.function_tracer_pcode.proof.formula.types import (
    ExtraVariableInfo,
    ParameterInfo,
)


def collect_param_info(params: List[Dict], suffix: str) -> List[ParameterInfo]:
    """解析結果から ParameterInfo 一覧を構築する。"""
    result: List[ParameterInfo] = []
    for param in params:
        # (index, 幅, 符号) の読み方は入力領域の封印と同じ 1 つの規則（Issue #185）
        index = parameter_descriptor_index(param)
        name = param.get("name", f"param_{index}")
        size = parameter_descriptor_bits(param)
        is_signed = parameter_descriptor_signed(param)
        abi_register_name = _parameter_register_name(param)
        abi_bank = _parameter_abi_bank(param)
        result.append(
            ParameterInfo(
                original_name=name,
                smt_name=f"{name}{suffix}",
                bit_width=size,
                index=index,
                is_signed=is_signed,
                type_class=_parameter_type_class(param),
                abi_register_name=abi_register_name,
                abi_bank=abi_bank,
                abi_bank_ordinal=_parameter_abi_bank_ordinal(param, abi_bank),
            )
        )

    result.sort(key=lambda item: item.index)
    return result


def _parameter_type_class(param: Mapping) -> str:
    # synthetic の出所の名乗りは core の登録（``SYNTHETIC_PARAMETER_KINDS``）だけで判定する
    synthetic_kind = synthetic_parameter_kind(param)
    if synthetic_kind is not None:
        return synthetic_kind

    type_name = normalize_type_name(
        get_data_type_display_name(param.get("data_type_obj"), param.get("data_type"))
    )
    data_type_obj = param.get("data_type_obj")
    if data_type_obj is not None and is_pointer_data_type(data_type_obj, type_name):
        return "pointer"
    if data_type_obj is None and _type_name_looks_pointer(type_name):
        return "pointer"
    if _type_name_looks_floating(type_name):
        return "fp"
    if _type_name_looks_integral(type_name):
        return "int"
    return "unknown"


def _parameter_register_name(param: Mapping) -> Optional[str]:
    storage = param.get("storage")
    if storage is None:
        return None
    if isinstance(storage, Mapping):
        value = storage.get("register_name") or storage.get("base_register_name")
    else:
        value = getattr(storage, "register_name", None) or getattr(storage, "base_register_name", None)
    if not value:
        return None
    return str(value).strip().lower()


def _parameter_abi_bank(param: Mapping) -> Optional[str]:
    register_name = _parameter_register_name(param)
    if not register_name:
        return None
    if _register_name_looks_fp(register_name):
        return "fp"
    if _register_name_looks_gp(register_name):
        return "gp"
    return None


def _parameter_abi_bank_ordinal(param: Mapping, bank: Optional[str]) -> Optional[int]:
    if bank not in {"gp", "fp"}:
        return None
    register_name = _parameter_register_name(param)
    if not register_name:
        return None
    match = re.search(r"(\d+)", register_name)
    if match is None:
        return None
    try:
        return int(match.group(1))
    except ValueError:
        return None


def _register_name_looks_fp(register_name: Optional[str]) -> bool:
    if not register_name:
        return False
    return bool(re.fullmatch(r"(f|d|s|q|v)\d+.*", register_name))


def _register_name_looks_gp(register_name: Optional[str]) -> bool:
    if not register_name:
        return False
    return bool(re.fullmatch(r"(a|x|w|r)\d+.*", register_name))


def _type_name_looks_floating(type_name: str) -> bool:
    return any(token in type_name for token in ("float", "double"))


def _type_name_looks_pointer(type_name: str) -> bool:
    if not type_name:
        return False
    if "*" in type_name or type_name.endswith(" pointer") or " pointer " in type_name:
        return True
    return bool(re.search(r"(^|[\s_])ptr($|[\s_])", type_name))


def _type_name_looks_integral(type_name: str) -> bool:
    if not type_name:
        return False
    integral_tokens = (
        "bool",
        "byte",
        "char",
        "short",
        "int",
        "long",
        "size_t",
        "ssize_t",
        "word",
        "dword",
        "qword",
    )
    return any(token in type_name for token in integral_tokens)


def merge_param_and_extra_vars(
    params: List[ParameterInfo],
    extra_vars: List[ExtraVariableInfo],
) -> List[ParameterInfo]:
    """追加変数を return 展開用の ParameterInfo として統合する。"""
    result = list(params)
    for extra_var in extra_vars:
        result.append(
            ParameterInfo(
                original_name=extra_var.original_name,
                smt_name=extra_var.smt_name,
                bit_width=extra_var.bit_width,
                index=-1,
                is_signed=True,
            )
        )
    return result


def build_symbol_name_mapping(param_infos: List[ParameterInfo]) -> Mapping[str, str]:
    """最終 SMT シンボル名の写像を作る。"""
    mapping: Dict[str, str] = {}
    for param in param_infos:
        mapping[param.original_name] = param.smt_name
    return mapping


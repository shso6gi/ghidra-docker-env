# -*- coding: utf-8 -*-
"""FormulaBuilder のパラメータ関連ヘルパー。"""

from __future__ import annotations

import re
from typing import Dict, List, Optional, Mapping, Tuple

from scripts.function_tracer_pcode.core.signature import (
    get_data_type_display_name,
    is_pointer_data_type,
    normalize_type_name,
)

from scripts.function_tracer_pcode.proof.formula.types import (
    ExtraVariableInfo,
    ParameterInfo,
    ParameterPair,
)


def collect_param_info(params: List[Dict], suffix: str) -> List[ParameterInfo]:
    """解析結果から ParameterInfo 一覧を構築する。"""
    result: List[ParameterInfo] = []
    for param in params:
        name = param.get("name", f"param_{param.get('index', 0)}")
        size = param.get("size", 4) * 8
        index = param.get("index", 0)
        is_signed = param.get("is_signed", True)
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


def build_parameter_pairs(
    params1: List[ParameterInfo],
    params2: List[ParameterInfo],
) -> List[ParameterPair]:
    """2つの関数のパラメータを安全な evidence ベースで対応付ける。"""
    matched1: set[int] = set()
    matched2: set[int] = set()
    pairs: List[ParameterPair] = []

    params2_by_name: Dict[str, List[int]] = {}
    for j, param in enumerate(params2):
        params2_by_name.setdefault(param.original_name, []).append(j)

    for i, param1 in enumerate(params1):
        if not _parameter_name_match_is_strong(param1):
            continue
        candidates = [
            j
            for j in params2_by_name.get(param1.original_name, [])
            if (
                j not in matched2
                and _parameter_name_match_is_strong(params2[j])
                and _parameter_role_signature(param1) == _parameter_role_signature(params2[j])
            )
        ]
        if len(candidates) != 1:
            continue
        j = candidates[0]
        pairs.append(ParameterPair(index=param1.index, param1=param1, param2=params2[j]))
        matched1.add(i)
        matched2.add(j)

    if _parameter_role_reordering_allowed(params1, params2):
        sig_to_params1: Dict[Tuple[Optional[str], int, bool], List[int]] = {}
        sig_to_params2: Dict[Tuple[Optional[str], int, bool], List[int]] = {}
        for i, param in enumerate(params1):
            if i in matched1:
                continue
            sig_to_params1.setdefault(_parameter_role_signature(param), []).append(i)
        for j, param in enumerate(params2):
            if j in matched2:
                continue
            sig_to_params2.setdefault(_parameter_role_signature(param), []).append(j)

        for signature in sorted(set(sig_to_params1) & set(sig_to_params2), key=repr):
            if signature[0] not in {"int", "fp"}:
                continue
            left = sig_to_params1[signature]
            right = sig_to_params2[signature]
            if len(left) != 1 or len(right) != 1:
                continue
            i = left[0]
            j = right[0]
            pairs.append(ParameterPair(index=params1[i].index, param1=params1[i], param2=params2[j]))
            matched1.add(i)
            matched2.add(j)

    remaining1_by_index = {}
    remaining2_by_index = {}
    all_indices = set()

    for i, param in enumerate(params1):
        if i in matched1:
            continue
        remaining1_by_index[param.index] = param
        all_indices.add(param.index)

    for j, param in enumerate(params2):
        if j in matched2:
            continue
        remaining2_by_index[param.index] = param
        all_indices.add(param.index)

    for index in sorted(all_indices):
        pairs.append(
            ParameterPair(
                index=index,
                param1=remaining1_by_index.get(index),
                param2=remaining2_by_index.get(index),
            )
        )

    return sorted(pairs, key=_parameter_pair_sort_key)


def _parameter_pair_sort_key(pair: ParameterPair) -> Tuple[int, int, int]:
    left_index = pair.param1.index if pair.param1 is not None else pair.index
    right_index = pair.param2.index if pair.param2 is not None else pair.index
    return (
        left_index if left_index is not None else 1 << 20,
        right_index if right_index is not None else 1 << 20,
        pair.index,
    )


def _parameter_role_signature(param: ParameterInfo) -> Tuple[Optional[str], int, bool]:
    return (param.type_class, int(param.bit_width), bool(param.is_signed))


def _parameter_role_reordering_allowed(
    params1: List[ParameterInfo],
    params2: List[ParameterInfo],
) -> bool:
    return (
        _has_mips64_split_register_bank_evidence(params1)
        and _has_mixed_register_bank_evidence(params2)
    ) or (
        _has_mips64_split_register_bank_evidence(params2)
        and _has_mixed_register_bank_evidence(params1)
    )


def _has_mixed_register_bank_evidence(params: List[ParameterInfo]) -> bool:
    banks = {param.abi_bank for param in params if param.abi_bank in {"gp", "fp"}}
    return {"gp", "fp"}.issubset(banks)


def _has_mips64_split_register_bank_evidence(params: List[ParameterInfo]) -> bool:
    if not _has_mixed_register_bank_evidence(params):
        return False
    return any(_register_name_looks_mips64_fp(param.abi_register_name) for param in params) and any(
        _register_name_looks_mips64_gp(param.abi_register_name) for param in params
    )


def _parameter_type_class(param: Mapping) -> str:
    if param.get("synthetic_recursive_summary"):
        return "synthetic_recursive_summary"
    if param.get("synthetic_pure_call_summary"):
        return "synthetic_pure_call_summary"

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


def _register_name_looks_mips64_fp(register_name: Optional[str]) -> bool:
    if not register_name:
        return False
    return bool(re.fullmatch(r"f\d+.*", register_name))


def _register_name_looks_mips64_gp(register_name: Optional[str]) -> bool:
    if not register_name:
        return False
    return bool(re.fullmatch(r"a\d+(_lo|_hi)?.*", register_name))


def _parameter_name_match_is_strong(param: ParameterInfo) -> bool:
    if param.type_class in {"synthetic_recursive_summary", "synthetic_pure_call_summary"}:
        return True
    name = param.original_name or ""
    return not re.fullmatch(r"param_\d+", name)


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


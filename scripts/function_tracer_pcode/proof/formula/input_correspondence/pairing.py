# -*- coding: utf-8 -*-
"""比較する 2 関数の parameter をどれとどれで結ぶか（最終 relation の第 1 段）。

pairing の方針は最終 ``InputCorrespondence`` だけが使う。pair が決まったあと、
各 pair にどの relation（R0〜R5）を与えるかは ``relation.py`` が決める。
"""

from __future__ import annotations

import re
from typing import Dict, List, Optional, Tuple

from scripts.function_tracer_pcode.core.parameter_domain import SYNTHETIC_PARAMETER_KINDS
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo, ParameterPair


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


def _register_name_looks_mips64_fp(register_name: Optional[str]) -> bool:
    if not register_name:
        return False
    return bool(re.fullmatch(r"f\d+.*", register_name))


def _register_name_looks_mips64_gp(register_name: Optional[str]) -> bool:
    if not register_name:
        return False
    return bool(re.fullmatch(r"a\d+(_lo|_hi)?.*", register_name))


def _parameter_name_match_is_strong(param: ParameterInfo) -> bool:
    if param.type_class in SYNTHETIC_PARAMETER_KINDS:
        return True
    name = param.original_name or ""
    return not re.fullmatch(r"param_\d+", name)

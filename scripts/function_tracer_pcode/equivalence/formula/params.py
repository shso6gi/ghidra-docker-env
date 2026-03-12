# -*- coding: utf-8 -*-
"""FormulaBuilder のパラメータ関連ヘルパー。"""

from __future__ import annotations

import re
from typing import Dict, List

from .types import ExtraVariableInfo, ParameterInfo, ParameterPair


def collect_param_info(params: List[Dict], suffix: str) -> List[ParameterInfo]:
    """解析結果から ParameterInfo 一覧を構築する。"""
    result: List[ParameterInfo] = []
    for param in params:
        name = param.get("name", f"param_{param.get('index', 0)}")
        size = param.get("size", 4) * 8
        index = param.get("index", 0)
        is_signed = param.get("is_signed", True)
        result.append(
            ParameterInfo(
                original_name=name,
                smt_name=f"{name}{suffix}",
                bit_width=size,
                index=index,
                is_signed=is_signed,
            )
        )

    result.sort(key=lambda item: item.index)
    return result


def build_parameter_pairs(
    params1: List[ParameterInfo],
    params2: List[ParameterInfo],
) -> List[ParameterPair]:
    """2つの関数のパラメータを index ベースで対応付ける。"""
    pairs: List[ParameterPair] = []

    all_indices = set()
    params1_by_index = {}
    params2_by_index = {}

    for param in params1:
        params1_by_index[param.index] = param
        all_indices.add(param.index)

    for param in params2:
        params2_by_index[param.index] = param
        all_indices.add(param.index)

    for index in sorted(all_indices):
        pairs.append(
            ParameterPair(
                index=index,
                param1=params1_by_index.get(index),
                param2=params2_by_index.get(index),
            )
        )

    return pairs


def build_parameter_constraint(pair: ParameterPair) -> List[str]:
    """パラメータ間の等価制約を構築する。"""
    if pair.param1 is None or pair.param2 is None:
        return [f"; Parameter index {pair.index}: missing in one function"]

    param1 = pair.param1
    param2 = pair.param2

    if not pair.has_width_mismatch():
        return [
            f"; {param1.smt_name} and {param2.smt_name}: same width ({param1.bit_width}bit)",
            f"(assert (= {param1.smt_name} {param2.smt_name}))",
        ]

    overlap_bits = pair.get_overlapping_width()
    lines = [
        f"; {param1.smt_name} ({param1.bit_width}bit) vs {param2.smt_name} ({param2.bit_width}bit)",
        f"; Overlapping bits: {overlap_bits}",
        f"; Constraint: lower {overlap_bits} bits are equal",
    ]

    if param1.bit_width < param2.bit_width:
        lines.append(
            f"(assert (= {param1.smt_name} ((_ extract {overlap_bits - 1} 0) {param2.smt_name})))"
        )
        lines.append(
            f"; Upper bits of {param2.smt_name} [{param2.bit_width - 1}:{overlap_bits}] are free"
        )
    else:
        lines.append(
            f"(assert (= ((_ extract {overlap_bits - 1} 0) {param1.smt_name}) {param2.smt_name}))"
        )
        lines.append(
            f"; Upper bits of {param1.smt_name} [{param1.bit_width - 1}:{overlap_bits}] are free"
        )

    return lines


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


def replace_symbol_names(smt_expr: str, param_infos: List[ParameterInfo]) -> str:
    """SMT式中の元シンボル名をサフィックス付き名へ置換する。"""
    result = smt_expr
    sorted_params = sorted(param_infos, key=lambda item: -len(item.original_name))

    for param in sorted_params:
        pattern = r"\b" + re.escape(param.original_name) + r"\b"
        result = re.sub(pattern, param.smt_name, result)

    return result

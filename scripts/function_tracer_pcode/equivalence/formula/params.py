# -*- coding: utf-8 -*-
"""FormulaBuilder のパラメータ関連ヘルパー。"""

from __future__ import annotations

from typing import Dict, List, Optional, TYPE_CHECKING, Mapping

from .types import ExtraVariableInfo, ParameterInfo, ParameterPair

if TYPE_CHECKING:
    from .variable import ExtraVariableAnalysis, ParameterFragmentInfo


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

    semantic_overlap = _get_semantic_overlap_bits(param1, param2)
    if semantic_overlap is not None:
        return [
            (
                f"; {param1.smt_name} and {param2.smt_name}: "
                f"semantic lower {semantic_overlap} bits must match"
            ),
            (
                f"(assert (= ((_ extract {semantic_overlap - 1} 0) {param1.smt_name}) "
                f"((_ extract {semantic_overlap - 1} 0) {param2.smt_name})))"
            ),
        ]

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


def build_fragment_backed_parameter_constraint(
    pair: ParameterPair,
    fragment_info1: Optional["ParameterFragmentInfo"] = None,
    fragment_info2: Optional["ParameterFragmentInfo"] = None,
) -> Optional[List[str]]:
    """Use parameter-fragment evidence to constrain full-width equality."""
    if pair.param1 is None or pair.param2 is None:
        return None

    param1 = pair.param1
    param2 = pair.param2

    if param1.bit_width < param2.bit_width:
        fragment_info = fragment_info1
        narrow = param1
        wide = param2
    elif param2.bit_width < param1.bit_width:
        fragment_info = fragment_info2
        narrow = param2
        wide = param1
    else:
        return None

    if fragment_info is None:
        return None
    if fragment_info.parent_param_index != pair.index:
        return None
    if fragment_info.parent_param_bit_width != narrow.bit_width:
        return None
    if fragment_info.base_register_size_bits != wide.bit_width:
        return None

    extend_bits = wide.bit_width - narrow.bit_width
    if extend_bits <= 0:
        return None

    ext_op = (
        "sign_extend"
        if fragment_info.extension_type.name == "SIGN_EXTEND"
        else "zero_extend"
    )
    return [
        (
            f"; {wide.smt_name}: fully constrained from fragment-backed "
            f"{narrow.smt_name} via {ext_op}"
        ),
        (
            f"(assert (= {wide.smt_name} ((_ {ext_op} {extend_bits}) "
            f"{narrow.smt_name})))"
        ),
    ]


def collect_fragment_infos_by_param_index(
    analyses: Dict[str, "ExtraVariableAnalysis"],
) -> Dict[int, "ParameterFragmentInfo"]:
    """Collect at most one safely-constrainable fragment per parameter index."""
    result: Dict[int, "ParameterFragmentInfo"] = {}
    for analysis in analyses.values():
        if not analysis.can_safely_constrain() or analysis.fragment_info is None:
            continue
        parent_index = analysis.fragment_info.parent_param_index
        if parent_index < 0 or parent_index in result:
            continue
        result[parent_index] = analysis.fragment_info
    return result


def build_parameter_semantic_constraints(params: List[ParameterInfo]) -> List[str]:
    """Build self-consistency constraints for narrowed parameter semantics."""
    lines: List[str] = []
    for param in params:
        semantic_bits = param.semantic_narrow_bits
        signedness = param.semantic_signedness
        if (
            semantic_bits is None
            or signedness not in {"signed", "unsigned"}
            or semantic_bits >= param.bit_width
        ):
            continue

        extend_bits = param.bit_width - semantic_bits
        ext_op = "sign_extend" if signedness == "signed" else "zero_extend"
        lines.append(
            f"; {param.smt_name}: constrain to {signedness} {semantic_bits}-bit semantic value"
        )
        lines.append(
            f"(assert (= {param.smt_name} ((_ {ext_op} {extend_bits}) "
            f"((_ extract {semantic_bits - 1} 0) {param.smt_name}))))"
        )
    return lines


def _get_semantic_overlap_bits(
    param1: ParameterInfo,
    param2: ParameterInfo,
) -> Optional[int]:
    candidates = []
    if param1.semantic_narrow_bits is not None:
        candidates.append(param1.semantic_narrow_bits)
    if param2.semantic_narrow_bits is not None:
        candidates.append(param2.semantic_narrow_bits)
    if not candidates:
        return None

    overlap_bits = min(candidates)
    if overlap_bits <= 0:
        return None
    if overlap_bits > min(param1.bit_width, param2.bit_width):
        return None
    return overlap_bits


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
    """SMT式中のシンボル名を最終名へ置換する。

    既存コードとの互換性のために残すヘルパー。
    新規実装では AST の ``to_smt(symbol_name_mapping=...)`` を使う想定。
    """
    if not smt_expr:
        return smt_expr

    mapping = _build_symbol_name_mapping(param_infos)
    return _replace_symbols_in_smt_text(smt_expr, mapping)


def build_symbol_name_mapping(param_infos: List[ParameterInfo]) -> Mapping[str, str]:
    """最終 SMT シンボル名の写像を作る。"""
    mapping: Dict[str, str] = {}
    for param in param_infos:
        mapping[param.original_name] = param.smt_name
    return mapping


def _build_symbol_name_mapping(param_infos: List[ParameterInfo]) -> Mapping[str, str]:
    """旧内部実装の互換ラッパー（将来のリファクタ時に削除予定）。"""
    return build_symbol_name_mapping(param_infos)


def _replace_symbols_in_smt_text(smt_expr: str, mapping: Mapping[str, str]) -> str:
    """トークン単位でSMT文字列中のシンボル名を置換する。

    正規表現ではなく、識別子トークン境界での置換にする。
    """
    if not mapping:
        return smt_expr

    result: List[str] = []
    i = 0
    length = len(smt_expr)
    while i < length:
        ch = smt_expr[i]
        if ch == "_" or ch.isalpha():
            start = i
            i += 1
            while i < length and (smt_expr[i].isalnum() or smt_expr[i] == "_"):
                i += 1
            token = smt_expr[start:i]
            result.append(mapping.get(token, token))
            continue

        result.append(ch)
        i += 1

    return "".join(result)

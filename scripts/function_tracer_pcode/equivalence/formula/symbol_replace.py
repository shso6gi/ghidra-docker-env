# -*- coding: utf-8 -*-
"""シンボル名置換ユーティリティ"""

from typing import Callable, List, Mapping, Sequence, Any

from ...model import Condition, Expression


def build_symbol_replacer(
    params_info: List,
    extra_vars_info: List
) -> Callable[[Any], str]:
    """パラメータ名 → SMT名の最終置換関数を構築する。

    文字列入力だけでなく、Expression/Condition も受け取れる。
    """
    mapping = _build_symbol_mapping(params_info, extra_vars_info)

    def replacer(node: object) -> str:
        if isinstance(node, (Expression, Condition)):
            return node.to_smt(symbol_name_mapping=mapping)
        if isinstance(node, str):
            return _replace_symbol_text(node, mapping)
        return _replace_symbol_text(str(node), mapping)

    return replacer


def _build_symbol_mapping(
    params_info: Sequence,
    extra_vars_info: Sequence,
) -> Mapping[str, str]:
    mapping = {}
    for item in params_info:
        mapping[item.original_name] = item.smt_name
    for item in extra_vars_info:
        mapping[item.original_name] = item.smt_name
    return mapping


def _replace_symbol_text(smt_expr: str, mapping: Mapping[str, str]) -> str:
    """文字列 SMT 式のシンボル名を置換する（非正規表現）。"""
    if not smt_expr or not mapping:
        return smt_expr

    result: List[str] = []
    index = 0
    length = len(smt_expr)
    while index < length:
        ch = smt_expr[index]
        if ch == "_" or ch.isalpha():
            start = index
            index += 1
            while index < length and (smt_expr[index].isalnum() or smt_expr[index] == "_"):
                index += 1
            token = smt_expr[start:index]
            result.append(mapping.get(token, token))
            continue

        result.append(ch)
        index += 1

    return "".join(result)

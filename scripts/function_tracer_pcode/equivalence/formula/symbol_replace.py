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
    """文字列 SMT 式のシンボル名を置換する（内部限定フォールバック）。"""
    if not smt_expr or not mapping:
        return smt_expr

    result: List[str] = []
    index = 0
    length = len(smt_expr)
    while index < length:
        ch = smt_expr[index]

        if ch.isspace():
            result.append(ch)
            index += 1
            continue

        if ch == ";":
            line_end = smt_expr.find("\n", index)
            if line_end < 0:
                line_end = length
            else:
                line_end += 1
            result.append(smt_expr[index:line_end])
            index = line_end
            continue

        if ch == '"':
            end = _consume_quoted_string(smt_expr, index)
            result.append(smt_expr[index:end])
            index = end
            continue

        if ch == "|":
            end, token = _consume_quoted_symbol(smt_expr, index)
            replacement = mapping.get(token)
            if replacement is None:
                result.append(smt_expr[index:end])
            else:
                result.append(f"|{_escape_quoted_symbol(replacement)}|")
            index = end
            continue

        if ch in ("(", ")"):
            result.append(ch)
            index += 1
            continue

        token_end = index
        while token_end < length:
            current = smt_expr[token_end]
            if current.isspace() or current in ("(", ")", '"', "|", ";"):
                break
            token_end += 1

        token = smt_expr[index:token_end]
        if token:
            result.append(mapping.get(token, token))
        index = token_end

    return "".join(result)


def _consume_quoted_string(smt_expr: str, start: int) -> int:
    """文字列リテラルを次に同一行内で閉じるまで読み飛ばす。"""

    index = start + 1
    length = len(smt_expr)
    escaped = False
    while index < length:
        ch = smt_expr[index]
        index += 1
        if escaped:
            escaped = False
            continue
        if ch == "\\":
            escaped = True
            continue
        if ch == "\"":
            break
    return index


def _consume_quoted_symbol(smt_expr: str, start: int) -> tuple[int, str]:
    """シンボル名のクォート部（|...|）を読み飛ばし、内部文字列を返す。"""

    index = start + 1
    length = len(smt_expr)
    escaped = False
    symbol_chars: List[str] = []
    while index < length:
        ch = smt_expr[index]
        index += 1
        if escaped:
            symbol_chars.append(ch)
            escaped = False
            continue
        if ch == "\\":
            symbol_chars.append(ch)
            escaped = True
            continue
        if ch == "|":
            break
        symbol_chars.append(ch)
    return index, "".join(symbol_chars)


def _escape_quoted_symbol(name: str) -> str:
    """クォートシンボル内部で使う転義処理（既存文字列を保全）。"""

    return name.replace("\\\\", "\\\\\\\\").replace("|", "\\|")

# -*- coding: utf-8 -*-
"""型判定ヘルパー関数"""


def is_long_type(type_str: str) -> bool:
    """型名が long/ulong 系かどうかを判定"""
    type_lower = type_str.lower().strip()
    return (
        "long" in type_lower and
        "longlong" not in type_lower and
        "long long" not in type_lower
    )


def is_int_type(type_str: str) -> bool:
    """型名が int/uint 系かどうかを判定"""
    type_lower = type_str.lower().strip()
    return (
        "int" in type_lower and
        "long" not in type_lower and
        "short" not in type_lower and
        "pointer" not in type_lower and
        "*" not in type_lower
    )


def is_unsigned_type(type_str: str) -> bool:
    """型名が unsigned 系かどうかを判定"""
    type_lower = type_str.lower().strip()
    return (
        "unsigned" in type_lower or
        (type_lower.startswith("u") and not type_lower.startswith("undefined"))
    )


def get_type_name_from_param(param: dict) -> str:
    """パラメータ辞書から型名を取得"""
    dt = param.get("data_type_obj")
    if dt is not None and hasattr(dt, 'getName'):
        return str(dt)
    return param.get("data_type", "")
# -*- coding: utf-8 -*-
"""型判定ヘルパー関数"""

from scripts.function_tracer_pcode.core.signature import (
    get_data_type_display_name,
    get_declared_type_size_bytes,
    is_unsigned_data_type,
)


def is_long_type(type_ref) -> bool:
    """型が long/ulong 系かどうかを判定"""
    if isinstance(type_ref, dict):
        data_type_obj = type_ref.get("data_type_obj")
        type_name = type_ref.get("data_type")
    else:
        data_type_obj = None
        type_name = type_ref

    size = get_declared_type_size_bytes(data_type_obj, type_name)
    return bool(size == 8)


def is_int_type(type_ref) -> bool:
    """型が int/uint 系かどうかを判定"""
    if isinstance(type_ref, dict):
        data_type_obj = type_ref.get("data_type_obj")
        type_name = type_ref.get("data_type")
    else:
        data_type_obj = None
        type_name = type_ref

    size = get_declared_type_size_bytes(data_type_obj, type_name)
    return bool(size == 4)


def is_unsigned_type(type_ref) -> bool:
    """型が unsigned 系かどうかを判定"""
    if isinstance(type_ref, dict):
        return is_unsigned_data_type(
            type_ref.get("data_type_obj"),
            type_ref.get("data_type"),
        )
    return is_unsigned_data_type(None, type_ref)


def get_type_name_from_param(param: dict) -> str:
    """パラメータ辞書から表示用の型名を取得"""
    return get_data_type_display_name(
        param.get("data_type_obj"),
        param.get("data_type"),
    ) or ""

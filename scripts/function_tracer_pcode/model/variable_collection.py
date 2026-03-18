# -*- coding: utf-8 -*-
"""Variable collection helpers for Expression and Condition."""

from typing import Dict, Optional, Set

from .storage import StorageInfo


def collect_variables(expr) -> Set[str]:
    """式に含まれる変数名の集合を返す。"""
    variables: Set[str] = set()
    collect_variables_into(expr, variables)
    return variables


def contains_memory_access(expr) -> bool:
    """式木のどこかに MEMORY ノードが含まれるか判定する。"""
    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type == expr_kind.MEMORY:
        return True

    if expr_type in (expr_kind.BINARY_OP, expr_kind.UNARY_OP, expr_kind.CALL):
        return any(contains_memory_access(operand) for operand in expr.operands)

    if expr_type == expr_kind.PHI and expr.value:
        for cond, val in expr.value:
            if cond is not None and hasattr(cond, "expression"):
                if contains_memory_access(cond.expression):
                    return True
            if hasattr(val, "expr_type") and contains_memory_access(val):
                return True

    return False


def collect_variables_into(expr, variables: Set[str]) -> None:
    """式から再帰的に変数名を収集する。"""
    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type == expr_kind.PARAMETER:
        if expr.name:
            variables.add(expr.name)
        return

    if expr_type == expr_kind.VARIABLE:
        if expr.name:
            variables.add(expr.name)
        return

    if expr_type in (expr_kind.BINARY_OP, expr_kind.UNARY_OP):
        for operand in expr.operands:
            operand._collect_variables(variables)
        return

    if expr_type == expr_kind.CALL:
        for operand in expr.operands:
            operand._collect_variables(variables)
        return

    if expr_type == expr_kind.MEMORY:
        for operand in expr.operands:
            operand._collect_variables(variables)
        return

    if expr_type == expr_kind.PHI and expr.value:
        for cond, val in expr.value:
            if cond is not None and hasattr(cond, "_collect_variables"):
                cond._collect_variables(variables)
            if hasattr(val, "_collect_variables"):
                val._collect_variables(variables)


def collect_variables_with_storage(expr) -> Dict[str, Optional[StorageInfo]]:
    """式に含まれる変数名とストレージ情報を返す。"""
    variables: Dict[str, Optional[StorageInfo]] = {}
    collect_variables_with_storage_into(expr, variables)
    return variables


def collect_variables_with_storage_into(
    expr,
    variables: Dict[str, Optional[StorageInfo]],
) -> None:
    """式から再帰的に変数名とストレージ情報を収集する。"""
    expr_type = expr.expr_type
    expr_kind = expr_type.__class__

    if expr_type in (expr_kind.PARAMETER, expr_kind.VARIABLE):
        if expr.name and expr.name not in variables:
            variables[expr.name] = expr.storage_info
        return

    if expr_type in (expr_kind.BINARY_OP, expr_kind.UNARY_OP):
        for operand in expr.operands:
            operand._collect_variables_with_storage(variables)
        return

    if expr_type == expr_kind.CALL:
        for operand in expr.operands:
            operand._collect_variables_with_storage(variables)
        return

    if expr_type == expr_kind.MEMORY:
        for operand in expr.operands:
            operand._collect_variables_with_storage(variables)
        return

    if expr_type == expr_kind.PHI and expr.value:
        for cond, val in expr.value:
            if cond is not None and hasattr(cond, "_collect_variables_with_storage"):
                cond._collect_variables_with_storage(variables)
            if hasattr(val, "_collect_variables_with_storage"):
                val._collect_variables_with_storage(variables)

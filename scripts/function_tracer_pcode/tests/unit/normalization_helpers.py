# -*- coding: utf-8 -*-
"""Shared helpers for normalization-related unit tests."""

from typing import Optional, Tuple

from scripts.function_tracer_pcode.core import Expression, ExpressionType


def make_param(name: str, data_type: Optional[str] = None, size: int = 8) -> Expression:
    return Expression(
        ExpressionType.PARAMETER,
        name=name,
        size=size,
        data_type=data_type,
    )


def make_const(value: int, size: int = 8) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=size)


def make_neg(expr: Expression, size: int = 8) -> Expression:
    return Expression(
        ExpressionType.UNARY_OP,
        operator="INT_2COMP",
        operands=[expr],
        size=size,
    )


def make_modulo_expansion(
    dividend_name: str = "param_1",
    divisor_name: str = "param_2",
    data_type: Optional[str] = "long",
    size: int = 8,
) -> Tuple[Expression, Expression, Expression]:
    dividend = make_param(dividend_name, data_type=data_type, size=size)
    divisor = make_param(divisor_name, data_type=data_type, size=size)
    div_expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SDIV",
        operands=[dividend, divisor],
        size=size,
    )
    mult_expr = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_MULT",
        operands=[div_expr, divisor],
        size=size,
    )
    modulo_expansion = Expression(
        ExpressionType.BINARY_OP,
        operator="INT_SUB",
        operands=[dividend, mult_expr],
        size=size,
    )
    return dividend, divisor, modulo_expansion

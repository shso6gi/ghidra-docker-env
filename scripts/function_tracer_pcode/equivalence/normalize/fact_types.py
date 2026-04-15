# -*- coding: utf-8 -*-
"""Data models for normalization facts."""

from dataclasses import dataclass
from typing import Dict, Optional, Set

from ...model import Expression, StructuralKey, expression_key


@dataclass
class SignFacts:
    """符号・範囲に関する facts"""

    nonneg_vars: Set[str]
    pos_vars: Set[str]
    neg_vars: Set[str]
    nonzero_vars: Set[str]
    nonneg_exprs: Set[StructuralKey]
    pos_exprs: Set[StructuralKey]
    neg_exprs: Set[StructuralKey]
    nonzero_exprs: Set[StructuralKey]
    upper_bounds: Dict[str, int]

    def __init__(self):
        self.nonneg_vars = set()
        self.pos_vars = set()
        self.neg_vars = set()
        self.nonzero_vars = set()
        self.nonneg_exprs = set()
        self.pos_exprs = set()
        self.neg_exprs = set()
        self.nonzero_exprs = set()
        self.upper_bounds = {}

    def merge(self, other: "SignFacts") -> None:
        self.nonneg_vars.update(other.nonneg_vars)
        self.pos_vars.update(other.pos_vars)
        self.neg_vars.update(other.neg_vars)
        self.nonzero_vars.update(other.nonzero_vars)
        self.nonneg_exprs.update(other.nonneg_exprs)
        self.pos_exprs.update(other.pos_exprs)
        self.neg_exprs.update(other.neg_exprs)
        self.nonzero_exprs.update(other.nonzero_exprs)
        for var_name, bound in other.upper_bounds.items():
            current = self.upper_bounds.get(var_name)
            if current is None or bound < current:
                self.upper_bounds[var_name] = bound

    def is_nonneg(self, var_name: str) -> bool:
        return var_name in self.nonneg_vars or var_name in self.pos_vars

    def is_pos(self, var_name: str) -> bool:
        return var_name in self.pos_vars

    def is_neg(self, var_name: str) -> bool:
        return var_name in self.neg_vars

    def is_nonzero(self, var_name: str) -> bool:
        return (
            var_name in self.nonzero_vars
            or var_name in self.pos_vars
            or var_name in self.neg_vars
        )

    def is_expr_nonneg(self, expr: Expression) -> bool:
        key = expr_key(expr)
        return key in self.nonneg_exprs or key in self.pos_exprs

    def is_expr_pos(self, expr: Expression) -> bool:
        return expr_key(expr) in self.pos_exprs

    def is_expr_neg(self, expr: Expression) -> bool:
        return expr_key(expr) in self.neg_exprs

    def is_expr_nonzero(self, expr: Expression) -> bool:
        key = expr_key(expr)
        return (
            key in self.nonzero_exprs
            or key in self.pos_exprs
            or key in self.neg_exprs
        )

    def get_upper_bound(self, var_name: str) -> Optional[int]:
        return self.upper_bounds.get(var_name)


def expr_key(expr: Expression) -> StructuralKey:
    return expression_key(expr, normalize_commutative=True)

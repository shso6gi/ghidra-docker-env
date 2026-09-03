# -*- coding: utf-8 -*-
"""Pattern-driven normalization fact inference."""

from typing import Optional

from scripts.function_tracer_pcode.core import Expression
from scripts.function_tracer_pcode.semantics.normalize.fact_helpers import (
    get_var_name,
    is_and_operation,
    is_zero,
)
from scripts.function_tracer_pcode.semantics.normalize.fact_types import SignFacts


def extract_and_comparison_facts(
    operator: Optional[str],
    left: Expression,
    right: Expression,
    facts: SignFacts,
    debug: bool,
) -> None:
    """AND演算を含む比較から facts を推論"""
    if operator == "INT_SLESSEQUAL" and is_zero(left):
        and_expr = right
        if is_and_operation(and_expr) and len(and_expr.operands) >= 2:
            var1_name = get_var_name(and_expr.operands[0])
            var2_name = get_var_name(and_expr.operands[1])
            if var1_name and var2_name:
                if facts.is_neg(var1_name):
                    facts.nonneg_vars.add(var2_name)
                    if debug:
                        print(
                            f"[Facts] {var2_name} is nonneg "
                            f"(0 <= ({var1_name} & {var2_name}) and {var1_name} < 0)"
                        )
                if facts.is_neg(var2_name):
                    facts.nonneg_vars.add(var1_name)
                    if debug:
                        print(
                            f"[Facts] {var1_name} is nonneg "
                            f"(0 <= ({var1_name} & {var2_name}) and {var2_name} < 0)"
                        )
        return

    if operator == "INT_SLESS" and is_and_operation(left) and is_zero(right):
        operands = left.operands
        if len(operands) >= 2:
            var1_name = get_var_name(operands[0])
            var2_name = get_var_name(operands[1])
            if var1_name:
                facts.neg_vars.add(var1_name)
                facts.nonzero_vars.add(var1_name)
                if debug:
                    print(f"[Facts] {var1_name} is neg (({var1_name} & ...) < 0)")
            if var2_name:
                facts.neg_vars.add(var2_name)
                facts.nonzero_vars.add(var2_name)
                if debug:
                    print(f"[Facts] {var2_name} is neg ((... & {var2_name}) < 0)")

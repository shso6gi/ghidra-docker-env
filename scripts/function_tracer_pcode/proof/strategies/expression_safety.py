# -*- coding: utf-8 -*-
"""SMT-backed expression safety checks for pairwise equivalence."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.analysis.condition.normalizer import ConditionNormalizer
from scripts.function_tracer_pcode.core import Condition, ExpressionType
from scripts.function_tracer_pcode.core.render_smt import expression_contains_unsupported_smt_ops
from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
    _run_query_with_timeout,
)


@dataclass(frozen=True)
class ConditionBinding:
    """A condition together with the renderer needed for its symbol namespace."""

    condition: Condition
    render_fn: Optional[Callable]


class ExpressionSafetyChecker:
    """Checks whether an expression tree is solver-safe under guard conditions.

    This checker intentionally avoids ConditionSimplifier. Reachability-sensitive
    pruning is done with direct guard matching and SMT satisfiability only.
    """

    def __init__(
        self,
        *,
        solver_runner,
        debug_print,
        per_query_timeout: int,
        base_ctx: Optional[Dict[str, object]] = None,
    ) -> None:
        self.solver_runner = solver_runner
        self.debug_print = debug_print
        self.per_query_timeout = max(1, int(per_query_timeout or 1))
        self.base_ctx = dict(base_ctx or {})
        self._expr_cache: Dict[Tuple[int, Tuple[Tuple[int, int], ...], int], bool] = {}
        self._active_expr_checks: set[Tuple[int, Tuple[Tuple[int, int], ...], int]] = set()
        self._query_cache: Dict[Tuple[str, ...], Optional[bool]] = {}

    def case_contains_unresolved(
        self,
        case,
        *,
        own_render_fn=None,
        extra_conditions: Optional[Sequence[Condition]] = None,
        extra_render_fn=None,
        query_label: str = "case",
    ) -> bool:
        own_bindings = self._bind_conditions(case.conditions, own_render_fn)
        extra_bindings = self._bind_conditions(extra_conditions or [], extra_render_fn)

        value_expr = case.value_expr
        if (
            not self._is_void_return_placeholder(value_expr)
            and self.expression_contains_unresolved(
                value_expr,
                render_fn=own_render_fn,
                context_bindings=own_bindings + extra_bindings,
                query_label=f"{query_label}:value",
            )
        ):
            return True

        for index, condition in enumerate(case.conditions):
            context_bindings = extra_bindings + [
                ConditionBinding(other, own_render_fn)
                for offset, other in enumerate(case.conditions)
                if offset != index
            ]
            if self.expression_contains_unresolved(
                condition.expression,
                render_fn=own_render_fn,
                context_bindings=context_bindings,
                query_label=f"{query_label}:cond[{index}]",
            ):
                return True

        return False

    @staticmethod
    def _is_void_return_placeholder(expr) -> bool:
        if getattr(expr, "expr_type", None) != ExpressionType.UNKNOWN:
            return False
        return str(getattr(expr, "name", "") or "").lower() == "void"

    def value_contains_unresolved(
        self,
        case,
        *,
        own_render_fn=None,
        extra_conditions: Optional[Sequence[Condition]] = None,
        extra_render_fn=None,
        query_label: str = "value",
    ) -> bool:
        if self._is_void_return_placeholder(case.value_expr):
            return False
        context_bindings = self._bind_conditions(case.conditions, own_render_fn) + self._bind_conditions(
            extra_conditions or [],
            extra_render_fn,
        )
        return self.expression_contains_unresolved(
            case.value_expr,
            render_fn=own_render_fn,
            context_bindings=context_bindings,
            query_label=query_label,
        )

    def expression_contains_unresolved(
        self,
        expr,
        *,
        render_fn=None,
        context_bindings: Sequence[ConditionBinding],
        query_label: str,
    ) -> bool:
        if expr is None:
            return True

        cache_key = (
            id(expr),
            self._bindings_cache_key(context_bindings),
            id(render_fn),
        )
        cached = self._expr_cache.get(cache_key)
        if cached is not None:
            return cached
        if cache_key in self._active_expr_checks:
            self.debug_print(
                f"  Safety check recursion detected at {query_label}; treating as unresolved"
            )
            return True

        self._active_expr_checks.add(cache_key)
        try:
            result = self._expression_contains_unresolved_impl(
                expr,
                render_fn=render_fn,
                context_bindings=context_bindings,
                query_label=query_label,
            )
        finally:
            self._active_expr_checks.remove(cache_key)

        self._expr_cache[cache_key] = result
        return result

    def _expression_contains_unresolved_impl(
        self,
        expr,
        *,
        render_fn=None,
        context_bindings: Sequence[ConditionBinding],
        query_label: str,
    ) -> bool:
        expr_type = getattr(expr, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_type is None or expr_kind is None:
            return True

        if expr_type == expr_kind.UNKNOWN:
            return True
        if expression_contains_unsupported_smt_ops(expr):
            return True

        if expr_type == expr_kind.PHI and expr.value:
            return self._phi_contains_unresolved(
                expr,
                render_fn=render_fn,
                context_bindings=context_bindings,
                query_label=query_label,
            )

        for operand in getattr(expr, "operands", []) or []:
            if self.expression_contains_unresolved(
                operand,
                render_fn=render_fn,
                context_bindings=context_bindings,
                query_label=f"{query_label}:operand",
            ):
                return True

        return False

    def _phi_contains_unresolved(
        self,
        expr,
        *,
        render_fn,
        context_bindings: Sequence[ConditionBinding],
        query_label: str,
    ) -> bool:
        explicit_prefix: List[Condition] = []

        for branch_index, (branch_cond, branch_value) in enumerate(expr.value or []):
            status, branch_context = self._build_phi_branch_context(
                explicit_prefix,
                branch_cond,
                render_fn=render_fn,
                context_bindings=context_bindings,
                query_label=f"{query_label}:phi[{branch_index}]",
            )
            if branch_cond is not None:
                explicit_prefix.append(branch_cond)

            if status is False:
                continue
            if status is None:
                return True

            if self.expression_contains_unresolved(
                branch_value,
                render_fn=render_fn,
                context_bindings=branch_context,
                query_label=f"{query_label}:phi[{branch_index}]:value",
            ):
                return True

        return False

    def _build_phi_branch_context(
        self,
        explicit_prefix: Sequence[Condition],
        branch_cond: Optional[Condition],
        *,
        render_fn,
        context_bindings: Sequence[ConditionBinding],
        query_label: str,
    ) -> Tuple[Optional[bool], List[ConditionBinding]]:
        branch_context = list(context_bindings)

        for prefix_index, prior_cond in enumerate(explicit_prefix):
            negated = prior_cond.negate()
            status = self._condition_feasible_under_context(
                negated,
                render_fn=render_fn,
                context_bindings=branch_context,
                query_label=f"{query_label}:prior[{prefix_index}]",
            )
            if status is not True:
                return status, branch_context
            branch_context.append(ConditionBinding(negated, render_fn))

        if branch_cond is None:
            return True, branch_context

        status = self._condition_feasible_under_context(
            branch_cond,
            render_fn=render_fn,
            context_bindings=branch_context,
            query_label=f"{query_label}:guard",
        )
        if status is not True:
            return status, branch_context

        branch_context.append(ConditionBinding(branch_cond, render_fn))
        return True, branch_context

    def _condition_feasible_under_context(
        self,
        condition: Condition,
        *,
        render_fn,
        context_bindings: Sequence[ConditionBinding],
        query_label: str,
    ) -> Optional[bool]:
        direct = self._direct_condition_relation(
            condition,
            render_fn=render_fn,
            context_bindings=context_bindings,
        )
        if direct is not None:
            return direct

        if self.expression_contains_unresolved(
            condition.expression,
            render_fn=render_fn,
            context_bindings=context_bindings,
            query_label=f"{query_label}:expr",
        ):
            return None

        query_bindings = list(context_bindings) + [ConditionBinding(condition, render_fn)]
        return self._query_bindings_feasibility(
            query_bindings,
            query_label=query_label,
        )

    def _direct_condition_relation(
        self,
        condition: Condition,
        *,
        render_fn,
        context_bindings: Sequence[ConditionBinding],
    ) -> Optional[bool]:
        for binding in context_bindings:
            if binding.render_fn is not render_fn:
                continue
            if ConditionNormalizer.are_equivalent(condition, binding.condition):
                return True
            if ConditionNormalizer.are_contradictory(condition, binding.condition):
                return False
        return None

    def _query_bindings_feasibility(
        self,
        bindings: Sequence[ConditionBinding],
        *,
        query_label: str,
    ) -> Optional[bool]:
        rendered_assertions: List[str] = []
        for binding in bindings:
            rendered = self._render_condition(binding.condition, binding.render_fn)
            if rendered is None:
                return None
            rendered_assertions.append(rendered)

        cache_key = tuple(rendered_assertions)
        if cache_key in self._query_cache:
            return self._query_cache[cache_key]

        lines = [
            "; " + "=" * 60,
            f"; Expression safety reachability: {query_label}",
            "; " + "=" * 60,
            "",
            f"(set-logic {self.base_ctx.get('smt_logic', 'QF_BV')})",
            "",
        ]
        lines.extend(self.base_ctx.get("header_lines", []))
        for assertion in rendered_assertions:
            lines.append(f"(assert {assertion})")
        lines.append("(check-sat)")
        query = "\n".join(lines)

        result = _run_query_with_timeout(
            self.solver_runner,
            query,
            timeout=min(self.per_query_timeout, 5),
        )
        if result.is_equivalent is True:
            decision: Optional[bool] = False
        elif result.is_equivalent is False:
            decision = True
        else:
            decision = None
            self.debug_print(
                f"  Safety reachability query was inconclusive at {query_label}"
            )

        self._query_cache[cache_key] = decision
        return decision

    def _bind_conditions(
        self,
        conditions: Sequence[Condition],
        render_fn,
    ) -> List[ConditionBinding]:
        return [ConditionBinding(condition, render_fn) for condition in conditions]

    def _bindings_cache_key(
        self,
        bindings: Sequence[ConditionBinding],
    ) -> Tuple[Tuple[int, int], ...]:
        return tuple((id(binding.condition), id(binding.render_fn)) for binding in bindings)

    def _render_condition(
        self,
        condition: Condition,
        render_fn,
    ) -> Optional[str]:
        if condition is None:
            return None
        if render_fn is None:
            return condition.to_smt(float_mode="fp")
        try:
            rendered = render_fn(condition)
        except TypeError:
            rendered = render_fn(condition.to_smt(float_mode="fp"))

        if isinstance(rendered, str):
            return rendered

        to_smt = getattr(rendered, "to_smt", None)
        if callable(to_smt):
            return to_smt(float_mode="fp")
        return str(rendered)

"""Canonicalisation of traced expressions to location leaves."""

from __future__ import annotations

from typing import List, Optional
from scripts.function_tracer_pcode.core import (
    Expression,
    Condition,
    ExpressionType,
    CanonicalLocation,
)
from scripts.function_tracer_pcode.analysis.effects.summary import (
    _reduce_expression_under_conditions,
    canonicalize_expr_read_location,
    _expressions_equivalent,
    canonicalize_post_state_subexpressions,
    collapse_post_state_expr_to_canonical_read,
    collapse_post_state_expr_to_canonical_memory,
    expression_contains_complex_location_reads,
    expression_contains_post_state_reads,
    locations_match,
    memory_expression_for_location,
    normalize_post_state_expression,
    rewrite_loads_from_effects,
    rewrite_observed_loads_from_effects,
    should_attempt_root_post_state_collapse,
)
from scripts.function_tracer_pcode.analysis.memory_resolver import concretize_readonly_loads


class CanonicalizationMixin:
    """Canonicalisation of traced expressions to location leaves."""

    def _canonicalize_expression_to_location_leaf(
        self,
        expr: Expression,
        location: CanonicalLocation,
        conditions: List[Condition],
    ) -> Optional[Expression]:
        if not self.parameters:
            return expr

        candidate = memory_expression_for_location(location, self.parameters)
        if candidate is None:
            return expr

        expr_location = canonicalize_expr_read_location(expr, self.parameters)
        if expr_location is not None and locations_match(expr_location, location, conditions):
            return candidate
        if expr_location is not None and self.effect_summary is not None:
            expected = rewrite_loads_from_effects(
                candidate,
                conditions,
                self.effect_summary.effects,
                self.parameters,
            )
            reduced_expr = _reduce_expression_under_conditions(expr, conditions)
            reduced_expected = _reduce_expression_under_conditions(expected, conditions)
            if _expressions_equivalent(
                reduced_expr if reduced_expr is not None else expr,
                reduced_expected if reduced_expected is not None else expected,
            ):
                return candidate

        if expr.expr_type == ExpressionType.MEMORY and not expr.operands:
            return expr

        if expr.expr_type in (ExpressionType.BINARY_OP, ExpressionType.UNARY_OP, ExpressionType.CALL, ExpressionType.INTRINSIC, ExpressionType.MEMORY):
            rewritten_operands = [
                self._canonicalize_expression_to_location_leaf(operand, location, conditions)
                for operand in expr.operands
            ]
            if any(operand is None for operand in rewritten_operands):
                return expr
            if all(new is old for new, old in zip(rewritten_operands, expr.operands)):
                return expr
            return expr.clone_with(operands=rewritten_operands)

        if expr.expr_type == ExpressionType.PHI and expr.value:
            changed = False
            branches = []
            for cond, value in expr.value:
                combined_conditions = list(conditions)
                if cond is not None:
                    combined_conditions.append(cond)
                rewritten_value = self._canonicalize_expression_to_location_leaf(
                    value,
                    location,
                    combined_conditions,
                )
                branches.append((cond, rewritten_value))
                changed = changed or (rewritten_value is not value)
            if not changed:
                return expr
            rebuilt = Expression.phi(branches)
            rebuilt.size = expr.size
            return rebuilt

        return expr

    def _resolve_canonical_location_under_branch_expression(
        self,
        input_varnode,
        location,
        conditions: List[Condition],
        depth: int,
    ) -> Optional[Expression]:
        if self.effect_summary is None or not getattr(self.effect_summary, "effects", None):
            return None
        if not self.parameters:
            return None

        candidate = memory_expression_for_location(location, self.parameters)
        if candidate is None:
            return None

        try:
            branch_expr = self.tracer.trace_varnode(input_varnode, depth, use_cache=False)
        except Exception:
            branch_expr = None

        rewritten_branch = (
            self._canonicalize_expression_to_location_leaf(branch_expr, location, conditions)
            if branch_expr is not None
            else None
        )
        reduced = (
            _reduce_expression_under_conditions(rewritten_branch, conditions)
            if rewritten_branch is not None
            else None
        )
        resolved = reduced if reduced is not None else (rewritten_branch if rewritten_branch is not None else candidate)
        if self._expression_contains_unknown_or_call(resolved):
            return None
        if self._expression_contains_phi(resolved):
            if self.debug:
                self._debug_print(
                    "Canonical MULTIEQUAL location still contains PHI under current conditions",
                    depth,
                )
            return None
        return resolved

    def _trace_and_canonicalize_input_value(
        self,
        varnode,
        conditions: List[Condition],
        depth: int,
    ) -> Optional[Expression]:
        if self.effect_summary is None or not getattr(self.effect_summary, "effects", None):
            return None
        if not self.parameters:
            return None

        try:
            traced = self.tracer.trace_varnode(varnode, depth, use_cache=False)
        except Exception:
            return None

        canonicalized = self._canonicalize_traced_expression(traced, conditions)
        if (
            traced is not None
            and not expression_contains_post_state_reads(canonicalized)
        ):
            rewritten_observed = rewrite_observed_loads_from_effects(
                traced,
                conditions,
                self.effect_summary.effects,
                self.parameters,
            )
            if (
                rewritten_observed is not None
                and not _expressions_equivalent(rewritten_observed, traced)
                and self._expression_contains_phi(rewritten_observed)
            ):
                return None
        if (
            traced is not None
            and canonicalized is traced
            and traced.expr_type == ExpressionType.MEMORY
        ):
            pruned_leaf = collapse_post_state_expr_to_canonical_memory(
                traced,
                self.effect_summary.effects,
                self.parameters,
                return_conditions=conditions,
            )
            if pruned_leaf is not None:
                reduced = _reduce_expression_under_conditions(pruned_leaf, conditions)
                canonicalized = reduced if reduced is not None else pruned_leaf
                if self.debug and not _expressions_equivalent(traced, canonicalized):
                    self._debug_print(
                        "Canonicalized MULTIEQUAL branch memory leaf: "
                        f"{self._debug_expr_summary(traced)} -> {self._debug_expr_summary(canonicalized)}",
                        depth,
                    )
        if canonicalized is traced:
            return None
        if self._expression_contains_unknown_or_call(canonicalized):
            return None
        if self._expression_contains_phi(canonicalized):
            return None
        return canonicalized

    def _canonicalize_traced_expression(
        self,
        expr: Expression,
        conditions: List[Condition],
    ) -> Expression:
        if self.effect_summary is None or not getattr(self.effect_summary, "effects", None):
            return expr
        if not self.parameters:
            return expr
        rewritten_observed = rewrite_observed_loads_from_effects(
            expr,
            conditions,
            self.effect_summary.effects,
            self.parameters,
        )
        observed_changed = (
            rewritten_observed is not expr
            and not _expressions_equivalent(rewritten_observed, expr)
        )
        if observed_changed:
            if self.debug:
                self._debug_print(
                    "Observed-load rewrite resolved: "
                    f"{self._debug_expr_summary(expr)} -> {self._debug_expr_summary(rewritten_observed)}",
                    0,
                )
            rewritten_base = rewritten_observed if rewritten_observed is not None else expr
            if self._observed_load_rewrite_preserves_wrapper_shape(expr, rewritten_base):
                return rewritten_base
            rewrite_retains_phi = self._expression_contains_phi(rewritten_base)
            normalized = normalize_post_state_expression(
                rewritten_base,
                conditions,
                self.effect_summary.effects,
                self.parameters,
                symbolic_post_state=True,
            )
            normalized_original = normalize_post_state_expression(
                expr,
                conditions,
                self.effect_summary.effects,
                self.parameters,
                symbolic_post_state=True,
            )
            if (
                rewrite_retains_phi
                and normalized_original is not None
                and expression_contains_post_state_reads(normalized_original)
                and not self._expression_contains_phi(normalized_original)
            ):
                return normalized_original
            if normalized is not None and expression_contains_post_state_reads(normalized):
                if expr.expr_type != ExpressionType.MEMORY and normalized.expr_type == ExpressionType.MEMORY:
                    return expr
                return normalized
            if rewrite_retains_phi:
                if (
                    normalized_original is not None
                    and expression_contains_post_state_reads(normalized_original)
                ):
                    return normalized_original
                if (
                    normalized_original is not None
                    and normalized is not None
                    and self._expression_contains_phi(normalized)
                    and not self._expression_contains_phi(normalized_original)
                ):
                    return normalized_original
                if normalized is not None and self._expression_contains_phi(normalized):
                    return normalized
                return rewritten_base
            if (
                normalized_original is not None
                and expression_contains_post_state_reads(normalized_original)
            ):
                if expr.expr_type != ExpressionType.MEMORY and normalized_original.expr_type == ExpressionType.MEMORY:
                    return expr
                return normalized_original
            if (
                normalized is not None
                and not self._expression_contains_phi(normalized)
                and not _expressions_equivalent(normalized, expr)
            ):
                return normalized
            if (
                normalized is not None
                and normalized_original is not None
                and self._expression_contains_phi(normalized)
                and not self._expression_contains_phi(normalized_original)
            ):
                return normalized_original
            return normalized if normalized is not None else rewritten_base
        canonicalized = canonicalize_post_state_subexpressions(
            expr,
            conditions,
            self.effect_summary.effects,
            self.parameters,
            symbolic_post_state=True,
            allow_memory_leaf_collapse=(expr.expr_type == ExpressionType.MEMORY),
        )
        rewrite_target = canonicalized if canonicalized is not None else expr
        rewritten_post_state = (
            rewrite_loads_from_effects(
                rewrite_target,
                conditions,
                self.effect_summary.effects,
                self.parameters,
            )
            if (
                expression_contains_complex_location_reads(rewrite_target, self.parameters)
                and not expression_contains_post_state_reads(rewrite_target)
            )
            else rewrite_target
        )
        reduced = _reduce_expression_under_conditions(
            rewritten_post_state if rewritten_post_state is not None else (canonicalized if canonicalized is not None else expr),
            conditions,
        )
        resolved = reduced if reduced is not None else expr
        resolved = self._collapse_root_object_state_if_safe(resolved, conditions)
        if self.read_memory_value is not None and self.parameters:
            concretized = concretize_readonly_loads(
                resolved,
                conditions,
                self.parameters,
                self.read_memory_value,
                self.image_base,
                self.debug,
            )
            if concretized is not None:
                resolved = concretized
        return resolved

    def _observed_load_rewrite_preserves_wrapper_shape(
        self,
        original: Optional[Expression],
        rewritten: Optional[Expression],
    ) -> bool:
        if original is None or rewritten is None:
            return False
        if original.expr_type != rewritten.expr_type:
            return False
        if original.expr_type == ExpressionType.MEMORY:
            original_location = canonicalize_expr_read_location(original, self.parameters)
            rewritten_location = canonicalize_expr_read_location(rewritten, self.parameters)
            return (
                original_location is not None
                and rewritten_location is not None
                and original_location == rewritten_location
                and int(original.size or 0) == int(rewritten.size or 0)
            )
        if original.expr_type in {
            ExpressionType.CONSTANT,
            ExpressionType.PARAMETER,
            ExpressionType.VARIABLE,
            ExpressionType.UNKNOWN,
        }:
            return _expressions_equivalent(original, rewritten)
        if getattr(original, "operator", None) != getattr(rewritten, "operator", None):
            return False
        original_operands = list(getattr(original, "operands", []) or [])
        rewritten_operands = list(getattr(rewritten, "operands", []) or [])
        if len(original_operands) != len(rewritten_operands):
            return False
        return all(
            self._observed_load_rewrite_preserves_wrapper_shape(lhs, rhs)
            for lhs, rhs in zip(original_operands, rewritten_operands)
        )

    def _collapse_root_object_state_if_safe(
        self,
        expr: Expression,
        conditions: List[Condition],
    ) -> Expression:
        if not should_attempt_root_post_state_collapse(expr):
            return expr
        collapsed = collapse_post_state_expr_to_canonical_read(
            expr,
            self.effect_summary.effects,
            self.parameters,
            return_conditions=conditions,
            symbolic_post_state=True,
        )
        return collapsed if collapsed is not None else expr

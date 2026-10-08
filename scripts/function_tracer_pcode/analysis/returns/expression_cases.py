"""Object-centric expression case expansion, runtime guards and unresolved-value accounting."""

from __future__ import annotations

from typing import Any, Callable, List, Mapping, Optional, Sequence, Set, Tuple
from scripts.function_tracer_pcode.core.expression import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.structural import expression_key_safe, unidentified_identity
from scripts.function_tracer_pcode.analysis.returns._shared import (
    CanonicalLocation,
    ConditionNormalizer,
    ConditionSimplifier,
    EffectSummary,
    _expression_contains_observed_loads,
    _expression_location_ref,
    _expressions_equivalent,
    _expressions_equivalent_under_conditions,
    _iter_expression_nodes,
    _materialize_existing_effect_value_carrier,
    canonicalize_expr_read_location,
    eval_constant_raw,
    expression_contains_post_state_reads,
    lower_post_state_expression_for_smt,
    promote_observed_loads_to_post_state_reads,
    rewrite_observed_loads_from_effects,
)
from scripts.function_tracer_pcode.analysis.session import AnalysisSession


def clone_expression(expr: Expression) -> Expression:
    """Deep-copy an expression tree (pure; no facade state)."""
    return expr.clone_with(operands=[clone_expression(op) for op in expr.operands])


class ExpressionCaseService:
    """ReturnAnalyzer から切り出した式ケース展開・runtime guard・未解決値計数の collaborator。

    per-analysis state: ``AnalysisSession`` を返す ``session`` supplier を 1 本保持し、呼び出し時に
    ``self.session().parameters`` を読む（nested ``_analysis_context`` の push/pop に追随する）。
    ``contains_multiequal`` は自己再帰以外の内部呼び出しを持たない leaf であり、外部呼び出しは
    すべて facade ``ReturnAnalyzer._contains_multiequal`` を経由する（class-level patch seam）。
    """

    def __init__(
        self,
        *,
        session: Callable[[], "AnalysisSession"],
    ) -> None:
        self.session = session

    def expression_contains_equivalent_subexpr(
        self,
        expr: Optional[Expression],
        target: Optional[Expression],
    ) -> bool:
        if expr is None or target is None:
            return False
        if _expressions_equivalent(expr, target):
            return True
        for operand in getattr(expr, "operands", []) or []:
            if self.expression_contains_equivalent_subexpr(operand, target):
                return True
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None and self.expression_contains_equivalent_subexpr(cond.expression, target):
                    return True
                if self.expression_contains_equivalent_subexpr(value, target):
                    return True
        return False


    def clone_expression(self, expr: Expression) -> Expression:
        return clone_expression(expr)


    def collect_expression_object_keys(
        self,
        expr: Optional[Expression],
        out: Set[Tuple[object, ...]],
    ) -> None:
        if expr is None:
            return
        key = expression_key_safe(expr, include_memory_read_order=False)
        if key is not None:
            out.add(key)
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None:
                    self.collect_expression_object_keys(cond.expression, out)
                self.collect_expression_object_keys(value, out)
            return
        for operand in expr.operands or []:
            self.collect_expression_object_keys(operand, out)


    def expression_references_only_allowed_objects(
        self,
        expr: Optional[Expression],
        args: List[Expression],
    ) -> bool:
        if expr is None:
            return True

        allowed_subtrees: Set[Tuple[object, ...]] = set()
        for arg in args or []:
            self.collect_expression_object_keys(arg, allowed_subtrees)
        return self.expression_references_allowed_subtrees(expr, allowed_subtrees)


    def expression_references_allowed_subtrees(
        self,
        expr: Optional[Expression],
        allowed_subtrees: Set[Tuple[object, ...]],
    ) -> bool:
        if expr is None:
            return True
        expr_key = expression_key_safe(expr, include_memory_read_order=False)
        if expr_key in allowed_subtrees:
            return True

        if expr.expr_type == ExpressionType.UNKNOWN:
            runtime_ref = getattr(expr, "runtime_ref", None)
            return getattr(runtime_ref, "deferred_call_ref", None) is not None
        if expr.expr_type == ExpressionType.CALL:
            return False

        if expr.expr_type in {ExpressionType.CONSTANT, ExpressionType.LITERAL}:
            return True

        if expr.expr_type in {ExpressionType.PARAMETER, ExpressionType.VARIABLE}:
            if getattr(expr, "runtime_ref", None) is not None:
                return True
            return False

        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                if cond is not None and not self.expression_references_allowed_subtrees(
                    cond.expression,
                    allowed_subtrees,
                ):
                    return False
                if not self.expression_references_allowed_subtrees(value, allowed_subtrees):
                    return False
            return True

        if expr.expr_type == ExpressionType.MEMORY and not expr.operands:
            return getattr(expr, "runtime_ref", None) is not None

        for operand in expr.operands or []:
            if not self.expression_references_allowed_subtrees(operand, allowed_subtrees):
                return False
        return True


    def fold_constant_expression(
        self,
        expr: Optional[Expression],
        *,
        fallback_expr: Optional[Expression] = None,
    ) -> Optional[Expression]:
        if expr is None:
            return None
        evaluated = eval_constant_raw(expr)
        if evaluated is None:
            return expr
        raw_value, bits = evaluated
        template = fallback_expr or expr
        size_bytes = int(getattr(template, "size", 0) or 0)
        if size_bytes <= 0:
            size_bytes = max(1, (bits + 7) // 8)
        return Expression.constant(raw_value, size=size_bytes)


    def resolve_precise_object_state_value(
        self,
        value: Optional[Expression],
        conditions: List[Condition],
        effect_summary: EffectSummary,
    ) -> Optional[Expression]:
        if value is None:
            return None

        candidates: List[Expression] = [value]
        comparison_targets: List[Expression] = [value]
        if _expression_contains_observed_loads(value):
            observed_rewritten = rewrite_observed_loads_from_effects(
                value,
                conditions,
                effect_summary.effects,
                self.session().parameters,
            )
            if observed_rewritten is not None:
                candidates.append(observed_rewritten)
                comparison_targets.append(observed_rewritten)
            observed_post_state = promote_observed_loads_to_post_state_reads(
                value,
                conditions,
                effect_summary.effects,
                self.session().parameters,
                symbolic_post_state=True,
            )
            if observed_post_state is not None:
                comparison_targets.append(observed_post_state)
                lowered_observed_post_state = lower_post_state_expression_for_smt(
                    observed_post_state,
                    conditions,
                    effect_summary.effects,
                    self.session().parameters,
                )
                if lowered_observed_post_state is not None:
                    comparison_targets.append(lowered_observed_post_state)

        for candidate in candidates:
            materialized = _materialize_existing_effect_value_carrier(
                candidate,
                conditions,
                effect_summary.effects,
                self.session().parameters,
            )
            if materialized is None or materialized is candidate:
                continue
            if expression_contains_post_state_reads(materialized):
                continue
            if not any(
                _expressions_equivalent_under_conditions(
                    materialized,
                    comparison_target,
                    conditions,
                    self.session().parameters,
                )
                for comparison_target in comparison_targets
            ):
                continue
            return materialized

        return value


    def is_direct_location_carrier(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        if _expression_location_ref(expr) is not None:
            return True
        return expr.expr_type == ExpressionType.MEMORY and bool(expr.operands)


    def expression_has_nontrivial_location_wrapper(
        self,
        expr: Optional[Expression],
        location: CanonicalLocation,
    ) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            for index, operand in enumerate(expr.operands):
                operand_location = canonicalize_expr_read_location(
                    operand,
                    self.session().parameters,
                )
                if operand_location is None or operand_location != location:
                    continue
                other_operand = expr.operands[1 - index]
                if self.wrapper_preserves_collapsed_operand(
                    expr.operator,
                    other_operand,
                    kept_operand_index=index,
                ):
                    return False
                return True
            return False
        if expr.expr_type == ExpressionType.UNARY_OP:
            return True
        if expr.expr_type in {ExpressionType.CALL, ExpressionType.INTRINSIC}:
            return True
        return False


    def wrapper_preserves_collapsed_operand(
        self,
        operator: Optional[str],
        shared_operand: Optional[Expression],
        *,
        kept_operand_index: int,
    ) -> bool:
        if shared_operand is None or shared_operand.expr_type != ExpressionType.CONSTANT:
            return False

        try:
            shared_value = int(shared_operand.value)
        except Exception:
            return False

        bit_width = max(1, int(shared_operand.get_bit_width() or 0))
        mask = (1 << bit_width) - 1
        normalized = shared_value & mask

        if operator in {"INT_ADD", "INT_OR", "INT_XOR"}:
            return normalized == 0
        if operator == "INT_AND":
            return normalized == mask
        if operator in {"INT_LEFT", "INT_RIGHT", "INT_SRIGHT"}:
            return kept_operand_index == 0 and normalized == 0
        if operator == "INT_SUB":
            return kept_operand_index == 0 and normalized == 0
        return False


    def count_unresolved_value_nodes(self, expr: Optional[Expression]) -> int:
        if expr is None:
            return 1
        count = 1 if expr.expr_type == ExpressionType.UNKNOWN else 0
        if expr.expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                cond_expr = getattr(cond, "expression", None) if cond is not None else None
                if cond_expr is not None:
                    count += self.count_unresolved_value_nodes(cond_expr)
                count += self.count_unresolved_value_nodes(value)
            return count
        for operand in getattr(expr, "operands", []) or []:
            count += self.count_unresolved_value_nodes(operand)
        return count


    def count_object_centric_unknowns(self, expr: Optional[Expression]) -> int:
        count = 0
        for current in _iter_expression_nodes(expr):
            if getattr(current, "expr_type", None) != ExpressionType.UNKNOWN:
                continue
            runtime_ref = getattr(current, "runtime_ref", None)
            stable_key = getattr(runtime_ref, "stable_key", None)
            if callable(stable_key):
                try:
                    if stable_key() is not None:
                        count += 1
                except Exception:
                    continue
        return count


    def count_opaque_unknowns(self, expr: Optional[Expression]) -> int:
        count = 0
        for current in _iter_expression_nodes(expr):
            if getattr(current, "expr_type", None) != ExpressionType.UNKNOWN:
                continue
            runtime_ref = getattr(current, "runtime_ref", None)
            kind = getattr(runtime_ref, "kind", None)
            stable_key = getattr(runtime_ref, "stable_key", None)
            if kind == "opaque_unknown" or not callable(stable_key):
                count += 1
        return count


    def count_phi_nodes(self, expr: Optional[Expression]) -> int:
        count = 0
        for current in _iter_expression_nodes(expr):
            if getattr(current, "expr_type", None) == ExpressionType.PHI:
                count += 1
        return count


    def expand_object_centric_expression_cases(
        self,
        expr: Optional[Expression],
        base_conditions: List[Condition],
    ) -> List[Tuple[Expression, List[Condition]]]:
        if expr is None:
            return []

        simplified_base = ConditionSimplifier.simplify_conditions_object_centric(base_conditions)
        if ConditionSimplifier.object_centric_is_contradiction(simplified_base):
            return []
        direct_runtime_guards = self.direct_expression_runtime_guard_conditions(expr)
        if direct_runtime_guards:
            simplified_base = ConditionSimplifier.simplify_conditions_object_centric(
                list(simplified_base) + list(direct_runtime_guards)
            )
            if ConditionSimplifier.object_centric_is_contradiction(simplified_base):
                return []

        folded_expr = self.fold_constant_expression(
            expr,
            fallback_expr=expr,
        )
        if folded_expr is not None:
            expr = folded_expr

        boolean_cases = self.expand_boolean_expression_cases(
            expr,
            simplified_base,
        )
        if boolean_cases is not None:
            return self.deduplicate_expression_cases(boolean_cases)

        if expr.expr_type == ExpressionType.PHI and expr.value:
            expanded: List[Tuple[Expression, List[Condition]]] = []
            prior_guards: List[Condition] = []
            for cond, value in expr.value:
                combined_conditions = list(simplified_base)
                for prior in prior_guards:
                    combined_conditions.append(prior.negate())
                if cond is not None:
                    combined_conditions.append(cond)
                    prior_guards.append(cond)
                nested_conditions = ConditionSimplifier.simplify_conditions_object_centric(
                    combined_conditions
                )
                if ConditionSimplifier.object_centric_is_contradiction(nested_conditions):
                    continue
                expanded.extend(
                    self.expand_object_centric_expression_cases(
                        value,
                        nested_conditions,
                    )
                )
            return self.deduplicate_expression_cases(expanded)

        if expr.expr_type == ExpressionType.MEMORY and expr.operands:
            address_cases = self.expand_object_centric_expression_cases(
                expr.operands[0],
                simplified_base,
            )
            if not address_cases:
                return [(expr, simplified_base)]
            expanded = [
                (expr.clone_with(operands=[address]), case_conditions)
                for address, case_conditions in address_cases
                if not ConditionSimplifier.object_centric_is_contradiction(case_conditions)
            ]
            return self.deduplicate_expression_cases(expanded)

        if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
            operand_cases = self.expand_object_centric_expression_cases(
                expr.operands[0],
                simplified_base,
            )
            if not operand_cases:
                return [(expr, simplified_base)]
            expanded = []
            for operand, case_conditions in operand_cases:
                if ConditionSimplifier.object_centric_is_contradiction(case_conditions):
                    continue
                rebuilt = expr.clone_with(operands=[operand])
                rebuilt = self.fold_constant_expression(rebuilt, fallback_expr=expr)
                expanded.append((rebuilt, case_conditions))
            return self.deduplicate_expression_cases(expanded)

        if expr.expr_type == ExpressionType.BINARY_OP and len(expr.operands) == 2:
            left_cases = self.expand_object_centric_expression_cases(
                expr.operands[0],
                simplified_base,
            )
            right_cases = self.expand_object_centric_expression_cases(
                expr.operands[1],
                simplified_base,
            )
            if not left_cases:
                left_cases = [(expr.operands[0], simplified_base)]
            if not right_cases:
                right_cases = [(expr.operands[1], simplified_base)]

            expanded: List[Tuple[Expression, List[Condition]]] = []
            for left_value, left_conditions in left_cases:
                for right_value, right_conditions in right_cases:
                    combined_conditions = ConditionSimplifier.simplify_conditions_object_centric(
                        list(simplified_base) + list(left_conditions) + list(right_conditions)
                    )
                    if ConditionSimplifier.object_centric_is_contradiction(combined_conditions):
                        continue
                    rebuilt = expr.clone_with(operands=[left_value, right_value])
                    rebuilt = self.fold_constant_expression(rebuilt, fallback_expr=expr)
                    expanded.append(
                        (
                            rebuilt,
                            combined_conditions,
                        )
                    )
            return self.deduplicate_expression_cases(expanded)

        return [(expr, simplified_base)]


    def expand_boolean_expression_cases(
        self,
        expr: Optional[Expression],
        base_conditions: List[Condition],
    ) -> Optional[List[Tuple[Expression, List[Condition]]]]:
        if expr is None or not self.is_boolean_expression(expr):
            return None

        condition = Condition(expr, False)
        if ConditionSimplifier.object_centric_is_contradiction(
            list(base_conditions) + [condition.negate()]
        ):
            return [(Expression.constant(1, size=max(1, expr.size or 1)), base_conditions)]
        if ConditionSimplifier.object_centric_is_contradiction(
            list(base_conditions) + [condition]
        ):
            return [(Expression.constant(0, size=max(1, expr.size or 1)), base_conditions)]

        true_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            list(base_conditions) + [condition]
        )
        false_conditions = ConditionSimplifier.simplify_conditions_object_centric(
            list(base_conditions) + [condition.negate()]
        )

        cases: List[Tuple[Expression, List[Condition]]] = []
        if not ConditionSimplifier.object_centric_is_contradiction(true_conditions):
            cases.append((Expression.constant(1, size=max(1, expr.size or 1)), true_conditions))
        if not ConditionSimplifier.object_centric_is_contradiction(false_conditions):
            cases.append((Expression.constant(0, size=max(1, expr.size or 1)), false_conditions))
        if not cases:
            return []
        return cases


    def is_boolean_expression(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return False
        if expr.expr_type == ExpressionType.BINARY_OP:
            return expr.operator in {
                "INT_EQUAL",
                "INT_NOTEQUAL",
                "INT_LESS",
                "INT_LESSEQUAL",
                "INT_SLESS",
                "INT_SLESSEQUAL",
                "BOOL_AND",
                "BOOL_OR",
                "BOOL_XOR",
            }
        return expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE"


    def deduplicate_expression_cases(
        self,
        cases: List[Tuple[Expression, List[Condition]]],
    ) -> List[Tuple[Expression, List[Condition]]]:
        deduplicated: List[Tuple[Expression, List[Condition]]] = []
        for value, conditions in cases:
            simplified_conditions = ConditionSimplifier.simplify_conditions_object_centric(
                conditions
            )
            if ConditionSimplifier.object_centric_is_contradiction(simplified_conditions):
                continue
            duplicate = False
            for existing_value, existing_conditions in deduplicated:
                if (
                    _expressions_equivalent(existing_value, value)
                    and self.condition_lists_equivalent(existing_conditions, simplified_conditions)
                ):
                    duplicate = True
                    break
            if not duplicate:
                deduplicated.append((value, simplified_conditions))
        return deduplicated


    def condition_lists_equivalent(
        self,
        left: List[Condition],
        right: List[Condition],
    ) -> bool:
        if len(left) != len(right):
            return False
        unmatched = list(right)
        for left_condition in left:
            matched_index = next(
                (
                    index for index, right_condition in enumerate(unmatched)
                    if ConditionNormalizer.are_equivalent(left_condition, right_condition)
                ),
                None,
            )
            if matched_index is None:
                return False
            unmatched.pop(matched_index)
        return not unmatched


    def expression_runtime_guard_conditions(
        self,
        expr: Optional[Expression],
    ) -> List[Condition]:
        guards: List[Condition] = []
        seen: Set[tuple] = set()
        for node in self.iter_expression_nodes_for_unconditional_runtime_guards(expr):
            runtime_ref = getattr(node, "runtime_ref", None)
            for guard in self.runtime_ref_guard_conditions(runtime_ref):
                try:
                    key = guard.structural_key(budget=256)
                except Exception:
                    # key を作れない guard は何とも重複しない（`id()` は object の死後に再利用される。
                    # Issue #215 C-K5）
                    key = unidentified_identity("runtime_guard_key_failed")
                if key in seen:
                    continue
                seen.add(key)
                guards.append(guard)
        return guards


    def iter_expression_nodes_for_unconditional_runtime_guards(
        self,
        expr: Optional[Expression],
    ):
        if expr is None:
            return
        stack = [expr]
        while stack:
            current = stack.pop()
            if current is None:
                continue
            yield current
            if getattr(current, "expr_type", None) == ExpressionType.PHI:
                continue
            operands = getattr(current, "operands", None) or ()
            stack.extend(reversed([operand for operand in operands if operand is not None]))


    def direct_expression_runtime_guard_conditions(
        self,
        expr: Optional[Expression],
    ) -> List[Condition]:
        if expr is None:
            return []
        return self.runtime_ref_guard_conditions(getattr(expr, "runtime_ref", None))


    def runtime_ref_guard_conditions(
        self,
        runtime_ref,
    ) -> List[Condition]:
        guards: List[Condition] = []
        for owner in (
            runtime_ref,
            getattr(runtime_ref, "accumulator_proof", None),
            getattr(runtime_ref, "loop_summary", None),
        ):
            for guard in tuple(getattr(owner, "guard_constraints", ()) or ()):
                if isinstance(guard, Condition):
                    guards.append(guard)
        return guards


    def expression_contains_unresolved_value(self, expr: Optional[Expression]) -> bool:
        if expr is None:
            return True

        expr_type = getattr(expr, "expr_type", None)
        if expr_type is None:
            return True

        if expr_type == ExpressionType.UNKNOWN:
            return True

        if expr_type == ExpressionType.PHI and expr.value:
            for cond, value in expr.value:
                cond_expr = getattr(cond, "expression", None) if cond is not None else None
                if cond_expr is not None and self.expression_contains_unresolved_value(cond_expr):
                    return True
                if self.expression_contains_unresolved_value(value):
                    return True
            return False

        for operand in getattr(expr, "operands", []) or []:
            if self.expression_contains_unresolved_value(operand):
                return True

        return False


    def contains_multiequal(self, varnode, depth: int = 0) -> bool:
        """Return値のチェーン内にMULTIEQUALが含まれるかチェック"""
        if depth > 15:
            return False

        if varnode is None:
            return False

        def_op = varnode.getDef()
        if def_op is None:
            return False

        mnemonic = def_op.getMnemonic()

        if mnemonic == "MULTIEQUAL":
            return True

        for i in range(def_op.getNumInputs()):
            input_vn = def_op.getInput(i)
            if self.contains_multiequal(input_vn, depth + 1):
                return True

        return False


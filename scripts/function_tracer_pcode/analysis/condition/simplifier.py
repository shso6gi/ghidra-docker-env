# -*- coding: utf-8 -*-
"""条件の簡略化・矛盾検出モジュール（強化版）"""

from dataclasses import dataclass
from typing import Any, Iterable, List, Dict, Set, Optional, Tuple
from scripts.function_tracer_pcode.core import (
    Expression,
    Condition,
    ExpressionType,
    condition_key,
    key_contains_placeholder,
)
from scripts.function_tracer_pcode.core.semantic_freeze import publish
from scripts.function_tracer_pcode.core.stage_clock import stage_region
from scripts.function_tracer_pcode.core.structural import expression_provenance_key
from scripts.function_tracer_pcode.analysis.debug import summarize_expression, summarize_condition
from scripts.function_tracer_pcode.analysis.condition.bitvector import (
    eval_constant_raw,
    normalize_raw_value,
    to_signed_value,
)
from scripts.function_tracer_pcode.core.render_smt import (
    expression_contains_unsupported_smt_ops,
    expression_returns_bool,
    expression_smt_bit_width,
)
from scripts.function_tracer_pcode.analysis.condition.normalizer import ConditionNormalizer
from scripts.function_tracer_pcode.analysis.condition.scalar import (
    ScalarConstraint,
    extract_scalar_constraint,
)
from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
from scripts.function_tracer_pcode.analysis.condition.simplifier_cnf import CnfReasoningMixin
from scripts.function_tracer_pcode.analysis.condition.simplifier_scalar import ScalarBoundsMixin
from scripts.function_tracer_pcode.analysis.condition.simplifier_debug import SimplifierDebugMixin
from scripts.function_tracer_pcode.analysis.condition.simplifier_support import (
    ConditionRecoverableSimplificationError,
    _CONDITION_RECOVERABLE_ERRORS,
    BooleanAtom,
    BooleanLiteral,
    BooleanClause,
)


@dataclass(frozen=True)
class ConditionConstraintSet:
    """Object-centric normalized view over a list of ``Condition`` objects."""

    conditions: Tuple[Condition, ...]
    contradiction_indices: Tuple[int, ...]
    implied_norms: frozenset
    solver_backed: bool = False

    @classmethod
    def from_conditions(cls, conditions: Iterable[Condition]) -> "ConditionConstraintSet":
        normalized = ConditionSimplifier._normalize_condition_list(list(conditions or []))
        return cls(
            conditions=tuple(normalized["conditions"]),
            contradiction_indices=tuple(sorted(normalized["contradiction_indices"])),
            implied_norms=frozenset(normalized["implied_norms"]),
            solver_backed=bool(normalized.get("solver_backed", False)),
        )

    @property
    def is_contradictory(self) -> bool:
        return bool(self.contradiction_indices)

    def simplified_conditions(self) -> List[Condition]:
        return list(self.conditions)

    def signature(self):
        return ConditionNormalizer.conditions_signature(self.conditions)

    def implies_condition(self, condition: Condition) -> bool:
        return ConditionSimplifier._condition_is_implied(
            condition,
            list(self.conditions),
            set(self.implied_norms),
            prefer_solver=self.solver_backed,
        )

    def implies_all(self, conditions: Iterable[Condition]) -> bool:
        return all(self.implies_condition(condition) for condition in (conditions or []))

    def residual_against(self, context: Iterable[Condition]) -> List[Condition]:
        context_set = (
            context
            if isinstance(context, ConditionConstraintSet)
            else ConditionConstraintSet.from_conditions(context or [])
        )
        return [
            condition
            for condition in self.conditions
            if not context_set.implies_condition(condition)
        ]

    def overlaps_with(self, other: Iterable[Condition]) -> bool:
        other_set = (
            other
            if isinstance(other, ConditionConstraintSet)
            else ConditionConstraintSet.from_conditions(other or [])
        )
        if self.is_contradictory or other_set.is_contradictory:
            return False
        formula_overlap = ConditionSimplifier._formula_is_unsat(
            list(self.conditions) + list(other_set.conditions)
        )
        if formula_overlap is True:
            return False
        combined = list(self.conditions) + list(other_set.conditions)
        return not ConditionConstraintSet.from_conditions(combined).is_contradictory


def _published_conditions(conditions):
    """簡約が作り直した条件集合を公開して返す。

    `Condition` は構築と同時に凍結されるので、条件そのものに「まだ精緻化する」
    段階は無い。作り直したこの集合が完成形なので、**作ったここが公開点**。
    呼び手（式の描画側）は consumer なので、向こうで公開させない。
    """

    return [publish(condition) for condition in conditions]


class ConditionSimplifier(CnfReasoningMixin, ScalarBoundsMixin, SimplifierDebugMixin):
    """
    条件の簡略化と矛盾検出を行うクラス
    """
    
    # デバッグフラグ（外部から設定可能）
    DEBUG: bool = False
    _DEBUG_MESSAGE_LIMIT: int = 2000
    _debug_message_count: int = 0
    _debug_suppressed: bool = False
    _DEBUG_REPEAT_LIMIT: int = 8
    _debug_repeat_counts: Dict[Tuple[str, str], int] = {}
    _active_normalization_keys: Set[Tuple[object, ...]] = set()
    _active_reduction_keys: Set[Tuple[int, Tuple[int, ...]]] = set()
    _active_implied_keys: Set[Tuple[Tuple[int, ...], Tuple[int, ...]]] = set()
    _active_formula_implies_keys: Set[Tuple[object, ...]] = set()
    _formula_implies_cache: Dict[Tuple[object, ...], Optional[bool]] = {}
    _implied_cache: Dict[Tuple[Tuple[int, ...], int], Optional[bool]] = {}
    _FORMULA_IMPLIES_CACHE_LIMIT: int = 8192
    _IMPLIED_CACHE_LIMIT: int = 8192
    _CONTEXTUAL_REDUCTION_MAX_ITERATIONS: int = 4
    _CONTEXTUAL_REDUCTION_MAX_CONDITIONS: int = 64
    
    @classmethod
    def _conditions_structurally_equal(cls, left: Condition, right: Condition) -> bool:
        if left.negated != right.negated:
            return False
        if left.expression is right.expression:
            return True
        return left.expression.equals(right.expression)
    
    @classmethod
    def _normalize_raw_value(cls, value: int, bits: int) -> int:
        return normalize_raw_value(value, bits)

    @classmethod
    def _to_signed_value(cls, value: int, bits: int) -> int:
        return to_signed_value(value, bits)

    @classmethod
    def _eval_constant_raw(cls, expr: Expression) -> Optional[Tuple[int, int]]:
        return eval_constant_raw(expr)

    @classmethod
    def evaluate_condition_truth(cls, condition: Condition) -> Optional[bool]:
        expr = condition.expression
        negated = condition.negated

        while expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE":
            negated = not negated
            if expr.operands:
                expr = expr.operands[0]
            else:
                break

        evaluated = cls._eval_constant_raw(expr)
        if evaluated is None:
            return None

        raw_value, _bits = evaluated
        truth = raw_value != 0
        return not truth if negated else truth

    @classmethod
    def flatten_condition(cls, condition: Condition) -> List[Condition]:
        """
        条件を平坦化（論理演算を展開）
        
        Examples:
            not (A or B) -> [not A, not B]
            not (A and B) -> [not A] or [not B] (CNF化が必要なので、この場合は展開しない)
            A or B -> そのまま（単一の選言なので分解不可）
        
        Returns:
            展開された条件のリスト（AND結合）、または元の条件
        """
        expr = condition.expression
        negated = condition.negated
        
        cls._debug_condition_event("flatten_condition", Condition(expr, negated), 1)
        
        # 二重否定を解消
        while expr.expr_type == ExpressionType.UNARY_OP and expr.operator == "BOOL_NEGATE":
            negated = not negated
            if expr.operands:
                expr = expr.operands[0]
            else:
                break
        
        # not (A or B) -> (not A) and (not B)（ド・モルガンの法則）
        if negated and expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "BOOL_OR":
            cls._debug_print("  Detected: not (A or B)", 2)
            results = []
            for operand in expr.operands:
                # 各オペランドを否定
                results.append(Condition(operand, negated=True))
            cls._debug_print(f"  -> Flattened to {len(results)} conditions", 2)
            return results
        
        # not (A and B) -> (not A) or (not B)
        # これはCNF化が必要なので、ここでは扱わず元のまま返す
        if negated and expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "BOOL_AND":
            cls._debug_print("  Detected: not (A and B) - keeping as-is", 2)
            return [Condition(expr, negated=True)]
        
        # A and B -> [A, B]
        if not negated and expr.expr_type == ExpressionType.BINARY_OP and expr.operator == "BOOL_AND":
            cls._debug_print("  Detected: A and B", 2)
            results = []
            for operand in expr.operands:
                results.append(Condition(operand, negated=False))
            cls._debug_print(f"  -> Flattened to {len(results)} conditions", 2)
            return results
        
        # それ以外はそのまま
        cls._debug_print("  -> No flattening", 2)
        return [Condition(expr, negated=negated)]

    @classmethod
    def _collect_implied_condition_norms(cls, conditions: List[Condition]) -> Set[Tuple[str, str, str, bool]]:
        implied: Set[Tuple[str, str, str, bool]] = set()
        stack: List[Condition] = list(conditions or [])
        seen: Set[int] = set()

        while stack:
            condition = stack.pop()
            if condition is None:
                continue
            cond_id = id(condition)
            if cond_id in seen:
                continue
            seen.add(cond_id)

            try:
                normalized = ConditionNormalizer.normalize_for_contradiction(condition)
            except _CONDITION_RECOVERABLE_ERRORS:
                continue
            implied.add(normalized)

            try:
                expr = getattr(condition, "expression", None)
            except _CONDITION_RECOVERABLE_ERRORS:
                expr = None
            if (
                not getattr(condition, "negated", False)
                and expr is not None
                and getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP
                and getattr(expr, "operator", None) == "BOOL_AND"
            ):
                operands = list(getattr(expr, "operands", None) or [])
                for operand in operands[:2]:
                    if operand is not None:
                        try:
                            stack.append(Condition(operand, False))
                        except _CONDITION_RECOVERABLE_ERRORS:
                            continue

        clauses = []
        if not any(cls._condition_contains_solver_opaque_node(condition) for condition in (conditions or [])):
            try:
                clauses = cls._conditions_to_cnf_clauses(conditions)
            except _CONDITION_RECOVERABLE_ERRORS:
                clauses = None
        else:
            clauses = None
        if clauses is not None:
            for clause in clauses:
                if not clause or len(clause.literals) != 1:
                    continue
                atom = clause.literals[0]
                if not isinstance(atom, tuple) or len(atom) != 2:
                    continue
                lhs, polarity = atom
                if not isinstance(lhs, tuple) or len(lhs) != 3:
                    continue
                left, op, right = lhs
                if not isinstance(polarity, bool):
                    continue
                try:
                    implied.add((left, op, right, polarity))
                except _CONDITION_RECOVERABLE_ERRORS:
                    pass

        return implied

    @classmethod
    def _condition_contains_solver_opaque_node(cls, condition: Optional[Condition]) -> bool:
        expr = getattr(condition, "expression", None)
        if expr is None:
            return False
        pending = [expr]
        while pending:
            current = pending.pop()
            if current is None:
                continue
            expr_type = getattr(current, "expr_type", None)
            expr_kind = getattr(expr_type, "__class__", None)
            if expr_type is None or expr_kind is None:
                continue
            if expr_type in {expr_kind.UNKNOWN, expr_kind.CALL, expr_kind.PHI}:
                return True
            operands = list(getattr(current, "operands", None) or [])
            pending.extend(operand for operand in operands if operand is not None)
            if expr_type == expr_kind.PHI:
                for phi_condition, phi_value in getattr(current, "value", None) or []:
                    phi_expr = getattr(phi_condition, "expression", None) if phi_condition is not None else None
                    if phi_expr is not None:
                        pending.append(phi_expr)
                    if phi_value is not None:
                        pending.append(phi_value)
        return False

    @classmethod
    def _condition_is_implied(
        cls,
        condition: Condition,
        context_conditions: Optional[List[Condition]] = None,
        implied_conditions: Optional[Set[Tuple[str, str, str, bool]]] = None,
        prefer_solver: bool = False,
    ) -> bool:
        context_list = list(context_conditions or [])
        context_signature = tuple(cls._safe_condition_ids(context_list))
        condition_signature = cls._safe_condition_id(condition)
        cache_key = (context_signature, condition_signature)
        if cache_key in cls._active_implied_keys:
            return False
        if len(cache_key[0]) > cls._CONTEXTUAL_REDUCTION_MAX_CONDITIONS:
            return False
        if cache_key in cls._implied_cache:
            return bool(cls._implied_cache[cache_key])

        def _store_implied_cache(result: bool) -> bool:
            if len(cls._implied_cache) >= cls._IMPLIED_CACHE_LIMIT:
                cls._implied_cache.clear()
            cls._implied_cache[cache_key] = result
            return result

        cls._active_implied_keys.add(cache_key)
        try:
            formula_result: Optional[bool] = None
            if context_list:
                formula_result = cls._formula_implies(context_list, condition)
                if formula_result is True:
                    return _store_implied_cache(True)

            implied_conditions = implied_conditions or set()
            try:
                normalized = ConditionNormalizer.normalize_for_contradiction(condition)
            except _CONDITION_RECOVERABLE_ERRORS:
                normalized = None
            if normalized is not None and normalized in implied_conditions:
                return _store_implied_cache(True)

            scalar_fact = cls._extract_scalar_constraint(condition)
            if scalar_fact is not None and context_list:
                try:
                    scalar_implied = cls._scalar_constraint_is_implied(
                        scalar_fact,
                        list(context_list or []),
                    )
                except _CONDITION_RECOVERABLE_ERRORS:
                    scalar_implied = False
                if scalar_implied:
                    return _store_implied_cache(True)

            expr = getattr(condition, "expression", None)
            if (
                getattr(condition, "negated", False) is False
                and expr is not None
                and getattr(expr, "expr_type", None) == ExpressionType.BINARY_OP
                and getattr(expr, "operator", None) == "BOOL_AND"
            ):
                stack = [Condition(condition.expression.operands[0], False), Condition(condition.expression.operands[1], False)]
                visited_ids: Set[int] = set()
                while stack:
                    current = stack.pop()
                    if current is None:
                        continue
                    if id(current) in visited_ids:
                        continue
                    visited_ids.add(id(current))
                    current_expr = getattr(current, "expression", None)
                    if (
                        getattr(current, "negated", False) is False
                        and current_expr is not None
                        and getattr(current_expr, "expr_type", None) == ExpressionType.BINARY_OP
                        and getattr(current_expr, "operator", None) == "BOOL_AND"
                    ):
                        operands = list(getattr(current_expr, "operands", None) or [])
                        if len(operands) >= 2:
                            try:
                                left = Condition(operands[0], False)
                                right = Condition(operands[1], False)
                            except _CONDITION_RECOVERABLE_ERRORS:
                                return _store_implied_cache(False)
                            stack.append(left)
                            stack.append(right)
                        continue

                    try:
                        if ConditionNormalizer.normalize_for_contradiction(current) not in implied_conditions:
                            return _store_implied_cache(False)
                    except _CONDITION_RECOVERABLE_ERRORS:
                        return _store_implied_cache(False)
                return _store_implied_cache(True)

            implied_result = formula_result is True
            return _store_implied_cache(implied_result)
        finally:
            cls._active_implied_keys.discard(cache_key)

    @classmethod
    def _expression_can_collapse_to_boolean_constant(
        cls,
        expr: Expression,
    ) -> bool:
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

    @classmethod
    def _constant_expression_from_eval(
        cls,
        expr: Expression,
        raw_value: int,
        bits: int,
    ) -> Expression:
        size_bytes = int(getattr(expr, "size", 0) or 0)
        if size_bytes <= 0:
            size_bytes = max(1, (bits + 7) // 8)
        return Expression.constant(raw_value, size=size_bytes)

    @classmethod
    def _condition_is_contradicted(
        cls,
        condition: Condition,
        context_conditions: List[Condition],
        implied_conditions: Optional[Set[Tuple[str, str, str, bool]]] = None,
    ) -> bool:
        formula_result = cls._formula_is_unsat(list(context_conditions) + [condition])
        if formula_result is True:
            return True
        implied = implied_conditions if implied_conditions is not None else cls._collect_implied_condition_norms(context_conditions)
        if cls._condition_is_implied(condition.negate(), context_conditions, implied):
            return True
        return any(
            ConditionNormalizer.are_contradictory(condition, context)
            for context in context_conditions
        )

    @classmethod
    def _reduce_expression_under_conditions(
        cls,
        expr: Expression,
        conditions: List[Condition],
        *,
        _active_reduction_keys: Optional[Set[Tuple[int, Tuple[int, ...]]]] = None,
    ) -> Expression:
        if expr is None:
            return expr

        active_reduction_keys = set() if _active_reduction_keys is None else _active_reduction_keys
        reduction_key = cls._reduction_context_key(expr, conditions)
        if reduction_key in active_reduction_keys:
            if cls._debug_available():
                cls._debug_print(
                    "Detected circular reduction context; skip recursion for "
                    f"{cls._debug_expr_summary(expr)}",
                    2,
                )
            return expr
        active_reduction_keys.add(reduction_key)
        try:
            if cls._expression_can_collapse_to_boolean_constant(expr):
                try:
                    true_condition = Condition(expr, False)
                    if cls._formula_implies(conditions, true_condition):
                        return cls._constant_expression_from_eval(
                            expr,
                            1,
                            max(1, expr.get_bit_width()),
                        )
                    if cls._formula_implies(conditions, true_condition.negate()):
                        return cls._constant_expression_from_eval(
                            expr,
                            0,
                            max(1, expr.get_bit_width()),
                        )
                except _CONDITION_RECOVERABLE_ERRORS:
                    pass
            if expr.expr_type == ExpressionType.PHI and expr.value:
                implied = cls._collect_implied_condition_norms(conditions)

                for cond, value in expr.value:
                    if cond is None:
                        continue
                    if cls._condition_is_implied(cond, conditions, implied):
                        return cls._reduce_expression_under_conditions(
                            value,
                            list(conditions) + [cond],
                            _active_reduction_keys=active_reduction_keys,
                        )

                surviving = []
                for cond, value in expr.value:
                    if cond is not None and cls._condition_is_contradicted(cond, conditions, implied):
                        continue
                    combined = list(conditions)
                    if cond is not None:
                        combined.append(cond)
                    reduced_value = cls._reduce_expression_under_conditions(
                        value,
                        combined,
                        _active_reduction_keys=active_reduction_keys,
                    )
                    surviving.append((cond, reduced_value))

                if not surviving:
                    return expr
                if len(surviving) == 1:
                    return surviving[0][1]

                changed = len(surviving) != len(expr.value)
                if not changed:
                    for (orig_cond, orig_value), (new_cond, new_value) in zip(expr.value, surviving):
                        if orig_cond != new_cond or orig_value is not new_value:
                            changed = True
                            break
                if not changed:
                    return expr

                rebuilt = Expression.phi(surviving)
                rebuilt.size = expr.size
                return rebuilt

            if expr.expr_type in (
                ExpressionType.BINARY_OP,
                ExpressionType.UNARY_OP,
                ExpressionType.CALL,
                ExpressionType.INTRINSIC,
                ExpressionType.MEMORY,
            ):
                new_operands = [
                    cls._reduce_expression_under_conditions(
                        op,
                        conditions,
                        _active_reduction_keys=active_reduction_keys,
                    )
                    for op in expr.operands
                ]
                if all(new is old for new, old in zip(new_operands, expr.operands)):
                    rebuilt = expr
                else:
                    rebuilt = Expression(
                        expr_type=expr.expr_type,
                        value=expr.value,
                        operator=expr.operator,
                        operands=new_operands,
                        size=expr.size,
                        name=expr.name,
                        data_type=expr.data_type,
                        data_type_obj=getattr(expr, "data_type_obj", None),
                        storage_info=expr.storage_info,
                        read_order_key=expr.read_order_key,
                        runtime_ref=getattr(expr, "runtime_ref", None),
                        opcode=getattr(expr, "opcode", None),
                    )
                evaluated = cls._eval_constant_raw(rebuilt)
                if evaluated is not None:
                    raw_value, bits = evaluated
                    return cls._constant_expression_from_eval(rebuilt, raw_value, bits)
                return rebuilt

            return expr
        finally:
            active_reduction_keys.discard(reduction_key)

    @classmethod
    def _contextually_reduce_conditions(cls, conditions: List[Condition]) -> List[Condition]:
        current = list(conditions)
        for _ in range(cls._CONTEXTUAL_REDUCTION_MAX_ITERATIONS):
            reduced: List[Condition] = []
            changed = False
            for index, cond in enumerate(current):
                context = current[:index] + current[index + 1:]
                if any(
                    cls.are_equivalent_conditions(cond, other)
                    for other in context
                ):
                    reduced.append(cond)
                    continue
                reduced_expr = cls._reduce_expression_under_conditions(cond.expression, context)
                rewritten = Condition(reduced_expr, cond.negated)
                flattened = cls.flatten_condition(rewritten)
                reduced.extend(flattened)
                if len(flattened) != 1 or not cls._conditions_structurally_equal(flattened[0], cond):
                    changed = True
            if not changed:
                return current
            current = reduced
        return current

    @classmethod
    def _normalize_condition_list(
        cls,
        conditions: List[Condition],
    ) -> Dict[str, object]:
        if not conditions:
            return {
                "conditions": [],
                "contradiction_indices": set(),
                "implied_norms": set(),
                "solver_backed": False,
            }

        guard_key = cls._condition_object_cache_key(conditions)
        use_nonrecursive = (
            guard_key in cls._active_normalization_keys
            or cls._should_skip_contextual_reduction(conditions)
        )
        if use_nonrecursive:
            return cls._normalize_condition_list_nonrecursive(conditions)

        cls._active_normalization_keys.add(guard_key)
        try:
            flattened: List[Condition] = []
            contradiction_indices: Set[int] = set()

            for cond in conditions:
                truth_value = cls.evaluate_condition_truth(cond)
                if truth_value is True:
                    continue
                flattened.extend(cls.flatten_condition(cond))

            original_flattened = list(flattened)
            flattened = cls._contextually_reduce_conditions(flattened)
            if (
                len(original_flattened) > 1
                and any(cls.evaluate_condition_truth(cond) is False for cond in flattened)
            ):
                preserve_direct_witness = False
                for i in range(len(original_flattened)):
                    for j in range(i + 1, len(original_flattened)):
                        if ConditionNormalizer.are_contradictory(
                            original_flattened[i],
                            original_flattened[j],
                        ):
                            preserve_direct_witness = True
                            break
                    if preserve_direct_witness:
                        break
                if preserve_direct_witness:
                    flattened = original_flattened

            unique_conditions: List[Condition] = []
            unique_canonicals: Dict[Tuple[str, str, str, bool], int] = {}
            comparison_map: Dict[Tuple[str, str, str], Dict[bool, int]] = {}
            fallback_conditions: List[Tuple[int, Condition]] = []
            scalar_groups: Dict[Tuple[str, int], Dict[str, Any]] = {}
            unsupported_indices: List[int] = []

            for cond in flattened:
                truth_value = cls.evaluate_condition_truth(cond)
                if truth_value is True:
                    continue

                try:
                    canonical = ConditionNormalizer.normalize_for_contradiction(cond)
                except _CONDITION_RECOVERABLE_ERRORS:
                    canonical = None
                if canonical is None:
                    current_index = len(unique_conditions)
                    unique_conditions.append(cond)
                    unsupported_indices.append(current_index)
                    continue
                if canonical in unique_canonicals:
                    continue

                current_index = len(unique_conditions)
                unique_canonicals[canonical] = current_index
                unique_conditions.append(cond)

                if truth_value is False:
                    contradiction_indices.add(current_index)

                left, op, right, polarity = canonical
                if op:
                    polarity_map = comparison_map.setdefault((left, op, right), {})
                    prior_index = polarity_map.get(polarity)
                    if prior_index is not None:
                        contradiction_indices.update({prior_index, current_index})
                    opposite_index = polarity_map.get(not polarity)
                    if opposite_index is not None:
                        contradiction_indices.update({opposite_index, current_index})
                    polarity_map[polarity] = current_index
                else:
                    fallback_conditions.append((current_index, cond))

                fact = cls._extract_scalar_constraint(cond)
                if fact is None:
                    unsupported_indices.append(current_index)
                    continue

                group = scalar_groups.setdefault(
                    fact.key,
                    {
                        "eq": {},
                        "ne": {},
                        "lower": {False: None, True: None},
                        "upper": {False: None, True: None},
                    },
                )

                if fact.kind == "eq":
                    existing = group["eq"].get(fact.raw_value)
                    if existing is not None:
                        contradiction_indices.update({existing, current_index})
                    group["eq"].setdefault(fact.raw_value, current_index)
                elif fact.kind == "ne":
                    existing = group["ne"].get(fact.raw_value)
                    if existing is not None:
                        contradiction_indices.update({existing, current_index})
                    group["ne"].setdefault(fact.raw_value, current_index)
                elif fact.kind == "lower":
                    signed = fact.signed
                    if fact.value is None or fact.inclusive is None:
                        continue
                    candidate = (fact.value, fact.inclusive, current_index)
                    current = group["lower"][signed]
                    group["lower"][signed] = cls._select_stronger_lower(current, candidate)
                elif fact.kind == "upper":
                    signed = fact.signed
                    if fact.value is None or fact.inclusive is None:
                        continue
                    candidate = (fact.value, fact.inclusive, current_index)
                    current = group["upper"][signed]
                    group["upper"][signed] = cls._select_stronger_upper(current, candidate)

            for i in range(len(fallback_conditions)):
                for j in range(i + 1, len(fallback_conditions)):
                    index_i, cond_i = fallback_conditions[i]
                    index_j, cond_j = fallback_conditions[j]
                    if ConditionNormalizer.are_contradictory(cond_i, cond_j):
                        contradiction_indices.update({index_i, index_j})

            formula_unsat = cls._formula_is_unsat(unique_conditions)
            if formula_unsat:
                contradiction_indices.update(range(len(unique_conditions)))

            keep_indices: Set[int] = set(unsupported_indices)

            for key, group in scalar_groups.items():
                bits = key[1]
                eq_items = sorted(group["eq"].items(), key=lambda item: item[1])
                ne_items = sorted(group["ne"].items(), key=lambda item: item[1])

                if len(eq_items) > 1:
                    contradiction_indices.update(index for _raw, index in eq_items)
                if eq_items:
                    eq_raw, eq_index = eq_items[0]
                    keep_indices.add(eq_index)

                    ne_index = group["ne"].get(eq_raw)
                    if ne_index is not None:
                        contradiction_indices.update({eq_index, ne_index})
                        keep_indices.add(ne_index)

                    for signed in (False, True):
                        lower = group["lower"][signed]
                        upper = group["upper"][signed]
                        eq_value = cls._to_signed_value(eq_raw, bits) if signed else eq_raw
                        if lower is not None:
                            lower_effective = cls._effective_lower_bound(lower[0], lower[1], signed, bits)
                            if eq_value < lower_effective:
                                contradiction_indices.update({eq_index, lower[2]})
                                keep_indices.add(lower[2])
                        if upper is not None:
                            upper_effective = cls._effective_upper_bound(upper[0], upper[1], signed, bits)
                            if eq_value > upper_effective:
                                contradiction_indices.update({eq_index, upper[2]})
                                keep_indices.add(upper[2])
                    continue

                keep_indices.update(index for _raw, index in ne_items)
                for signed in (False, True):
                    lower = group["lower"][signed]
                    upper = group["upper"][signed]
                    if lower is not None:
                        keep_indices.add(lower[2])
                    if upper is not None:
                        keep_indices.add(upper[2])

                    if lower is None or upper is None:
                        continue

                    if cls._bounds_contradict(
                        (lower[0], lower[1]),
                        (upper[0], upper[1]),
                        signed,
                        bits,
                    ):
                        contradiction_indices.update({lower[2], upper[2]})
                        continue

                    lower_effective = cls._effective_lower_bound(lower[0], lower[1], signed, bits)
                    upper_effective = cls._effective_upper_bound(upper[0], upper[1], signed, bits)
                    if lower_effective == upper_effective:
                        singleton_raw = cls._normalize_raw_value(lower_effective, bits)
                        ne_index = group["ne"].get(singleton_raw)
                        if ne_index is not None:
                            contradiction_indices.update({lower[2], upper[2], ne_index})
                            keep_indices.add(ne_index)

            selected_indices = keep_indices
            if contradiction_indices:
                selected_indices = set(unsupported_indices) | set(contradiction_indices)
                if not selected_indices:
                    selected_indices = set(contradiction_indices)

            selected = [
                condition
                for index, condition in enumerate(unique_conditions)
                if index in selected_indices
            ]
            solver_backed = cls._can_use_solver_reasoning(selected)

            return {
                "conditions": selected,
                "contradiction_indices": contradiction_indices,
                "implied_norms": cls._collect_implied_condition_norms(selected),
                "solver_backed": solver_backed,
            }
        finally:
            cls._active_normalization_keys.discard(guard_key)

    @classmethod
    def _normalize_condition_list_nonrecursive(
        cls,
        conditions: List[Condition],
    ) -> Dict[str, object]:
        flattened: List[Condition] = []
        contradiction_indices: Set[int] = set()
        seen_keys: Set[Tuple[object, ...]] = set()
        selected: List[Condition] = []

        for cond in conditions:
            truth_value = cls.evaluate_condition_truth(cond)
            if truth_value is True:
                continue
            for flat in cls.flatten_condition(cond):
                flat_truth = cls.evaluate_condition_truth(flat)
                if flat_truth is True:
                    continue
                flattened.append(flat)

        for cond in flattened:
            try:
                key = cls._safe_condition_cache_key([cond], budget=128)[0]
            except _CONDITION_RECOVERABLE_ERRORS:
                key = ("unsafe", cls._safe_condition_id(cond))
            if key in seen_keys:
                continue
            seen_keys.add(key)
            if cls.evaluate_condition_truth(cond) is False:
                contradiction_indices.add(len(selected))
            for other_index, other in enumerate(selected):
                if ConditionNormalizer.are_contradictory(cond, other):
                    contradiction_indices.update({other_index, len(selected)})
                    break
            selected.append(cond)

        solver_backed = cls._can_use_solver_reasoning(selected)
        if not contradiction_indices and solver_backed:
            solver_unsat = cls._formula_is_unsat(selected)
            if solver_unsat is True:
                contradiction_indices.add(0)

        return {
            "conditions": selected,
            "contradiction_indices": contradiction_indices,
            "implied_norms": cls._collect_implied_condition_norms(selected),
            "solver_backed": solver_backed,
        }

    @classmethod
    def _condition_object_cache_key(
        cls,
        conditions: Iterable[Condition],
    ) -> Tuple[int, ...]:
        keys = [cls._safe_condition_id(cond) for cond in (conditions or []) if cond is not None]
        keys.sort()
        return tuple(keys)

    @classmethod
    def _should_skip_contextual_reduction(
        cls,
        conditions: Iterable[Condition],
    ) -> bool:
        for cond in conditions or []:
            if cond is None:
                continue
            try:
                key = condition_key(cond, budget=96)
            except _CONDITION_RECOVERABLE_ERRORS:
                key = ("unsafe", cls._safe_condition_id(cond))
            if key_contains_placeholder(key):
                return True
            metrics = cls._condition_metrics(cond)
            if metrics["has_unknown"] and metrics["phi_depth"] > 0 and metrics["node_count"] > 24:
                return True
            if metrics["phi_depth"] > 1 and metrics["node_count"] > 32:
                return True
            if metrics["phi_depth"] > 0 and metrics["node_count"] > 96:
                return True
        return False

    @classmethod
    def _is_solver_compatible_condition(cls, condition: Condition) -> bool:
        expr = getattr(condition, "expression", None)
        if expr is None:
            return False

        if not expression_returns_bool(expr):
            expr_bits = expression_smt_bit_width(expr)
            if expr_bits > 1:
                return False

        if expression_contains_unsupported_smt_ops(expr, allow_call=True):
            return False

        metrics = cls._condition_metrics(condition)
        if metrics["phi_depth"] > 3:
            return False
        if metrics["node_count"] > 192:
            return False
        if metrics["has_unknown"] and metrics["node_count"] > 96:
            return False
        return True

    @classmethod
    def _should_use_solver_reasoning(
        cls,
        conditions: Iterable[Condition],
    ) -> bool:
        condition_list = [cond for cond in (conditions or []) if cond is not None]
        if not condition_list:
            return False
        if len(condition_list) > 32:
            return False
        if not ConditionSMTOracle.is_available():
            return False
        total_nodes = 0
        for condition in condition_list:
            if not cls._is_solver_compatible_condition(condition):
                return False
            total_nodes += cls._condition_metrics(condition).get("node_count", 0)
        if total_nodes > 640:
            return False
        return cls._can_use_solver_reasoning(condition_list)

    @classmethod
    def _can_use_solver_reasoning(
        cls,
        conditions: Iterable[Condition],
    ) -> bool:
        if not list(conditions or []):
            return False
        return ConditionSMTOracle.is_available()

    @classmethod
    def _condition_metrics(
        cls,
        condition: Condition,
    ) -> Dict[str, int | bool]:
        node_count = 0
        phi_depth = 0
        has_unknown = False
        active: Set[int] = set()
        pending: List[Tuple[Expression, int]] = [(condition.expression, 0)]
        while pending:
            expr, depth = pending.pop()
            if expr is None:
                continue
            expr_id = id(expr)
            if expr_id in active:
                continue
            active.add(expr_id)
            node_count += 1
            if expr.expr_type == ExpressionType.UNKNOWN:
                has_unknown = True
            if expr.expr_type == ExpressionType.PHI:
                phi_depth = max(phi_depth, depth + 1)
                for branch_cond, branch_value in reversed(expr.value or []):
                    if branch_value is not None:
                        pending.append((branch_value, depth + 1))
                    cond_expr = getattr(branch_cond, "expression", None) if branch_cond is not None else None
                    if cond_expr is not None:
                        pending.append((cond_expr, depth + 1))
                continue
            for operand in reversed(list(getattr(expr, "operands", None) or [])):
                pending.append((operand, depth))
        return {
            "node_count": node_count,
            "phi_depth": phi_depth,
            "has_unknown": has_unknown,
        }

    @classmethod
    def build_constraint_set(
        cls,
        conditions: Iterable[Condition],
    ) -> ConditionConstraintSet:
        return ConditionConstraintSet.from_conditions(list(conditions or []))

    @classmethod
    def build_object_centric_condition_basis(
        cls,
        conditions: Iterable[Condition],
    ) -> List[Condition]:
        flattened: List[Condition] = []
        for condition in list(conditions or []):
            if condition is None:
                continue
            for flat in cls.flatten_condition(condition):
                truth_value = cls.evaluate_condition_truth(flat)
                if truth_value is True:
                    continue
                if any(flat.equals(existing) for existing in flattened):
                    continue
                flattened.append(flat)

        ranked_conditions = sorted(
            enumerate(flattened),
            key=lambda item: (cls._condition_complexity_key(item[1]), item[0]),
        )

        basis: List[Condition] = []
        for _index, condition in ranked_conditions:
            if cls._condition_is_implied(
                condition,
                list(basis),
                prefer_solver=True,
            ):
                continue
            basis.append(condition)
        return basis

    @classmethod
    def _condition_complexity_key(
        cls,
        condition: Condition,
    ) -> Tuple[int, int, int]:
        expr = getattr(condition, "expression", None)

        def expr_cost(node: Optional[Expression]) -> Tuple[int, int]:
            if node is None:
                return (0, 0)
            bool_ops = 1 if (
                node.expr_type == ExpressionType.BINARY_OP
                and str(getattr(node, "operator", "")).startswith("BOOL_")
            ) else 0
            child_nodes = list(getattr(node, "operands", []) or [])
            total_nodes = 1
            for child in child_nodes:
                child_bool_ops, child_total_nodes = expr_cost(child)
                bool_ops += child_bool_ops
                total_nodes += child_total_nodes
            return bool_ops, total_nodes

        bool_ops, total_nodes = expr_cost(expr)
        negation_penalty = 1 if getattr(condition, "negated", False) else 0
        return (bool_ops + negation_penalty, total_nodes, negation_penalty)

    @classmethod
    def object_centric_conditions_signature(
        cls,
        conditions: Iterable[Condition],
    ) -> Tuple[object, ...]:
        signature = []
        for condition in cls.build_object_centric_condition_basis(conditions):
            try:
                signature.append(condition.structural_key(budget=256))
            except _CONDITION_RECOVERABLE_ERRORS:
                signature.append(("unsafe", cls._safe_condition_id(condition)))
        signature.sort(key=repr)
        return tuple(signature)

    @classmethod
    def object_centric_is_contradiction(
        cls,
        conditions: Iterable[Condition],
    ) -> bool:
        basis = cls.build_object_centric_condition_basis(conditions)
        if not basis:
            return False

        try:
            unsat_cache_key = ("raw-unsat", cls._safe_condition_cache_key(basis))
        except _CONDITION_RECOVERABLE_ERRORS:
            unsat_cache_key = ("raw-unsat",)
        solver_unsat = ConditionSMTOracle.conjunction_is_unsat(
            basis,
            cache_key=unsat_cache_key,
        )
        if solver_unsat is not None:
            return solver_unsat

        normalized = cls._normalize_condition_list_nonrecursive(basis)
        return bool(normalized["contradiction_indices"])

    @classmethod
    def simplify_conditions_object_centric(
        cls,
        conditions: Iterable[Condition],
    ) -> List[Condition]:
        # Issue #124: 条件簡約の公開 entry（同名 region に合算される）。
        with stage_region("condition_simplify"):
            return _published_conditions(
                cls.build_object_centric_condition_basis(conditions)
            )

    @classmethod
    def subtract_implied_conditions(
        cls,
        conditions: Iterable[Condition],
        context_conditions: Iterable[Condition],
    ) -> List[Condition]:
        context_set = cls.build_constraint_set(list(context_conditions or []))
        return [
            condition
            for condition in cls.build_constraint_set(list(conditions or [])).conditions
            if not context_set.implies_condition(condition)
        ]
    
    @classmethod
    def is_contradiction(cls, conditions: List[Condition]) -> bool:
        """条件リストが矛盾しているかチェックする。"""
        return cls.build_constraint_set(conditions).is_contradictory
    
    @classmethod
    def are_equivalent_conditions(cls, cond1: Condition, cond2: Condition) -> bool:
        """
        2つの条件が等価かチェック（normalizer に委譲）
        """
        return ConditionNormalizer.are_equivalent(cond1, cond2)
    
    @classmethod
    def simplify_conditions(cls, conditions: List[Condition]) -> List[Condition]:
        """条件リストを object-centric に簡略化する。"""
        # Issue #124: 条件簡約の公開 entry（同名 region に合算される）。
        with stage_region("condition_simplify"):
            return _published_conditions(
                cls.build_constraint_set(conditions).simplified_conditions()
            )

    @classmethod
    def reduce_expression_under_conditions(
        cls,
        expr: Expression,
        conditions: Iterable[Condition],
    ) -> Expression:
        """式を条件文脈の下で object-centric に簡約する。"""
        return cls._reduce_expression_under_conditions(expr, list(conditions or []))
    
    @classmethod
    def get_simplified_condition_string(cls, condition: Condition) -> str:
        """
        条件を簡略化した文字列で返す（normalizer に委譲）
        """
        return ConditionNormalizer.get_simplified_string(condition)

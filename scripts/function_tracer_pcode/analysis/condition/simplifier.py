# -*- coding: utf-8 -*-
"""条件の簡略化・矛盾検出モジュール（強化版）"""

from dataclasses import dataclass
from typing import Any, Iterable, List, Dict, Set, Optional, Tuple
from ...model import Expression, Condition, ExpressionType, condition_key, key_contains_placeholder
from ...model.structural import expression_provenance_key
from ..debug import summarize_expression, summarize_condition
from .bitvector import eval_constant_raw, normalize_raw_value, to_signed_value
from ...model.render_smt import (
    expression_contains_unsupported_smt_ops,
    expression_returns_bool,
    expression_smt_bit_width,
)
from .normalizer import ConditionNormalizer
from .scalar import ScalarConstraint, extract_scalar_constraint
from .smt_oracle import ConditionSMTOracle


BooleanAtom = Tuple[object, str, object]
BooleanLiteral = Tuple[BooleanAtom, bool]
_CONDITION_RECOVERABLE_ERRORS = (
    AttributeError,
    IndexError,
    KeyError,
    TypeError,
    ValueError,
    RecursionError,
)


class ConditionRecoverableSimplificationError(ValueError):
    """Raised when condition simplification cannot prove a fact soundly."""


@dataclass(frozen=True)
class BooleanClause:
    """CNF 句の object-centric 表現。"""

    literals: Tuple[BooleanLiteral, ...]
    source_indices: Tuple[int, ...]


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


class ConditionSimplifier:
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
    def reset_debug_state(cls) -> None:
        cls._debug_message_count = 0
        cls._debug_suppressed = False
        cls._debug_repeat_counts.clear()

    @classmethod
    def _debug_available(cls) -> bool:
        return cls.DEBUG and cls._debug_message_count < cls._DEBUG_MESSAGE_LIMIT

    @classmethod
    def _debug_print(cls, msg: str, indent: int = 0):
        if not cls.DEBUG:
            return
        if cls._debug_message_count >= cls._DEBUG_MESSAGE_LIMIT:
            if not cls._debug_suppressed:
                prefix = "  " * indent
                print(
                    f"{prefix}[CondSimplifier] debug output suppressed after "
                    f"{cls._DEBUG_MESSAGE_LIMIT} messages"
                )
                cls._debug_suppressed = True
            return
        cls._debug_message_count += 1
        prefix = "  " * indent
        print(f"{prefix}[CondSimplifier] {msg}")

    @classmethod
    def _debug_expr_summary(cls, expr: Optional[Expression], max_depth: int = 4) -> str:
        if not cls._debug_available():
            return "<debug-suppressed>"
        return summarize_expression(expr, max_depth=max_depth)

    @classmethod
    def _debug_condition_summary(cls, condition: Optional[Condition], max_depth: int = 4) -> str:
        if not cls._debug_available():
            return "<debug-suppressed>"
        return summarize_condition(condition, max_depth=max_depth)

    @classmethod
    def _safe_condition_id(cls, condition: Optional[Condition]) -> int:
        try:
            if condition is None:
                return 0
            return hash(condition.structural_key(budget=96))
        except _CONDITION_RECOVERABLE_ERRORS:
            try:
                expr = getattr(condition, "expression", None)
                return hash((bool(getattr(condition, "negated", False)), id(expr)))
            except _CONDITION_RECOVERABLE_ERRORS:
                return 0

    @classmethod
    def _safe_condition_ids(cls, conditions: Iterable[Condition]) -> Tuple[int, ...]:
        keys: List[int] = []
        for condition in (conditions or []):
            keys.append(cls._safe_condition_id(condition))
        return tuple(sorted(keys))

    @classmethod
    def _safe_condition_cache_key(cls, conditions: Iterable[Condition], budget: int = 96) -> Tuple[object, ...]:
        keys: List[object] = []
        for condition in (conditions or []):
            try:
                key = condition_key(condition, budget=budget)
                if key_contains_placeholder(key):
                    key = ("placeholder", cls._safe_condition_id(condition))
            except _CONDITION_RECOVERABLE_ERRORS:
                key = ("unsafe", cls._safe_condition_id(condition))
            keys.append(key)
        keys.sort(key=repr)
        return tuple(keys)

    @classmethod
    def _debug_condition_event(
        cls,
        event: str,
        condition: Condition,
        indent: int = 0,
    ) -> None:
        if not cls._debug_available():
            return

        summary = cls._debug_condition_summary(condition)
        key = (event, summary)
        count = cls._debug_repeat_counts.get(key, 0) + 1
        if len(cls._debug_repeat_counts) > 4096:
            cls._debug_repeat_counts.clear()
        cls._debug_repeat_counts[key] = count

        if count <= cls._DEBUG_REPEAT_LIMIT:
            cls._debug_print(f"{event}: {summary}", indent)
        elif count == cls._DEBUG_REPEAT_LIMIT + 1:
            cls._debug_print(
                f"{event}: {summary} (further repeats suppressed)",
                indent,
            )

    @classmethod
    def _literal_from_condition(
        cls,
        condition: Condition,
    ) -> BooleanLiteral:
        left, op, right, polarity = ConditionNormalizer.normalize_for_contradiction(condition)
        return ((left, op, right), polarity)

    @classmethod
    def _merge_clause_literals(
        cls,
        literals: Iterable[BooleanLiteral],
    ) -> Optional[Tuple[BooleanLiteral, ...]]:
        seen: Dict[BooleanAtom, bool] = {}
        merged: List[BooleanLiteral] = []
        for atom, polarity in literals:
            prior = seen.get(atom)
            if prior is not None:
                if prior != polarity:
                    return None
                continue
            seen[atom] = polarity
            merged.append((atom, polarity))
        merged.sort(key=cls._literal_sort_key)
        return tuple(merged)

    @classmethod
    def _literal_sort_key(cls, literal: BooleanLiteral) -> Tuple[object, ...]:
        atom, polarity = literal
        try:
            left, op, right = atom
            return (
                cls._total_sort_key(cls._atom_term_sort_key(left)),
                str(op),
                cls._total_sort_key(cls._atom_term_sort_key(right)),
                bool(polarity),
            )
        except _CONDITION_RECOVERABLE_ERRORS as exc:
            raise ConditionRecoverableSimplificationError(
                "could not build deterministic CNF literal sort key"
            ) from exc

    @classmethod
    def _atom_term_sort_key(cls, term: object) -> Tuple[object, ...]:
        if isinstance(term, Expression):
            return ("expr", expression_provenance_key(term, safe_budget=256))
        if term is None:
            return ("none",)
        if isinstance(term, (str, int, bool, float)):
            return (type(term).__name__, term)
        if isinstance(term, tuple):
            return ("tuple", tuple(cls._atom_term_sort_key(item) for item in term))
        if isinstance(term, list):
            return ("list", tuple(cls._atom_term_sort_key(item) for item in term))
        if isinstance(term, dict):
            entries = [
                (
                    cls._atom_term_sort_key(key),
                    cls._atom_term_sort_key(value),
                )
                for key, value in term.items()
            ]
            return (
                "dict",
                tuple(
                    sorted(
                        entries,
                        key=lambda item: cls._total_sort_key(item),
                    )
                ),
            )
        structural_key = getattr(term, "structural_key", None)
        if callable(structural_key):
            return ("structural", structural_key())
        stable_key = getattr(term, "stable_key", None)
        if callable(stable_key):
            return ("stable", stable_key())
        raise ConditionRecoverableSimplificationError(
            f"no stable sort key for {type(term).__module__}.{type(term).__qualname__}"
        )

    @classmethod
    def _total_sort_key(cls, value: object) -> Tuple[object, ...]:
        if value is None:
            return ("none",)
        if isinstance(value, bool):
            return ("bool", value)
        if isinstance(value, int):
            return ("int", value)
        if isinstance(value, float):
            return ("float", repr(value))
        if isinstance(value, str):
            return ("str", value)
        if isinstance(value, tuple):
            return ("tuple", tuple(cls._total_sort_key(item) for item in value))
        if isinstance(value, list):
            return ("list", tuple(cls._total_sort_key(item) for item in value))
        if isinstance(value, dict):
            return (
                "dict",
                tuple(
                    sorted(
                        (
                            cls._total_sort_key(key),
                            cls._total_sort_key(item),
                        )
                        for key, item in value.items()
                    )
                ),
            )
        raise ConditionRecoverableSimplificationError(
            f"non-total CNF sort key component: {type(value).__module__}.{type(value).__qualname__}"
        )

    @classmethod
    def _false_clause(
        cls,
        source_index: int,
    ) -> BooleanClause:
        return BooleanClause(tuple(), (source_index,))

    @classmethod
    def _is_false_clause_set(
        cls,
        clauses: List[BooleanClause],
    ) -> bool:
        return len(clauses) == 1 and not clauses[0].literals

    @classmethod
    def _cnf_or(
        cls,
        left: List[BooleanClause],
        right: List[BooleanClause],
        *,
        max_clauses: int,
    ) -> Optional[List[BooleanClause]]:
        if not left or not right:
            return []
        if cls._is_false_clause_set(left):
            return list(right)
        if cls._is_false_clause_set(right):
            return list(left)

        result: List[BooleanClause] = []
        for left_clause in left:
            for right_clause in right:
                merged_literals = cls._merge_clause_literals(
                    list(left_clause.literals) + list(right_clause.literals)
                )
                if merged_literals is None:
                    continue
                merged_sources = tuple(
                    sorted(set(left_clause.source_indices) | set(right_clause.source_indices))
                )
                result.append(BooleanClause(merged_literals, merged_sources))
                if len(result) > max_clauses:
                    return None

        return result

    @classmethod
    def _expression_to_cnf_clauses(
        cls,
        expr: Expression,
        negated: bool,
        source_index: int,
        *,
        max_clauses: int,
    ) -> Optional[List[BooleanClause]]:
        current = expr
        current_negated = negated
        while (
            current is not None
            and current.expr_type == ExpressionType.UNARY_OP
            and current.operator == "BOOL_NEGATE"
        ):
            current_negated = not current_negated
            if not current.operands:
                break
            current = current.operands[0]

        if current is None:
            return [cls._false_clause(source_index)] if current_negated else []

        truth_value = cls.evaluate_condition_truth(Condition(current, current_negated))
        if truth_value is True:
            return []
        if truth_value is False:
            return [cls._false_clause(source_index)]

        if (
            current.expr_type == ExpressionType.BINARY_OP
            and current.operator in {"BOOL_AND", "BOOL_OR"}
            and len(current.operands) == 2
        ):
            left_expr, right_expr = current.operands
            if current.operator == "BOOL_AND":
                if not current_negated:
                    left = cls._expression_to_cnf_clauses(
                        left_expr,
                        False,
                        source_index,
                        max_clauses=max_clauses,
                    )
                    right = cls._expression_to_cnf_clauses(
                        right_expr,
                        False,
                        source_index,
                        max_clauses=max_clauses,
                    )
                    if left is None or right is None:
                        return None
                    combined = list(left) + list(right)
                    return combined if len(combined) <= max_clauses else None
                left = cls._expression_to_cnf_clauses(
                    left_expr,
                    True,
                    source_index,
                    max_clauses=max_clauses,
                )
                right = cls._expression_to_cnf_clauses(
                    right_expr,
                    True,
                    source_index,
                    max_clauses=max_clauses,
                )
                if left is None or right is None:
                    return None
                return cls._cnf_or(left, right, max_clauses=max_clauses)

            if not current_negated:
                left = cls._expression_to_cnf_clauses(
                    left_expr,
                    False,
                    source_index,
                    max_clauses=max_clauses,
                )
                right = cls._expression_to_cnf_clauses(
                    right_expr,
                    False,
                    source_index,
                    max_clauses=max_clauses,
                )
                if left is None or right is None:
                    return None
                return cls._cnf_or(left, right, max_clauses=max_clauses)

            left = cls._expression_to_cnf_clauses(
                left_expr,
                True,
                source_index,
                max_clauses=max_clauses,
            )
            right = cls._expression_to_cnf_clauses(
                right_expr,
                True,
                source_index,
                max_clauses=max_clauses,
            )
            if left is None or right is None:
                return None
            combined = list(left) + list(right)
            return combined if len(combined) <= max_clauses else None

        literal = cls._literal_from_condition(Condition(current, current_negated))
        return [BooleanClause((literal,), (source_index,))]

    @classmethod
    def _conditions_to_cnf_clauses(
        cls,
        conditions: Iterable[Condition],
        *,
        max_clauses: int = 64,
    ) -> Optional[List[BooleanClause]]:
        result: List[BooleanClause] = []
        for index, condition in enumerate(list(conditions or [])):
            clauses = cls._expression_to_cnf_clauses(
                condition.expression,
                condition.negated,
                index,
                max_clauses=max_clauses,
            )
            if clauses is None:
                return None
            result.extend(clauses)
            if len(result) > max_clauses:
                return None
        return result

    @classmethod
    def _simplify_clauses_with_assignment(
        cls,
        clauses: List[Tuple[BooleanLiteral, ...]],
        assignments: Dict[BooleanAtom, bool],
    ) -> Optional[List[Tuple[BooleanLiteral, ...]]]:
        simplified: List[Tuple[BooleanLiteral, ...]] = []
        for clause in clauses:
            unresolved: List[BooleanLiteral] = []
            clause_satisfied = False
            for atom, polarity in clause:
                assigned = assignments.get(atom)
                if assigned is None:
                    unresolved.append((atom, polarity))
                    continue
                if assigned == polarity:
                    clause_satisfied = True
                    break
            if clause_satisfied:
                continue
            if not unresolved:
                return None
            unresolved_tuple = tuple(sorted(set(unresolved), key=cls._literal_sort_key))
            if unresolved_tuple not in simplified:
                simplified.append(unresolved_tuple)
        return simplified

    @classmethod
    def _clauses_are_satisfiable(
        cls,
        clauses: List[Tuple[BooleanLiteral, ...]],
        assignments: Optional[Dict[BooleanAtom, bool]] = None,
    ) -> bool:
        current_assignments = dict(assignments or {})
        current_clauses = list(clauses)

        while True:
            reduced = cls._simplify_clauses_with_assignment(current_clauses, current_assignments)
            if reduced is None:
                return False
            if not reduced:
                return True

            unit_literals = [clause[0] for clause in reduced if len(clause) == 1]
            if not unit_literals:
                current_clauses = reduced
                break

            changed = False
            for atom, polarity in unit_literals:
                existing = current_assignments.get(atom)
                if existing is not None:
                    if existing != polarity:
                        return False
                    continue
                current_assignments[atom] = polarity
                changed = True
            current_clauses = reduced
            if not changed:
                break

        branch_literal = min(current_clauses, key=len)[0]
        branch_atom, branch_polarity = branch_literal

        true_assignments = dict(current_assignments)
        true_assignments[branch_atom] = branch_polarity
        if cls._clauses_are_satisfiable(current_clauses, true_assignments):
            return True

        false_assignments = dict(current_assignments)
        false_assignments[branch_atom] = not branch_polarity
        return cls._clauses_are_satisfiable(current_clauses, false_assignments)

    @classmethod
    def _formula_is_unsat(
        cls,
        conditions: Iterable[Condition],
    ) -> Optional[bool]:
        condition_list = list(conditions or [])
        if cls._should_use_solver_reasoning(condition_list):
            try:
                cache_key = ("unsat", cls._safe_condition_cache_key(condition_list))
            except _CONDITION_RECOVERABLE_ERRORS:
                cache_key = ("unsat",)
            try:
                solver_result = ConditionSMTOracle.conjunction_is_unsat(
                    condition_list,
                    cache_key=cache_key,
                )
            except _CONDITION_RECOVERABLE_ERRORS:
                solver_result = None
            if solver_result is not None:
                return solver_result
        try:
            clauses = cls._conditions_to_cnf_clauses(condition_list)
            if clauses is None:
                return None
            clause_literals = [clause.literals for clause in clauses]
            return not cls._clauses_are_satisfiable(clause_literals)
        except _CONDITION_RECOVERABLE_ERRORS:
            return None

    @classmethod
    def _formula_implies(
        cls,
        context_conditions: Iterable[Condition],
        condition: Condition,
    ) -> Optional[bool]:
        try:
            context_list = list(context_conditions or [])
            negated_condition = condition.negate()
            implication_conditions = context_list + [negated_condition]
            cache_key = (
                "implies",
                cls._safe_condition_cache_key(context_list),
                cls._safe_condition_cache_key([negated_condition]),
            )
        except _CONDITION_RECOVERABLE_ERRORS:
            return None

        if cache_key in cls._formula_implies_cache:
            return cls._formula_implies_cache[cache_key]
        if cache_key in cls._active_formula_implies_keys:
            cls._debug_print(
                "Skipping recursive _formula_implies guard hit",
                0,
            )
            return None
        cls._active_formula_implies_keys.add(cache_key)
        result: Optional[bool]

        try:
            try:
                use_solver = cls._should_use_solver_reasoning(implication_conditions)
            except _CONDITION_RECOVERABLE_ERRORS:
                use_solver = False

            if use_solver:
                try:
                    solver_result = ConditionSMTOracle.conjunction_is_unsat(
                        implication_conditions,
                        cache_key=cache_key,
                    )
                except _CONDITION_RECOVERABLE_ERRORS:
                    solver_result = None
                if solver_result is not None:
                    result = solver_result
                else:
                    try:
                        clauses = cls._conditions_to_cnf_clauses(implication_conditions)
                    except _CONDITION_RECOVERABLE_ERRORS:
                        clauses = None
                    if clauses is None:
                        result = None
                    else:
                        try:
                            clause_literals = [clause.literals for clause in clauses]
                            result = not cls._clauses_are_satisfiable(clause_literals)
                        except _CONDITION_RECOVERABLE_ERRORS:
                            result = None
            else:
                try:
                    clauses = cls._conditions_to_cnf_clauses(implication_conditions)
                except _CONDITION_RECOVERABLE_ERRORS:
                    clauses = None
                if clauses is None:
                    result = None
                else:
                    try:
                        clause_literals = [clause.literals for clause in clauses]
                        result = not cls._clauses_are_satisfiable(clause_literals)
                    except _CONDITION_RECOVERABLE_ERRORS:
                        result = None
        finally:
            cls._active_formula_implies_keys.discard(cache_key)

        if len(cls._formula_implies_cache) >= cls._FORMULA_IMPLIES_CACHE_LIMIT:
            cls._formula_implies_cache.clear()
        cls._formula_implies_cache[cache_key] = result
        return result

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
    def _extract_scalar_constraint(
        cls,
        condition: Condition,
    ) -> Optional[ScalarConstraint]:
        return extract_scalar_constraint(condition)

    @classmethod
    def extract_scalar_constraint(
        cls,
        condition: Condition,
    ) -> Optional[ScalarConstraint]:
        """条件を単一のスカラ制約として解釈する公開ラッパー"""
        return cls._extract_scalar_constraint(condition)

    @classmethod
    def _effective_lower_bound(
        cls,
        value: int,
        inclusive: bool,
        signed: bool,
        bits: int,
    ) -> int:
        minimum = -(1 << (bits - 1)) if signed else 0
        return max(minimum, value if inclusive else value + 1)

    @classmethod
    def _effective_upper_bound(
        cls,
        value: int,
        inclusive: bool,
        signed: bool,
        bits: int,
    ) -> int:
        maximum = (1 << (bits - 1)) - 1 if signed else (1 << bits) - 1
        return min(maximum, value if inclusive else value - 1)

    @classmethod
    def _bounds_contradict(
        cls,
        lower: Optional[Tuple[int, bool]],
        upper: Optional[Tuple[int, bool]],
        signed: bool,
        bits: int,
    ) -> bool:
        if lower is None or upper is None:
            return False
        lower_effective = cls._effective_lower_bound(lower[0], lower[1], signed, bits)
        upper_effective = cls._effective_upper_bound(upper[0], upper[1], signed, bits)
        return lower_effective > upper_effective

    @classmethod
    def _select_stronger_lower(
        cls,
        current: Optional[Tuple[int, bool, int]],
        candidate: Tuple[int, bool, int],
    ) -> Tuple[int, bool, int]:
        if current is None:
            return candidate

        current_effective = cls._effective_lower_bound(
            current[0],
            current[1],
            signed=False,
            bits=128,
        )
        candidate_effective = cls._effective_lower_bound(
            candidate[0],
            candidate[1],
            signed=False,
            bits=128,
        )

        if candidate_effective > current_effective:
            return candidate
        if candidate_effective < current_effective:
            return current
        return candidate if candidate[2] < current[2] else current

    @classmethod
    def _select_stronger_upper(
        cls,
        current: Optional[Tuple[int, bool, int]],
        candidate: Tuple[int, bool, int],
    ) -> Tuple[int, bool, int]:
        if current is None:
            return candidate

        current_effective = cls._effective_upper_bound(
            current[0],
            current[1],
            signed=False,
            bits=128,
        )
        candidate_effective = cls._effective_upper_bound(
            candidate[0],
            candidate[1],
            signed=False,
            bits=128,
        )

        if candidate_effective < current_effective:
            return candidate
        if candidate_effective > current_effective:
            return current
        return candidate if candidate[2] < current[2] else current

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
    def _collect_scalar_context(
        cls,
        conditions: List[Condition],
    ) -> Dict[Tuple[object, int], Dict[str, object]]:
        context: Dict[Tuple[object, int], Dict[str, object]] = {}
        for index, cond in enumerate(conditions or []):
            if cond is None:
                continue

            try:
                fact = cls._extract_scalar_constraint(cond)
            except _CONDITION_RECOVERABLE_ERRORS:
                continue

            if fact is None:
                continue
            entry = context.setdefault(
                fact.key,
                {
                    "eq_raw_values": set(),
                    "ne_raw_values": set(),
                    "lower": {False: None, True: None},
                    "upper": {False: None, True: None},
                },
            )

            if fact.kind == "eq":
                entry["eq_raw_values"].add(fact.raw_value)
                continue
            if fact.kind == "ne":
                entry["ne_raw_values"].add(fact.raw_value)
                continue
            if fact.value is None or fact.inclusive is None:
                continue

            candidate = (fact.value, fact.inclusive, index)
            if fact.kind == "lower":
                entry["lower"][fact.signed] = cls._select_stronger_lower(
                    entry["lower"][fact.signed],
                    candidate,
                )
            else:
                entry["upper"][fact.signed] = cls._select_stronger_upper(
                    entry["upper"][fact.signed],
                    candidate,
                )
        return context

    @classmethod
    def _reduction_context_key(
        cls,
        expr,
        conditions: Optional[List[Condition]],
    ) -> Tuple[int, Tuple[int, ...]]:
        context_ids = set()
        for condition in conditions or ():
            if condition is not None:
                context_ids.add(id(condition))
        return id(expr), tuple(sorted(context_ids))

    @classmethod
    def _scalar_constraint_is_implied(
        cls,
        fact: ScalarConstraint,
        context_conditions: List[Condition],
    ) -> bool:
        context = cls._collect_scalar_context(context_conditions)
        entry = context.get(fact.key)
        if entry is None:
            return False

        bits = fact.key[1]
        eq_raw_values = entry["eq_raw_values"]
        ne_raw_values = entry["ne_raw_values"]
        lower = entry["lower"][fact.signed]
        upper = entry["upper"][fact.signed]

        if len(eq_raw_values) == 1:
            eq_raw = next(iter(eq_raw_values))
            eq_value = cls._to_signed_value(eq_raw, bits) if fact.signed else eq_raw
            if fact.kind == "eq":
                return eq_raw == fact.raw_value
            if fact.kind == "ne":
                return eq_raw != fact.raw_value
            if fact.kind == "lower":
                required = cls._effective_lower_bound(
                    fact.value,
                    bool(fact.inclusive),
                    fact.signed,
                    bits,
                )
                return eq_value >= required
            if fact.kind == "upper":
                required = cls._effective_upper_bound(
                    fact.value,
                    bool(fact.inclusive),
                    fact.signed,
                    bits,
                )
                return eq_value <= required

        if fact.kind == "eq":
            if lower is None or upper is None:
                return False
            lower_effective = cls._effective_lower_bound(lower[0], lower[1], fact.signed, bits)
            upper_effective = cls._effective_upper_bound(upper[0], upper[1], fact.signed, bits)
            if lower_effective != upper_effective:
                return False
            collapsed_raw = cls._normalize_raw_value(lower_effective, bits)
            return collapsed_raw == fact.raw_value and collapsed_raw not in ne_raw_values

        if fact.kind == "ne":
            if fact.raw_value in ne_raw_values:
                return True
            fact_value = cls._to_signed_value(fact.raw_value, bits) if fact.signed else fact.raw_value
            if lower is not None:
                lower_effective = cls._effective_lower_bound(lower[0], lower[1], fact.signed, bits)
                if fact_value < lower_effective:
                    return True
            if upper is not None:
                upper_effective = cls._effective_upper_bound(upper[0], upper[1], fact.signed, bits)
                if fact_value > upper_effective:
                    return True
            return False

        if fact.kind == "lower":
            if lower is None:
                return False
            current_effective = cls._effective_lower_bound(lower[0], lower[1], fact.signed, bits)
            required_effective = cls._effective_lower_bound(
                fact.value,
                bool(fact.inclusive),
                fact.signed,
                bits,
            )
            return current_effective >= required_effective

        if fact.kind == "upper":
            if upper is None:
                return False
            current_effective = cls._effective_upper_bound(upper[0], upper[1], fact.signed, bits)
            required_effective = cls._effective_upper_bound(
                fact.value,
                bool(fact.inclusive),
                fact.signed,
                bits,
            )
            return current_effective <= required_effective

        return False

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
            cls._debug_print(
                f"Detected circular reduction context; skip recursion for {cls._debug_expr_summary(expr)}",
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
        return cls.build_object_centric_condition_basis(conditions)

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
        return cls.build_constraint_set(conditions).simplified_conditions()

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

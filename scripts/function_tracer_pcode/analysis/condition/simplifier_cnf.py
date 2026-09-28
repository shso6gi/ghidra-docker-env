"""CNF clause construction, satisfiability and implication."""

from __future__ import annotations

from typing import Iterable, List, Dict, Optional, Tuple
from scripts.function_tracer_pcode.core import Expression, Condition, ExpressionType
from scripts.function_tracer_pcode.core.structural import expression_provenance_key
from scripts.function_tracer_pcode.analysis.condition.condition_cache import (
    cache_lookup,
    cache_store,
    root_memo,
)
from scripts.function_tracer_pcode.core.condition_metrics import (
    note_dpll_decision,
    satisfiability_call,
)
from scripts.function_tracer_pcode.analysis.condition.normalizer import ConditionNormalizer
from scripts.function_tracer_pcode.analysis.condition.query_identity import SolverQueryIdentity
from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle
from scripts.function_tracer_pcode.analysis.condition.simplifier_support import (
    ConditionRecoverableSimplificationError,
    _CONDITION_RECOVERABLE_ERRORS,
    BooleanAtom,
    BooleanLiteral,
    BooleanClause,
    note_reentry_guard_hit,
    reentry_guard_scope,
)


class CnfReasoningMixin:
    """CNF clause construction, satisfiability and implication."""

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

    #: literal の項 1 つの並べ替え key（項 object ごとの memo。値は項だけで決まる）
    TERM_SORT_KEY_MEMO = "cnf.term_sort_key"

    @classmethod
    def _literal_sort_key(cls, literal: BooleanLiteral) -> Tuple[object, ...]:
        atom, polarity = literal
        try:
            left, op, right = atom
            return (
                cls._term_total_sort_key(left),
                str(op),
                cls._term_total_sort_key(right),
                bool(polarity),
            )
        except _CONDITION_RECOVERABLE_ERRORS as exc:
            raise ConditionRecoverableSimplificationError(
                "could not build deterministic CNF literal sort key"
            ) from exc

    @classmethod
    def _term_total_sort_key(cls, term: object) -> Tuple[object, ...]:
        """項の全順序の key（`_total_sort_key(_atom_term_sort_key(term))`）。

        Issue #105 PR-105-A: 項は正規化の構造 key（部分 key を共有する入れ子の tuple）で、
        DPLL の 1 手ごとに節の literal を並べ直すたびに作り直していた。値は項 object だけで
        決まる（tuple は不変、式は凍結済み）ので、pair の cache scope の中では項 object ごとに
        1 回だけ作る（`root_memo`、object を保持するので `id()` の再利用で取り違えない）。
        作るときも共有された部分 key を 1 回だけ辿る（木として展開しない）。値と順序は従来と同じ。
        """

        return root_memo(cls.TERM_SORT_KEY_MEMO, term, cls._build_term_total_sort_key)

    @classmethod
    def _build_term_total_sort_key(cls, term: object) -> Tuple[object, ...]:
        return cls._total_sort_key(cls._atom_term_sort_key(term, {}), {})

    @classmethod
    def _atom_term_sort_key(cls, term: object, _memo: Optional[Dict[int, Tuple[object, ...]]] = None) -> Tuple[object, ...]:
        if isinstance(term, (tuple, list, dict)) and _memo is not None:
            cached = _memo.get(id(term))
            if cached is not None:
                return cached[1]
            key = cls._atom_term_sort_key_uncached(term, _memo)
            _memo[id(term)] = (term, key)
            return key
        return cls._atom_term_sort_key_uncached(term, _memo)

    @classmethod
    def _atom_term_sort_key_uncached(
        cls, term: object, _memo: Optional[Dict[int, Tuple[object, ...]]]
    ) -> Tuple[object, ...]:
        if isinstance(term, Expression):
            return ("expr", expression_provenance_key(term, safe_budget=256))
        if term is None:
            return ("none",)
        if isinstance(term, (str, int, bool, float)):
            return (type(term).__name__, term)
        if isinstance(term, tuple):
            return ("tuple", tuple(cls._atom_term_sort_key(item, _memo) for item in term))
        if isinstance(term, list):
            return ("list", tuple(cls._atom_term_sort_key(item, _memo) for item in term))
        if isinstance(term, dict):
            entries = [
                (
                    cls._atom_term_sort_key(key, _memo),
                    cls._atom_term_sort_key(value, _memo),
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
    def _total_sort_key(cls, value: object, _memo: Optional[Dict[int, Tuple[object, ...]]] = None) -> Tuple[object, ...]:
        if isinstance(value, (tuple, list, dict)) and _memo is not None:
            cached = _memo.get(id(value))
            if cached is not None:
                return cached[1]
            key = cls._total_sort_key_uncached(value, _memo)
            _memo[id(value)] = (value, key)
            return key
        return cls._total_sort_key_uncached(value, _memo)

    @classmethod
    def _total_sort_key_uncached(
        cls, value: object, _memo: Optional[Dict[int, Tuple[object, ...]]]
    ) -> Tuple[object, ...]:
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
            return ("tuple", tuple(cls._total_sort_key(item, _memo) for item in value))
        if isinstance(value, list):
            return ("list", tuple(cls._total_sort_key(item, _memo) for item in value))
        if isinstance(value, dict):
            return (
                "dict",
                tuple(
                    sorted(
                        (
                            cls._total_sort_key(key, _memo),
                            cls._total_sort_key(item, _memo),
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
        # 計測だけ（PR-105-B の決定回数予算の分布）。判定には触れない。
        note_dpll_decision()

        true_assignments = dict(current_assignments)
        true_assignments[branch_atom] = branch_polarity
        if cls._clauses_are_satisfiable(current_clauses, true_assignments):
            return True

        false_assignments = dict(current_assignments)
        false_assignments[branch_atom] = not branch_polarity
        return cls._clauses_are_satisfiable(current_clauses, false_assignments)

    @classmethod
    def _clause_set_is_unsat(cls, condition_list: List[Condition]) -> Optional[bool]:
        """CNF + DPLL による判定（最上位の充足可能性判定 1 回 = 計測枠 1 つ）。

        二値（`_clauses_are_satisfiable` の否定）: 予算の無い今の DPLL は完全なので
        `not` は正確。三値の `SatVerdict` へ移して `not` を消すのは PR-105-B（D1-B）。
        """

        clauses = cls._conditions_to_cnf_clauses(condition_list)
        if clauses is None:
            return None
        clause_literals = [clause.literals for clause in clauses]
        with satisfiability_call():
            return not cls._clauses_are_satisfiable(clause_literals)

    @classmethod
    def _conjunction_is_unsat(cls, condition_list: List[Condition]) -> Optional[bool]:
        """条件の conjunction が充足不能か（`True` / `False` / 判定できない `None`）。

        `_formula_is_unsat` と `_formula_implies`（文脈 ∧ ¬条件）の **唯一の実装**。どちらも
        同じ問い（conjunction の充足不能性）なので、表も 1 つ（`CONJUNCTION_UNSAT_TABLE`）で
        key は conjunction の `SolverQueryIdentity`（bucket → 完全比較）。

        * solver を使ってよい conjunction なら条件 oracle、答えが無ければ CNF + DPLL
        * `None`（判定できなかった）も覚えた値で、hit しても `True` / `False` には化けない
        * 例外は覚えない。再入（同じ conjunction の判定の途中）は `None` で、**その途中で
          作った答えは覚えない**（`reentry_guard_scope`: 再入で打ち切った答えは呼ばれ方に
          依存するので、覚えると「いつ・どこから最初に聞かれたか」で答えが変わる）
        """

        try:
            key = SolverQueryIdentity.from_conditions(condition_list)
        except _CONDITION_RECOVERABLE_ERRORS:
            return None
        found, cached = cache_lookup(
            cls.CONJUNCTION_UNSAT_TABLE, key, limit=cls._FORMULA_IMPLIES_CACHE_LIMIT
        )
        if found:
            return cached
        if key in cls._active_formula_implies_keys:
            cls._debug_print("Skipping recursive formula guard hit", 0)
            note_reentry_guard_hit()
            return None
        cls._active_formula_implies_keys.add(key)
        try:
            with reentry_guard_scope() as guard:
                result = cls._compute_conjunction_is_unsat(condition_list)
        finally:
            cls._active_formula_implies_keys.discard(key)
        if guard.clean:
            cache_store(
                cls.CONJUNCTION_UNSAT_TABLE, key, result, limit=cls._FORMULA_IMPLIES_CACHE_LIMIT
            )
        return result

    @classmethod
    def _compute_conjunction_is_unsat(cls, condition_list: List[Condition]) -> Optional[bool]:
        try:
            use_solver = cls._should_use_solver_reasoning(condition_list)
        except _CONDITION_RECOVERABLE_ERRORS:
            use_solver = False
        if use_solver:
            try:
                solver_result = ConditionSMTOracle.conjunction_is_unsat(condition_list)
            except _CONDITION_RECOVERABLE_ERRORS:
                solver_result = None
            if solver_result is not None:
                return solver_result
        try:
            return cls._clause_set_is_unsat(condition_list)
        except _CONDITION_RECOVERABLE_ERRORS:
            return None

    @classmethod
    def _formula_is_unsat(
        cls,
        conditions: Iterable[Condition],
    ) -> Optional[bool]:
        """条件の conjunction が充足不能か（`_conjunction_is_unsat`）。"""

        return cls._conjunction_is_unsat(list(conditions or []))

    @classmethod
    def _formula_implies(
        cls,
        context_conditions: Iterable[Condition],
        condition: Condition,
    ) -> Optional[bool]:
        """文脈が条件を含意するか = 文脈 ∧ ¬条件 が充足不能か（`_conjunction_is_unsat`）。"""

        try:
            context_list = list(context_conditions or [])
            negated_condition = condition.negate()
        except _CONDITION_RECOVERABLE_ERRORS:
            return None
        return cls._conjunction_is_unsat(context_list + [negated_condition])

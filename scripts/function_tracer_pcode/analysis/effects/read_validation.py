# -*- coding: utf-8 -*-
"""入口の memory の読み出しが、先行する store に依存しないことの検査（Issue #282, I3）。

SMT に入る `MEMORY` の node（post-state の読み出しは lowering の後）は、**その側の pre-state の memory** の
読み出しとして描かれる。その描画が正しいのは、同じ経路でその読み出しより前に実行され得るどの store とも
重ならない（`location_relation` が `DISJOINT`）ときだけ。重なり得る store（別の parameter・重なる offset・
幅の違う store・位置の分からない store）の後の読み出しを入口の値で描くと、その store を無視した値で
左右を比べることになる（偽 EQ の形。設計 v3 §6.2 の `w7b`）。

この検査が唯一の判定で、lowering の各経路（`rewrite_loads_from_effects` など）がどう値を作ったかに
依らず、最後に描かれる式を見る。PHI は branch の順の意味（前の branch の条件の否定の下で次の branch）で
経路の条件を積み、store の条件と矛盾する経路では、その store を先行するものとみなさない。

順序: 読み出しの key（`read_order_key` / `ObservedMemoryReadRef`）は store と同じ `core.program_order` の
key（#283）。key の無い読み出しは関数の出口の読み出し（すべての store の後）とみなす。store の値・条件の
中の key の無い読み出しは、その store より前とみなす。

検査に落ちた読み出しがあれば `memory_read_alias_unresolved` で EQ と NOT_EQ の両方を止める。store chain
で正しく描く（精度の回復）のは後続（PR-282-P）。
"""

from __future__ import annotations

import weakref
from typing import List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.core.memory_relation import MemoryRelation

MEMORY_READ_ALIAS_UNRESOLVED_REASON = "memory_read_alias_unresolved"

#: 関数の出口の読み出し（すべての store の後）の順序。lowering が簡約できなかった出口の状態の読み出しに付け、
#: 入口の値の読み出し（順序の無い・小さい順序の node）と区別する
POST_STATE_READ_ORDER = 1 << 62

#: 1 つの解析で調べる読み出しの上限。超えたら判定できないとして止める（UNKNOWN の側）
_MAX_CHECKED_READS = 4096


class _ReadCheckBudgetExceeded(Exception):
    pass


def _check_failures():
    from scripts.function_tracer_pcode.core.operand_derivation import OperandDerivationRefused

    return (OperandDerivationRefused, ArithmeticError, LookupError, TypeError, ValueError, AttributeError, RecursionError)


def _sequence(value) -> list:
    """列として持つ field だけを読む（型の分からない値は空。mock の属性を列と読まない）。"""

    return list(value) if isinstance(value, (list, tuple)) else []


def _negated(condition: Condition) -> Condition:
    return Condition(condition.expression, not bool(condition.negated))


def _effect_is_contradicted(path_conditions: Sequence[Condition], effect) -> bool:
    from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier

    combined = list(path_conditions) + list(getattr(effect, "conditions", None) or ())
    if not combined:
        return False
    return bool(ConditionSimplifier.object_centric_is_contradiction(combined))


def _read_order(node: Expression) -> Optional[int]:
    from scripts.function_tracer_pcode.analysis.effects.expression_forms import (
        _impl__expression_observed_order_key as observed_order_key,
    )

    try:
        return observed_order_key(node)
    except (TypeError, ValueError):
        return None


class _Checker:
    def __init__(self, effects, parameters) -> None:
        self.effects = list(effects)
        self.parameters = list(parameters or ())
        self.findings: List[Tuple[str, ...]] = []
        self.checked = 0

    def check_read(self, node: Expression, path_conditions: Sequence[Condition], default_order: Optional[int]) -> None:
        from scripts.function_tracer_pcode.analysis.effects.location import (
            _impl_canonicalize_expr_read_location as canonicalize_expr_read_location,
        )
        from scripts.function_tracer_pcode.analysis.effects.location_relation import location_relation

        self.checked += 1
        if self.checked > _MAX_CHECKED_READS:
            raise _ReadCheckBudgetExceeded()
        order = _read_order(node)
        if order is None:
            order = default_order
        # 位置を作れない読み出し（None）は、どの store とも関係が分からない（`location_relation` が UNKNOWN）
        location = canonicalize_expr_read_location(node, self.parameters)
        for effect in self.effects:
            effect_order = getattr(effect, "order_key", None)
            if order is not None and effect_order is not None and int(effect_order) >= int(order):
                continue
            if _effect_is_contradicted(path_conditions, effect):
                continue
            conditions = list(path_conditions) + list(getattr(effect, "conditions", None) or ())
            relation = location_relation(location, getattr(effect, "location", None), conditions)
            if relation is not MemoryRelation.DISJOINT:
                self.findings.append(
                    (
                        "read",
                        repr(location.stable_key()) if location is not None else "unlocated",
                        "store",
                        repr(effect.location.stable_key()),
                        relation.name,
                    )
                )
                return

    def walk(self, expr: Optional[Expression], path_conditions: Sequence[Condition], default_order: Optional[int]) -> None:
        if expr is None or self.findings:
            return
        expr_type = getattr(expr, "expr_type", None)
        if expr_type == ExpressionType.PHI:
            prior: List[Condition] = []
            for cond, value in list(getattr(expr, "value", None) or ()):
                branch_conditions = list(path_conditions) + [_negated(item) for item in prior]
                if cond is not None:
                    self.walk(getattr(cond, "expression", None), branch_conditions, default_order)
                    branch_conditions = branch_conditions + [cond]
                    prior.append(cond)
                self.walk(value, branch_conditions, default_order)
            return
        if expr_type == ExpressionType.MEMORY:
            self.check_read(expr, path_conditions, default_order)
        for operand in list(getattr(expr, "operands", None) or ()):
            self.walk(operand, path_conditions, default_order)


def _lowered(expr, conditions, effects, parameters):
    """描かれる形（post-state の読み出しは lowering の後）。lowering の結果に残る post-state の読み出しは別の
    reason（`symbolic_post_state_reads`）が扱う。"""

    from scripts.function_tracer_pcode.analysis.effects.summary import (
        expression_contains_post_state_reads,
        lower_post_state_expression_for_smt_if_needed,
    )

    if expr is None or not expression_contains_post_state_reads(expr):
        return expr
    lowered = lower_post_state_expression_for_smt_if_needed(expr, conditions, effects, parameters)
    return lowered if lowered is not None else expr


#: 解析ごとの検査の結果。解析の object は hash できない（dataclass）ので id で引き、弱参照で同じ object かを確かめる。
#: 値は検査が読む object の列（identity で比べる）と結果
_FINDINGS_MEMO: dict = {}
_FINDINGS_MEMO_LIMIT = 4096


def _memo_inputs(analysis) -> Tuple[object, ...]:
    effect_summary = getattr(analysis, "effect_summary", None)
    returns = _sequence(getattr(analysis, "returns", None))
    return (
        effect_summary,
        getattr(effect_summary, "effects", None),
        getattr(effect_summary, "frame_local_effects", None),
        getattr(analysis, "parameters", None),
        *_sequence(getattr(effect_summary, "effects", None)),
        *_sequence(getattr(effect_summary, "frame_local_effects", None)),
        *(item for ret in returns for item in (ret, getattr(ret, "value", None), getattr(ret, "conditions", None))),
        *(cond for ret in returns for cond in _sequence(getattr(ret, "conditions", None))),
    )


def unresolved_memory_read_aliases(analysis) -> List[Tuple[str, ...]]:
    """`analysis` の戻り値・条件・store の値と条件のうち、先行する store との関係を証明できない入口の memory の
    読み出し（空なら検査に通った）。判定できない（上限超過）ときも 1 件の finding を返す。"""

    inputs = _memo_inputs(analysis)
    cached = _FINDINGS_MEMO.get(id(analysis))
    if (
        cached is not None
        and cached[0]() is analysis
        and len(cached[1]) == len(inputs)
        and all(a is b for a, b in zip(cached[1], inputs))
    ):
        return list(cached[2])
    findings = _unresolved_memory_read_aliases(analysis)
    try:
        owner = weakref.ref(analysis)
    except TypeError:
        return findings
    if len(_FINDINGS_MEMO) >= _FINDINGS_MEMO_LIMIT:
        _FINDINGS_MEMO.clear()
    _FINDINGS_MEMO[id(analysis)] = (owner, inputs, tuple(findings))
    return findings


def _unresolved_memory_read_aliases(analysis) -> List[Tuple[str, ...]]:
    effect_summary = getattr(analysis, "effect_summary", None)
    observed_effects = _sequence(getattr(effect_summary, "effects", None))
    effects = observed_effects + _sequence(getattr(effect_summary, "frame_local_effects", None))
    if not effects:
        return []
    parameters = _sequence(getattr(analysis, "parameters", None))
    checker = _Checker(effects, parameters)
    try:
        # lowering は本番と同じ形（観測する store だけ: `effect_integration`）。frame の store との関係は検査が見る
        for ret in _sequence(getattr(analysis, "returns", None)):
            conditions = list(getattr(ret, "conditions", None) or ())
            checker.walk(_lowered(ret.value, conditions, observed_effects, parameters), conditions, None)
            for cond in conditions:
                checker.walk(
                    _lowered(getattr(cond, "expression", None), conditions, observed_effects, parameters),
                    conditions,
                    None,
                )
        for effect in observed_effects:
            conditions = list(getattr(effect, "conditions", None) or ())
            order = getattr(effect, "order_key", None)
            checker.walk(getattr(effect, "value", None), conditions, order)
            for cond in conditions:
                checker.walk(getattr(cond, "expression", None), conditions, order)
    except _ReadCheckBudgetExceeded:
        return [("budget", str(_MAX_CHECKED_READS))]
    except _check_failures() as exc:
        # 検査を完了できない（lowering・位置の正規化の失敗）なら、読み出しが store に依存しないとは言えない
        return [("check_failed", type(exc).__name__)]
    return checker.findings

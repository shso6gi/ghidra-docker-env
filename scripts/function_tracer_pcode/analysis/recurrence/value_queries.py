"""Recurrence の式を SMT で比べる公開の入口（Issue #297）。

recurrence の builder が候補の検査に使う query（式の同値）を、P-code を読まない呼び出し側（promotion の
proof）にも同じ形で出す。builder の host（``StructuralRecurrenceSummarizer``）が公開の service として
宣言した 2 つ（``expression_query_symbols``・``prove_expressions_equal_under_conditions``）だけを使い、
private な method には触れない。proof にとってはここが唯一の入口である。

- 局所の z3 で、#298 の UB の前提を加えない。UNSAT だけを成立とし、timeout・unknown・query を
  作れないとき・式の symbol を識別できないときは成立しない（``False``）。
- P-code・tracer を使わない。builder の service が tracer に触れたら :class:`QueryNeedsProgram`
  （``ValueError``）で止まる（成立としない）。
"""

from __future__ import annotations

from typing import Any, Sequence


class QueryNeedsProgram(ValueError):
    """式の query が P-code・tracer を読もうとした（この入口では読ませない）。"""


class _NoProgram:
    def __getattr__(self, name: str) -> Any:
        raise QueryNeedsProgram(f"recurrence value query must not read the program ({name})")


def _host():
    from scripts.function_tracer_pcode.analysis.recurrence.summarizer import StructuralRecurrenceSummarizer

    return StructuralRecurrenceSummarizer(_NoProgram())


def prove_values_equal_under(left: Any, right: Any, conditions: Sequence[Any] = ()) -> bool:
    """``conditions``（``Condition`` の連言）の下で ``left == right`` が恒真であること。"""

    if left is None or right is None:
        return False
    host = _host()
    conditions = [item for item in conditions or () if item is not None]
    parameters = host.expression_query_symbols(
        left, right, *(item.expression for item in conditions),
    )
    if parameters is None:
        return False
    return bool(host.prove_expressions_equal_under_conditions(left, right, conditions, parameters))


def condition_sets_equivalent(left: Sequence[Any], right: Sequence[Any]) -> bool:
    """2 つの条件の集合（それぞれ連言）が同値であること。

    条件の oracle ではなく、:func:`prove_values_equal_under` と同じ式の query で示す（連言の bool 値どうしの
    同値）。式の値と条件で symbol の識別（引数は番号）を 1 つにするため: 条件の oracle は引数を型・置き場所で
    識別するので、同じ引数でも作り方の違う式を別の値として扱う。
    """

    left_value, right_value = _conjunction(left), _conjunction(right)
    if left_value is None or right_value is None:
        return False
    return prove_values_equal_under(left_value, right_value, ())


def _conjunction(conditions: Sequence[Any]) -> Any:
    from scripts.function_tracer_pcode.core import Expression

    terms = []
    for condition in conditions or ():
        if condition is None or getattr(condition, "expression", None) is None:
            return None
        expr = condition.expression
        if bool(getattr(condition, "negated", False)):
            expr = Expression.unary_op("BOOL_NEGATE", expr)
            expr.size = 1
        terms.append(expr)
    if not terms:
        return None
    value = terms[0]
    for term in terms[1:]:
        value = Expression.binary_op("BOOL_AND", value, term)
        value.size = 1
    return value

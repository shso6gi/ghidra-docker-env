# -*- coding: utf-8 -*-
"""Debug-only expression rendering regressions."""

from dataclasses import dataclass, field
from typing import Tuple
from unittest.mock import Mock

from scripts.function_tracer_pcode.analysis.debug import render
from scripts.function_tracer_pcode.analysis.debug.render import (
    summarize_conditions,
    summarize_expression,
    summarize_expression_identity,
    summarize_expressions,
    summarize_runtime_ref,
    summarize_structural_preview,
    summarize_values,
)
from scripts.function_tracer_pcode.analysis.returns.analyzer import ReturnAnalyzer
from scripts.function_tracer_pcode.core import Condition, Expression
from scripts.function_tracer_pcode.semantics.transform.expander import ExpressionExpander
from scripts.function_tracer_pcode.semantics.transform.expander_support import ExpandedValue


def test_expander_debug_expr_summary_does_not_require_full_to_string(monkeypatch):
    tracer = Mock()
    tracker = Mock()
    expander = ExpressionExpander(tracer, tracker, debug=True)

    expr = Expression.binary_op(
        "INT_ADD",
        Expression.unknown("phi_circular"),
        Expression.binary_op("INT_MULT", Expression.parameter("n"), Expression.constant(2, 4)),
    )

    def _boom(_self, simplify=True):
        raise AssertionError("full to_string should not be used for debug summary")

    monkeypatch.setattr(Expression, "to_string", _boom)

    summary = expander._debug_expr_summary(expr)

    assert "INT_ADD" in summary
    assert "UNKNOWN(phi_circular)" in summary


def test_expander_debug_budget_skips_heavy_summary_work(monkeypatch):
    tracer = Mock()
    tracker = Mock()
    expander = ExpressionExpander(tracer, tracker, debug=True)
    expander._debug_message_limit = 0

    expr = Expression.binary_op(
        "INT_ADD",
        Expression.parameter("n"),
        Expression.constant(2, 4),
    )

    def _boom(_self, simplify=True):
        raise AssertionError("suppressed expander debug should not call full to_string")

    monkeypatch.setattr(Expression, "to_string", _boom)

    assert expander._debug_expr_summary(expr) == "<debug-suppressed>"


def test_return_analyzer_dispose_ignores_jvm_not_running_error():
    analyzer = ReturnAnalyzer(program=Mock(), debug=False)
    analyzer._decompiler = Mock()
    analyzer._decompiler.dispose.side_effect = Exception("Java Virtual Machine is not running")

    analyzer.dispose()

    assert analyzer._decompiler is None


# ------------------------------------------------- 列サマリーの有界性（#22）


class _ExplosiveIterable:
    """``allowed`` 個を超えて読まれたら失敗する iterable（長さは名乗らない）。"""

    def __init__(self, items, allowed: int):
        self._items = list(items)
        self._allowed = allowed
        self.consumed = 0

    def __iter__(self):
        for item in self._items:
            self.consumed += 1
            if self.consumed > self._allowed:
                raise AssertionError(
                    f"debug summary consumed {self.consumed} elements "
                    f"(allowed {self._allowed})"
                )
            yield item


def _expressions(count: int):
    return [Expression.parameter(f"p{index}") for index in range(count)]


def test_sequence_summary_reports_the_exact_remainder_for_a_sized_sequence():
    summary = summarize_expressions(_expressions(10), max_items=3)

    assert summary.startswith("[PARAM(p0), PARAM(p1), PARAM(p2),")
    assert summary.endswith("+7 more]")


def test_sequence_summary_renders_only_the_listed_elements(monkeypatch):
    """``max_items`` より後ろの要素は render しない（出力だけでなく作業も有界）。"""

    rendered = []

    def _counting(expr, max_depth: int = 4) -> str:
        rendered.append(expr)
        return "x"

    monkeypatch.setattr(render, "summarize_expression", _counting)

    assert render.summarize_expressions(_expressions(50), max_items=4) == "[x, x, x, x, +46 more]"
    assert len(rendered) == 4


def test_sequence_summary_does_not_drain_an_iterable_of_unknown_length():
    """長さを名乗らない iterable は ``max_items + 1`` 個までしか読まない。"""

    items = _ExplosiveIterable(_expressions(1000), allowed=4)

    summary = summarize_expressions(items, max_items=3)

    assert summary == "[PARAM(p0), PARAM(p1), PARAM(p2), +more]"
    assert items.consumed == 4


def test_condition_sequence_summary_is_bounded_the_same_way():
    conditions = [Condition(Expression.parameter(f"p{index}")) for index in range(6)]

    assert summarize_conditions(conditions, max_items=2) == "[PARAM(p0), PARAM(p1), +4 more]"
    assert summarize_conditions(_ExplosiveIterable(conditions, allowed=3), max_items=2) == (
        "[PARAM(p0), PARAM(p1), +more]"
    )


def test_value_sequence_summary_bounds_both_the_count_and_each_element():
    assert summarize_values(["a", "b", "c"], max_items=2) == "[a, b, +1 more]"
    assert summarize_values(["x" * 200], max_text=8) == "[xxxxxxxx...]"
    assert summarize_values(None) == "[]"
    assert summarize_values([None]) == "[None]"


def test_repr_of_an_expanded_value_stays_bounded():
    """``repr()`` は暗黙に呼ばれるので、長い条件列でも先頭しか見ない。"""

    conditions = [Condition(Expression.parameter(f"p{index}")) for index in range(200)]

    text = repr(ExpandedValue(Expression.parameter("v"), conditions))

    assert "+192 more" in text
    assert len(text) < 400



# ------------------------------- runtime ref 表示の走査量（Issue #22 レビュー）


#: ``stable_key`` / ``semantic_key`` が呼ばれた記録。例外は production 側の
#: 広い ``except`` に握られることがあるので、raise ではなく呼び出し自体を数える。
_HEAVY_KEY_CALLS: list = []


@dataclass(frozen=True, repr=False)
class _ExplosiveRuntimeRef:
    """重いキー生成と ``repr`` を持つ runtime ref。

    実際の ``LoopSummaryRef.stable_key`` は seed / witness / guard / case を
    全部辿って式のキーを組み立てる。debug 表示のために起動してはいけない。
    """

    kind: str = "loop"
    count: int = 3
    keyable: bool = True
    descriptor: Tuple[int, ...] = field(default_factory=lambda: tuple(range(10_000)))

    def stable_key(self):
        _HEAVY_KEY_CALLS.append("stable_key")
        return ("loop", self.descriptor)

    def semantic_key(self):
        _HEAVY_KEY_CALLS.append("semantic_key")
        return ("loop", self.descriptor)

    def __repr__(self):  # pragma: no cover - 呼ばれたら失敗
        raise AssertionError("debug summary must not repr a runtime ref")


def test_runtime_ref_summary_never_builds_a_stable_key():
    _HEAVY_KEY_CALLS.clear()

    summary = summarize_runtime_ref(_ExplosiveRuntimeRef())

    assert summary == "_ExplosiveRuntimeRef[kind=loop, count=3, keyable=True]"
    assert "descriptor" not in summary
    assert _HEAVY_KEY_CALLS == []


def test_runtime_ref_summary_falls_back_to_the_type_name():
    _HEAVY_KEY_CALLS.clear()

    class _Opaque:
        def stable_key(self):
            _HEAVY_KEY_CALLS.append("stable_key")
            return ("opaque",)

    assert summarize_runtime_ref(_Opaque()) == "_Opaque"
    assert summarize_runtime_ref(None) == "None"
    assert _HEAVY_KEY_CALLS == []


def test_expression_identity_summary_does_not_walk_the_runtime_ref():
    """structural key は node 予算で有界。runtime ref のキーは組み立てない。"""

    expr = Expression.binary_op(
        "INT_ADD", Expression.variable("v", 4), Expression.constant(2, 4)
    )
    expr.runtime_ref = _ExplosiveRuntimeRef()
    expr.operands[0].runtime_ref = _ExplosiveRuntimeRef()
    _HEAVY_KEY_CALLS.clear()

    text = summarize_expression_identity(expr)

    assert _HEAVY_KEY_CALLS == []
    assert "structural_preview=[BINARY_OP:INT_ADD" in text
    assert "runtime_ref=_ExplosiveRuntimeRef[kind=loop" in text


def test_value_summary_does_not_stringify_arbitrary_objects():
    assert summarize_values([_ExplosiveRuntimeRef()]) == "[<_ExplosiveRuntimeRef>]"
    assert summarize_values([1, "a", None, True]) == "[1, a, None, True]"

# ------------------------------ preview の hard bound（Issue #22 レビュー 3 巡目）


class _CountingSequence:
    """反復された要素数を数える列。exact な組み込み型ではない。"""

    def __init__(self, items):
        self._items = list(items)
        self.consumed = 0

    def __len__(self):
        return len(self._items)

    def __iter__(self):
        for item in self._items:
            self.consumed += 1
            yield item


class _HostileInt(int):
    def __str__(self):  # pragma: no cover - 呼ばれたら失敗
        raise AssertionError("debug summary must not call __str__ on a subclass")

    __repr__ = __str__


class _HostileStr(str):
    def __str__(self):  # pragma: no cover - 呼ばれたら失敗
        raise AssertionError("debug summary must not call __str__ on a subclass")

    __repr__ = __str__


def _records(preview: str):
    return preview[1:-1].split(", ") if preview not in ("[]", "None") else []


def test_structural_preview_reads_only_max_fanout_call_arguments():
    arguments = _CountingSequence(_expressions(10_000))
    call = Expression.call("f", [])
    call.operands = arguments

    preview = summarize_structural_preview(call, max_fanout=3)

    assert arguments.consumed == 3
    assert len(_records(preview)) <= render.DEFAULT_MAX_PREVIEW_NODES + 1


def test_structural_preview_reads_only_max_fanout_phi_branches():
    branches = _CountingSequence(
        (Condition(Expression.parameter(f"c{index}")), Expression.parameter(f"v{index}"))
        for index in range(10_000)
    )
    phi = Expression.phi([])
    phi.value = branches

    preview = summarize_structural_preview(phi, max_fanout=2)

    assert branches.consumed == 2
    assert preview.startswith("[PHI")


def test_structural_preview_stops_at_the_node_limit():
    expr = Expression.parameter("p0")
    for index in range(200):
        expr = Expression.binary_op("INT_ADD", expr, Expression.parameter(f"p{index}"))

    preview = summarize_structural_preview(expr, max_nodes=6)

    records = _records(preview)
    assert records[-1] == "+more"
    assert len(records) == 7


def test_structural_preview_never_expands_a_node_value():
    node = Expression.variable("v", 4)
    node.value = list(range(100_000))

    preview = summarize_structural_preview(node)

    assert "value=<list len=100000>" in preview
    assert "0, 1, 2" not in preview


def test_structural_preview_is_cycle_safe():
    left = Expression.parameter("a")
    shared = Expression.binary_op("INT_ADD", left, left)

    preview = summarize_structural_preview(shared)

    assert "<shared>" in preview


def test_primitive_text_never_materializes_a_large_value():
    huge = 1 << 5000
    assert render._primitive_text(huge) == f"<int bits={huge.bit_length()}>"
    assert render._primitive_text(255) == "255"
    assert render._primitive_text("x" * 500, max_text=8) == "xxxxxxxx..."
    assert render._primitive_text(b"\x00" * 4096) == "<bytes len=4096>"
    assert render._primitive_text(list(range(10_000))) == "<list len=10000>"


def test_primitive_text_does_not_run_a_subclass_dunder():
    assert render._primitive_text(_HostileInt(5)) == "<_HostileInt>"
    assert render._primitive_text(_HostileStr("x")) == "<_HostileStr>"


def test_expression_summary_does_not_materialize_a_constant_value():
    constant = Expression.constant(0, 4)
    constant.value = 1 << 5000

    assert summarize_expression(constant) == f"CONST(<int bits={(1 << 5000).bit_length()}>)"

# -*- coding: utf-8 -*-
"""Expander combination guard regressions."""

from unittest.mock import Mock

import pytest

from scripts.function_tracer_pcode.analysis.condition import ConditionSimplifier
from scripts.function_tracer_pcode.model import CanonicalLocation, Expression, LocationBaseRef, UnknownValueRef
from scripts.function_tracer_pcode.model.render_smt import (
    UnknownSmtExtensionWidthError,
    expression_contains_unsupported_smt_ops,
    expression_smt_bit_width,
)
from scripts.function_tracer_pcode.model.runtime_refs import PostStateReadRef
from scripts.function_tracer_pcode.transform.expander import ExpandedValue, ExpressionExpander


def test_combine_input_expansions_deduplicates_duplicate_pairs_before_simplify(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)

    monkeypatch.setattr(
        ConditionSimplifier,
        "is_contradiction",
        classmethod(lambda cls, conds: False),
    )

    monkeypatch.setattr(
        ConditionSimplifier,
        "simplify_conditions",
        classmethod(lambda cls, conds: list(conds)),
    )

    left = ExpandedValue(Expression.parameter("x"), [])
    right = ExpandedValue(Expression.constant(4, 4), [])

    result = expander._combine_input_expansions_with_conditions(
        "INT_ADD",
        [[left, left, left], [right, right, right]],
        [],
        depth=0,
    )

    assert len(result) == 1
    assert result[0].value.operator == "INT_ADD"


def test_combine_input_expansions_adds_unknown_when_budget_exceeded(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)
    expander._max_combination_attempts = 2

    monkeypatch.setattr(
        ConditionSimplifier,
        "is_contradiction",
        classmethod(lambda cls, conds: False),
    )
    monkeypatch.setattr(
        ConditionSimplifier,
        "simplify_conditions",
        classmethod(lambda cls, conds: list(conds)),
    )

    left_expansions = [
        ExpandedValue(Expression.parameter("a"), []),
        ExpandedValue(Expression.parameter("b"), []),
    ]
    right_expansions = [
        ExpandedValue(Expression.constant(1, 4), []),
        ExpandedValue(Expression.constant(2, 4), []),
    ]

    result = expander._combine_input_expansions_with_conditions(
        "INT_ADD",
        [left_expansions, right_expansions],
        [],
        depth=0,
    )

    assert any(
        ev.value.expr_type.name == "UNKNOWN" and ev.value.name == "INT_ADD_budget_exceeded"
        for ev in result
    )


@pytest.mark.parametrize(("mnemonic", "smt_operator"), [
    ("INT_ZEXT", "zero_extend"),
    ("INT_SEXT", "sign_extend"),
])
def test_combine_input_expansions_preserves_extension_output_width(
    monkeypatch,
    mnemonic,
    smt_operator,
):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)
    monkeypatch.setattr(
        ConditionSimplifier,
        "is_contradiction",
        classmethod(lambda cls, conds: False),
    )

    operand = Expression.unknown("phi_no_valid_branch")
    operand.size = 4
    result = expander._combine_input_expansions_with_conditions(
        mnemonic,
        [[ExpandedValue(operand, [])]],
        [],
        depth=0,
        output_size=8,
    )

    assert len(result) == 1
    rebuilt = result[0].value
    assert rebuilt.size == 8
    assert expression_smt_bit_width(rebuilt) == 64
    smt = rebuilt.to_smt()
    assert smt.count(f"((_ {smt_operator} 32)") == 1


def test_combine_input_expansions_preserves_int2float_output_width(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)
    monkeypatch.setattr(
        ConditionSimplifier,
        "is_contradiction",
        classmethod(lambda cls, conds: False),
    )
    operand = Expression.parameter("n", size=4)

    result = expander._combine_input_expansions_with_conditions(
        "INT2FLOAT",
        [[ExpandedValue(operand, [])]],
        [],
        depth=0,
        output_size=8,
    )

    assert len(result) == 1
    rebuilt = result[0].value
    assert rebuilt.operator == "INT2FLOAT"
    assert rebuilt.size == 8
    assert rebuilt.to_smt(float_mode="fp") == "((_ to_fp 11 53) RNE n)"


@pytest.mark.parametrize("mnemonic", ["INT_ZEXT", "INT_SEXT"])
def test_unknown_extension_output_width_fails_closed(mnemonic):
    operand = Expression.unknown("phi_no_valid_branch")
    operand.size = 4
    extension = Expression.unary_op(mnemonic, operand)
    extension.size = 0

    assert extension.get_bit_width() == 0
    assert expression_smt_bit_width(extension) == 0
    assert expression_contains_unsupported_smt_ops(extension)
    with pytest.raises(UnknownSmtExtensionWidthError):
        extension.to_smt()


def test_combine_input_expansions_counts_unique_results_for_budget(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)
    expander._max_combination_attempts = 1

    monkeypatch.setattr(
        ConditionSimplifier,
        "is_contradiction",
        classmethod(lambda cls, conds: False),
    )
    monkeypatch.setattr(
        ConditionSimplifier,
        "simplify_conditions",
        classmethod(lambda cls, conds: list(conds)),
    )

    a = Expression.parameter("a")
    b = Expression.parameter("b")
    c = Expression.parameter("c")

    left_expansions = [
        ExpandedValue(Expression.binary_op("INT_ADD", a, b), []),
        ExpandedValue(Expression.binary_op("INT_ADD", b, a), []),
    ]
    right_expansions = [
        ExpandedValue(c, []),
        ExpandedValue(c, []),
    ]

    result = expander._combine_input_expansions_with_conditions(
        "INT_ADD",
        [left_expansions, right_expansions],
        [],
        depth=0,
    )

    assert len(result) == 1
    assert all(
        not (ev.value.expr_type.name == "UNKNOWN" and ev.value.name == "INT_ADD_budget_exceeded")
        for ev in result
    )


def test_expand_expression_cases_binary_op_uses_budget_aware_combiner(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)
    expander._max_combination_attempts = 1

    monkeypatch.setattr(
        ConditionSimplifier,
        "is_contradiction",
        classmethod(lambda cls, conds: False),
    )
    monkeypatch.setattr(
        ConditionSimplifier,
        "simplify_conditions",
        classmethod(lambda cls, conds: list(conds)),
    )

    a = Expression.parameter("a")
    b = Expression.parameter("b")
    c = Expression.parameter("c")

    expr = Expression.binary_op(
        "INT_ADD",
        Expression.phi(
            [
                (None, Expression.binary_op("INT_ADD", a, b)),
                (None, Expression.binary_op("INT_ADD", b, a)),
            ]
        ),
        Expression.phi(
            [
                (None, c),
                (None, c),
            ]
        ),
    )

    result = expander._expand_expression_cases(expr, [], depth=0)

    assert len(result) == 1
    assert all(
        not (ev.value.expr_type.name == "UNKNOWN" and ev.value.name == "INT_ADD_budget_exceeded")
        for ev in result
    )


def test_combine_input_expansions_drops_fully_contradictory_pairs(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)

    monkeypatch.setattr(
        ConditionSimplifier,
        "is_contradiction",
        classmethod(lambda cls, conds: True),
    )

    left = ExpandedValue(Expression.parameter("x"), [])
    right = ExpandedValue(Expression.constant(4, 4), [])

    result = expander._combine_input_expansions_with_conditions(
        "INT_ADD",
        [[left], [right]],
        [],
        depth=0,
    )

    assert result == []


def test_budget_results_use_traced_fallback_when_available(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)

    monkeypatch.setattr(
        ConditionSimplifier,
        "simplify_conditions",
        classmethod(lambda cls, conds: list(conds)),
    )

    traced = Expression.phi(
        [
            (None, Expression.constant(0, 4)),
            (None, Expression.constant(1, 4)),
        ]
    )

    monkeypatch.setattr(
        expander,
        "_trace_operation_expression",
        lambda pcode_op, conditions, depth, output_size=0: traced,
    )

    class _FakeOp:
        def getMnemonic(self):
            return "INT_ADD"

    original = [
        ExpandedValue(
            Expression.unknown(
                "INT_ADD_budget_exceeded",
                runtime_ref=UnknownValueRef.budget_exceeded(operation="INT_ADD"),
            ),
            [],
        ),
        ExpandedValue(Expression.constant(7, 4), []),
    ]

    result = expander._maybe_replace_budget_results_with_traced_fallback(
        _FakeOp(),
        original,
        [],
        depth=0,
        output_size=4,
    )

    assert len(result) == 1
    assert result[0].value.expr_type.name == "PHI"


def test_budget_results_use_traced_fallback_when_only_non_budget_unknown_remains(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)

    monkeypatch.setattr(
        ConditionSimplifier,
        "simplify_conditions",
        classmethod(lambda cls, conds: list(conds)),
    )

    monkeypatch.setattr(
        expander,
        "_trace_operation_expression",
        lambda pcode_op, conditions, depth, output_size=0: Expression.binary_op(
            "INT_ADD",
            Expression.unknown("still_unknown"),
            Expression.constant(1, 4),
        ),
    )

    class _FakeOp:
        def getMnemonic(self):
            return "INT_ADD"

    original = [
        ExpandedValue(
            Expression.unknown(
                "INT_ADD_budget_exceeded",
                runtime_ref=UnknownValueRef.budget_exceeded(operation="INT_ADD"),
            ),
            [],
        )
    ]

    result = expander._maybe_replace_budget_results_with_traced_fallback(
        _FakeOp(),
        original,
        [],
        depth=0,
        output_size=4,
    )

    assert len(result) == 1
    assert result[0].value.operator == "INT_ADD"


def test_budget_results_remain_when_traced_fallback_contains_call(monkeypatch):
    expander = ExpressionExpander(Mock(), Mock(), debug=False)

    monkeypatch.setattr(
        expander,
        "_trace_operation_expression",
        lambda pcode_op, conditions, depth, output_size=0: Expression.call(
            "opaque_call",
            [Expression.constant(1, 4)],
        ),
    )

    class _FakeOp:
        def getMnemonic(self):
            return "INT_ADD"

    original = [
        ExpandedValue(
            Expression.unknown(
                "INT_ADD_budget_exceeded",
                runtime_ref=UnknownValueRef.budget_exceeded(operation="INT_ADD"),
            ),
            [],
        )
    ]

    result = expander._maybe_replace_budget_results_with_traced_fallback(
        _FakeOp(),
        original,
        [],
        depth=0,
        output_size=4,
    )

    assert len(result) == 1
    assert result[0].value.expr_type.name == "UNKNOWN"
    assert result[0].value.name == "INT_ADD_budget_exceeded"


def test_expand_operation_prefers_whole_object_shortcut_for_post_state_reads_without_effect_summary(monkeypatch):
    tracer = Mock()
    expander = ExpressionExpander(tracer, Mock(), debug=False)

    post_state_expr = Expression.binary_op(
        "INT_ADD",
        Expression.variable(
            "poststate_stackframe_tail_n32_size_4",
            size=4,
            runtime_ref=PostStateReadRef(
                location=CanonicalLocation(
                    base_ref=LocationBaseRef.stack_frame(),
                    offset=-32,
                    size=4,
                )
            ),
        ),
        Expression.constant(1, 4),
    )

    monkeypatch.setattr(expander, "_op_requires_recursive_expansion", lambda _op: True)
    monkeypatch.setattr(
        expander,
        "_expand_whole_operation_object_centrically",
        lambda _op, _conds, _depth, output_size=0, context_label="operation": [
            ExpandedValue(post_state_expr, list(_conds))
        ],
    )

    class _FakeOutput:
        def getSize(self):
            return 4

    class _FakeLeaf:
        def getDef(self):
            return None

    class _FakeIndirectDef:
        def getMnemonic(self):
            return "INDIRECT"

        def getNumInputs(self):
            return 1

        def getInput(self, index):
            return _FakeLeaf()

    class _FakeInput:
        def getDef(self):
            return _FakeIndirectDef()

    class _FakeOp:
        def getMnemonic(self):
            return "INT_ADD"

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            return _FakeInput()

        def getOutput(self):
            return _FakeOutput()

    result = expander._expand_operation(_FakeOp(), [], depth=0)

    assert len(result) == 1
    assert result[0].value == post_state_expr


def test_expand_expression_cases_preserves_post_state_object_graph_without_recursive_split():
    expander = ExpressionExpander(Mock(), Mock(), debug=False)
    expr = Expression.binary_op(
        "INT_ADD",
        Expression.variable(
            "poststate_stackframe_tail_n32_size_4",
            size=4,
            runtime_ref=PostStateReadRef(
                location=CanonicalLocation(
                    base_ref=LocationBaseRef.stack_frame(),
                    offset=-32,
                    size=4,
                )
            ),
        ),
        Expression.constant(1, 4),
    )

    result = expander._expand_expression_cases(expr, [], depth=0)

    assert len(result) == 1
    assert result[0].value == expr


def test_operation_shortcut_detects_indirect_op_itself_without_recursive_input_markers():
    expander = ExpressionExpander(Mock(), Mock(), debug=False)

    class _FakeLeaf:
        def getDef(self):
            return None

    class _FakeIndirectOp:
        def getMnemonic(self):
            return "INDIRECT"

        def getNumInputs(self):
            return 2

        def getInput(self, index):
            return _FakeLeaf()

    assert expander._operation_may_benefit_from_whole_object_shortcut(_FakeIndirectOp())

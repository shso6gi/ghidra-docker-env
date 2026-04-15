# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.model import Expression
from scripts.function_tracer_pcode.transform.rewrite.rules.normalization import (
    CommutativeNormalizationRule,
)


def test_commutative_normalization_uses_object_keys_when_structural_key_fails(monkeypatch):
    rule = CommutativeNormalizationRule()
    left = Expression.parameter("b", index=1, size=4)
    right = Expression.parameter("a", index=0, size=4)
    expr = Expression.binary_op("INT_ADD", left, right)
    expr.size = 4

    def _boom_structural(*_args, **_kwargs):
        raise AssertionError("normalization should not require Expression.structural_key")

    def _boom_to_smt(*_args, **_kwargs):
        raise AssertionError("normalization should not require Expression.to_smt")

    def _boom_to_string(*_args, **_kwargs):
        raise AssertionError("normalization should not require Expression.to_string")

    monkeypatch.setattr(Expression, "structural_key", _boom_structural)
    monkeypatch.setattr(Expression, "to_smt", _boom_to_smt)
    monkeypatch.setattr(Expression, "to_string", _boom_to_string)

    normalized = rule.apply(expr)

    assert normalized is not expr
    assert normalized.operator == "INT_ADD"
    assert normalized.operands[0].name == "a"
    assert normalized.operands[1].name == "b"

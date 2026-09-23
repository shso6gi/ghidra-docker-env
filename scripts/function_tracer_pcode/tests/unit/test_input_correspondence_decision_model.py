# -*- coding: utf-8 -*-
"""Issue #167: production の final relation を独立な判定表（v5 §4.5）と突き合わせる。

``tests/fixtures/issue167/decision_model.py`` は repo を import しない再実装。ここでは
その入力（幅・IEE・raw の読み幅）を実際の analysis と validator 済み合成 IEE に写し、
``build_input_correspondence_set`` の結果（relation と、側ごとに入力仮定を使ってよい
書き換え規則）と全組合せで一致することを確かめる。
"""

from __future__ import annotations

import itertools

import pytest

from scripts.function_tracer_pcode.core import Condition, Expression, ExpressionType, ReturnInfo
from scripts.function_tracer_pcode.proof.formula import input_correspondence as ic
from scripts.function_tracer_pcode.proof.formula.input_correspondence import evidence as iee_contract
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    AbiExtensionRule,
    StorageObservation,
    TrustedParameterClassification,
    build_input_correspondence_set,
    validate_input_extension_evidence,
)
from scripts.function_tracer_pcode.semantics.rewrite_contract import ExtensionKind
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis
from scripts.function_tracer_pcode.tests.fixtures.issue167 import decision_model as model


def _use(width: int, demand):
    x = Expression(ExpressionType.PARAMETER, name="x", value=0, size=width // 8)
    if demand is None:
        read = x
    else:
        read = Expression(
            ExpressionType.BINARY_OP, operator="SUBPIECE",
            operands=[x, Expression(ExpressionType.CONSTANT, value=0, size=8)], size=demand // 8,
        )
    zero = Expression(ExpressionType.CONSTANT, value=0, size=read.size)
    return Expression(ExpressionType.BINARY_OP, operator="INT_EQUAL", operands=[read, zero], size=1)


def _analysis(side: model.Side, binary_id: str):
    analysis = create_mock_analysis(
        "f",
        parameters=[{"name": "x", "index": 0, "size": side.width // 8, "data_type": "long", "is_signed": True}],
        returns=[ReturnInfo(address="0x1000", conditions=[Condition(_use(side.width, side.demand))],
                            value=Expression(ExpressionType.CONSTANT, value=0, size=4))],
    )
    analysis.binary_id = binary_id
    evidence = ()
    if side.iee is not None:
        logical, kind_name = side.iee
        kind = ExtensionKind.SIGN if kind_name == "sign" else ExtensionKind.ZERO
        binding = ic.analysis_parameter_binding(analysis, 0)
        rule = AbiExtensionRule("synthetic", binding.binary_id, "register", side.width, logical, None, kind, "test")
        classification = TrustedParameterClassification(
            binding, logical, kind is ExtensionKind.SIGN, "int", "synthetic", "0" * 64,
            _factory_token=iee_contract._TRUSTED_CLASSIFICATION_TOKEN,
        )
        storage = StorageObservation(binding, "r0", "register", 0, side.width, side.width)
        iee, reasons = validate_input_extension_evidence(rule, classification, storage)
        assert reasons == ()
        evidence = (iee,)
    return analysis, evidence


def _production(left, right):
    left_analysis, left_iee = _analysis(left, "L")
    right_analysis, right_iee = _analysis(right, "R")
    relation_set = build_input_correspondence_set(
        left_analysis, right_analysis, input_extension_evidence=left_iee + right_iee
    )
    (item,) = relation_set.correspondences
    entailed = tuple(
        (side, assumption.narrow_bits, assumption.kind.value) for side, assumption in item.entailed
    )
    relation = model.Relation(item.kind.value, item.rule, item.tie_bits, entailed, item.decisive_sufficient)
    # 片側で入力仮定を使ってよい規則（parameter は index 0 だけ）。
    permitted = {
        side: tuple(rule for rule, index in relation_set.authorization(side).permitted_rules() if index == 0)
        for side in (ic.LEFT, ic.RIGHT)
    }
    return relation, permitted


def _sides():
    for width in (32, 64):
        for demand in (16, 32, None):
            if demand is not None and demand > width:
                continue
            for iee in (None, (32, "sign"), (32, "zero"), (16, "sign")):
                if iee is not None and iee[0] >= width:
                    continue
                yield model.Side(width, iee, demand)


SIDES = tuple(_sides())


@pytest.mark.parametrize(("left", "right"), list(itertools.product(SIDES, SIDES)))
def test_production_relation_matches_the_independent_decision_model(left, right):
    relation, permitted = _production(left, right)
    expected = model.decide(left, right)
    assert relation == expected
    # rule 単位の許可も独立 model と一致する（required(rule) ⊆ entailed(final)）。
    for side in (ic.LEFT, ic.RIGHT):
        assert permitted[side] == model.permitted_rules(expected, side), side


def test_the_rule_table_and_the_model_agree_on_assumption_consuming_rules():
    from scripts.function_tracer_pcode.semantics.rewrite_contract import REWRITE_RULES

    production = {
        name: tuple(sorted(kind.value for kind in rule.image_kinds))
        for name, rule in REWRITE_RULES.items()
        if rule.consumes_input_extension
    }
    assert production == {name: tuple(sorted(kinds)) for name, kinds in model.ASSUMPTION_CONSUMING_RULES.items()}


def test_decision_model_v4_cases_hold():
    assert model.main() == 0

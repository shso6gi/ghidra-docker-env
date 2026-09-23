# -*- coding: utf-8 -*-
"""Issue #167: semantic-width 書き換えの契約（rule 表・authorization・書き換え済みの印）。

* 入力仮定を使えるのは rule 表で ``consumes_input_extension`` の規則だけで、仮定は
  ``RewriteAuthorization.grant`` からだけ受け取る（``required(rule) ⊆ entailed(final)``）。
* normalizer は表に無い規則を適用できない。
* 書き換え結果（normalize / 出力面の揃え）から最終 relation は作れない。
* FormulaBuilder は relation を作らず、渡された最終 relation だけを使う。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.core import Expression, ExpressionType, ReturnInfo
from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    RawAnalysisRequiredError,
    build_input_correspondence_set,
)
from scripts.function_tracer_pcode.semantics.rewrite_contract import (
    EMPTY_REWRITE_AUTHORIZATION,
    REWRITE_RULES,
    ExtensionKind,
    RewriteAssumption,
    RewriteAuthorization,
    RewriteRule,
    is_rewritten_surface,
)
from scripts.function_tracer_pcode.semantics.semantic_width import (
    SemanticWidthNormalizer,
    align_return_value_extension_surfaces,
    normalize_analysis_semantic_width,
)
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


SIGN32 = RewriteAssumption(0, 64, 32, ExtensionKind.SIGN)
ZERO32 = RewriteAssumption(0, 64, 32, ExtensionKind.ZERO)


def test_identity_rules_never_receive_an_input_assumption():
    authorization = RewriteAuthorization((SIGN32,))
    for name, rule in REWRITE_RULES.items():
        if not rule.consumes_input_extension:
            assert rule.image_kinds == frozenset(), name
            assert authorization.grant(name, 0, 64) is None, name


def test_grant_requires_the_same_parameter_width_and_a_kind_the_rule_preserves():
    authorization = RewriteAuthorization((SIGN32,))
    assert authorization.grant("signed_order_on_sign_extension_images", 0, 64) is SIGN32
    assert authorization.grant("equality_on_extension_images", 0, 64) is SIGN32
    # zext の順序規則は sext 像に使えない。
    assert authorization.grant("unsigned_order_on_zero_extension_images", 0, 64) is None
    # 別の parameter・別の幅には効かない。
    assert authorization.grant("signed_order_on_sign_extension_images", 1, 64) is None
    assert authorization.grant("signed_order_on_sign_extension_images", 0, 32) is None
    assert EMPTY_REWRITE_AUTHORIZATION.grant("equality_on_extension_images", 0, 64) is None

    zero = RewriteAuthorization((ZERO32,))
    assert zero.permitted_rules() == (
        ("equality_on_extension_images", 0),
        ("unsigned_order_on_zero_extension_images", 0),
    )


def test_unknown_rules_are_programming_errors():
    with pytest.raises(ValueError, match="unknown semantic-width rewrite rule"):
        EMPTY_REWRITE_AUTHORIZATION.grant("subpiece_of_division_on_extension_images", 0, 64)
    normalizer = SemanticWidthNormalizer({}, EMPTY_REWRITE_AUTHORIZATION)
    with pytest.raises(ValueError, match="unknown semantic-width rewrite rule"):
        normalizer._rewritten("bare_arithmetic_narrowing", Expression(ExpressionType.CONSTANT, value=0, size=4))


def test_a_rule_that_consumes_an_assumption_must_name_its_image_kinds():
    with pytest.raises(ValueError):
        RewriteRule("consumes_without_kinds", consumes_input_extension=True)


def test_the_authorization_digest_binds_the_rule_table():
    """rule 表の契約が変われば NormalizationCertificate の入力も変わる。"""

    from scripts.function_tracer_pcode.proof.call_effect import preflight

    assert any(
        version.startswith("semantic_width_normalizer_v3:") for version in preflight._NORMALIZATION_RULE_VERSIONS
    )
    assert RewriteAuthorization((SIGN32,)).digest != RewriteAuthorization((ZERO32,)).digest


def _rewritable(name):
    """``x == 0``（定数だけ 32 bit）: comparison_zero_constant_width が必ず書き換える。"""

    x = Expression(ExpressionType.PARAMETER, name="x", value=0, size=8)
    zero = Expression(ExpressionType.CONSTANT, value=0, size=4)
    value = Expression(ExpressionType.BINARY_OP, operator="INT_EQUAL", operands=[x, zero], size=1)
    return create_mock_analysis(
        name,
        return_type="bool",
        parameters=[{"name": "x", "index": 0, "size": 8, "data_type": "long", "is_signed": True}],
        returns=[ReturnInfo(address="0x1000", conditions=[], value=value)],
    )


def test_the_relation_producer_refuses_a_rewritten_surface():
    raw1, raw2 = _rewritable("f"), _rewritable("g")
    build_input_correspondence_set(raw1, raw2)  # raw は受け付ける
    normalized = normalize_analysis_semantic_width(raw1)
    assert normalized is not raw1 and is_rewritten_surface(normalized)
    assert not is_rewritten_surface(raw1)
    with pytest.raises(RawAnalysisRequiredError):
        build_input_correspondence_set(normalized, raw2)
    with pytest.raises(RawAnalysisRequiredError):
        build_input_correspondence_set(raw1, normalized)


def test_aligned_return_surfaces_are_marked_only_when_they_change():
    raw1, raw2 = _rewritable("f"), _rewritable("g")
    aligned1, aligned2 = align_return_value_extension_surfaces(raw1, raw2)
    for raw, aligned in ((raw1, aligned1), (raw2, aligned2)):
        assert is_rewritten_surface(aligned) is (aligned is not raw)


@pytest.mark.parametrize("method", ["build_base_context", "build_equivalence_formula_extended"])
def test_the_formula_builder_does_not_make_a_relation(method):
    raw1, raw2 = _rewritable("f"), _rewritable("g")
    builder = FormulaBuilder(debug=False)
    with pytest.raises(TypeError):
        getattr(builder, method)(raw1, raw2)
    with pytest.raises(TypeError, match="final InputCorrespondenceSet"):
        getattr(builder, method)(raw1, raw2, input_correspondence=None)
    getattr(builder, method)(raw1, raw2, input_correspondence=build_input_correspondence_set(raw1, raw2))

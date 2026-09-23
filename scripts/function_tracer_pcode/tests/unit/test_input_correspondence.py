# -*- coding: utf-8 -*-
"""Issue #167: 最終 InputCorrespondence（premise / authorization / decisive 十分性）。

v5 §4.11 の各項目を、修正前に落ちる形で固定する。SMT の判定は実 production の
normalizer・FormulaBuilder・SMT lowering の出力を z3 に解かせる（手書きの理想式は
使わない）。合成 IEE を使う test は consumer test で、production provider は
IEE を発行しない（``test_input_extension_provider_*``）。
"""

from __future__ import annotations

from typing import Any, Dict, List

import pytest
import z3

from scripts.function_tracer_pcode.checker.arch.input_extension import (
    explain_input_extension_evidence,
    provide_input_extension_evidence,
)
from scripts.function_tracer_pcode.core import (
    CanonicalLocation,
    Condition,
    Expression,
    ExpressionType,
    LocationBaseRef,
    ReturnInfo,
    StorageInfo,
)
from scripts.function_tracer_pcode.analysis.effects.models import (
    CallArgumentEvidence,
    EffectSummary,
    StoreEffect,
    UnsupportedCallEffectRef,
)
from scripts.function_tracer_pcode.proof.formula import input_correspondence as ic
from scripts.function_tracer_pcode.proof.formula.input_correspondence import evidence as iee_contract
from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder
from scripts.function_tracer_pcode.proof.formula.input_correspondence import (
    AbiExtensionRule,
    InputCorrespondenceStatus,
    InputRelationKind,
    ParameterBinding,
    StorageObservation,
    TrustedParameterClassification,
    build_input_correspondence_set,
    validate_input_extension_evidence,
)
from scripts.function_tracer_pcode.semantics.param_semantics import infer_parameter_semantics
from scripts.function_tracer_pcode.semantics.projection_closure import (
    scan_parameter_demand,
    scan_projection_closure,
)
from scripts.function_tracer_pcode.semantics.rewrite_contract import ExtensionKind
from scripts.function_tracer_pcode.semantics.semantic_width import normalize_analysis_semantic_width
from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis


# ---------------------------------------------------------------------------
# builders
# ---------------------------------------------------------------------------


def _param(name: str, size: int, index: int = 0, storage_info=None) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, value=index, size=size, storage_info=storage_info)


def _const(value: int, size: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=size)


def _bin(op: str, left: Expression, right: Expression, size: int) -> Expression:
    return Expression(ExpressionType.BINARY_OP, operator=op, operands=[left, right], size=size)


def _un(op: str, operand: Expression, size: int) -> Expression:
    return Expression(ExpressionType.UNARY_OP, operator=op, operands=[operand], size=size)


def _low(expr: Expression, size: int) -> Expression:
    return _bin("SUBPIECE", expr, _const(0, 8), size)


def _ret(value: Expression, *conditions: Expression, negated: bool = False) -> ReturnInfo:
    return ReturnInfo(address="0x1000", conditions=[Condition(c, negated) for c in conditions], value=value)


def _desc(name: str, size: int, index: int = 0, data_type: str = None, **extra) -> Dict[str, Any]:
    data_type = data_type or {8: "long", 4: "int", 2: "short", 1: "char"}[size]
    return {"name": name, "index": index, "size": size, "data_type": data_type, "is_signed": True, **extra}


def _analysis(name: str, params: List[Dict[str, Any]], returns: List[ReturnInfo], return_type: str = "int", **extra):
    analysis = create_mock_analysis(name, return_type=return_type, parameters=params, returns=returns)
    for key, value in extra.items():
        setattr(analysis, key, value)
    return analysis


def _bound(analysis, index: int = 0) -> ParameterBinding:
    binding = ic.analysis_parameter_binding(analysis, index)
    assert binding is not None
    return binding


def _synthetic_iee(analysis, index: int, *, logical_bits: int, storage_bits: int, kind: ExtensionKind):
    """consumer test 用の合成 IEE（validator を通す。production にこの出所は無い）。"""

    binding = _bound(analysis, index)
    rule = AbiExtensionRule(
        abi_id="synthetic-test-abi",
        binary_id=binding.binary_id,
        register_class="register",
        storage_bits=storage_bits,
        logical_bits=logical_bits,
        is_signed=None,
        kind=kind,
        source_reference="test fixture",
    )
    classification = TrustedParameterClassification(
        binding, logical_bits, kind is ExtensionKind.SIGN, "int",
        "synthetic_test_signature", "0" * 64,
        _factory_token=iee_contract._TRUSTED_CLASSIFICATION_TOKEN,
    )
    storage = StorageObservation(binding, "r0", "register", 0, storage_bits, storage_bits)
    evidence, reasons = validate_input_extension_evidence(rule, classification, storage)
    assert reasons == ()
    return evidence


def _with_binary(analysis, binary_id: str = "B1"):
    analysis.binary_id = binary_id
    return analysis


def _sat(formula: str) -> z3.CheckSatResult:
    solver = z3.Solver()
    body = "\n".join(
        line for line in formula.splitlines()
        if line.strip() not in {"(check-sat)", "(get-model)"}
    )
    solver.from_string(body)
    return solver.check()


def _monolithic(left, right, **kwargs) -> z3.CheckSatResult:
    kwargs.setdefault("input_correspondence", build_input_correspondence_set(left, right))
    formula = FormulaBuilder(debug=False).build_equivalence_formula_extended(left, right, **kwargs).formula
    return _sat(formula)


# ---------------------------------------------------------------------------
# §4.11-1 / 2 / 8: W1, W6, W3
# ---------------------------------------------------------------------------


def test_cross_use_hint_does_not_narrow_a_full_width_use():
    """W1: 同じ x の 32 bit use（hint の出所）が 64 bit の ``x == 0`` を狭めない。"""

    x = _param("x", 8)
    use_a = _bin("INT_EQUAL", _low(x, 4), _const(5, 4), 1)
    use_b = _bin("INT_EQUAL", x, _const(0, 8), 1)
    analysis = _analysis("f", [_desc("x", 8)], [_ret(_const(1, 4), use_a), _ret(_const(2, 4), use_b)])
    assert infer_parameter_semantics(analysis)[0].narrow_bits == 32

    normalized = normalize_analysis_semantic_width(analysis, infer_parameter_semantics(analysis))

    assert normalized.returns[1].conditions[0].expression.to_smt() == "(= x (_ bv0 64))"


def _w6_pair():
    def build(wide_compare: bool):
        x = _param("x", 8)
        guard = _bin("INT_EQUAL", _low(x, 4), _const(0x7FFFFFFF, 4), 1)
        compared = _bin("INT_EQUAL", x, _const(0, 8), 1) if wide_compare else _bin(
            "INT_EQUAL", _low(x, 4), _const(0, 4), 1
        )
        analysis = _analysis(
            "f",
            [_desc("x", 8)],
            [_ret(_const(7, 4), guard), _ret(_un("INT_ZEXT", compared, 4), guard, negated=True)],
        )
        return analysis

    return build(True), build(False)


def test_w6_pre_normalization_high_bit_dependency_is_not_equivalent():
    """W6: ``x == 0``（64 bit）と ``(int)x == 0`` は x = 1<<32 で異なる。修正前は UNSAT。"""

    left, right = _w6_pair()
    assert _monolithic(left, right) == z3.sat


def test_w3_identical_function_is_not_separated_by_upper_bits():
    """W3: 同じ関数同士で、tie が hint で狭まり上位 bit だけ違う model を許さない。"""

    def build():
        x = _param("x", 8)
        guard = _bin("INT_EQUAL", _low(x, 4), _const(5, 4), 1)
        return _analysis(
            "g", [_desc("x", 8)], [_ret(_const(0, 8), guard), _ret(x, guard, negated=True)], return_type="long"
        )

    left, right = build(), build()
    correspondence = build_input_correspondence_set(left, right)
    (item,) = correspondence.correspondences
    assert item.kind is InputRelationKind.FULL_REGISTER_EQUALITY
    assert _monolithic(left, right) == z3.unsat


# ---------------------------------------------------------------------------
# §4.11-3 / 4 / 10 / 14 / 15: synthetic IEE consumers and fallback
# ---------------------------------------------------------------------------


def _extension_pair(left_bits: int, right_bits: int, *, left_use=None, right_use=None):
    left_x = _param("x", left_bits // 8)
    right_x = _param("x", right_bits // 8)
    left = _with_binary(_analysis(
        "f", [_desc("x", left_bits // 8)],
        [_ret(_un("INT_ZEXT", (left_use or (lambda p: _bin("INT_SLESS", p, _const(5, left_bits // 8), 1)))(left_x), 4))],
    ), "B1")
    right = _with_binary(_analysis(
        "f", [_desc("x", right_bits // 8)],
        [_ret(_un("INT_ZEXT", (right_use or (lambda p: _bin("INT_SLESS", p, _const(5, right_bits // 8), 1)))(right_x), 4))],
    ), "B2")
    return left, right


def test_synthetic_sign_iee_yields_extension_bound_and_enables_sign_rules():
    """§4.11-3: 合成 IEE(SIGN, 32) + 他側 32 bit → EXTENSION_BOUND、sign 規則が有効。"""

    left, right = _extension_pair(64, 32)
    iee = _synthetic_iee(left, 0, logical_bits=32, storage_bits=64, kind=ExtensionKind.SIGN)

    correspondence = build_input_correspondence_set(left, right, input_extension_evidence=(iee,))
    (item,) = correspondence.correspondences
    assert (item.kind, item.rule, item.tie_bits) == (InputRelationKind.EXTENSION_BOUND, "R2", 32)
    assert [side for side, _ in item.entailed] == ["left"]
    lines = "\n".join(correspondence.premise_lines(*_infos(left, right)))
    assert "(assert (= x_1 ((_ sign_extend 32) ((_ extract 31 0) x_1))))" in lines
    assert "(assert (= ((_ extract 31 0) x_1) x_2))" in lines

    normalized = normalize_analysis_semantic_width(
        left, authorization=correspondence.authorization(ic.LEFT)
    )
    assert "(bvslt ((_ extract 31 0) x) (_ bv5 32))" in normalized.returns[0].value.to_smt()


def test_synthetic_zero_iee_enables_only_zero_rules():
    """§4.11-4: 合成 IEE(ZERO, 32) → EXTENSION_BOUND、unsigned 比較だけ狭まる。"""

    left, right = _extension_pair(
        64, 32,
        left_use=lambda p: _bin("INT_LESS", p, _const(5, 8), 1),
        right_use=lambda p: _bin("INT_LESS", p, _const(5, 4), 1),
    )
    iee = _synthetic_iee(left, 0, logical_bits=32, storage_bits=64, kind=ExtensionKind.ZERO)
    correspondence = build_input_correspondence_set(left, right, input_extension_evidence=(iee,))
    lines = "\n".join(correspondence.premise_lines(*_infos(left, right)))
    assert "zero_extend 32" in lines

    authorization = correspondence.authorization(ic.LEFT)
    unsigned = normalize_analysis_semantic_width(left, authorization=authorization)
    assert "(bvult ((_ extract 31 0) x) (_ bv5 32))" in unsigned.returns[0].value.to_smt()

    signed_left, _ = _extension_pair(64, 32)
    signed = normalize_analysis_semantic_width(signed_left, authorization=authorization)
    assert "(bvslt x (_ bv5 64))" in signed.returns[0].value.to_smt()


def _infos(left, right):
    from scripts.function_tracer_pcode.proof.formula.params import collect_param_info

    return collect_param_info(left.parameters, "_1"), collect_param_info(right.parameters, "_2")


def test_fallback_to_full_equality_drops_extension_and_its_rewrites():
    """§4.11-14: left IEE32 / right 無し、両側 64 bit → FULL。前提も書き換えも消える。"""

    left, right = _extension_pair(64, 64)
    iee = _synthetic_iee(left, 0, logical_bits=32, storage_bits=64, kind=ExtensionKind.SIGN)
    correspondence = build_input_correspondence_set(left, right, input_extension_evidence=(iee,))
    (item,) = correspondence.correspondences
    assert item.kind is InputRelationKind.FULL_REGISTER_EQUALITY
    assert item.entailed == ()
    assert correspondence.authorization(ic.LEFT).assumptions == ()
    lines = "\n".join(correspondence.premise_lines(*_infos(left, right)))
    assert "_extend" not in lines

    normalized = normalize_analysis_semantic_width(
        left, authorization=correspondence.authorization(ic.LEFT)
    )
    assert normalized.returns[0].value.to_smt() == left.returns[0].value.to_smt()


def test_iee32_against_iee16_is_not_an_extension_bound():
    """§4.11-15: logical 幅が違う IEE 同士は R1 にならず、どちらの比較も狭まらない。"""

    left, right = _extension_pair(64, 64)
    left_iee = _synthetic_iee(left, 0, logical_bits=32, storage_bits=64, kind=ExtensionKind.SIGN)
    right_iee = _synthetic_iee(right, 0, logical_bits=16, storage_bits=64, kind=ExtensionKind.SIGN)
    correspondence = build_input_correspondence_set(
        left, right, input_extension_evidence=(left_iee, right_iee)
    )
    (item,) = correspondence.correspondences
    assert item.kind is InputRelationKind.FULL_REGISTER_EQUALITY
    assert correspondence.authorization(ic.LEFT).assumptions == ()
    assert correspondence.authorization(ic.RIGHT).assumptions == ()


def test_mixed_sign_and_zero_iee_premise_keeps_the_top_bit_value():
    """§4.11-10 (C3): 左 sign / 右 zero の R1 で、下位 32 bit = 0x80000000 が premise を満たす。

    修正前は hint 由来の自己整合制約が両側に別種の ext を課し、この入力を除外した。
    """

    left, right = _extension_pair(64, 64)
    left_iee = _synthetic_iee(left, 0, logical_bits=32, storage_bits=64, kind=ExtensionKind.SIGN)
    right_iee = _synthetic_iee(right, 0, logical_bits=32, storage_bits=64, kind=ExtensionKind.ZERO)
    correspondence = build_input_correspondence_set(
        left, right, input_extension_evidence=(left_iee, right_iee)
    )
    (item,) = correspondence.correspondences
    assert (item.kind, item.rule) == (InputRelationKind.EXTENSION_BOUND, "R1")
    premise = "\n".join(line for line in correspondence.premise_lines(*_infos(left, right)) if line.startswith("(assert"))
    formula = (
        "(declare-const x_1 (_ BitVec 64))\n(declare-const x_2 (_ BitVec 64))\n"
        + premise
        + "\n(assert (= ((_ extract 31 0) x_1) #x80000000))\n"
    )
    assert _sat(formula) == z3.sat


def test_output_observation_alone_is_not_input_extension_evidence():
    """§4.11-5: 幅の違う pair で IEE が無ければ WIDTH_OVERLAP。wide 未 closure は不十分。"""

    left = _analysis("f", [_desc("x", 4)], [_ret(_param("x", 4))])
    right = _analysis("f", [_desc("x", 8)], [_ret(_low(_param("x", 8), 4), _bin("INT_SLESS", _param("x", 8), _const(0, 8), 1))])
    assert provide_input_extension_evidence(left, right) == ()

    correspondence = build_input_correspondence_set(left, right)
    (item,) = correspondence.correspondences
    assert item.kind is InputRelationKind.WIDTH_OVERLAP
    assert item.entailed == ()
    assert not item.decisive_sufficient
    assert any("wide_side_not_closed:right@32" in ref for ref in correspondence.insufficiency_evidence())


# ---------------------------------------------------------------------------
# P1〜P10: production provider negatives
# ---------------------------------------------------------------------------


def _mips_register(name: str, size_bits: int, *, offset_bits: int = 0, base_bits: int = 64):
    return {
        "is_register": True, "space_name": "register", "offset": 0x20,
        "size": size_bits // 8, "size_bits": size_bits, "register_name": name,
        "base_register_name": name.split("_")[0], "base_register_size_bits": base_bits,
        "bit_offset_in_base": offset_bits,
    }


@pytest.mark.parametrize(
    ("label", "descriptor"),
    [
        ("P1_long8", _desc("x", 8, data_type="long", storage=_mips_register("a0", 64))),
        ("P2_ulong8", _desc("x", 8, data_type="ulong", storage=_mips_register("a0", 64))),
        ("P3_pointer", _desc("x", 8, data_type="int *", storage=_mips_register("a0", 64))),
        ("P4_undefined8", _desc("x", 8, data_type="undefined8", storage=_mips_register("a0", 64))),
        ("P5_synthetic", _desc("x", 8, data_type="long", synthetic_recursive_summary=True)),
        ("P6_storage_only", {"name": "x", "index": 0, "size": 8, "storage": _mips_register("a0", 64)}),
        ("P7_inferred_int4_storage64", _desc("x", 4, data_type="int", storage=_mips_register("a0", 64))),
        ("P8_int4_storage32", _desc("x", 4, data_type="int", storage=_mips_register("a0_lo", 32))),
        ("P9_abi_unknown_arm64", _desc("x", 4, data_type="int", storage=_mips_register("w0", 32))),
    ],
)
def test_input_extension_provider_issues_no_evidence_without_trusted_signature(label, descriptor):
    """P1〜P9: Ghidra の推論型・storage・arch だけでは IEE を発行しない（v5 §4.4）。"""

    analysis = _with_binary(_analysis("f", [descriptor], [_ret(_const(0, 4))]))
    decisions = explain_input_extension_evidence(analysis)

    assert provide_input_extension_evidence(analysis) == ()
    assert len(decisions) == 1
    evidence, refusal = decisions[0]
    assert evidence is None, label
    assert "trusted_signature_source_unavailable" in refusal.reasons
    assert "abi_identity_unverified" in refusal.reasons


def test_iee_validator_rejects_mismatched_identity_and_untrusted_parts():
    """P10: 3 命題が別の parameter / binary を指す、または信頼されない型は IEE にならない。"""

    analysis = _with_binary(_analysis("f", [_desc("x", 8), _desc("y", 8, index=1)], [_ret(_const(0, 4))]))
    binding0 = _bound(analysis, 0)
    binding1 = _bound(analysis, 1)
    rule = AbiExtensionRule("abi", binding0.binary_id, "register", 64, 32, None, ExtensionKind.SIGN, "ref")
    classification = TrustedParameterClassification(
        binding0, 32, True, "int", "kind", "d" * 64, _factory_token=iee_contract._TRUSTED_CLASSIFICATION_TOKEN
    )
    storage_other = StorageObservation(binding1, "a1", "register", 0, 64, 64)
    storage_ok = StorageObservation(binding0, "a0", "register", 0, 64, 64)

    assert validate_input_extension_evidence(rule, classification, storage_other)[1] == (
        "classification_storage_binding_mismatch",
    )
    wrong_binary = AbiExtensionRule("abi", "B9", "register", 64, 32, None, ExtensionKind.SIGN, "ref")
    assert "abi_rule_binary_mismatch" in validate_input_extension_evidence(wrong_binary, classification, storage_ok)[1]
    long_classification = TrustedParameterClassification(
        binding0, 64, True, "int", "kind", "d" * 64, _factory_token=iee_contract._TRUSTED_CLASSIFICATION_TOKEN
    )
    assert "no_extension_between_logical_and_storage" in validate_input_extension_evidence(
        rule, long_classification, storage_ok
    )[1]
    pointer = TrustedParameterClassification(
        binding0, 32, True, "pointer", "kind", "d" * 64, _factory_token=iee_contract._TRUSTED_CLASSIFICATION_TOKEN
    )
    assert "classification_not_integral" in validate_input_extension_evidence(rule, pointer, storage_ok)[1]
    with pytest.raises(ValueError):
        TrustedParameterClassification(binding0, 32, True, "int", "ghidra_inferred", "d" * 64)
    with pytest.raises(ValueError):
        ic.InputExtensionEvidence(binding0, 32, 64, ExtensionKind.SIGN, "abi", "d", "a0")


def test_iee_is_ignored_when_it_is_bound_to_another_analysis():
    """P10: 別 binary の IEE は relation に使われない（binding の照合）。"""

    left, right = _extension_pair(64, 32)
    foreign = _with_binary(_analysis("f", [_desc("x", 8)], [_ret(_const(0, 4))]), "OTHER")
    iee = _synthetic_iee(foreign, 0, logical_bits=32, storage_bits=64, kind=ExtensionKind.SIGN)
    correspondence = build_input_correspondence_set(left, right, input_extension_evidence=(iee,))
    (item,) = correspondence.correspondences
    assert item.kind is InputRelationKind.WIDTH_OVERLAP
    assert item.entailed == ()


# ---------------------------------------------------------------------------
# §4.11-7 / 17: closure witnesses per surface
# ---------------------------------------------------------------------------


def _closure(analysis, bits: int = 32, index: int = 0, width: int = 64):
    return scan_projection_closure(analysis, index, width, bits)


def _witness(closure, surface: str, reason: str) -> bool:
    return any(item.surface == surface and item.reason == reason for item in closure.witnesses)


def test_closure_witness_on_path_condition():
    x = _param("x", 8)
    analysis = _analysis("f", [_desc("x", 8)], [_ret(_low(x, 4), _bin("INT_SLESS", x, _const(0, 8), 1))])
    closure = _closure(analysis)
    assert not closure.closed
    assert _witness(closure, "path_condition", "bare_parameter")


def test_closure_witness_on_return_value_and_closed_low_extract():
    x = _param("x", 8)
    closed = _closure(_analysis("f", [_desc("x", 8)], [_ret(_low(x, 4))]))
    assert closed.closed
    opened = _closure(_analysis("f", [_desc("x", 8)], [_ret(x)], return_type="long"))
    assert _witness(opened, "return_value", "bare_parameter")


def test_closure_witnesses_on_visible_store_value_condition_and_destination():
    x = _param("x", 8)
    low_x = _low(x, 4)
    global_loc = CanonicalLocation(base_ref=LocationBaseRef.stack_frame(), offset=8, size=4)
    param_loc = CanonicalLocation(base_ref=LocationBaseRef.parameter("x", index=0), offset=0, size=4)
    value_store = StoreEffect(location=global_loc, value=x, conditions=[], order_key=1)
    condition_store = StoreEffect(
        location=global_loc, value=low_x, conditions=[Condition(_bin("INT_EQUAL", x, _const(1, 8), 1))], order_key=2
    )
    destination_store = StoreEffect(location=param_loc, value=_const(0, 4), conditions=[], order_key=3)
    for effect, surface, reason in (
        (value_store, "store_value", "bare_parameter"),
        (condition_store, "store_condition", "bare_parameter"),
        (destination_store, "store_destination", "store_destination_parameter_base"),
    ):
        analysis = _analysis(
            "f", [_desc("x", 8)], [_ret(low_x)],
            effect_summary=EffectSummary(parameter_names=["x"], effects=[effect]),
        )
        closure = _closure(analysis)
        assert _witness(closure, surface, reason), (surface, closure.witnesses)


def test_closure_witnesses_on_call_argument_and_call_effect():
    x = _param("x", 8)
    evidence = CallArgumentEvidence(
        pcode_op_ref=("op", 1), target_ref=None, callee_param_identities=(("p", 0),),
        arguments=(x,), sources=("abi",), coverage_complete=True,
    )
    with_argument = _analysis(
        "f", [_desc("x", 8)], [_ret(_const(0, 4))],
        effect_summary=EffectSummary(parameter_names=["x"], effects=[], call_argument_evidence={("op", 1): evidence}),
    )
    assert _witness(_closure(with_argument), "call_argument", "bare_parameter")

    unsupported = UnsupportedCallEffectRef(
        pcode_op_ref=None, target_ref=None, reason="opaque", order_key=1, arguments=(_low(x, 4),),
    )
    with_call = _analysis(
        "f", [_desc("x", 8)], [_ret(_const(0, 4))],
        effect_summary=EffectSummary(parameter_names=["x"], effects=[], unsupported_call_sites=(unsupported,)),
    )
    assert _witness(_closure(with_call), "call_effect", "unsupported_call_effect")


def test_closure_witnesses_on_synthetic_expression_and_loop_summary():
    x = _param("x", 8)
    synthetic = _analysis(
        "f", [_desc("x", 8)], [_ret(_const(0, 4))],
        effect_summary=EffectSummary(parameter_names=["x"], effects=[], synthetic_expr=_bin("INT_ADD", x, _const(1, 8), 8)),
    )
    assert _witness(_closure(synthetic), "synthetic_expression", "bare_parameter")

    loop = Expression.intrinsic("COUNTED_LOOP_SUM", [_low(x, 4)], size=4, runtime_ref=object())
    looped = _analysis("f", [_desc("x", 8)], [_ret(loop)])
    assert _witness(_closure(looped), "return_value", "opaque_runtime_ref")


def test_unknown_and_opaque_nodes_do_not_close():
    x = _param("x", 8)
    unknown = Expression(ExpressionType.UNKNOWN, name="u", size=4)
    call = Expression(ExpressionType.CALL, name="g", operands=[_low(x, 4)], size=4)
    for value, reason in ((unknown, "unknown_node"), (call, "opaque_call")):
        closure = _closure(_analysis("f", [_desc("x", 8)], [_ret(value)]))
        assert _witness(closure, "return_value", reason)


def test_cyclic_expression_does_not_close():
    """閉路は公開境界でも拒否されるが、scanner 自身も skip せず witness にする。"""

    from types import SimpleNamespace

    x = _param("x", 8)
    node = _bin("INT_ADD", _low(x, 4), _const(1, 4), 4)
    node.operands[1] = node
    # ReturnInfo は構築時に閉路を拒否するので、走査器へは duck-typed に直接渡す。
    raw = SimpleNamespace(
        parameters=[_desc("x", 8)],
        returns=[SimpleNamespace(value=node, conditions=[])],
    )
    closure = _closure(raw)
    assert _witness(closure, "return_value", "cycle")


class _JInt(int):
    """JPype の ``JInt`` と同じく int の派生型（Ghidra 由来の leaf の index）。"""


def test_ghidra_int_subclass_index_is_still_the_parameter():
    """subset で見つけた fail-open の回帰: leaf の index が int 派生型で、storage の表現が
    descriptor と違っても、同じ parameter の occurrence として数える。

    修正前は ``type(value) is int`` で index を読み飛ばし、storage key の比較で
    「別 parameter」と判定して closure が空虚に成立した（SEMANTIC_PROJECTION(16)
    になり、確認済み等価の pair が NOT_EQ になった）。
    """

    leaf_storage = StorageInfo(
        is_register=True, space_name="register", offset=0x4000, size=4, size_bits=32,
        register_name="w0", base_register_name="x0", base_register_size_bits=64,
    )
    left_x = Expression(ExpressionType.PARAMETER, name="param_1", value=_JInt(0), size=4, storage_info=leaf_storage)
    right_x = Expression(ExpressionType.PARAMETER, name="param_1", value=_JInt(0), size=4)
    descriptor = _desc("param_1", 4, storage={"is_register": True, "space_name": "register", "offset": 16384,
                                              "size": 4, "size_bits": 32, "register_name": "w0"})
    left = _analysis("foo", [descriptor], [_ret(_bin("INT_MULT", left_x, _const(3, 4), 4))])
    right = _analysis("foo", [_desc("param_1", 4)], [_ret(_bin("INT_MULT", right_x, _const(3, 4), 4))])

    assert not scan_projection_closure(left, 0, 32, 16).closed
    (item,) = build_input_correspondence_set(left, right).correspondences
    assert item.kind is InputRelationKind.FULL_REGISTER_EQUALITY


def test_parameter_leaf_matches_by_name_when_index_disagrees():
    """lowering は名前で束縛するので、index が食い違っても名前が同じなら occurrence。"""

    stale = Expression(ExpressionType.PARAMETER, name="x", value=5, size=8)
    analysis = _analysis("f", [_desc("x", 8)], [_ret(_const(0, 4), _bin("INT_EQUAL", stale, _const(0, 8), 1))])
    assert _witness(_closure(analysis), "path_condition", "bare_parameter")


def test_closure_is_decided_per_width():
    x = _param("x", 8)
    analysis = _analysis("f", [_desc("x", 8)], [_ret(_low(x, 4))])
    demand = scan_parameter_demand(analysis, 0, 64)
    assert demand.closure(32).closed
    assert not demand.closure(16).closed
    assert demand.closure(16).witnesses[0].reason == "extract_outside_projection"


def test_register_alias_is_a_hidden_input_even_next_to_a_bare_use():
    """裸の occurrence があっても、同じ式の register 別名読みは隠れない。"""

    x = _param("x", 4)
    hi = Expression(ExpressionType.VARIABLE, name="in_a0_hi", size=4)
    value = _bin("INT_ADD", _bin("PIECE", hi, x, 8), _un("INT_SEXT", x, 8), 8)
    demand = scan_parameter_demand(_analysis("f", [_desc("x", 4)], [_ret(value)], return_type="long"), 0, 32)
    assert any(item.reason == "register_alias" for item in demand.hidden_inputs)


def _stack_variable(name: str, size: int) -> Expression:
    stack = StorageInfo(is_register=False, space_name="stack", offset=8, size=size)
    return Expression(ExpressionType.VARIABLE, name=name, size=size, storage_info=stack)


def test_variable_named_like_the_parameter_is_the_parameter():
    """lowering は VARIABLE を名前で parameter の symbol に束縛する。同名の VARIABLE は
    storage に関係なく parameter の全幅 occurrence（修正前は走査されず、同一関数が
    SEMANTIC_PROJECTION(32) の tie だけで比べられ、上位 bit の違いで SAT になった）。
    """

    def analysis():
        return _analysis("f", [_desc("a", 8)], [_ret(_stack_variable("a", 8))], return_type="long")

    assert _witness(_closure(analysis()), "return_value", "bare_parameter")
    left, right = analysis(), analysis()
    (item,) = build_input_correspondence_set(left, right).correspondences
    assert item.kind is InputRelationKind.FULL_REGISTER_EQUALITY
    assert _monolithic(left, right) == z3.unsat

    # 別 parameter と同名の VARIABLE は、その parameter（target の bit は読まない）。
    x = _param("x", 8)
    other = _analysis(
        "f", [_desc("x", 8), _desc("b", 8, index=1)],
        [_ret(_bin("INT_ADD", _low(x, 4), _low(_stack_variable("b", 8), 4), 4))],
    )
    assert _closure(other).closed


def test_parameter_leaf_resolving_to_no_row_is_an_unknown_hidden_input():
    """表のどの行にも解決しない PARAMETER leaf は lowering で側ごとの自由 symbol になる。
    target との対応が言えないので closure を壊し、全幅の R4 も不十分にする。
    """

    stray = Expression(ExpressionType.PARAMETER, name="y", value=5, size=8)

    def analysis():
        return _analysis("f", [_desc("x", 8)], [_ret(stray)], return_type="long")

    demand = scan_parameter_demand(analysis(), 0, 64)
    assert any(item.reason == "parameter_identity_unknown" for item in demand.witnesses)
    assert any(item.reason == "parameter_identity_unknown" for item in demand.hidden_inputs)
    relation = build_input_correspondence_set(analysis(), analysis())
    (item,) = relation.correspondences
    assert item.kind is InputRelationKind.FULL_REGISTER_EQUALITY
    assert not item.decisive_sufficient
    assert relation.status is InputCorrespondenceStatus.INSUFFICIENT

    # 表の別の行に解決する leaf は別 parameter（target の closure は壊さない）。
    x = _param("x", 8)
    other = Expression(ExpressionType.PARAMETER, name="z", value=1, size=8)
    two = _analysis(
        "f", [_desc("x", 8), _desc("z", 8, index=1)], [_ret(_bin("INT_ADD", _low(x, 4), _low(other, 4), 4))]
    )
    assert _closure(two).closed


def test_deferred_call_arguments_are_an_observed_surface():
    """展開しなかった call（再帰要約の対象）の引数も観測に入る。

    修正前は ``deferred_calls`` を走査せず、``g(x >> 32)`` の上位 bit 読みが見えずに
    closure at 32 が空虚に成立した。引数を回収しきれていない call は witness。
    """

    from scripts.function_tracer_pcode.core.analysis import DeferredCallInfo

    x = _param("x", 8)
    high = _bin("INT_RIGHT", x, _const(32, 8), 8)
    complete = DeferredCallInfo(placeholder_name="g_call", arguments=[high], call_argument_recovery_status="complete")
    analysis = _analysis("f", [_desc("x", 8)], [_ret(_low(x, 4))], deferred_calls={("g", 1): complete})
    assert _witness(_closure(analysis), "call_argument", "bare_parameter")

    closed_argument = DeferredCallInfo(
        placeholder_name="g_call", arguments=[_low(x, 4)], call_argument_recovery_status="complete"
    )
    closed = _analysis("f", [_desc("x", 8)], [_ret(_low(x, 4))], deferred_calls={("g", 1): closed_argument})
    assert _closure(closed).closed

    partial = DeferredCallInfo(placeholder_name="g_call", arguments=[_low(x, 4)])
    incomplete = _analysis("f", [_desc("x", 8)], [_ret(_low(x, 4))], deferred_calls={("g", 1): partial})
    assert _witness(_closure(incomplete), "call_argument", "call_argument_incomplete")


def _register_storage(name: str, offset: int) -> StorageInfo:
    return StorageInfo(
        is_register=True, space_name="register", offset=offset, size=8, size_bits=64,
        register_name=name, base_register_name=name, base_register_offset=offset,
        base_register_size=8, base_register_size_bits=64,
    )


def test_store_destination_through_the_parameter_register_is_a_witness():
    """``storage`` base の宛先 address は、その storage の入口値。parameter の register
    なら parameter の bit を読む（修正前は固定 base 扱いで witness を出さなかった）。
    """

    a0 = _register_storage("a0", 0x20)
    a1 = _register_storage("a1", 0x28)
    x = _param("x", 8, storage_info=a0)

    def destination(storage: StorageInfo):
        base = LocationBaseRef.storage(
            space_id=None, space_name="register", offset=storage.offset, size=8,
            storage_identity_key=storage.storage_identity_key(),
        )
        location = CanonicalLocation(base_ref=base, offset=0, size=4)
        effect = StoreEffect(location=location, value=_const(0, 4), conditions=[], order_key=1)
        return _analysis(
            "f", [_desc("x", 8, storage_info=a0)], [_ret(_low(x, 4))],
            effect_summary=EffectSummary(parameter_names=["x"], effects=[effect]),
        )

    assert _witness(_closure(destination(a0)), "store_destination", "store_destination_parameter_base")
    assert _closure(destination(a1)).closed
    unknown = LocationBaseRef.storage(space_id=None, space_name="register", offset=0x20, size=8)
    effect = StoreEffect(location=CanonicalLocation(base_ref=unknown, offset=0, size=4), value=_const(0, 4),
                         conditions=[], order_key=1)
    no_identity = _analysis(
        "f", [_desc("x", 8, storage_info=a0)], [_ret(_low(x, 4))],
        effect_summary=EffectSummary(parameter_names=["x"], effects=[effect]),
    )
    assert _witness(_closure(no_identity), "store_destination", "store_destination_alias_unknown")


def test_parameter_leaf_wider_than_its_declaration_is_a_hidden_input():
    """leaf が宣言幅（32）より広い 64 bit を読むと、上位 32 bit は parameter の外
    （register の残り）。metadata 同期は leaf を宣言幅へ縮めるので、その bit は relation
    のどの tie にも入らない。全幅の R4 も十分とは言えない（旧実装は COMPLETE にした）。
    """

    wide_leaf = _param("x", 8)
    for value in (wide_leaf, _low(wide_leaf, 4)):
        def analysis():
            return _analysis("f", [_desc("x", 4)], [_ret(value)])

        demand = scan_parameter_demand(analysis(), 0, 32)
        assert any(item.reason == "parameter_leaf_wider_than_declaration" for item in demand.hidden_inputs)
        relation = build_input_correspondence_set(analysis(), analysis())
        (item,) = relation.correspondences
        assert item.kind is InputRelationKind.FULL_REGISTER_EQUALITY
        assert not item.decisive_sufficient

    narrow_leaf = _analysis("f", [_desc("x", 4)], [_ret(_param("x", 4))])
    assert scan_parameter_demand(narrow_leaf, 0, 32).hidden_inputs == ()


def test_loop_renderer_takes_the_final_relation_instead_of_rebuilding_it():
    """loop typed renderer の analysis は prepared surface。relation を渡さなければ
    builder が拒否する（旧実装は prepared analysis から relation を作り直した）。
    """

    import inspect

    from scripts.function_tracer_pcode.proof.strategies import pairwise_query_executor

    parameters = inspect.signature(pairwise_query_executor.preflight_loop_v2_solver_query).parameters
    assert parameters["input_correspondence"].default is inspect.Parameter.empty
    source = inspect.getsource(pairwise_query_executor)
    assert "build_input_correspondence_set" not in source


def test_auxiliary_extension_needs_every_source_of_the_slot_to_entail_it():
    """補助 query の symbol は (index, 幅) が同じなら左右どちらにもなり得る。片側だけが
    含意する仮定（R2'）を他方へ持ち込まない。R2（他方は狭い幅）なら引き継ぐ。
    """

    from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
    from scripts.function_tracer_pcode.semantics.rewrite_contract import RewriteAssumption

    sign32 = RewriteAssumption(0, 64, 32, ExtensionKind.SIGN)
    left = ParameterInfo("p", "p_1", 64, 0, is_signed=True, entailed_extension=sign32)
    right_wide = ParameterInfo("p", "p_2", 64, 0, is_signed=True)
    right_wide_entailed = ParameterInfo("p", "p_2", 64, 0, is_signed=True, entailed_extension=sign32)
    right_narrow = ParameterInfo("p", "p_2", 32, 0, is_signed=True)
    extensions = PairwiseStrategy._auxiliary_entailed_extensions_by_index
    assert extensions(None, (left, right_wide)) == {}
    assert extensions(None, (left, right_wide_entailed)) == {0: sign32}
    assert extensions(None, (left, right_narrow)) == {0: sign32}


# ---------------------------------------------------------------------------
# relation set status / R3 / R4 / R0
# ---------------------------------------------------------------------------


def test_semantic_projection_requires_closure_on_both_sides():
    x_left = _param("x", 8)
    x_right = _param("x", 8)
    left = _analysis("f", [_desc("x", 8)], [_ret(_low(x_left, 4))])
    right = _analysis("f", [_desc("x", 8)], [_ret(_low(x_right, 4))])
    (item,) = build_input_correspondence_set(left, right).correspondences
    assert (item.kind, item.tie_bits) == (InputRelationKind.SEMANTIC_PROJECTION, 32)

    right_bare = _analysis("f", [_desc("x", 8)], [_ret(_low(x_right, 4), _bin("INT_EQUAL", x_right, _const(0, 8), 1))])
    (item,) = build_input_correspondence_set(left, right_bare).correspondences
    assert item.kind is InputRelationKind.FULL_REGISTER_EQUALITY
    assert item.decisive_sufficient


def test_relation_is_symmetric_under_side_swap():
    left, right = _extension_pair(64, 32)
    iee = _synthetic_iee(left, 0, logical_bits=32, storage_bits=64, kind=ExtensionKind.SIGN)
    forward = build_input_correspondence_set(left, right, input_extension_evidence=(iee,))
    backward = build_input_correspondence_set(right, left, input_extension_evidence=(iee,))
    (f_item,) = forward.correspondences
    (b_item,) = backward.correspondences
    assert (f_item.kind, f_item.rule, f_item.tie_bits) == (b_item.kind, b_item.rule, b_item.tie_bits)
    assert [side for side, _ in f_item.entailed] == ["left"]
    assert [side for side, _ in b_item.entailed] == ["right"]


def test_missing_side_and_structural_defects_are_insufficient_but_empty_is_sufficient():
    one = _analysis("f", [_desc("x", 4)], [_ret(_const(0, 4))])
    none = _analysis("f", [], [_ret(_const(0, 4))])
    missing = build_input_correspondence_set(one, none)
    assert missing.status is InputCorrespondenceStatus.INSUFFICIENT
    assert missing.correspondences[0].kind is InputRelationKind.MISSING_SIDE

    empty = build_input_correspondence_set(none, _analysis("g", [], [_ret(_const(1, 4))]))
    assert empty.status is InputCorrespondenceStatus.EMPTY
    assert empty.decisive_sufficient
    assert empty.insufficiency_evidence() == ()

    duplicated = _analysis("f", [_desc("x", 4), _desc("y", 4, index=0)], [_ret(_const(0, 4))])
    defective = build_input_correspondence_set(duplicated, duplicated)
    assert defective.status is InputCorrespondenceStatus.INSUFFICIENT
    assert any("duplicate_parameter_index" in ref for ref in defective.insufficiency_evidence())


def test_self_consistency_constraints_are_gone_from_the_header():
    """修正前は hint から ``x == sext(low32 x)`` を header に足していた。"""

    x = _param("x", 8)
    analysis = _analysis("f", [_desc("x", 8)], [_ret(_const(0, 4), _bin("INT_SLESS", _low(x, 4), _const(3, 4), 1))])
    header = FormulaBuilder(debug=False).build_base_context(analysis, analysis, input_correspondence=build_input_correspondence_set(analysis, analysis))["header_lines"]
    assert not any("_extend" in line for line in header if line.startswith("(assert"))


def test_auxiliary_symbols_do_not_inherit_hint_widths():
    """§4.11-12: 補助 query は hint ではなく entailed な extension だけを使う。"""

    from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
    from scripts.function_tracer_pcode.proof.strategies.pairwise import PairwiseStrategy
    from unittest.mock import Mock

    strategy = PairwiseStrategy(Mock(), Mock(), debug=False)
    plain = ParameterInfo("x", "x_1", 64, 0)
    assert strategy._auxiliary_entailed_extensions_by_index((plain,)) == {}
    assert ic.extension_premise_lines([plain]) == []

    left, right = _extension_pair(64, 32)
    iee = _synthetic_iee(left, 0, logical_bits=32, storage_bits=64, kind=ExtensionKind.SIGN)
    correspondence = build_input_correspondence_set(left, right, input_extension_evidence=(iee,))
    (entailed,) = correspondence.parameter_infos(ic.LEFT, "_1")
    extensions = strategy._auxiliary_entailed_extensions_by_index((entailed,))
    assert extensions[0].narrow_bits == 32
    assert ic.extension_premise_lines([entailed])[-1] == (
        "(assert (= x_1 ((_ sign_extend 32) ((_ extract 31 0) x_1))))"
    )


# ---------------------------------------------------------------------------
# preflight: raw → relation → authorization → certificate
# ---------------------------------------------------------------------------


def test_prepared_surface_carries_the_relation_bound_into_its_certificate():
    from scripts.function_tracer_pcode.proof.call_effect.preflight import (
        CallProofDecisionMode,
        StrategySourceAnalysisPair,
        prepare_solver_surface,
    )

    left, right = _extension_pair(64, 32)
    iee = _synthetic_iee(left, 0, logical_bits=32, storage_bits=64, kind=ExtensionKind.SIGN)
    source = StrategySourceAnalysisPair.create(left, right, input_extension_evidence=(iee,))
    prepared = prepare_solver_surface(
        source,
        observation_contract_digest="obs",
        comparison_session_id="s",
        branch_id="b",
        generation=1,
        decision_mode=CallProofDecisionMode.PREFLIGHT_PROJECTION,
    )
    assert prepared.input_correspondence is source.input_correspondence()
    assert prepared.certificate.input_correspondence_digest == prepared.input_correspondence.digest
    assert prepared.is_valid_for(source)
    # 左の比較は prepared surface で最終 relation の authorization の下で狭まっている。
    assert "(bvslt ((_ extract 31 0) x) (_ bv5 32))" in prepared.analysis1.returns[0].value.to_smt()

    without_iee = StrategySourceAnalysisPair.create(left, right)
    assert not prepared.is_valid_for(without_iee)

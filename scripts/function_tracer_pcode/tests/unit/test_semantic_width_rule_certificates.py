# -*- coding: utf-8 -*-
"""Issue #167: rule 表（``rewrite_contract.REWRITE_RULES``）の規則ごとの SMT certificate。

各規則について **実 production の規則**（``SemanticWidthNormalizer``）が出した式と、
**実 SMT lowering**（``Expression.to_smt``）を z3 に渡して次を確かめる（v5 §4.6）。

1. 表のその規則が実際に発火している（``applied_rules`` で規則名まで照合、非空虚）。
2. ``sort(original) == sort(rewritten)``。
3. ``premise ∧ (original != rewritten)`` が UNSAT（Bool は xor）。
4. premise 自体が SAT（空の前提で UNSAT を得る空虚さが無い）。
5. 幅・定数の境界値でも 3 が成り立ち、その境界値が premise を満たす。
6. 入力仮定を消費する規則は、最終 relation の仮定（``RewriteAuthorization``）が
   無いと発火せず、欠いたまま書き換えた式には z3 が反例を返す。

表に規則を足したら、ここに certificate を足さないと
``test_every_rule_in_the_table_has_a_certificate`` が落ちる。入力仮定を消費する
規則は ``test_every_assumption_consuming_rule_has_a_missing_assumption_negative`` も要る。
"""

from __future__ import annotations

from typing import Dict, Iterable, Optional, Sequence, Tuple

import pytest
import z3

from scripts.function_tracer_pcode.core import Expression, ExpressionType
from scripts.function_tracer_pcode.core.render_smt import (
    SMT_SEMANTICS_REFUSALS,
    expression_returns_bool,
    expression_smt_bit_width,
)
from scripts.function_tracer_pcode.core.semantic_freeze import publish
from scripts.function_tracer_pcode.proof.formula.input_correspondence import extension_assumption_line
from scripts.function_tracer_pcode.semantics.param_semantics import ParameterSemanticHint
from scripts.function_tracer_pcode.semantics.rewrite_contract import (
    EMPTY_REWRITE_AUTHORIZATION,
    REWRITE_RULES,
    ExtensionKind,
    RewriteAssumption,
    RewriteAuthorization,
)
from scripts.function_tracer_pcode.semantics.semantic_width import SemanticWidthNormalizer


# ---------------------------------------------------------------------------
# harness
# ---------------------------------------------------------------------------


def _param(name: str, size: int, index: int) -> Expression:
    return Expression(ExpressionType.PARAMETER, name=name, value=index, size=size)


def _const(value: int, size: int) -> Expression:
    return Expression(ExpressionType.CONSTANT, value=value, size=size)


def _bin(op: str, left: Expression, right: Expression, size: int) -> Expression:
    return Expression(ExpressionType.BINARY_OP, operator=op, operands=[left, right], size=size)


def _un(op: str, operand: Expression, size: int) -> Expression:
    return Expression(ExpressionType.UNARY_OP, operator=op, operands=[operand], size=size)


def _low(expr: Expression, size: int) -> Expression:
    return _bin("SUBPIECE", expr, _const(0, 8), size)


def _hints(**by_index: ParameterSemanticHint) -> Dict[Tuple[object, ...], ParameterSemanticHint]:
    return {("parameter_index", int(index[1:])): hint for index, hint in by_index.items()}


def _normalize(
    expr: Expression,
    *,
    hints: Optional[Dict[Tuple[object, ...], ParameterSemanticHint]] = None,
    authorization: RewriteAuthorization = EMPTY_REWRITE_AUTHORIZATION,
) -> Tuple[Expression, Dict[str, int]]:
    """実 normalizer の出力と、適用された規則（表の名前）。"""

    normalizer = SemanticWidthNormalizer(hints or {}, authorization)
    # production と同じく、書き換えの入力も出力も公開済みの値として扱う。
    return publish(normalizer.rewrite_expression(publish(expr))), dict(normalizer.applied_rules)


def _rewrite(expr: Expression, **kwargs) -> Expression:
    return _normalize(expr, **kwargs)[0]


def _sort(expr: Expression) -> str:
    return "Bool" if expression_returns_bool(expr) else f"BV{expression_smt_bit_width(expr)}"


def _declarations(params: Iterable[Tuple[str, int]]) -> str:
    return "".join(f"(declare-const {name} (_ BitVec {bits}))\n" for name, bits in params)


def _check(text: str) -> z3.CheckSatResult:
    solver = z3.Solver()
    solver.from_string(text)
    return solver.check()


def _differs(original: Expression, rewritten: Expression) -> str:
    op = "xor" if _sort(original) == "Bool" else "distinct"
    return f"(assert ({op} {publish(original).to_smt()} {publish(rewritten).to_smt()}))\n"


def _premise(assumptions: Sequence[Tuple[str, RewriteAssumption]]) -> str:
    return "".join(extension_assumption_line(name, item) + "\n" for name, item in assumptions)


BOUNDARY_VALUES = {
    8: (0, 1, 0x7F, 0x80, 0xFF),
    16: (0, 1, 0x7FFF, 0x8000, 0xFFFF),
    32: (0, 1, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF),
    64: (0, 1, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFF80000000, 0x80000000),
}


def certify(
    rule: str,
    original: Expression,
    params: Sequence[Tuple[str, int]],
    assumptions: Sequence[Tuple[str, RewriteAssumption]] = (),
    **normalize_kwargs,
) -> Expression:
    """実規則で ``original`` を書き換え、``rule`` だけが発火したことと意味保存を確かめる。"""

    rewritten, applied = _normalize(original, **normalize_kwargs)
    assert rewritten.to_smt() != original.to_smt(), "rule did not fire"
    assert set(applied) == {rule}, applied
    assert _sort(rewritten) == _sort(original)
    declarations = _declarations(params)
    premise = _premise(assumptions)
    assert _check(declarations + premise) == z3.sat
    assert _check(declarations + premise + _differs(original, rewritten)) == z3.unsat
    for name, bits in params:
        for value in BOUNDARY_VALUES[bits]:
            pinned = declarations + premise + f"(assert (= {name} (_ bv{value} {bits})))\n"
            if _check(pinned) != z3.sat:
                continue  # この境界値は premise の外（ext の像でない）
            assert _check(pinned + _differs(original, rewritten)) == z3.unsat, (name, hex(value))
    return rewritten


def counterexample_exists(
    original: Expression,
    naive: Expression,
    params: Sequence[Tuple[str, int]],
    assumptions: Sequence[Tuple[str, RewriteAssumption]] = (),
) -> bool:
    text = _declarations(params) + _premise(assumptions) + _differs(original, naive)
    return _check(text) == z3.sat


CERTIFIED_RULES = set()
MISSING_ASSUMPTION_NEGATIVES = set()


def certifies(*rules: str):
    def mark(function):
        for rule in rules:
            assert rule in REWRITE_RULES, rule
            CERTIFIED_RULES.add(rule)
        return function
    return mark


def refutes_without_assumption(*rules: str):
    """入力仮定を消費する規則が、仮定を欠くと発火せず反例を持つことの test。"""

    def mark(function):
        for rule in rules:
            assert REWRITE_RULES[rule].consumes_input_extension, rule
            MISSING_ASSUMPTION_NEGATIVES.add(rule)
        return function
    return mark


def test_every_rule_in_the_table_has_a_certificate():
    assert CERTIFIED_RULES == set(REWRITE_RULES)


def test_every_assumption_consuming_rule_has_a_missing_assumption_negative():
    assert MISSING_ASSUMPTION_NEGATIVES == {
        name for name, rule in REWRITE_RULES.items() if rule.consumes_input_extension
    }


a32 = _param("a", 4, 0)
b32 = _param("b", 4, 1)
p64 = _param("p", 8, 0)
q64 = _param("q", 8, 1)
SIGN32_P = RewriteAssumption(0, 64, 32, ExtensionKind.SIGN)
SIGN32_Q = RewriteAssumption(1, 64, 32, ExtensionKind.SIGN)
ZERO32_P = RewriteAssumption(0, 64, 32, ExtensionKind.ZERO)
ZERO32_Q = RewriteAssumption(1, 64, 32, ExtensionKind.ZERO)


# ---------------------------------------------------------------------------
# subpiece_of_extension
# ---------------------------------------------------------------------------


@certifies("subpiece_of_extension")
@pytest.mark.parametrize("ext", ["INT_SEXT", "INT_ZEXT"])
def test_subpiece_of_extension(ext):
    original = _low(_un(ext, a32, 8), 4)
    certify("subpiece_of_extension", original, [("a", 32)])


def test_subpiece_of_extension_requires_matching_width():
    a16 = _param("a", 2, 0)
    original = _low(_un("INT_SEXT", a16, 8), 4)
    assert _rewrite(original).to_smt() == original.to_smt()


# ---------------------------------------------------------------------------
# subpiece_of_ring_operation
# ---------------------------------------------------------------------------


RING = ("INT_ADD", "INT_SUB", "INT_MULT", "INT_AND", "INT_OR", "INT_XOR")


@certifies("subpiece_of_ring_operation")
@pytest.mark.parametrize("op", RING)
def test_subpiece_of_ring_operation_on_extensions(op):
    original = _low(_bin(op, _un("INT_SEXT", a32, 8), _un("INT_ZEXT", b32, 8), 8), 4)
    certify("subpiece_of_ring_operation", original, [("a", 32), ("b", 32)])


@pytest.mark.parametrize("op", RING)
def test_subpiece_of_ring_operation_on_hinted_wide_parameters(op):
    """hint はどこで試すかの目安だけ。下位 bit の等式は入力仮定無しで成り立つ。"""

    original = _low(_bin(op, p64, q64, 8), 4)
    hints = _hints(i0=ParameterSemanticHint(32, "signed"), i1=ParameterSemanticHint(32, "signed"))
    certify("subpiece_of_ring_operation", original, [("p", 64), ("q", 64)], hints=hints)


@pytest.mark.parametrize("op", RING)
def test_bare_ring_operation_is_never_narrowed(op):
    """v5 §4.6: 全幅の算術結果を裸で狭めない（sort が変わる）。hint も IEE も関係ない。"""

    original = _bin(op, p64, q64, 8)
    hints = _hints(i0=ParameterSemanticHint(32, "signed"), i1=ParameterSemanticHint(32, "signed"))
    authorization = RewriteAuthorization((SIGN32_P, SIGN32_Q))
    assert _rewrite(original, hints=hints, authorization=authorization).to_smt() == original.to_smt()
    naive = _bin(op, _low(p64, 4), _low(q64, 4), 4)
    assert _sort(naive) != _sort(original)


def test_add_overflow_breaks_bare_narrowing_even_under_sign_extension():
    """``x + 1``（64 bit）は x が sext32 像でも low32 の加算と異なる（x = 0x7fffffff）。"""

    original = _bin("INT_ADD", p64, _const(1, 8), 8)
    naive = _un("INT_SEXT", _bin("INT_ADD", _low(p64, 4), _const(1, 4), 4), 8)
    assert counterexample_exists(original, naive, [("p", 64)], [("p", SIGN32_P)])


# ---------------------------------------------------------------------------
# division / remainder: 有効な規則ではない
# ---------------------------------------------------------------------------


#: ``SUBPIECE(div(ext(a), ext(b)), 0) == div(a, b)`` は幅に依らない恒等式だが、
#: production 幅（64→32）で実 lowering の certificate が得られない: z3 4.16.0 は
#: ``bvsdiv`` の 64→32 同値を 600 秒で決められない（``tests/fixtures/issue167/README.md``）。
#: 未証明の規則は有効にしないので、除算・剰余は狭めない。
DIVISION_CASES = [
    ("INT_SDIV", "INT_SEXT"), ("INT_SREM", "INT_SEXT"),
    ("INT_DIV", "INT_ZEXT"), ("INT_REM", "INT_ZEXT"),
]


@pytest.mark.parametrize(("op", "ext"), DIVISION_CASES)
def test_division_is_never_narrowed(op, ext):
    syntactic = _low(_bin(op, _un(ext, a32, 8), _un(ext, b32, 8), 8), 4)
    assert _normalize(syntactic) == (publish(syntactic), {})
    kind = ExtensionKind.SIGN if ext == "INT_SEXT" else ExtensionKind.ZERO
    entailed = RewriteAuthorization((
        RewriteAssumption(0, 64, 32, kind), RewriteAssumption(1, 64, 32, kind),
    ))
    on_parameters = _low(_bin(op, p64, q64, 8), 4)
    assert _normalize(on_parameters, authorization=entailed) == (publish(on_parameters), {})
    assert not any("div" in name for name in REWRITE_RULES)


def test_signed_division_on_zero_extended_composite_operands_differs():
    """v5 §4.6: parameter の SIGN 証拠があっても operand ``p & 0xff`` は zero 像。"""

    p16 = _param("p", 2, 0)
    q16 = _param("q", 2, 1)
    masked_p = _bin("INT_AND", p16, _const(0xFF, 2), 2)
    masked_q = _bin("INT_AND", q16, _const(0xFF, 2), 2)
    original = _low(_bin("INT_SDIV", masked_p, masked_q, 2), 1)
    sign8 = (RewriteAssumption(0, 16, 8, ExtensionKind.SIGN), RewriteAssumption(1, 16, 8, ExtensionKind.SIGN))
    hints = _hints(i0=ParameterSemanticHint(8, "signed"), i1=ParameterSemanticHint(8, "signed"))
    assert _rewrite(original, hints=hints, authorization=RewriteAuthorization(sign8)).to_smt() == original.to_smt()
    naive = _bin("INT_SDIV", _low(p16, 1), _low(q16, 1), 1)
    assert counterexample_exists(
        original, naive, [("p", 16), ("q", 16)], [("p", sign8[0]), ("q", sign8[1])]
    )


# ---------------------------------------------------------------------------
# mask_to_zero_extension
# ---------------------------------------------------------------------------


@certifies("mask_to_zero_extension")
def test_mask_becomes_zero_extension_of_low_part():
    original = _bin("INT_AND", p64, _const(0xFFFFFFFF, 8), 8)
    hints = _hints(i0=ParameterSemanticHint(32, "unsigned"))
    certify("mask_to_zero_extension", original, [("p", 64)], hints=hints)


def test_mask_rewrite_preserves_the_parent_sort_and_value():
    """v5 §4.6 必須反例: ``(~(p & 0xffffffff)) == 0xffffffff00000000``（p = 0xffffffff で真）。"""

    masked = _bin("INT_AND", p64, _const(0xFFFFFFFF, 8), 8)
    original = _bin("INT_EQUAL", _un("INT_NEGATE", masked, 8), _const(0xFFFFFFFF00000000, 8), 1)
    hints = _hints(i0=ParameterSemanticHint(32, "unsigned"))
    certify("mask_to_zero_extension", original, [("p", 64)], hints=hints)

    # 素朴な書き換え（下位 32 bit の否定を 64 bit の定数と比べる）は幅の違う比較で、伸ばし方が値を
    # 変えるので描画が拒否する（Issue #298: 以前は zero 拡張と推測し、反例で違いを示していた）
    naive = _bin("INT_EQUAL", _un("INT_NEGATE", _low(p64, 4), 4), _const(0xFFFFFFFF00000000, 8), 1)
    with pytest.raises(SMT_SEMANTICS_REFUSALS):
        publish(naive).to_smt()
    widened = _un("INT_ZEXT", _un("INT_NEGATE", _low(p64, 4), 4), 8)
    assert counterexample_exists(original, _bin("INT_EQUAL", widened, _const(0xFFFFFFFF00000000, 8), 1), [("p", 64)])


# ---------------------------------------------------------------------------
# comparison_constant_width_alignment
# ---------------------------------------------------------------------------


@certifies("comparison_constant_width_alignment")
@pytest.mark.parametrize(("op", "constant"), [
    ("INT_EQUAL", 4), ("INT_NOTEQUAL", 7), ("INT_EQUAL", 0x7FFFFFFF), ("INT_LESSEQUAL", 4), ("INT_LESS", 0x7FFFFFFF),
])
def test_comparison_constant_is_aligned_to_the_narrow_operand(op, constant):
    """符号なしの比較で、定数が zero・sign どちらの拡張の像にも入る（狭い幅で最上位 bit が 0）ときだけ揃える。

    Issue #298: 描画は幅の違う比較の狭い側を比較の符号で伸ばさない。揃えも、伸ばし方に依らず
    ``a op low_N(c)`` と同値な形に限る。
    """

    original = _bin(op, a32, _const(constant, 8), 1)
    rewritten, applied = _normalize(original)
    assert set(applied) == {"comparison_constant_width_alignment"}, applied
    assert rewritten.operands[1].size == 4  # 定数を狭い側の幅へ揃えた
    # 描画も伸ばし方に依らない同じ形で比べる（揃える前後で同じ意味）
    declarations = _declarations([("a", 32)])
    assert _check(declarations + _differs(original, rewritten)) == z3.unsat


@pytest.mark.parametrize(("op", "constant"), [
    ("INT_SLESS", 4), ("INT_SLESS", 0xFFFFFFFFFFFFFFFC), ("INT_SLESSEQUAL", 0xFFFFFFFF80000000),
    ("INT_LESS", 0xFFFFFFFF), ("INT_EQUAL", 0x80000000),
    ("INT_LESS", 0xFFFFFFFFFFFFFFFF), ("INT_EQUAL", 0xFFFFFFFF80000000), ("INT_SLESS", 0x80000000),
])
def test_comparison_constant_whose_meaning_depends_on_the_extension_is_kept(op, constant):
    """符号付きの順序の比較・狭い幅で最上位 bit が 1 の定数は、狭い側の伸ばし方で意味が変わる。揃えず、描画も拒否する。"""

    original = _bin(op, a32, _const(constant, 8), 1)
    rewritten = _rewrite(original)
    assert rewritten.operands[1].size == 8  # 定数を狭めていない
    with pytest.raises(SMT_SEMANTICS_REFUSALS):
        publish(original).to_smt()
    by_zero = _bin(op, _un("INT_ZEXT", a32, 8), _const(constant, 8), 1)
    by_sign = _bin(op, _un("INT_SEXT", a32, 8), _const(constant, 8), 1)
    assert counterexample_exists(by_zero, by_sign, [("a", 32)])


# ---------------------------------------------------------------------------
# comparison_zero_constant_width
# ---------------------------------------------------------------------------


@certifies("comparison_zero_constant_width")
@pytest.mark.parametrize("op", [
    "INT_EQUAL", "INT_NOTEQUAL", "INT_SLESS", "INT_SLESSEQUAL", "INT_LESS", "INT_LESSEQUAL",
])
def test_comparison_zero_constant_is_widened_to_the_peer(op):
    """lowering は狭い側を ext で揃えるが、0 はどの ext でも 0。"""

    original = _bin(op, p64, _const(0, 4), 1)
    certify("comparison_zero_constant_width", original, [("p", 64)])


@pytest.mark.parametrize("zero_size", [4, 8])
def test_comparison_zero_constant_is_aligned_to_a_boolean_peer(zero_size):
    """比較結果（Bool）と 0 の比較も同じ規則。lowering は Bool を ite で bit 化する。"""

    less = _bin("INT_SLESS", a32, b32, 1)
    original = _bin("INT_EQUAL", less, _const(0, zero_size), 1)
    certify("comparison_zero_constant_width", original, [("a", 32), ("b", 32)])


def test_nonzero_narrow_constant_is_not_widened():
    original = _bin("INT_SLESS", p64, _const(0x80000000, 4), 1)
    assert _normalize(original) == (publish(original), {})


# ---------------------------------------------------------------------------
# comparisons on extension images（演算子ごとに規則が 1 つ）
# ---------------------------------------------------------------------------


COMPARISON_IMAGE_CASES = [
    ("equality_on_extension_images", "INT_EQUAL", "INT_SEXT"),
    ("equality_on_extension_images", "INT_NOTEQUAL", "INT_ZEXT"),
    ("signed_order_on_sign_extension_images", "INT_SLESS", "INT_SEXT"),
    ("signed_order_on_sign_extension_images", "INT_SLESSEQUAL", "INT_SEXT"),
    ("unsigned_order_on_zero_extension_images", "INT_LESS", "INT_ZEXT"),
    ("unsigned_order_on_zero_extension_images", "INT_LESSEQUAL", "INT_ZEXT"),
]


@certifies(*{case[0] for case in COMPARISON_IMAGE_CASES})
@pytest.mark.parametrize(("rule", "op", "ext"), COMPARISON_IMAGE_CASES)
def test_comparison_of_syntactic_extension_images(rule, op, ext):
    original = _bin(op, _un(ext, a32, 8), _un(ext, b32, 8), 1)
    certify(rule, original, [("a", 32), ("b", 32)])


PARAMETER_IMAGE_CASES = [
    ("signed_order_on_sign_extension_images", "INT_SLESS", SIGN32_P, 5),
    ("signed_order_on_sign_extension_images", "INT_SLESSEQUAL", SIGN32_P, 0xFFFFFFFFFFFFFFFB),
    ("equality_on_extension_images", "INT_EQUAL", SIGN32_P, 0xFFFFFFFF80000000),
    ("unsigned_order_on_zero_extension_images", "INT_LESS", ZERO32_P, 0xFFFFFFFF),
    ("equality_on_extension_images", "INT_NOTEQUAL", ZERO32_P, 0),
]


@refutes_without_assumption(*{case[0] for case in PARAMETER_IMAGE_CASES})
@pytest.mark.parametrize(("rule", "op", "assumption", "constant"), PARAMETER_IMAGE_CASES)
def test_comparison_of_parameter_needs_the_entailed_extension(rule, op, assumption, constant):
    original = _bin(op, p64, _const(constant, 8), 1)
    authorization = RewriteAuthorization((assumption,))
    assert (rule, 0) in authorization.permitted_rules()
    rewritten = certify(rule, original, [("p", 64)], [("p", assumption)], authorization=authorization)

    # 最終 relation の仮定が無いと規則は発火せず、欠いたまま書き換えた式には反例がある。
    assert _normalize(original)[1].get(rule) is None
    assert counterexample_exists(original, rewritten, [("p", 64)])


@pytest.mark.parametrize("op", ["INT_LESS", "INT_EQUAL"])
def test_comparison_through_a_mask_image_is_certified(op):
    """``p & 0xffffffff`` は恒等的に zext 像（mask 規則が発火しない signed hint でも）。"""

    masked = _bin("INT_AND", p64, _const(0xFFFFFFFF, 8), 8)
    original = _bin(op, masked, _const(0x10, 8), 1)
    hints = _hints(i0=ParameterSemanticHint(32, "signed"))
    rule = "unsigned_order_on_zero_extension_images" if op == "INT_LESS" else "equality_on_extension_images"
    certify(rule, original, [("p", 64)], hints=hints)


@pytest.mark.parametrize("constant", [5, 0xFFFFFFFFFFFFFFFB, 0x7FFFFFFF])
def test_comparison_of_a_syntactic_image_with_a_constant_in_its_image(constant):
    original = _bin("INT_SLESS", _un("INT_SEXT", a32, 8), _const(constant, 8), 1)
    certify("signed_order_on_sign_extension_images", original, [("a", 32)])


def test_normalize_analysis_preserves_every_return_value_and_condition():
    """analysis 全体の書き換え（metadata 同期・規則・条件の簡約）でも、各 return の値と
    条件が元と同じ意味（全入力で一致）であること。"""

    from scripts.function_tracer_pcode.core import Condition, ReturnInfo
    from scripts.function_tracer_pcode.semantics.semantic_width import normalize_analysis_semantic_width
    from scripts.function_tracer_pcode.tests.conftest import create_mock_analysis

    ring = _low(_bin("INT_ADD", _un("INT_SEXT", a32, 8), _un("INT_ZEXT", b32, 8), 8), 4)
    guard = _bin("INT_SLESS", _un("INT_SEXT", a32, 8), _const(0xFFFFFFFFFFFFFFFB, 8), 1)
    zero_guard = _bin("INT_EQUAL", b32, _const(0, 8), 1)
    analysis = create_mock_analysis(
        "f",
        parameters=[
            {"name": "a", "index": 0, "size": 4, "data_type": "int", "is_signed": True},
            {"name": "b", "index": 1, "size": 4, "data_type": "int", "is_signed": True},
        ],
        returns=[
            ReturnInfo(address="0x1000", conditions=[Condition(guard), Condition(zero_guard, True)], value=ring),
            ReturnInfo(address="0x1004", conditions=[Condition(guard, True)], value=_const(0, 4)),
        ],
    )
    normalized = normalize_analysis_semantic_width(analysis)
    params = [("a", 32), ("b", 32)]
    changed = 0
    for before, after in zip(analysis.returns, normalized.returns):
        pairs = [(before.value, after.value)]
        # 条件は簡約で並びや個数が変わり得るので、連言どうしを比べる。
        pairs.append((
            _conjunction(before.conditions),
            _conjunction(after.conditions),
        ))
        for original, rewritten in pairs:
            if publish(original).to_smt() != publish(rewritten).to_smt():
                changed += 1
            assert _check(_declarations(params) + _differs(original, rewritten)) == z3.unsat
    assert changed


def _conjunction(conditions):
    """条件列を 1 つの Bool 式にする（test 用。lowering は Condition と同じ）。"""

    expr = Expression(ExpressionType.CONSTANT, value=1, size=1)
    expr = _bin("INT_EQUAL", expr, _const(1, 1), 1)
    for condition in conditions:
        term = condition.expression
        if condition.negated:
            term = _un("BOOL_NEGATE", term, 1)
        expr = _bin("BOOL_AND", expr, term, 1)
    return expr


def test_signed_to_unsigned_comparison_conversion_is_not_performed():
    """v5 §4.6 必須反例: ``sext32(0x80000000) <u 0`` は偽、``<s 0`` は真。

    SIGN の前提があっても unsigned 比較を signed へ変えない（逆も同じ）。
    """

    original = _bin("INT_LESS", p64, _const(16, 8), 1)
    authorization = RewriteAuthorization((SIGN32_P,))
    assert _rewrite(original, authorization=authorization).to_smt() == original.to_smt()
    converted = _bin("INT_SLESS", _low(p64, 4), _const(16, 4), 1)
    assert counterexample_exists(original, converted, [("p", 64)], [("p", SIGN32_P)])

    widened = _bin("INT_LESS", _un("INT_SEXT", a32, 8), _const(16, 8), 1)
    hints = _hints(i0=ParameterSemanticHint(32, "signed", signedness_source="explicit"))
    assert _rewrite(widened, hints=hints).to_smt() == widened.to_smt()


def test_mixed_extension_kinds_in_equality_are_not_narrowed():
    """``sext(a) == zext(b)`` は ``a == b`` と違う（a = b = 0x80000000）。"""

    original = _bin("INT_EQUAL", _un("INT_SEXT", a32, 8), _un("INT_ZEXT", b32, 8), 1)
    assert _rewrite(original).to_smt() == original.to_smt()
    assert counterexample_exists(original, _bin("INT_EQUAL", a32, b32, 1), [("a", 32), ("b", 32)])


def test_zero_image_does_not_license_signed_comparison():
    original = _bin("INT_SLESS", p64, _const(5, 8), 1)
    authorization = RewriteAuthorization((ZERO32_P,))
    assert _rewrite(original, authorization=authorization).to_smt() == original.to_smt()
    naive = _bin("INT_SLESS", _low(p64, 4), _const(5, 4), 1)
    assert counterexample_exists(original, naive, [("p", 64)], [("p", ZERO32_P)])


# ---------------------------------------------------------------------------
# fragment collapse is not an enabled rule
# ---------------------------------------------------------------------------


def test_independent_fragment_is_not_collapsed():
    """v5 §4.6: lo を固定して独立な hi を変えると ``PIECE(hi, lo)`` と ``sext(lo)`` は違う。"""

    hi = Expression(ExpressionType.VARIABLE, name="in_a0_hi", size=4)
    original = _bin("PIECE", hi, a32, 8)
    authorization = RewriteAuthorization((RewriteAssumption(0, 32, 16, ExtensionKind.SIGN),))
    assert _rewrite(original, authorization=authorization).to_smt() == original.to_smt()
    naive = _un("INT_SEXT", a32, 8)
    assert counterexample_exists(original, naive, [("a", 32), ("in_a0_hi", 32)])
    assert "fragment" not in " ".join(REWRITE_RULES)

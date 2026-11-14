# -*- coding: utf-8 -*-
"""Issue #298: UB の制約・式の幅・証明の前提を、EQ / NOT_EQ の根拠として正しく扱う。

* EQ の前提に UB の制約を課さない。P-code の演算は全ての入力で定義されていて、binary の
  演算から source の演算・符号・実行条件は示せない（課すと正当な入力を除いて偽 EQ になる）。
* NOT_EQ の witness は、両方の関数の全ての演算（PHI の条件と値を含む）の UB の制約を
  無条件に課した反例の領域に入る入力に限る（UB を上から近似。#31 の保護を包む）。
  value query の model が外れたら、領域の中で解き直す。
* shift・負号で演算が被演算子より広い形は、伸ばし方（zero / sign）に依らないと示せるとき
  だけ演算の幅で計算し、それ以外は描画が拒否する（推測で拡張を決めない）。
* 証明の前提（header・組の追加の assert）が SAT と示せない比較の UNSAT は EQ の根拠に
  しない（``proof_premise_unsatisfiable``）。guard だけで到達不能な組は引き続き使う。

production の check 経路（phase workflow・strategy・z3 CLI・authority）をそのまま使い、
Ghidra の解析だけを合成する（``_production_check_harness``）。fixture は合成で、EqBench の
ground truth ではない。各 fixture の docstring に、source 上の意味と、base（``668767d9``）・
レビュー時の head（``0eaef1f8``）での結果を書く。描画の正しさは、P-code の意味に基づく
独立の参照値（この file の ``_pcode_*``）と z3 の評価で照合する。
"""

from __future__ import annotations

import re
import shutil
import subprocess

import pytest

from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from scripts.function_tracer_pcode.core.render_smt import SMT_SEMANTICS_REFUSALS
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
from scripts.function_tracer_pcode.proof.obligations.premise import (
    PROOF_PREMISE_UNSATISFIABLE_REASON_ID,
    ProofPremiseUnsatisfiable,
    require_satisfiable_premises,
)
from scripts.function_tracer_pcode.proof.ub.constraints import UbConstraintBuilder
from scripts.function_tracer_pcode.tests.conftest import create_mock_data_type_manager, resolve_mock_data_type
from scripts.function_tracer_pcode.tests.unit._production_check_harness import run_production_check
from scripts.function_tracer_pcode.tests.unit._publication import published
from scripts.function_tracer_pcode.tests.unit.test_void_effect_only_return_abi_issue104 import _abi_facts

_DTM = create_mock_data_type_manager()
INT32_MIN = 0x80000000


# ---------------------------------------------------------------------------
# 合成の解析
# ---------------------------------------------------------------------------


def _param(name, size, data_type, index):
    return Expression.parameter(name, index, data_type=data_type, size=size)


def _const(value, size):
    return Expression.constant(value, size=size)


def _bin(operator, left, right, size=None):
    expr = Expression.binary_op(operator, left, right)
    if size is not None:
        expr.size = size
    return expr


def _neg(operand, size=None):
    expr = Expression.unary_op("INT_2COMP", operand)
    expr.size = size if size is not None else operand.size
    return expr


def _phi(branches, size):
    expr = Expression.phi(branches)
    expr.size = size
    return expr


def _descriptor(name, size, data_type, signed, index):
    return {
        "name": name, "index": index, "size": size, "data_type": data_type, "is_signed": signed,
        "data_type_obj": resolve_mock_data_type(data_type, _DTM),
    }


def _analysis(name, parameters, returns, *, return_type="int", return_size=4):
    analysis = FunctionReturnAnalysis(
        function_name=name, entry_point="0x1000", parameters=parameters, returns=returns,
        return_type=return_type, binary_id=f"bin-{name}",
    )
    analysis.return_abi_facts = _abi_facts(
        return_type=f"/{return_type}", type_length=return_size, storage="PRESENT",
    )
    return analysis


def _unary_fn(name, value, *, param="x", size=4, data_type="uint", signed=False, return_type="uint",
              return_size=4):
    """1 引数・1 return の関数（値は ``value(param)``）。"""
    p = _param(param, size, data_type, 0)
    return _analysis(
        name, [_descriptor(param, size, data_type, signed, 0)], [ReturnInfo("0x10", value(p), [])],
        return_type=return_type, return_size=return_size,
    )


def _outcome(result):
    final = result.get("final_outcome")
    if isinstance(final, dict):
        return final.get("outcome")
    return final


def _reason_ids(result):
    return {str(row.get("reason_id")) for row in result.get("c_active_base") or ()}


# ---------------------------------------------------------------------------
# P-code の意味に基づく独立の参照値と、描画の z3 による評価
# ---------------------------------------------------------------------------


def _pcode_shift(operator, value, count, bits):
    """P-code の shift（Ghidra の定義: 量が幅以上なら 0、INT_SRIGHT は符号で埋める）。"""
    mask = (1 << bits) - 1
    value &= mask
    if operator == "INT_LEFT":
        return 0 if count >= bits else (value << count) & mask
    if operator == "INT_RIGHT":
        return 0 if count >= bits else value >> count
    signed = value - (1 << bits) if value >> (bits - 1) else value
    if count >= bits:
        return mask if signed < 0 else 0
    return (signed >> count) & mask


def _zext(value, from_bits):
    return value & ((1 << from_bits) - 1)


def _sext(value, from_bits, to_bits):
    value = _zext(value, from_bits)
    if value >> (from_bits - 1):
        value |= ((1 << to_bits) - 1) ^ ((1 << from_bits) - 1)
    return value


def _z3_value(smt, declarations):
    """``declarations``（名前 → (幅, 値)）の下での ``smt`` の値（z3 CLI）。"""
    if shutil.which("z3") is None:
        pytest.fail("the reference check needs the z3 CLI on PATH")
    lines = ["(set-logic QF_BV)"]
    for name, (bits, value) in declarations.items():
        lines.append(f"(declare-const {name} (_ BitVec {bits}))")
        lines.append(f"(assert (= {name} (_ bv{value} {bits})))")
    lines += ["(check-sat)", f"(get-value ({smt}))"]
    out = subprocess.run(["z3", "-in"], input="\n".join(lines), capture_output=True, text=True, check=True).stdout
    assert out.startswith("sat"), out
    literal = re.search(r"(#x[0-9a-fA-F]+|#b[01]+|\(_ bv(\d+) \d+\))\)\)\s*$", out)
    assert literal, out
    token = literal.group(1)
    if token.startswith("#x"):
        return int(token[2:], 16)
    if token.startswith("#b"):
        return int(token[2:], 2)
    return int(literal.group(2))


# ---------------------------------------------------------------------------
# 指摘 1: shift の幅（被演算子 32 bit・演算 64 bit）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("operator,bits", [
    ("INT_LEFT", 32), ("INT_RIGHT", 32), ("INT_SRIGHT", 32), ("INT_LEFT", 64), ("INT_SRIGHT", 64),
])
@pytest.mark.parametrize("value", [0, 1, 0x7FFFFFFF, INT32_MIN, 0xFFFFFFFF])
def test_well_formed_shift_rendering_matches_the_pcode_reference(operator, bits, value):
    """演算と被演算子の幅が同じ shift は、量の境界（0・幅-1・幅・幅+1・大きい値）で P-code と一致する。"""
    x = Expression(ExpressionType.PARAMETER, name="x", size=bits // 8)
    n = Expression(ExpressionType.PARAMETER, name="n", size=4)
    smt = published(_bin(operator, x, n, size=bits // 8)).to_smt()
    for count in (0, 1, bits - 1, bits, bits + 1, 0xFFFFFFFF):
        expected = _pcode_shift(operator, _sext(value, 32, bits), count, bits)
        assert _z3_value(smt, {"x": (bits, _sext(value, 32, bits)), "n": (32, count)}) == expected


@pytest.mark.parametrize("value", [0, 1, 3, 0x7FFFFFFF, INT32_MIN, 0xFFFFFFFF])
@pytest.mark.parametrize("count", [32, 33, 40, 63, 64])
def test_left_shift_whose_extension_bits_are_shifted_out_renders_the_wide_operation(value, count):
    """32 bit の x の 64 bit の ``x << c``（c >= 32）は、zero / sign のどちらで伸ばしても同じ値。

    レビューの例（``INT_LEFT(x, 32)``、x = 1）: 64 bit の演算は 2^32。レビュー時の head は 32 bit で
    shift してから伸ばして 0 にした（定数 0 と EQ）。
    """
    x = Expression(ExpressionType.PARAMETER, name="x", size=4)
    smt = published(_bin("INT_LEFT", x, _const(count, 4), size=8)).to_smt()
    by_zero = _pcode_shift("INT_LEFT", _zext(value, 32), count, 64)
    by_sign = _pcode_shift("INT_LEFT", _sext(value, 32, 64), count, 64)
    assert by_zero == by_sign
    assert _z3_value(smt, {"x": (32, value)}) == by_zero


@pytest.mark.parametrize("shape", [
    ("INT_LEFT", "count", 31),    # 定数でも伸ばした bit が残る（c < 64 - 32）
    ("INT_LEFT", "variable", 0),  # 量が変数
    ("INT_RIGHT", "count", 32),
    ("INT_SRIGHT", "count", 4),
])
def test_shift_wider_than_its_operand_is_refused_when_the_extension_matters(shape):
    """伸ばし方で値が変わる形は描画が拒否する（strategy は UNKNOWN にする）。"""
    operator, kind, count = shape
    x = Expression(ExpressionType.PARAMETER, name="x", size=4)
    amount = _const(count, 4) if kind == "count" else Expression(ExpressionType.PARAMETER, name="n", size=4)
    if kind == "count":
        # 参照値でも zero / sign で結果が違う（拒否が必要な形であることの確認）
        assert _pcode_shift(operator, _zext(INT32_MIN, 32), count, 64) != _pcode_shift(
            operator, _sext(INT32_MIN, 32, 64), count, 64,
        )
    with pytest.raises(SMT_SEMANTICS_REFUSALS):
        published(_bin(operator, x, amount, size=8)).to_smt()


def test_shift_narrower_than_its_operand_keeps_the_low_bytes_of_the_full_shift():
    """演算が被演算子より狭い形は、全幅の shift の下位 byte（拒否しない・既存の表現）。"""
    x = Expression(ExpressionType.PARAMETER, name="x", size=8)
    smt = published(_bin("INT_RIGHT", x, _const(56, 4), size=1)).to_smt()
    value = 0x1234_5678_9ABC_DEF0
    assert _z3_value(smt, {"x": (64, value)}) == _pcode_shift("INT_RIGHT", value, 56, 64) & 0xFF


def test_negation_wider_than_its_operand_is_refused_unless_the_extension_is_determined():
    x = Expression(ExpressionType.PARAMETER, name="x", size=4)
    with pytest.raises(SMT_SEMANTICS_REFUSALS):
        published(_neg(x, size=8)).to_smt()
    # 最上位 bit が 0 の定数・比較の結果（0 / 1）は伸ばし方で値が変わらない
    smt = published(_neg(_const(1, 1), size=4)).to_smt()
    assert _z3_value(smt, {}) == 0xFFFFFFFF


def _wide_shift_fn(name, *, form):
    """被演算子 32 bit・演算 64 bit の ``INT_LEFT(x, 32)``（narrow）、well-formed な
    ``INT_LEFT(ZEXT(x), 32)``（wide）、定数 0（zero）。"""
    def value(x):
        if form == "zero":
            return _const(0, 8)
        operand = x
        if form == "wide":
            operand = Expression.unary_op("INT_ZEXT", x)
            operand.size = 8
        return _bin("INT_LEFT", operand, _const(32, 4), size=8)

    return _unary_fn(name, value, return_type="ulong", return_size=8)


def test_wide_left_shift_of_a_narrow_operand_is_not_equivalent_to_zero():
    """レビューの再現（人工）: レビュー時の head は 32 bit で shift して 0 とし、定数 0 と EQ。

    x = 1 で 64 bit の演算は 2^32（参照値）なので EQ は偽。NOT_EQ の witness には使わない:
    source が 32 bit の値の 32 bit の shift（UB）だった可能性を binary から除けない（反例の
    領域は被演算子の幅で上から近似する）。
    """
    result = run_production_check("i298-wide-shift", _wide_shift_fn("f", form="narrow"), _wide_shift_fn("g", form="zero"))

    assert _outcome(result) == "UNKNOWN"
    assert "counterexample_ub_domain_violated" in _reason_ids(result)


def test_wide_left_shift_of_a_narrow_operand_equals_the_well_formed_shift():
    """伸ばし方に依らない形は演算の幅で正確に描くので、well-formed な 64 bit の shift と EQ。

    レビュー時の head の描画（32 bit で shift して 0）ではこの組は EQ にならない。
    """
    result = run_production_check("i298-wide-eq", _wide_shift_fn("f", form="narrow"), _wide_shift_fn("g", form="wide"))

    assert _outcome(result) == "EQUIVALENT"


def test_wide_shift_whose_extension_is_unknown_is_not_decided():
    def value(x):
        return _bin("INT_RIGHT", x, _const(4, 4), size=8)

    left = _unary_fn("f", value, return_type="ulong", return_size=8)
    right = _unary_fn("g", lambda x: _const(0, 8), return_type="ulong", return_size=8)
    result = run_production_check("i298-wide-right", left, right)

    assert _outcome(result) not in {"EQUIVALENT", "NOT_EQ"}


# ---------------------------------------------------------------------------
# 指摘 2: 符号なしの負号に対する UB の制約（#31 の保護との両立）
# ---------------------------------------------------------------------------


def _negation_fn(name, *, patched, signed=True):
    """``f(x) = -(uint32_t)x``（patched=False）/ ``g(x) = x == INT_MIN ? 7 : -(uint32_t)x``。

    x = INT_MIN でも ``-(uint32_t)x`` は定義済み（f(INT_MIN) = INT_MIN、g(INT_MIN) = 7）。EQ は偽。
    base・レビュー時の head では、引数の符号（signed）から ``x != INT_MIN`` を EQ の前提に課し、
    EQUIVALENT になった。binary の負号から source の符号は示せない（``-(int)x`` なら UB）ので、
    INT_MIN は NOT_EQ の witness にもできない（#31: Eq の pow/test の偽 NOT_EQ を防ぐ保護）。
    """
    data_type = "int" if signed else "uint"
    x = _param("x", 4, data_type, 0)
    returns = [ReturnInfo("0x10", _neg(x), [])]
    if patched:
        is_min = Condition(_bin("INT_EQUAL", x, _const(INT32_MIN, 4)))
        returns = [
            ReturnInfo("0x10", _const(7, 4), [is_min]),
            ReturnInfo("0x20", _neg(x), [Condition(is_min.expression, True)]),
        ]
    return _analysis(name, [_descriptor("x", 4, data_type, signed, 0)], returns, return_type="uint")


def _negation_inline_fn(name, *, patched, signed=True):
    """``f(x) = -(uint32_t)x`` / ``g(x) = -(uint32_t)x + (x == INT_MIN)``（1 つの式の中で INT_MIN だけ違う）。

    レビューの再現（人工）: レビュー時の head は、比べる case の中の負号の制約
    ``x != INT_MIN`` を組の領域が空にならないので EQ の前提に課し、EQUIVALENT にした（base も同じ）。
    """
    data_type = "int" if signed else "uint"
    x = _param("x", 4, data_type, 0)
    value = _neg(x)
    if patched:
        is_min = _bin("INT_EQUAL", x, _const(INT32_MIN, 4))
        widened = Expression.unary_op("INT_ZEXT", is_min)
        widened.size = 4
        value = _bin("INT_ADD", value, widened)
    return _analysis(
        name, [_descriptor("x", 4, data_type, signed, 0)], [ReturnInfo("0x10", value, [])], return_type="uint",
    )


@pytest.mark.parametrize("signed", [True, False])
def test_negation_differing_only_at_int_min_inside_one_case_is_neither_eq_nor_not_eq(signed):
    result = run_production_check(
        f"i298-neg-inline-{int(signed)}", _negation_inline_fn("f", patched=False, signed=signed),
        _negation_inline_fn("g", patched=True, signed=signed),
    )

    assert _outcome(result) == "UNKNOWN"
    assert "counterexample_ub_domain_violated" in _reason_ids(result)


@pytest.mark.parametrize("signed", [True, False])
def test_negation_differing_only_at_int_min_is_neither_eq_nor_not_eq(signed):
    result = run_production_check(
        f"i298-neg-{int(signed)}", _negation_fn("f", patched=False, signed=signed),
        _negation_fn("g", patched=True, signed=signed),
    )

    assert _outcome(result) == "UNKNOWN"
    assert "counterexample_ub_domain_violated" in _reason_ids(result)


def test_negation_against_itself_stays_equivalent():
    result = run_production_check(
        "i298-neg-eq", _negation_fn("f", patched=False), _negation_fn("g", patched=False),
    )

    assert _outcome(result) == "EQUIVALENT"


# ---------------------------------------------------------------------------
# 指摘 3: PHI の値・条件の中の UB と反例
# ---------------------------------------------------------------------------


def _phi_fn(name, branches):
    n = _param("n", 4, "uint", 0)
    return _analysis(
        name, [_descriptor("n", 4, "uint", False, 0)],
        [ReturnInfo("0x10", _phi(branches(n), 4), [])], return_type="uint",
    )


def _small(n):
    return Condition(_bin("INT_LESS", n, _const(32, 4)))


def test_shift_in_a_phi_value_excludes_its_ub_input_from_the_witness():
    """``f(n) = n < 32 ? 0 : 1u << n`` / ``g(n) = n < 32 ? 0 : 1``（PHI の値の中の shift）。

    n >= 32 では f の shift が UB で、違いは UB の入力にしか無い（NOT_EQ の witness にならない）。
    base・レビュー時の head は PHI の値を辿らず、n = 32 を反例にして NOT_EQ にした。
    """
    left = _phi_fn("f", lambda n: [(_small(n), _const(0, 4)), (Condition(_small(n).expression, True), _bin("INT_LEFT", _const(1, 4), n))])
    right = _phi_fn("g", lambda n: [(_small(n), _const(0, 4)), (Condition(_small(n).expression, True), _const(1, 4))])
    result = run_production_check("i298-phi-value", left, right)

    assert _outcome(result) not in {"EQUIVALENT", "NOT_EQ"}


def test_shift_in_a_phi_condition_excludes_its_ub_input_from_the_witness():
    """``f(n) = (1u << n) == 8 ? 1 : 0`` / ``g(n) = (n & 31) == 3 ? 1 : 0``（PHI の条件の中の shift）。

    n < 32 では等しい。n = 35 で P-code の値は違う（f は 0、g は 1）が、f の shift が UB。
    """
    def f_branches(n):
        hit = Condition(_bin("INT_EQUAL", _bin("INT_LEFT", _const(1, 4), n), _const(8, 4)))
        return [(hit, _const(1, 4)), (Condition(hit.expression, True), _const(0, 4))]

    def g_branches(n):
        hit = Condition(_bin("INT_EQUAL", _bin("INT_AND", n, _const(31, 4)), _const(3, 4)))
        return [(hit, _const(1, 4)), (Condition(hit.expression, True), _const(0, 4))]

    result = run_production_check("i298-phi-cond", _phi_fn("f", f_branches), _phi_fn("g", g_branches))

    assert _outcome(result) not in {"EQUIVALENT", "NOT_EQ"}


def test_phi_with_a_shift_keeps_a_legal_counterexample():
    """``f(n) = n < 32 ? 1u << n : 0`` / ``g(n) = n < 32 ? 2u << n : 0``: n = 0 で 1 と 2（UB 無し）。"""
    def branches(scale):
        return lambda n: [
            (_small(n), _bin("INT_LEFT", _const(scale, 4), n)),
            (Condition(_small(n).expression, True), _const(0, 4)),
        ]

    result = run_production_check("i298-phi-neq", _phi_fn("f", branches(1)), _phi_fn("g", branches(2)))

    assert _outcome(result) == "NOT_EQ"


def test_phi_with_a_shift_against_itself_stays_equivalent():
    def branches(n):
        return [(_small(n), _bin("INT_LEFT", _const(1, 4), n)), (Condition(_small(n).expression, True), _const(0, 4))]

    result = run_production_check("i298-phi-eq", _phi_fn("f", branches), _phi_fn("g", branches))

    assert _outcome(result) == "EQUIVALENT"


def test_obligations_cover_phi_conditions_and_values():
    n = Expression(ExpressionType.PARAMETER, name="n", size=4)
    m = Expression(ExpressionType.PARAMETER, name="m", size=4)
    phi = _phi([
        (Condition(_bin("INT_EQUAL", _bin("INT_LEFT", _const(1, 4), n), _const(8, 4))), _neg(m)),
        (None, _bin("INT_RIGHT", m, n)),
    ], 4)
    terms = {o.term for o in UbConstraintBuilder().collect_obligations([published(phi)], [])}

    assert "(bvult n (_ bv32 32))" in terms  # 条件と値の両方の shift（同じ制約は 1 つ）
    assert "(not (= m (_ bv2147483648 32)))" in terms  # 値の中の負号
    # 条件の中の 1 << n の符号付きの表現範囲（1 <u 2^31 >> n、つまり n < 31）
    assert "(bvult (_ bv1 32) (bvlshr (_ bv2147483648 32) n))" in terms


# ---------------------------------------------------------------------------
# 指摘 4: 証明の前提の充足可能性
# ---------------------------------------------------------------------------


@pytest.fixture
def contradictory_header(monkeypatch):
    """比較の共通の前提（header）に ``(assert false)`` を足す（人工の矛盾）。"""
    from scripts.function_tracer_pcode.proof.formula.builder import FormulaBuilder

    original = FormulaBuilder._prepare_formula_context

    def prepare(self, *args, **kwargs):
        context = original(self, *args, **kwargs)
        context.header_lines = [*context.header_lines, "; injected contradiction", "(assert false)"]
        return context

    monkeypatch.setattr(FormulaBuilder, "_prepare_formula_context", prepare)


def test_contradictory_premise_is_not_equivalence_evidence(contradictory_header):
    """全ての query が前提だけで UNSAT。レビュー時の head では pairwise の証明が EQ になった。"""
    result = run_production_check(
        "i298-premise", _negation_fn("f", patched=False), _negation_fn("g", patched=False),
    )

    assert _outcome(result) == "UNKNOWN"
    assert PROOF_PREMISE_UNSATISFIABLE_REASON_ID in _reason_ids(result)


def test_premise_check_distinguishes_contradiction_from_unreachable_pairs():
    solved = []

    def solve(scope, query):
        solved.append(scope)
        return {"sat": True, "unsat": False, "unknown": None}[query]

    cache = {}
    assert require_satisfiable_premises(solve, [("a", "sat"), ("b", "sat")], cache=cache) == 1
    for status in ("unsat", "unknown"):
        with pytest.raises(ProofPremiseUnsatisfiable) as caught:
            require_satisfiable_premises(solve, [("a", "sat"), ("c", status)], cache=cache)
        assert caught.value.reason_id == PROOF_PREMISE_UNSATISFIABLE_REASON_ID
    assert solved == ["a", "c", "c"]


def test_premise_reason_id_matches_the_authority_registry():
    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_LIMITATION_OBSERVED_SITE,
        PROOF_PREMISE_UNSATISFIABLE_REASON_ID as AUTHORITY_REASON_ID,
    )

    assert PROOF_PREMISE_UNSATISFIABLE_REASON_ID == AUTHORITY_REASON_ID
    assert AUTHORITY_REASON_ID in ANALYSIS_LIMITATION_OBSERVED_SITE.reason_ids


# ---------------------------------------------------------------------------
# f / g: 別の経路の制約が正当な反例を除く（レビュー前からの例）
# ---------------------------------------------------------------------------


def _shift_by_x_minus_one(x):
    return _bin("INT_LEFT", _const(1, 4), _bin("INT_SUB", x, _const(1, 4)))


def _fg(name, zero_value):
    """``name(x) = x == 0 ? zero_value : 1u << (x - 1)``（x は unsigned int）。

    f は zero_value = 0、g は zero_value = 1。x = 0 で f(0) = 0、g(0) = 1。EQ は偽。
    base では ``(x - 1) < 32`` が全ての query の前提に入り、x = 0 を除くので EQUIVALENT。
    """

    x = _param("x", 4, "uint", 0)
    is_zero = Condition(_bin("INT_EQUAL", x, _const(0, 4)))
    return _analysis(
        name,
        [_descriptor("x", 4, "uint", False, 0)],
        [
            ReturnInfo("0x10", _const(zero_value, 4), [is_zero]),
            ReturnInfo("0x20", _shift_by_x_minus_one(x), [Condition(is_zero.expression, True)]),
        ],
        return_type="uint",
    )


def test_constraint_of_another_path_does_not_exclude_a_legal_counterexample():
    result = run_production_check("i298-fg", _fg("f", 0), _fg("g", 1))

    # x = 0 は source（shift が x != 0 の経路だけにある）では正しい反例だが、binary からは
    # shift が x = 0 で実行されない（source で巻き上げられていない）ことを示せない。反例の
    # 領域は UB を上から近似するので x = 0 を witness にしない。EQ にも NOT_EQ にもしない。
    assert _outcome(result) == "UNKNOWN"
    assert "counterexample_ub_domain_violated" in _reason_ids(result)


# ---------------------------------------------------------------------------
# hashCode の形: 64 bit の引数の上位 bit を読む式
# ---------------------------------------------------------------------------


def _hash(name, *, mix_high):
    """``name(long y) = (int)(y ^ (y >> 32))``（mix_high）/ ``(int)y``（not mix_high）。

    binary の形: ``SUBPIECE(y, 0) ^ SUBPIECE(INT_RIGHT(y, 32), 0)``（64 bit の shift）。
    mix_high と not mix_high は y = 1 << 32 で 1 と 0（EQ は偽）。
    """

    y = _param("y", 8, "undefined8", 0)
    low = _bin("SUBPIECE", y, _const(0, 4), size=4)
    value = low
    if mix_high:
        high = _bin("SUBPIECE", _bin("INT_RIGHT", y, _const(32, 4)), _const(0, 4), size=4)
        value = _bin("INT_XOR", low, high)
    return _analysis(
        name, [_descriptor("y", 8, "undefined8", False, 0)],
        [ReturnInfo("0x10", value, [])],
    )


def test_hashcode_shape_is_not_equivalent():
    result = run_production_check(
        "i298-hash", _hash("left", mix_high=True), _hash("right", mix_high=False),
    )

    assert _outcome(result) == "NOT_EQ"


def test_hashcode_shape_against_itself_stays_equivalent():
    result = run_production_check(
        "i298-hash-eq", _hash("left", mix_high=True), _hash("right", mix_high=True),
    )

    assert _outcome(result) == "EQUIVALENT"


def _constant_overshift(name, *, overshift):
    """``name(x) = overshift ? x << 40 : x``（32 bit。定数の shift 量が幅以上）。

    ``x << 40`` は全ての入力で UB。base ではその UB 除外 ``40 < 32`` が恒偽の前提になり、
    全ての query が UNSAT で、pairwise の証明は等価になった。
    """

    x = _param("x", 4, "uint", 0)
    value = _bin("INT_LEFT", x, _const(40, 4)) if overshift else x
    return _analysis(
        name, [_descriptor("x", 4, "uint", False, 0)], [ReturnInfo("0x10", value, [])],
        return_type="uint",
    )


def test_unsatisfiable_ub_constraint_is_not_equivalence_evidence():
    result = run_production_check(
        "i298-vacuous", _constant_overshift("f", overshift=True), _constant_overshift("g", overshift=False),
    )

    assert (result.get("solver_results") or {}).get("is_equivalent") is not True
    assert _outcome(result) == "UNKNOWN"
    assert "counterexample_ub_domain_violated" in _reason_ids(result)


# ---------------------------------------------------------------------------
# UB の制約は EQ の前提にならない / guard だけで到達不能な組
# ---------------------------------------------------------------------------


def _shift(name, *, masked):
    """``name(x, n) = x << n``（masked なら ``x << (n & 31)``）。32 bit。

    n >= 32 で 2 つの binary の値は違う（P-code: 0 と ``x << (n - 32)``）。source が ``x << n``
    なら n >= 32 は UB で C の意味では等しいが、binary の shift から source の shift は示せない。
    base・レビュー時の head は UB の制約を EQ の前提にして EQUIVALENT にした。
    """

    x = _param("x", 4, "uint", 0)
    n = _param("n", 4, "uint", 1)
    count = _bin("INT_AND", n, _const(31, 4)) if masked else n
    return _analysis(
        name,
        [_descriptor("x", 4, "uint", False, 0), _descriptor("n", 4, "uint", False, 1)],
        [ReturnInfo("0x10", _bin("INT_LEFT", x, count), [])],
        return_type="uint",
    )


def test_ub_constraint_of_the_compared_case_is_not_an_equivalence_premise():
    result = run_production_check("i298-shift", _shift("f", masked=False), _shift("g", masked=True))

    assert _outcome(result) == "UNKNOWN"
    assert "counterexample_ub_domain_violated" in _reason_ids(result)


def test_masked_shift_against_itself_stays_equivalent():
    result = run_production_check("i298-shift-eq", _shift("f", masked=True), _shift("g", masked=True))

    assert _outcome(result) == "EQUIVALENT"


def _guarded_shift(name, *, in_range_value):
    """``name(x, n) = n < 32 ? <in_range_value> : 0``（unsigned）。

    in_range_value が None なら ``x << n``。左右で ``n < 32`` と ``!(n < 32)`` の組は guard だけで
    到達不能（前提は SAT）。
    """

    x = _param("x", 4, "uint", 0)
    n = _param("n", 4, "uint", 1)
    in_range = Condition(_bin("INT_LESS", n, _const(32, 4)))
    value = _bin("INT_LEFT", x, n) if in_range_value is None else _const(in_range_value, 4)
    return _analysis(
        name,
        [_descriptor("x", 4, "uint", False, 0), _descriptor("n", 4, "uint", False, 1)],
        [
            ReturnInfo("0x10", value, [in_range]),
            ReturnInfo("0x20", _const(0, 4), [Condition(in_range.expression, True)]),
        ],
        return_type="uint",
    )


def test_case_pair_unreachable_by_guards_alone_still_proves_equivalence():
    result = run_production_check(
        "i298-guarded", _guarded_shift("f", in_range_value=None), _guarded_shift("g", in_range_value=None),
    )

    assert _outcome(result) == "EQUIVALENT"


def _always_ub(name, *, shifted):
    """``name(x, n) = n >= 32 ? (shifted ? x << n : 7) : 0``（unsigned）。

    f（shifted）の n >= 32 の経路は全ての入力で UB。違いは UB の入力にしか無い。
    base では EQUIVALENT。
    """

    x = _param("x", 4, "uint", 0)
    n = _param("n", 4, "uint", 1)
    big = Condition(_bin("INT_LESS", n, _const(32, 4)), True)
    value = _bin("INT_LEFT", x, n) if shifted else _const(7, 4)
    return _analysis(
        name,
        [_descriptor("x", 4, "uint", False, 0), _descriptor("n", 4, "uint", False, 1)],
        [
            ReturnInfo("0x10", value, [big]),
            ReturnInfo("0x20", _const(0, 4), [Condition(big.expression, False)]),
        ],
        return_type="uint",
    )


def test_ub_alone_distinguishing_a_reachable_case_pair_is_neither_eq_nor_not_eq():
    result = run_production_check("i298-always-ub", _always_ub("f", shifted=True), _always_ub("g", shifted=False))

    assert _outcome(result) == "UNKNOWN"
    assert "counterexample_ub_domain_violated" in _reason_ids(result)


def _narrow_domain(name, *, low_value):
    """``name(n) = n >= 10 ? n + low_value : 1u << (n ^ 0x12340)``（unsigned）。

    shift の UB の制約 ``(n ^ 0x12340) < 32`` は n を 0x12340..0x1235f に限る。f（low_value=0）と
    g（low_value=1）は n >= 10 の経路で常に違う。value query の model が領域の外に出ても、
    領域の中で解き直せば witness が見つかる（base では NOT_EQ）。
    """

    n = _param("n", 4, "uint", 0)
    big = Condition(_bin("INT_LESS", n, _const(10, 4)), True)
    shift = _bin("INT_LEFT", _const(1, 4), _bin("INT_XOR", n, _const(0x12340, 4)))
    return _analysis(
        name,
        [_descriptor("n", 4, "uint", False, 0)],
        [
            ReturnInfo("0x10", _bin("INT_ADD", n, _const(low_value, 4)), [big]),
            ReturnInfo("0x20", shift, [Condition(big.expression, False)]),
        ],
        return_type="uint",
    )


def test_witness_outside_the_ub_domain_is_searched_again_inside_it():
    result = run_production_check(
        "i298-narrow-domain", _narrow_domain("f", low_value=0), _narrow_domain("g", low_value=1),
    )

    assert _outcome(result) == "NOT_EQ"


# ---------------------------------------------------------------------------
# 部品の契約: 反例の領域の制約
# ---------------------------------------------------------------------------


def _infos(*specs):
    return [
        ParameterInfo(original_name=name, smt_name=f"{name}_1", bit_width=bits, index=i, is_signed=signed)
        for i, (name, bits, signed) in enumerate(specs)
    ]


def test_domain_width_over_approximates_with_the_narrower_of_operation_and_operand():
    y = Expression(ExpressionType.PARAMETER, name="y", size=4)
    var_shift = Expression(
        ExpressionType.BINARY_OP, operator="INT_RIGHT",
        operands=[y, Expression(ExpressionType.PARAMETER, name="n", size=4)], size=8,
    )
    (obligation,) = UbConstraintBuilder().collect_obligations([published(var_shift)], _infos(("y", 32, True)))

    assert obligation.term == "(bvult n (_ bv32 32))"


def test_byte_wide_shift_uses_the_byte_width():
    narrow = _bin("INT_LEFT", Expression(ExpressionType.PARAMETER, name="z", size=1),
                  Expression(ExpressionType.PARAMETER, name="k", size=1), size=1)
    (only,) = UbConstraintBuilder().collect_obligations(
        [published(narrow)], [], constraint_types={"shift_count"},
    )

    assert only.term == "(bvult k (_ bv8 8))"


def test_operations_on_the_store_observation_index_are_not_program_operations():
    """観測の番地（比べる面の記号）に依存する byte の取り出しの shift は制約しない。

    書いた値の中の program の演算（負号）は番地に依存しないので制約する。レビュー後の
    再走査で PHI の枝を辿るようになり、raytrace sphere の記録した組で面の shift が反例の
    領域を狭めて reason が動いたことへの対応（実 binary の記録で確認）。
    """
    from scripts.function_tracer_pcode.core.observation_index import observation_index_expression

    index = observation_index_expression()
    m = Expression(ExpressionType.PARAMETER, name="m", size=8)
    offset = _bin("INT_SUB", index, Expression(ExpressionType.PARAMETER, name="p", size=8), size=8)
    byte = _bin("INT_RIGHT", _neg(m), _bin("INT_MULT", offset, _const(8, 8), size=8), size=8)
    in_range = Condition(_bin("INT_LESS", offset, _const(8, 8)))
    surface = _phi([(in_range, byte), (None, _const(0, 8))], 8)
    terms = {o.term for o in UbConstraintBuilder().collect_obligations([published(surface)], [])}

    assert terms == {"(not (= m (_ bv9223372036854775808 64)))"}


# ---------------------------------------------------------------------------
# レビュー 2 回目 指摘 1: 定数の量は描画の値（8 bit の 256 は 0）で判断する
# ---------------------------------------------------------------------------


def test_shift_count_constant_is_judged_by_its_rendered_value():
    """``INT_LEFT(x32, 256:8) -> 64`` の量は 0。伸ばし方で値が変わる（x = INT_MIN）ので拒否する。

    レビュー時の head（``977aa229``）は生の 256 を「伸ばした bit を押し出す」と読み、zero 拡張で
    描いた（``ZEXT(x)`` と EQ）。``288:8``（= 32）は押し出すので正確に描く。
    """
    x = Expression(ExpressionType.PARAMETER, name="x", size=4)
    assert _pcode_shift("INT_LEFT", _zext(INT32_MIN, 32), 256 % 256, 64) != _pcode_shift(
        "INT_LEFT", _sext(INT32_MIN, 32, 64), 256 % 256, 64,
    )
    with pytest.raises(SMT_SEMANTICS_REFUSALS):
        published(_bin("INT_LEFT", x, _const(256, 1), size=8)).to_smt()
    smt = published(_bin("INT_LEFT", x, _const(288, 1), size=8)).to_smt()
    for value in (1, INT32_MIN, 0xFFFFFFFF):
        assert _z3_value(smt, {"x": (32, value)}) == _pcode_shift("INT_LEFT", _zext(value, 32), 32, 64)


def test_wide_shift_by_a_count_that_wraps_to_zero_is_not_equivalent_to_zext():
    def shifted(x):
        return _bin("INT_LEFT", x, _const(256, 1), size=8)

    def widened(x):
        expr = Expression.unary_op("INT_ZEXT", x)
        expr.size = 8
        return expr

    left = _unary_fn("f", shifted, return_type="ulong", return_size=8)
    right = _unary_fn("g", widened, return_type="ulong", return_size=8)
    result = run_production_check("i298-count-wrap", left, right)

    assert _outcome(result) != "EQUIVALENT"


def test_ub_constraints_read_constants_at_their_rendered_width():
    x = Expression(ExpressionType.PARAMETER, name="x", size=4)
    builder = UbConstraintBuilder()
    # 量 288:8 は 32（= 幅）: UB の量
    (wide,) = builder.collect_obligations(
        [published(_bin("INT_LEFT", x, _const(288, 1), size=4))], [], constraint_types={"shift_count"},
    )
    assert wide.term == "(bvult (_ bv288 8) (_ bv32 8))"
    # 量 256:8 は 0: UB にならない
    assert builder.collect_obligations(
        [published(_bin("INT_LEFT", x, _const(256, 1), size=4))], [], constraint_types={"shift_count"},
    ) == []


# ---------------------------------------------------------------------------
# レビュー 2 回目 指摘 3: 変数の左シフトの符号付きの UB と反例の領域
# ---------------------------------------------------------------------------


def _shift_one_fn(name, *, flip_sign):
    """``f(x) = x << 1`` / ``g(x) = (x << 1) ^ (x < 0)``（x は int）。

    違いは x < 0 だけで、そこは符号付きの左シフトが UB（負の値の左シフト）。NOT_EQ の witness に
    しない。レビュー時の head は正の定数の左シフトだけを制約し、x = INT_MIN を反例にした（NOT_EQ）。
    """
    x = _param("x", 4, "int", 0)
    value = _bin("INT_LEFT", x, _const(1, 4))
    if flip_sign:
        negative = Expression.unary_op("INT_ZEXT", _bin("INT_SLESS", x, _const(0, 4)))
        negative.size = 4
        value = _bin("INT_XOR", value, negative)
    return _analysis(name, [_descriptor("x", 4, "int", True, 0)], [ReturnInfo("0x10", value, [])])


def test_variable_left_shift_ub_excludes_its_inputs_from_the_witness():
    result = run_production_check(
        "i298-shl-var", _shift_one_fn("f", flip_sign=False), _shift_one_fn("g", flip_sign=True),
    )

    assert _outcome(result) == "UNKNOWN"
    assert "counterexample_ub_domain_violated" in _reason_ids(result)


def test_variable_left_shift_keeps_a_counterexample_inside_the_domain():
    """``f(x) = x << 1`` / ``g(x) = (x << 1) + 1``: x = 0 で 0 と 1（UB 無し）。"""
    def plus_one(name):
        x = _param("x", 4, "int", 0)
        return _analysis(
            name, [_descriptor("x", 4, "int", True, 0)],
            [ReturnInfo("0x10", _bin("INT_ADD", _bin("INT_LEFT", x, _const(1, 4)), _const(1, 4)), [])],
        )

    result = run_production_check("i298-shl-neq", _shift_one_fn("f", flip_sign=False), plus_one("g"))

    assert _outcome(result) == "NOT_EQ"


def test_variable_left_shift_against_itself_stays_equivalent():
    result = run_production_check(
        "i298-shl-eq", _shift_one_fn("f", flip_sign=True), _shift_one_fn("g", flip_sign=True),
    )

    assert _outcome(result) == "EQUIVALENT"


@pytest.mark.parametrize("value,count,ok", [
    (0, 31, True), (1, 30, True), (1, 31, False), (0x3FFFFFFF, 1, True), (0x40000000, 1, False),
    (INT32_MIN, 0, False), (0xFFFFFFFF, 1, False), (5, 0, True),
])
def test_signed_left_shift_obligation_matches_the_c_rule(value, count, ok):
    """E1 << E2（符号付き 32 bit）が定義される ⇔ 0 <= E1 かつ E1·2^E2 <= INT_MAX（C11 6.5.7）。"""
    x = Expression(ExpressionType.PARAMETER, name="x", size=4)
    n = Expression(ExpressionType.PARAMETER, name="n", size=4)
    (obligation,) = UbConstraintBuilder().collect_obligations(
        [published(_bin("INT_LEFT", x, n))], [], constraint_types={"signed_left_shift_overflow"},
    )
    signed = value - (1 << 32) if value >> 31 else value
    assert ok == (signed >= 0 and signed * (1 << count) <= 0x7FFFFFFF)
    assert _z3_value(f"(ite {obligation.term} (_ bv1 1) (_ bv0 1))", {"x": (32, value), "n": (32, count)}) == int(ok)


# ---------------------------------------------------------------------------
# レビュー 2 回目 指摘 4: 同じ前提は同じ query（共有する）
# ---------------------------------------------------------------------------


def test_identical_pair_premises_share_one_query_and_different_ones_do_not():
    from scripts.function_tracer_pcode.proof.strategies.pairwise_models import ReturnCase
    from scripts.function_tracer_pcode.proof.strategies.pairwise_query_builder import build_pair_premise_query

    def case(index, value):
        return ReturnCase(
            index=index, conditions=[], value_expr=published(_const(value, 4)), return_info=None,
            return_type="int", parameters=[],
        )

    base_ctx = {
        "header_lines": ["(declare-const p (_ BitVec 32))", "(assert (bvult p (_ bv9 32)))"],
        "smt_logic": "QF_BV",
        "pairwise_extra_assertions_by_pair": {
            "(1,0)": ["(assert (= p (_ bv1 32)))", "(assert (bvugt p (_ bv0 32)))"],
            "(1,1)": ["(assert (bvugt p (_ bv0 32)))", "(assert (= p (_ bv1 32)))"],
            "(2,0)": ["(assert (= p (_ bv2 32)))"],
        },
    }
    queries = {
        pair: build_pair_premise_query(base_ctx, case(i, i), case(j, j + 7), None, None, pair)
        for pair, (i, j) in {"(0,0)": (0, 0), "(0,1)": (0, 1), "(1,0)": (1, 0), "(1,1)": (1, 1), "(2,0)": (2, 0)}.items()
    }

    assert queries["(0,0)"] == queries["(0,1)"]  # 追加の assert の無い組は header だけ
    assert queries["(1,0)"] == queries["(1,1)"]  # 同じ追加の assert（順が違う）
    assert len({queries["(0,0)"], queries["(1,0)"], queries["(2,0)"]}) == 3
    assert "(assert (= p (_ bv2 32)))" in queries["(2,0)"]


# ---------------------------------------------------------------------------
# レビュー 2 回目 指摘 2: 宣言が被演算子より広い算術（#313 と shift の保護の接点）
# ---------------------------------------------------------------------------


def _zext64(x):
    expr = Expression.unary_op("INT_ZEXT", x)
    expr.size = 8
    return expr


def _mul_high_fn(name, *, form):
    """``(x * y) >> 32``（64 bit）。``narrow``: 乗算の被演算子が 32 bit（宣言 64 bit）、``wide``: ZEXT で
    64 bit にした well-formed な形、``zero``: 定数 0。

    レビュー時の head は ``narrow`` の乗算を 32 bit で描き（宣言より狭い。#313）、その上の 64 bit の
    shift の被演算子は宣言どうしでは 64 bit なので shift の保護も通り、``x * y >> 32`` を 0 にした
    （x = y = 65536 で 64 bit の値は 1）。
    """
    x = _param("x", 4, "uint", 0)
    y = _param("y", 4, "uint", 1)
    if form == "zero":
        value = _const(0, 8)
    else:
        left, right = (x, y) if form == "narrow" else (_zext64(x), _zext64(y))
        value = _bin("INT_RIGHT", _bin("INT_MULT", left, right, size=8), _const(32, 4), size=8)
    return _analysis(
        name,
        [_descriptor("x", 4, "uint", False, 0), _descriptor("y", 4, "uint", False, 1)],
        [ReturnInfo("0x10", value, [])],
        return_type="ulong", return_size=8,
    )


def test_arithmetic_declared_wider_than_its_operands_is_not_computed_narrow():
    x = Expression(ExpressionType.PARAMETER, name="x", size=4)
    y = Expression(ExpressionType.PARAMETER, name="y", size=4)
    narrow = _bin("INT_RIGHT", _bin("INT_MULT", x, y, size=8), _const(32, 4), size=8)
    with pytest.raises(SMT_SEMANTICS_REFUSALS):
        published(narrow).to_smt()
    wide = _bin("INT_RIGHT", _bin("INT_MULT", _zext64(x), _zext64(y), size=8), _const(32, 4), size=8)
    smt = published(wide).to_smt()
    for a, b in ((65536, 65536), (0xFFFFFFFF, 0xFFFFFFFF), (3, 5)):
        assert _z3_value(smt, {"x": (32, a), "y": (32, b)}) == (a * b) >> 32
    # 伸ばし方が決まる被演算子（最上位 bit が 0 の定数どうし）は宣言の幅で正確に描く
    product = _bin("INT_MULT", _const(0x10000, 4), _const(0x10000, 4), size=8)
    assert _z3_value(published(product).to_smt(), {}) == 0x100000000


def test_wide_product_of_narrow_operands_is_not_equivalent_to_zero():
    result = run_production_check("i298-mul-narrow", _mul_high_fn("f", form="narrow"), _mul_high_fn("g", form="zero"))

    assert _outcome(result) not in {"EQUIVALENT", "NOT_EQ"}


def test_well_formed_wide_product_keeps_its_counterexample():
    """x = y = 65536 で ``(zext(x) * zext(y)) >> 32`` は 1、定数 0 と違う（UB 無し）。"""
    result = run_production_check("i298-mul-wide", _mul_high_fn("f", form="wide"), _mul_high_fn("g", form="zero"))

    assert _outcome(result) == "NOT_EQ"


# ---------------------------------------------------------------------------
# レビュー 3 回目 指摘 1: 片方だけが狭い混合幅の算術（伸ばし方を推測しない）
# ---------------------------------------------------------------------------


def _mixed_add_fn(name, *, form):
    """``x + y``（y は 64 bit）。``narrow``: 32 bit の x をそのまま 64 bit の INT_ADD に置く（伸ばし方が式に
    無い）、``zext`` / ``sext``: x を明示的に伸ばす well-formed な形。

    レビュー時の head（``f709de03``）は narrow を宣言の符号で伸ばし（unsigned → zero）、zext と EQ にした。
    元の式が sign 拡張なら x = 0x80000000、y = 0 で違う。
    """
    x = _param("x", 4, "uint", 0)
    y = _param("y", 8, "ulong", 1)
    left = x
    if form != "narrow":
        left = Expression.unary_op("INT_ZEXT" if form == "zext" else "INT_SEXT", x)
        left.size = 8
    return _analysis(
        name,
        [_descriptor("x", 4, "uint", False, 0), _descriptor("y", 8, "ulong", False, 1)],
        [ReturnInfo("0x10", _bin("INT_ADD", left, y, size=8), [])],
        return_type="ulong", return_size=8,
    )


def test_one_sided_narrow_operand_is_not_extended_by_a_guess():
    x = Expression(ExpressionType.PARAMETER, name="x", size=4)
    y = Expression(ExpressionType.PARAMETER, name="y", size=8)
    by_zero = (_zext(INT32_MIN, 32) + 0) & ((1 << 64) - 1)
    by_sign = (_sext(INT32_MIN, 32, 64) + 0) & ((1 << 64) - 1)
    assert by_zero != by_sign  # 参照値: 伸ばし方で値が変わる
    with pytest.raises(SMT_SEMANTICS_REFUSALS):
        published(_bin("INT_ADD", x, y, size=8)).to_smt()
    # 伸ばし方で値が変わらない被演算子（最上位 bit が 0 の定数）は伸ばして計算する
    smt = published(_bin("INT_ADD", _const(5, 4), y, size=8)).to_smt()
    assert _z3_value(smt, {"y": (64, 7)}) == 12


def test_mixed_width_sum_is_not_equivalent_to_the_zero_extended_sum():
    result = run_production_check("i298-mixed", _mixed_add_fn("f", form="narrow"), _mixed_add_fn("g", form="zext"))

    assert _outcome(result) not in {"EQUIVALENT", "NOT_EQ"}


def test_explicit_extensions_keep_their_counterexample_and_equivalence():
    differ = run_production_check("i298-mixed-neq", _mixed_add_fn("f", form="sext"), _mixed_add_fn("g", form="zext"))
    same = run_production_check("i298-mixed-eq", _mixed_add_fn("f", form="zext"), _mixed_add_fn("g", form="zext"))

    assert _outcome(differ) == "NOT_EQ"
    assert _outcome(same) == "EQUIVALENT"


# ---------------------------------------------------------------------------
# レビュー 3 回目 指摘 2: Bool の SMT の幅は演算の幅ではない
# ---------------------------------------------------------------------------


def _bool_shift_fn(name, *, constant):
    """``(x != 0) << 1``（比較の結果は 1 byte の 0 / 1、shift は 4 byte）/ 定数 0。x = 1 で 2 と 0。

    レビュー時の head は比較の Bool sort の 1 bit を演算の幅として ``1 < 1`` の UB の制約を作り、正当な
    反例を除いて UNKNOWN にした（``0eaef1f8`` は NOT_EQ）。
    """
    x = _param("x", 4, "uint", 0)
    value = _const(0, 4) if constant else _bin(
        "INT_LEFT", _bin("INT_NOTEQUAL", x, _const(0, 4), size=1), _const(1, 4), size=4,
    )
    return _analysis(name, [_descriptor("x", 4, "uint", False, 0)], [ReturnInfo("0x10", value, [])], return_type="uint")


def test_comparison_result_shift_keeps_its_counterexample():
    result = run_production_check("i298-bool-shift", _bool_shift_fn("f", constant=False), _bool_shift_fn("g", constant=True))

    assert _outcome(result) == "NOT_EQ"


def test_ub_width_of_a_comparison_operand_is_its_value_width():
    x = Expression(ExpressionType.PARAMETER, name="x", size=4)
    shifted = _bin("INT_LEFT", _bin("INT_NOTEQUAL", x, _const(0, 4), size=1), _const(1, 4), size=4)
    terms = {o.term for o in UbConstraintBuilder().collect_obligations([published(shifted)], [])}

    assert "false" not in terms
    assert not any("(_ bv1 1)" in term for term in terms)
    assert _z3_value(published(shifted).to_smt(), {"x": (32, 1)}) == 2


# ---------------------------------------------------------------------------
# レビュー 3 回目 指摘 3: 描画の拒否を確定の証明・solver の query へ流さない
# ---------------------------------------------------------------------------


def test_loop_template_does_not_identify_values_whose_extension_is_unknown():
    from scripts.function_tracer_pcode.proof.loop_template_abstraction import prove_template_equivalence

    x = Expression(ExpressionType.PARAMETER, name="x", size=4)
    shift_by_zero = _bin("INT_LEFT", x, _const(0, 4), size=8)
    zext = Expression.unary_op("INT_ZEXT", x)
    zext.size = 8
    sext = Expression.unary_op("INT_SEXT", x)
    sext.size = 8

    assert prove_template_equivalence(published(shift_by_zero), published(zext), target_bits=64)[0] is False
    assert prove_template_equivalence(published(sext), published(zext), target_bits=64)[0] is False
    # 正例: 同じ拡張どうし、下位 32 bit だけを比べるなら sext と zext は等しい
    assert prove_template_equivalence(published(zext), published(zext.derive_with()), target_bits=64)[0] is True
    assert prove_template_equivalence(published(sext), published(zext), target_bits=32)[0] is True


def test_shift_by_zero_is_not_removed_when_the_operand_is_narrower():
    from scripts.function_tracer_pcode.semantics.normalize import NormalizationContext, normalize_expression

    x = Expression(ExpressionType.PARAMETER, name="x", size=4)
    narrow = published(_bin("INT_LEFT", x, _const(0, 4), size=8))
    same = published(_bin("INT_LEFT", x, _const(0, 4), size=4))

    assert normalize_expression(narrow, NormalizationContext()).operator == "INT_LEFT"
    assert normalize_expression(same, NormalizationContext()) is x


def test_division_guard_does_not_send_unrenderable_operands_to_the_solver():
    from unittest.mock import Mock

    from scripts.function_tracer_pcode.semantics.normalize import NormalizationContext
    from scripts.function_tracer_pcode.semantics.normalize.division_signedness_guarded import (
        normalize_udiv_with_guard,
    )

    p = Expression(ExpressionType.PARAMETER, name="p", size=4)
    q = Expression(ExpressionType.PARAMETER, name="q", size=8)
    division = published(_bin("INT_DIV", _neg(p, size=8), q, size=8))
    solver = Mock()

    result = normalize_udiv_with_guard(division, {}, [], [], solver, NormalizationContext(), lambda text: text)

    assert result.operator == "INT_DIV"  # 書き換えない（SDIV にしない）
    solver.assert_not_called()


def test_evidence_rendering_records_a_refusal_without_raising():
    from scripts.function_tracer_pcode.core.render_smt import render_expression_smt_evidence

    x = Expression(ExpressionType.PARAMETER, name="x", size=4)
    text = render_expression_smt_evidence(_bin("INT_LEFT", x, _const(0, 4), size=8))

    assert text.startswith("(unrendered ")


# ---------------------------------------------------------------------------
# レビュー 3 回目 指摘 4: comment だけが違う前提は 1 回だけ解く
# ---------------------------------------------------------------------------


def test_pair_premises_that_differ_only_in_comments_are_solved_once():
    from scripts.function_tracer_pcode.proof.strategies.pairwise_models import ReturnCase
    from scripts.function_tracer_pcode.proof.strategies.pairwise_query_executor import (
        require_satisfiable_pair_premises,
    )

    def case(index):
        return ReturnCase(
            index=index, conditions=[], value_expr=published(_const(index, 4)), return_info=None,
            return_type="int", parameters=[],
        )

    cases1 = [case(i) for i in range(3)]
    cases2 = [case(j) for j in range(4)]
    base_ctx = {
        "header_lines": ["(declare-const p (_ BitVec 32))"],
        "smt_logic": "QF_BV",
        "call_projection_assertions_by_pair": {
            f"({i},{j})": [f"; call projection for pair ({i},{j})\n(assert (bvult p (_ bv9 32)))"]
            for i in range(3) for j in range(4)
        },
    }
    calls = []

    class _Strategy:
        _active_normalization_stats = {}

        def _solve_premise_query(self, scope, query):
            calls.append(scope)
            return True

    require_satisfiable_pair_premises(_Strategy(), base_ctx, cases1, cases2, None, None)

    assert len(calls) == 1
    # 制約が違えば別の前提
    base_ctx["call_projection_assertions_by_pair"]["(2,3)"] = ["(assert (= p (_ bv1 32)))"]
    base_ctx.pop("proof_premise_status", None)
    calls.clear()
    require_satisfiable_pair_premises(_Strategy(), base_ctx, cases1, cases2, None, None)
    assert len(calls) == 2


# ---------------------------------------------------------------------------
# レビュー 3 回目（同種）: 幅の違う比較も伸ばし方を推測しない
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("operator,constant", [
    ("INT_EQUAL", 4), ("INT_NOTEQUAL", 0x7FFFFFFF), ("INT_LESS", 4), ("INT_LESSEQUAL", 0x7FFFFFFF),
])
def test_unsigned_comparison_with_a_sign_clear_constant_does_not_depend_on_the_extension(operator, constant):
    """``ext(x) op c``（c は狭い幅で最上位 bit が 0）は zero・sign どちらでも同じ値。参照値と照合する。"""
    x = Expression(ExpressionType.PARAMETER, name="x", size=4)
    smt = published(_bin(operator, x, _const(constant, 8), size=1)).to_smt()
    ops = {
        "INT_EQUAL": lambda a, b: a == b, "INT_NOTEQUAL": lambda a, b: a != b,
        "INT_LESS": lambda a, b: a < b, "INT_LESSEQUAL": lambda a, b: a <= b,
    }
    for value in (0, 4, 5, 0x7FFFFFFF, INT32_MIN, 0xFFFFFFFF):
        by_zero = ops[operator](_zext(value, 32), constant)
        by_sign = ops[operator](_sext(value, 32, 64), constant)
        assert by_zero == by_sign
        assert _z3_value(f"(ite {smt} (_ bv1 1) (_ bv0 1))", {"x": (32, value)}) == int(by_zero)


@pytest.mark.parametrize("operator,constant", [
    ("INT_SLESS", 4), ("INT_SLESSEQUAL", 0), ("INT_LESS", 0xFFFFFFFF), ("INT_EQUAL", 0xFFFFFFFF80000000),
])
def test_comparison_whose_value_depends_on_the_extension_is_refused(operator, constant):
    x = Expression(ExpressionType.PARAMETER, name="x", size=4)
    with pytest.raises(SMT_SEMANTICS_REFUSALS):
        published(_bin(operator, x, _const(constant, 8), size=1)).to_smt()


def test_zero_constant_is_not_narrowed_under_a_signed_ordering():
    from scripts.function_tracer_pcode.semantics.semantic_width import SemanticWidthNormalizer
    from scripts.function_tracer_pcode.semantics.rewrite_contract import EMPTY_REWRITE_AUTHORIZATION

    x = Expression(ExpressionType.PARAMETER, name="x", size=4)
    normalizer = SemanticWidthNormalizer({}, EMPTY_REWRITE_AUTHORIZATION)
    signed = normalizer.rewrite_expression(published(_bin("INT_SLESS", x, _const(0, 8), size=1)))
    unsigned = normalizer.rewrite_expression(published(_bin("INT_EQUAL", x, _const(0, 8), size=1)))

    assert signed.operands[1].size == 8  # 狭めない（x の伸ばし方を決めない）
    assert unsigned.operands[1].size == 4  # 等値は伸ばし方に依らない

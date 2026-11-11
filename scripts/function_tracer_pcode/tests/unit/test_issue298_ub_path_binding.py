# -*- coding: utf-8 -*-
"""Issue #298: UB 除外の制約は、その演算が実行される経路にだけ課す。

* EQ の前提には、比べる case の演算の制約だけを、その組の guard の下で課す。制約が
  guard だけでは到達できる組の領域を空にするなら課さない（UB 制約だけが入力を除いた
  UNSAT を EQ の根拠にしない）。
* NOT_EQ の witness は、両方の関数の全ての演算が UB を起こさない入力に限る（実行を上から
  近似した反例の領域）。
* UB の幅は binary の演算の幅（型の仮説が引数の葉を狭めても、演算の UB 条件は変えない）。

production の check 経路（phase workflow・strategy・z3 CLI・authority）をそのまま使い、
Ghidra の解析だけを合成する（``_production_check_harness``）。fixture は合成で、EqBench の
ground truth ではない。各 fixture の docstring に、source 上の意味と base（``668767d9``）での
結果を書く。
"""

from __future__ import annotations

from scripts.function_tracer_pcode.core import (
    Condition,
    Expression,
    ExpressionType,
    FunctionReturnAnalysis,
    ReturnInfo,
)
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
from scripts.function_tracer_pcode.proof.ub.constraints import UbConstraintBuilder
from scripts.function_tracer_pcode.proof.ub.premise import admissible_pair_obligations
from scripts.function_tracer_pcode.tests.conftest import create_mock_data_type_manager, resolve_mock_data_type
from scripts.function_tracer_pcode.tests.unit._production_check_harness import run_production_check
from scripts.function_tracer_pcode.tests.unit._publication import published
from scripts.function_tracer_pcode.tests.unit.test_void_effect_only_return_abi_issue104 import _abi_facts

_DTM = create_mock_data_type_manager()


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


def _outcome(result):
    final = result.get("final_outcome")
    if isinstance(final, dict):
        return final.get("outcome")
    return final


def _reason_ids(result):
    return {str(row.get("reason_id")) for row in result.get("c_active_base") or ()}


# ---------------------------------------------------------------------------
# f / g: premise は SAT だが、別の経路の制約が正当な反例を除く（レビューの例）
# ---------------------------------------------------------------------------


def _shift_by_x_minus_one(x):
    return _bin("INT_LEFT", _const(1, 4), _bin("INT_SUB", x, _const(1, 4)))


def _fg(name, zero_value):
    """``name(x) = x == 0 ? zero_value : 1u << (x - 1)``（x は unsigned int）。

    f は zero_value = 0、g は zero_value = 1。x = 0 で f(0) = 0、g(0) = 1（UB は無い:
    shift は x != 0 の経路でだけ実行される）。EQ は偽。
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

    # x = 0 は正しい反例だが、反例の領域は関数全体の UB 除外を無条件に課す（どの演算が
    # 実行されるかを binary の経路から示せない）ので、x = 0 を witness にできない。
    # EQ にも NOT_EQ にもせず、理由つきの UNKNOWN にする。
    assert _outcome(result) == "UNKNOWN"
    assert "counterexample_ub_domain_violated" in _reason_ids(result)


# ---------------------------------------------------------------------------
# hashCode の形: 64 bit の引数の上位 bit を読む式で、引数を 32 bit に狭める仮説
# ---------------------------------------------------------------------------


def _hash(name, *, mix_high):
    """``name(long y) = (int)(y ^ (y >> 32))``（mix_high）/ ``(int)y``（not mix_high）。

    binary の形: ``SUBPIECE(y, 0) ^ SUBPIECE(INT_RIGHT(y, 32), 0)``（64 bit の shift）。
    base では、``SUBPIECE(y, 0)`` だけを見た semantic hint が y を 32 bit に狭め、
    ``y >> 32`` が 32 bit の値の 32 bit の shift になる（UB 除外は恒偽の ``32 < 32``）。
    mix_high と not mix_high は y = 1 << 32 で 1 と 0（EQ は偽）。
    この合成の組は base でも P0（仮説の前）が反例を見つけて NOT_EQ になる。EqBench の
    hashCode では P0 が入力対応の不足で UNKNOWN になり、P1 の再試行で恒偽の前提が現れる
    （P1 の仮説の下の判定は Issue #185 の入力領域の authority が止める）。ここでは判定が
    EQ にならないことを固定する。
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


def test_hashcode_shape_is_not_equivalent_through_a_vacuous_premise():
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
    全ての query が UNSAT で、pairwise の証明は等価（``solver_results.is_equivalent`` が真）
    になる（AC1: premise が UNSAT の query を EQ に使う）。この合成の解析では、base の最終
    outcome は authority の終端の別の検査（Phase 7 の producer activation が無い）で ERROR に
    なるので、証明の結果そのものも確かめる。
    """

    x = _param("x", 4, "uint", 0)
    value = _bin("INT_LEFT", x, _const(40, 4)) if overshift else x
    return _analysis(
        name, [_descriptor("x", 4, "uint", False, 0)], [ReturnInfo("0x10", value, [])],
        return_type="uint",
    )


def test_unsatisfiable_ub_premise_is_not_equivalence_evidence():
    result = run_production_check(
        "i298-vacuous", _constant_overshift("f", overshift=True), _constant_overshift("g", overshift=False),
    )

    assert (result.get("solver_results") or {}).get("is_equivalent") is not True
    assert _outcome(result) == "UNKNOWN"
    assert "counterexample_ub_domain_violated" in _reason_ids(result)


# ---------------------------------------------------------------------------
# 正当な UB の利用（正例）: 比べる case の演算の制約は EQ の前提に使う
# ---------------------------------------------------------------------------


def _shift(name, *, masked):
    """``name(x, n) = x << n``（masked なら ``x << (n & 31)``）。32 bit。

    n < 32（C で UB の無い入力）では等しい。n >= 32 は ``x << n`` の UB。EQ（C の意味）。
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


def test_constraint_of_the_compared_case_still_proves_equivalence():
    result = run_production_check("i298-shift", _shift("f", masked=False), _shift("g", masked=True))

    assert _outcome(result) == "EQUIVALENT"


# ---------------------------------------------------------------------------
# guard だけで到達不能な組（正例）と、UB 制約だけが組を空にする形（負例）
# ---------------------------------------------------------------------------


def _guarded_shift(name, *, in_range_value):
    """``name(x, n) = n < 32 ? <in_range_value> : 0``（unsigned）。

    in_range_value が None なら ``x << n``。左右で ``n < 32`` と ``!(n < 32)`` の組は guard だけで
    到達不能（UB 除外は要らない）。
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

    f（shifted）の n >= 32 の経路は全ての入力で UB。この経路の組は「UB 制約だけが入力を
    除いた」組で、EQ の根拠にしない（base では EQUIVALENT）。
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


def test_ub_alone_emptying_a_reachable_case_pair_is_not_equivalence_evidence():
    result = run_production_check("i298-always-ub", _always_ub("f", shifted=True), _always_ub("g", shifted=False))

    assert _outcome(result) == "UNKNOWN"
    assert "counterexample_ub_domain_violated" in _reason_ids(result)


def _narrow_domain(name, *, low_value):
    """``name(n) = n >= 10 ? n + low_value : 1u << (n ^ 0x12340)``（unsigned）。

    shift の UB 除外 ``(n ^ 0x12340) < 32`` は n を 0x12340..0x1235f に限る。f（low_value=0）と
    g（low_value=1）は n >= 10 の経路で常に違う。この経路は shift を実行しないので、n = 10 も
    正しい反例だが、反例の領域（両方の関数の全ての演算の制約を無条件に課す）は
    n = 0x12340..0x1235f の witness だけを認める。value query の model が領域の外に出ても、
    領域の中で解き直せば witness が見つかる（base では UB 除外が全ての query の前提に入り
    NOT_EQUIVALENT）。
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
# 部品の契約
# ---------------------------------------------------------------------------


def _infos(*specs):
    return [
        ParameterInfo(original_name=name, smt_name=f"{name}_1", bit_width=bits, index=i, is_signed=signed)
        for i, (name, bits, signed) in enumerate(specs)
    ]


def test_shift_width_comes_from_the_binary_operation_not_the_narrowed_leaf():
    """型の仮説が葉だけを 32 bit にしても、64 bit の shift の UB 条件は ``count < 64``。"""

    y = Expression(ExpressionType.PARAMETER, name="y", size=4)  # 仮説で狭まった葉
    shift = Expression(ExpressionType.BINARY_OP, operator="INT_RIGHT", operands=[y, _const(32, 4)], size=8)
    var_shift = Expression(
        ExpressionType.BINARY_OP, operator="INT_LEFT",
        operands=[y, Expression(ExpressionType.PARAMETER, name="n", size=4)], size=8,
    )
    builder = UbConstraintBuilder()

    assert builder.collect_obligations([published(shift)], _infos(("y", 32, True))) == []
    (obligation,) = builder.collect_obligations(
        [published(var_shift)], _infos(("y", 32, True), ("n", 32, False)),
    )
    assert obligation.term == "(bvult n (_ bv64 32))"


def test_negation_whose_operand_was_narrowed_is_not_an_equivalence_premise():
    y = Expression(ExpressionType.PARAMETER, name="y", size=4)
    negation = Expression(ExpressionType.UNARY_OP, operator="INT_2COMP", operands=[y], size=8)

    (obligation,) = UbConstraintBuilder().collect_obligations([negation], _infos(("y", 32, True)))
    assert obligation.eq_admissible is False


def test_admissibility_drops_obligations_that_empty_the_region():
    lines = ("; c", "(assert (bvult n (_ bv32 32)))")

    assert admissible_pair_obligations(lines, lambda _l: True).lines == lines
    assert admissible_pair_obligations(lines, lambda _l: False).verdict == "region_excluded"
    assert admissible_pair_obligations(lines, lambda _l: False).lines == ()
    assert admissible_pair_obligations(lines, lambda _l: None).lines == ()
    assert admissible_pair_obligations(("; only a comment",), lambda _l: True).verdict == "none"

# -*- coding: utf-8 -*-
"""Issue #211（plan v4 PR-B）: 解析は比較の符号を多数決で書き換えない。

P-code の比較演算子（``INT_LESS`` / ``INT_SLESS`` ...）は機械語の意味である。同じ scalar に符号付きと
符号なしの比較が混ざっていても、片方へ揃える書き換えは「意味を変えない（形だけ）」か「意味を変える
（誤り）」のどちらかで、多数決の score はどちらなのかを決めない。撤去前は、解析の公開境界より前で
``repair_mixed_scalar_signedness`` が score の多い側へ比較を書き換えていた。

ここで固定すること:

* (a) 反例: 書き換えが path の許す入力で関数の値を変える形（``p211b``・Issue 本文の fixture）。解析の
  公開前の段（本物の ``ReturnAnalyzer.analyze_function_by_name``）を通しても比較は元のまま、関数の値も
  元のまま。
* (b) 対照: 混在の無い解析は段を通しても変わらない。意味を変えない混在（AC2）も書き換えず、等しさは
  solver が示す（形を揃えて示さない）。
* (c) production: 左右の解析が公開前の段を通った後、本物の checker で判定する。撤去前は、書き換えで
  本当に等価な pair が EQ にならず、等価でない pair が EQ になった。

左右・各 return は合成（EqBench の ground truth ではない）。期待する関係は、機械語の意味（書き換え前の
式）を z3 で評価して決め、test の中で確かめる。
"""

from __future__ import annotations

import shutil
from typing import Any, Dict, List, Optional

import pytest

from scripts.function_tracer_pcode.core.analysis import FunctionReturnAnalysis, ReturnInfo
from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.expression import Condition, Expression, ExpressionType
from scripts.function_tracer_pcode.tests.conftest import create_mock_data_type_manager, resolve_mock_data_type
from scripts.function_tracer_pcode.tests.unit._analyzer_pipeline_harness import analyze_through_pipeline
from scripts.function_tracer_pcode.tests.unit.test_void_effect_only_return_abi_issue104 import _abi_facts


_COMPARISONS = {"INT_LESS", "INT_LESSEQUAL", "INT_SLESS", "INT_SLESSEQUAL"}
_DTM = create_mock_data_type_manager()


# ---------------------------------------------------------------------------
# fixtures（合成）
# ---------------------------------------------------------------------------


def _value() -> Expression:
    return Expression.parameter("value", 0, data_type="int", size=4)


def _k(value: int) -> Expression:
    return Expression.constant(value, size=4)


def _cmp(operator: str, left: Expression, right: Expression) -> Expression:
    return Expression(ExpressionType.BINARY_OP, operator=operator, operands=[left, right], size=1)


def _cond(operator: str, left: Expression, right: Expression) -> Condition:
    return Condition(_cmp(operator, left, right), False)


def _tail(operator: str) -> Expression:
    """``ZEXT(100 <op> value) | 2``（``branch_sign_bucket`` の tail と同じ形）。"""

    selector = Expression(ExpressionType.UNARY_OP, operator="INT_ZEXT", operands=[_cmp(operator, _k(100), _value())], size=4)
    return Expression(ExpressionType.BINARY_OP, operator="INT_OR", operands=[selector, _k(2)], size=4)


def _analysis(name: str, returns: List[ReturnInfo]) -> FunctionReturnAnalysis:
    """解析器が return を得た時点の（公開前の）解析。"""

    analysis = FunctionReturnAnalysis(
        function_name=name,
        entry_point="0x401000",
        parameters=[{
            "name": "value", "index": 0, "size": 4, "data_type": "int", "is_signed": True,
            "data_type_obj": resolve_mock_data_type("int", _DTM),
        }],
        returns=returns,
        return_type="int",
        function_ref=CallTargetRef.from_name(name, program_id=sum(map(ord, name)), entry_offset=0x401000),
        binary_id="bin-" + name,
    )
    analysis.return_abi_facts = _abi_facts(return_type="/int", type_length=4, storage="PRESENT")
    return analysis


def _p211b(name: str = "f") -> FunctionReturnAnalysis:
    """``value s< -200`` のとき ``ZEXT(100 u< value) | 2``、それ以外は 0。

    符号付きの比較の score（負の定数との比較で 4 ずつ）が符号なしの 1 を上回るので、撤去前は tail の
    ``u<`` が ``s<`` に書き換わった。path が許す ``value = -250`` で、機械語の値は 3（``100 u< 0xffffff06``
    は真）、書き換え後は 2。
    """

    return _analysis(name, [
        ReturnInfo(address="0x401010", value=_tail("INT_LESS"),
                   conditions=[_cond("INT_SLESS", _value(), _k(-200))], branch_index=1),
        ReturnInfo(address="0x401020", value=_k(0),
                   conditions=[_cond("INT_SLESS", _k(-201), _value())], branch_index=2),
    ])


def _p211b_folded(name: str, value_on_negative_path: int) -> FunctionReturnAnalysis:
    """``_p211b`` と同じ path で、tail の代わりに定数を返す（比較の混在が無いので書き換えの対象外）。"""

    return _analysis(name, [
        ReturnInfo(address="0x401010", value=_k(value_on_negative_path),
                   conditions=[_cond("INT_SLESS", _value(), _k(-200))], branch_index=1),
        ReturnInfo(address="0x401020", value=_k(0),
                   conditions=[_cond("INT_SLESS", _k(-201), _value())], branch_index=2),
    ])


def _issue211_fixture() -> FunctionReturnAnalysis:
    """Issue #211 本文の fixture: 2 本目の path（``-101 s< value ∧ value != 0``）が ``value = -50`` を許す。"""

    return _analysis("branch_sign_bucket", [
        ReturnInfo(address="0x401004", value=_k(-2),
                   conditions=[_cond("INT_SLESS", _k(-101), _value()), _cond("INT_SLESS", _value(), _k(0))],
                   branch_index=10),
        ReturnInfo(address="0x401008", value=_tail("INT_LESS"),
                   conditions=[_cond("INT_SLESS", _k(-101), _value()), _cond("INT_NOTEQUAL", _value(), _k(0))],
                   branch_index=20),
    ])


def _meaning_preserving_mix(tail_operator: str, name: str = "f") -> FunctionReturnAnalysis:
    """混在はあるが、tail の path（``0 s< value``）の上では ``u<`` と ``s<`` が一致する形（Issue #211 AC2）。

    ``tail_operator="INT_LESS"`` のとき撤去前は score（符号付き 4 / 符号なし 1）で ``s<`` に書き換わった。
    """

    return _analysis(name, [
        ReturnInfo(address="0x401010", value=_tail(tail_operator),
                   conditions=[_cond("INT_SLESS", _k(0), _value())], branch_index=1),
        ReturnInfo(address="0x401020", value=_k(0),
                   conditions=[_cond("INT_SLESS", _value(), _k(1))], branch_index=2),
    ])


def _signed_only(name: str = "f") -> FunctionReturnAnalysis:
    return _analysis(name, [
        ReturnInfo(address="0x401010", value=_tail("INT_SLESS"),
                   conditions=[_cond("INT_SLESS", _value(), _k(-200))], branch_index=1),
        ReturnInfo(address="0x401020", value=_k(0),
                   conditions=[_cond("INT_SLESS", _k(-201), _value())], branch_index=2),
    ])


# ---------------------------------------------------------------------------
# 観測: 比較演算子の列と、機械語の意味（z3 で評価した値）
# ---------------------------------------------------------------------------


def _comparison_operators(expr: Any) -> List[str]:
    found: List[str] = []

    def walk(node: Any) -> None:
        if node is None:
            return
        if getattr(node, "expr_type", None) == ExpressionType.BINARY_OP and node.operator in _COMPARISONS:
            found.append(node.operator)
        for operand in getattr(node, "operands", None) or ():
            walk(operand)
        if getattr(node, "expr_type", None) == ExpressionType.PHI and node.value:
            for condition, value in node.value:
                walk(getattr(condition, "expression", None))
                walk(value)

    walk(expr)
    return found


def _operator_profile(analysis: Any) -> List[Dict[str, Any]]:
    """return ごとの（address、値の比較演算子、条件の比較演算子）。"""

    return sorted(
        (
            {
                "address": str(info.address),
                "value": _comparison_operators(info.value),
                "conditions": [op for cond in info.conditions or () for op in _comparison_operators(cond.expression)],
            }
            for info in analysis.returns or ()
        ),
        key=lambda row: row["address"],
    )


def _value_at(analysis: Any, value: int) -> Optional[int]:
    """公開した解析の関数の値を z3 で評価する（``value`` を固定し、条件が成り立つ最初の return の値。
    どの return の条件も成り立たなければ None）。"""

    z3 = pytest.importorskip("z3")
    from scripts.function_tracer_pcode.core.render_smt import condition_to_smt, expression_to_smt

    for info in analysis.returns:
        solver = z3.Solver()
        conditions = "".join(f"(assert {condition_to_smt(cond)})" for cond in info.conditions or ())
        solver.from_string(
            "(declare-const value_1 (_ BitVec 32))(declare-const value (_ BitVec 32))(declare-const out (_ BitVec 32))"
            f"(assert (= value (_ bv{value % (1 << 32)} 32)))(assert (= value_1 value))"
            f"{conditions}(assert (= out {expression_to_smt(info.value)}))"
        )
        if solver.check() == z3.sat:
            return solver.model().eval(z3.BitVec("out", 32)).as_signed_long()
    return None


def _machine_value_at(template: Any, value: int) -> Optional[int]:
    """書き換え前の式（template）の値。公開境界だけを通し、解析器の段は通さない。"""

    from scripts.function_tracer_pcode.tests.unit._production_check_harness import publish_like_the_analyzer

    return _value_at(publish_like_the_analyzer(template), value)


def _assert_no_comparison_was_flipped(published: Any, template: Any) -> None:
    """値の比較は元のまま。条件は段の正規化（return region の排他化）で増え得るが、元の比較は残る。"""

    from collections import Counter

    got = {row["address"]: row for row in _operator_profile(published)}
    for row in _operator_profile(template):
        assert got[row["address"]]["value"] == row["value"], row["address"]
        assert not Counter(row["conditions"]) - Counter(got[row["address"]]["conditions"]), row["address"]


# ---------------------------------------------------------------------------
# (a) 反例: 公開前の段を通しても比較は元のまま
# ---------------------------------------------------------------------------


def test_the_p211b_shape_is_a_real_counterexample():
    """反例の前提: ``value = -250`` で、書き換え前の式は 3、書き換え後の式（tail を ``s<``）は 2。"""

    assert _machine_value_at(_p211b(), -250) == 3
    assert _machine_value_at(_signed_only(), -250) == 2


@pytest.mark.parametrize("build", [_p211b, _issue211_fixture])
def test_analyzer_keeps_the_comparison_that_a_signedness_vote_would_flip(build):
    published = analyze_through_pipeline(build())

    _assert_no_comparison_was_flipped(published, build())
    assert "object_centric_scalar_signedness_repair" not in published.analysis_notes
    # 解析の関数の値は書き換え前の式の値と同じ（Issue 本文の fixture の 2 本目は ``value = -50`` を条件に
    # 含むが、1 本目が先に成り立つので関数の値は -2。``value <= -101`` と 0 ではどの return も成り立たない）。
    # 区間の両端と内側を見る。
    assert _value_at(published, -250) == 3 if build is _p211b else _value_at(published, -50) == -2
    for witness in (-2**31, -250, -201, -200, -101, -100, -50, -1, 0, 1, 100, 101, 2**31 - 1):
        assert _value_at(published, witness) == _machine_value_at(build(), witness), witness


# ---------------------------------------------------------------------------
# (b) 対照
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("build", [_signed_only, lambda: _p211b_folded("f", 3)])
def test_analysis_without_mixed_comparisons_passes_the_stage_unchanged(build):
    template = build()
    published = analyze_through_pipeline(template)

    _assert_no_comparison_was_flipped(published, template)
    assert len(published.returns) == len(template.returns)


def test_meaning_preserving_mix_is_kept_as_is_too():
    """AC2: path の上で意味が変わらない混在も書き換えない（意味を保つかは形ではなく solver が決める）。"""

    template = _meaning_preserving_mix("INT_LESS")
    published = analyze_through_pipeline(template)

    _assert_no_comparison_was_flipped(published, template)
    for witness in (-2**31, -1, 0, 1, 100, 101, 2**31 - 1):
        assert _value_at(published, witness) == _machine_value_at(_meaning_preserving_mix("INT_LESS"), witness)
        assert _value_at(published, witness) == _machine_value_at(_meaning_preserving_mix("INT_SLESS"), witness)


# ---------------------------------------------------------------------------
# (c) production: 公開前の段を通した左右を、本物の checker で判定する
# ---------------------------------------------------------------------------


def _production(case_id: str, left: Any, right: Any) -> Dict[str, Any]:
    from scripts.function_tracer_pcode.tests.unit._production_check_harness import run_production_check

    if shutil.which("z3") is None:
        pytest.fail("the production check needs the z3 CLI on PATH (not skipped: a missing solver must not pass)")
    return run_production_check(case_id, left, right, analyze=analyze_through_pipeline)


def test_production_check_keeps_an_equivalent_pair_equivalent():
    """左は tail に ``u<``、右は path の上で同じ値（3）の定数。撤去前は左だけ書き換わり EQ にならなかった。"""

    left, right = _p211b("f"), _p211b_folded("g", 3)
    assert _machine_value_at(_p211b("f"), -250) == _machine_value_at(_p211b_folded("g", 3), -250) == 3

    result = _production("pr211-p211b-eq", left, right)
    assert result["final_outcome"] == "EQUIVALENT"


def test_production_check_does_not_equate_the_vote_result_with_the_original():
    """右は撤去前の書き換えの結果と同じ関数（path の上で 2）。機械語では ``value = -250`` で 3 と 2 が違う。

    撤去前は左が書き換わって右と同じになり、誤った EQ になった。
    """

    left, right = _p211b("f"), _p211b_folded("g", 2)
    assert _machine_value_at(_p211b("f"), -250) == 3
    assert _machine_value_at(_p211b_folded("g", 2), -250) == 2

    result = _production("pr211-p211b-neq", left, right)
    assert result["final_outcome"] == "NOT_EQ"


def test_production_check_proves_a_meaning_preserving_mix_by_the_solver():
    """AC2 の対照: 形を揃えなくても、path の上で意味が同じなら solver が EQ を示す。"""

    result = _production("pr211-ac2-eq", _meaning_preserving_mix("INT_LESS", "f"), _meaning_preserving_mix("INT_SLESS", "g"))
    assert result["final_outcome"] == "EQUIVALENT"

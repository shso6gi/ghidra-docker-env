# -*- coding: utf-8 -*-
"""Issue #215: 予算付き構造 key の取り違えが production path の最終判定へ届かない。

phase workflow・stage plan・pairwise strategy・z3 CLI・production cutover connector は
すべて本物で、Ghidra の解析だけを差し替える（`_production_check_harness`）。

* **E2E-3**（1 回の case merge）: 左は ordered に ``(A → 1), (B → 1), (else → 0)``、
  右は ``(A → 1), (else → 0)``。A と B は末尾の定数だけが違う深い条件
  （``param_1 + 0 + … + (N-2) <s 10`` / ``<s 20`` を balanced な和で組む）。``param_1 + Σ ∈ [10, 20)`` で
  左は 1、右は 0 を返すので **NOT_EQ が正しい**。main（`2f30b9f`）では予算 256 の
  case key が A と B を同じにし、`extract_return_cases` が B の case を A に merge して
  捨てるので **final EQUIVALENT（偽）** になる。
* **E2E-1**（process 全体の oracle cache の汚染）: 左の最初の case は死んだ条件
  ``… <s INT_MIN``、次の case は末尾だけが違う生きた条件 ``… <s 20``。main では死んだ
  条件の UNSAT が cache され、budget 96 の key が同じ生きた条件もその UNSAT を引いて
  case が消える。右も同じ形で値だけが違う（1 と 2）ので **NOT_EQ が正しい**。main では
  消えた case のせいで return coverage の証明束が欠け、monolithic の結合で ERROR になる
  （誤った事実が判定面まで届いている）。
* control: width 10（予算内）では main でも NOT_EQ。
"""

from __future__ import annotations

import pytest

from scripts.function_tracer_pcode.core import Condition, Expression, ReturnInfo
from scripts.function_tracer_pcode.tests.unit._production_check_harness import run_production_check
from scripts.function_tracer_pcode.tests.unit.test_issue185_type_hypothesis_domain import (
    _analysis,
    _descriptor,
)

INT_MIN = -(2 ** 31)


def _const(value):
    return Expression.constant(value, size=4)


def _chain(width):
    """``param_1 + 0 + 1 + … + (width-2)`` を **balanced な和** で組む（distinct node ≈ 2·width）。

    深い左傾きの chain にしないのは、SMT 描画の幅計算が深さに対して超線形で、
    width 140 の chain だと 1 件 200 秒を超えるため（本 Issue とは無関係の既存の費用）。
    予算は distinct node で数えるので、浅くても末尾は打ち切られる。
    """

    nodes = [Expression.parameter("param_1", 0, data_type="int", size=4)]
    nodes += [_const(index) for index in range(width - 1)]
    while len(nodes) > 1:
        paired = [Expression.binary_op("INT_ADD", nodes[i], nodes[i + 1]) for i in range(0, len(nodes) - 1, 2)]
        if len(nodes) % 2:
            paired.append(nodes[-1])
        nodes = paired
    return nodes[0]


def _less(width, bound):
    return Condition(Expression.binary_op("INT_SLESS", _chain(width), _const(bound)))


def _parameters():
    return [_descriptor("param_1", 4, "int", True)]


def _e2e3(width):
    left = _analysis("left", _parameters(), [
        ReturnInfo("0x10", _const(1), [_less(width, 10)]),
        ReturnInfo("0x20", _const(1), [_less(width, 20)]),
        ReturnInfo("0x30", _const(0), []),
    ])
    right = _analysis("right", _parameters(), [
        ReturnInfo("0x10", _const(1), [_less(width, 10)]),
        ReturnInfo("0x30", _const(0), []),
    ])
    return left, right


def _e2e1(width):
    def side(name, live_value):
        return _analysis(name, _parameters(), [
            ReturnInfo("0x10", _const(5), [_less(width, INT_MIN)]),
            ReturnInfo("0x20", _const(live_value), [_less(width, 20)]),
            ReturnInfo("0x30", _const(0), []),
        ])

    return side("left", 1), side("right", 2)


@pytest.mark.parametrize("width", [10, 140])
def test_e2e3_a_single_case_merge_does_not_reach_a_false_equivalent(width):
    left, right = _e2e3(width)
    result = run_production_check(f"sn3-e2e3-{width}", left, right)
    assert result["final_outcome"] == "NOT_EQ", (result["final_outcome"], result.get("error_message"))
    assert result["is_equivalent"] is False


@pytest.mark.parametrize("width", [10, 60])
def test_e2e1_the_oracle_cache_is_not_shared_between_different_deep_conditions(width):
    from scripts.function_tracer_pcode.analysis.condition.smt_oracle import ConditionSMTOracle

    ConditionSMTOracle._unsat_cache.clear()
    left, right = _e2e1(width)
    result = run_production_check(f"sn3-e2e1-{width}", left, right)
    assert result["final_outcome"] == "NOT_EQ", (result["final_outcome"], result.get("error_message"))
    assert result["is_equivalent"] is False

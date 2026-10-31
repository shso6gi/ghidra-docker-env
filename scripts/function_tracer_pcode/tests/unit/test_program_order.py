# -*- coding: utf-8 -*-
"""Issue #281 / #285: 関数の中の program point の順序（`core.program_order`）。

key は関数の CFG の線形拡大（ある実行で a が b より前に実行され得るなら key(a) < key(b)）。基本 block の番号・
番地の順は実行順と限らない（分岐が前へ飛ぶ配置）。loop の中の point どうしは比べられない（`in_cycle`）。
"""

import pytest

from scripts.function_tracer_pcode.core.program_order import ProgramOrder


def test_the_key_orders_positions_within_a_block():
    order = ProgramOrder({0: []})
    assert order.key(0, 1) < order.key(0, 2)


def test_the_key_follows_the_cfg_not_the_block_numbers():
    """block 2 が block 1 より先に実行される配置（0 → 2 → 1）。番号の順ではなく辺の順に並ぶ。"""

    order = ProgramOrder({0: [2], 2: [1], 1: []})
    assert order.key(0, 9) < order.key(2, 0) < order.key(1, 0)
    # 後ろの block の先頭は、前の block の最後の op より後
    assert order.key(2, 50) < order.key(1, 0)


def test_every_path_of_a_diamond_is_ordered():
    """0 → {1, 2} → 3: どちらの腕の point も、入口の後・合流の前。"""

    order = ProgramOrder({0: [1, 2], 1: [3], 2: [3], 3: []})
    for arm in (1, 2):
        assert order.key(0, 5) < order.key(arm, 0) < order.key(3, 0)


def test_a_loop_is_one_component_whose_points_are_marked():
    """0 → 1 → 2 → 1（loop）、2 → 3。loop の外とは正しく比べ、loop の中は `in_cycle` にする。"""

    order = ProgramOrder({0: [1], 1: [2], 2: [1, 3], 3: []})
    assert order.has_cycle
    assert order.block_in_cycle(1) and order.block_in_cycle(2)
    assert not order.block_in_cycle(0) and not order.block_in_cycle(3)
    assert order.in_cycle(order.key(1, 0)) and order.in_cycle(order.key(2, 4))
    assert not order.in_cycle(order.key(0, 0)) and not order.in_cycle(order.key(3, 0))
    assert order.key(0, 9) < order.key(1, 0)
    assert order.key(2, 9) < order.key(3, 0)


def test_a_self_loop_is_a_cycle():
    order = ProgramOrder({0: [0, 1], 1: []})
    assert order.block_in_cycle(0)
    assert not order.block_in_cycle(1)


@pytest.mark.parametrize("block, position", [(7, 0), (None, 0), (0, None), (0, -1), (0, 1 << 32)])
def test_an_unknown_point_has_no_key(block, position):
    """分からない point に key を推測しない（consumer が順序の無い読み出しと区別できるように None）。"""

    assert ProgramOrder({0: []}).key(block, position) is None


def test_the_order_is_deterministic_for_unordered_arms():
    successors = {0: [2, 1], 1: [3], 2: [3], 3: []}
    first = ProgramOrder(successors)
    second = ProgramOrder({3: [], 2: [3], 1: [3], 0: [1, 2]})
    assert all(first.key(block, 0) == second.key(block, 0) for block in successors)


def test_may_precede_follows_the_key_outside_loops_and_is_true_inside_one_loop():
    order = ProgramOrder({0: [1], 1: [2], 2: [1, 3], 3: []})
    assert order.may_precede(order.key(0, 0), order.key(3, 0))
    assert not order.may_precede(order.key(3, 0), order.key(0, 0))
    # loop の中では、後ろの op も次の回で前になる
    assert order.may_precede(order.key(2, 5), order.key(1, 0))
    assert order.may_precede(order.key(1, 3), order.key(1, 1))
    # loop の後の op は loop の op より前にならない
    assert not order.may_precede(order.key(3, 0), order.key(1, 0))
    assert order.may_precede(None, order.key(1, 0))

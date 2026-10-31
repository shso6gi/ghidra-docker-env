# -*- coding: utf-8 -*-
"""tracer の op の順序の key（Issue #281 / #285）。

key は関数の CFG から作った program point の key（`core.program_order`）で、読み出し・書き込み・呼び出しの
位置で同じ。修正前は `SequenceNumber.getOrder()` そのもの（基本 block の中の位置）で、別の block の op と
比べられなかった。
"""

from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer
from scripts.function_tracer_pcode.tests.unit._program_order_fakes import FakeOp, fake_cfg


def _tracer(high_function):
    tracer = object.__new__(PcodeTracer)
    tracer.high_function = high_function
    return tracer


def test_a_later_block_orders_after_every_op_of_an_earlier_block():
    """block 1 の位置 0 は、block 0 の位置 7 より後（`getOrder()` だけなら 0 < 7 で逆になる）。"""

    high_function, blocks = fake_cfg({0: [1], 1: []})
    tracer = _tracer(high_function)
    assert tracer._get_op_order_key(FakeOp(blocks[0], 7)) < tracer._get_op_order_key(FakeOp(blocks[1], 0))


def test_the_key_follows_control_flow_not_the_block_numbers():
    high_function, blocks = fake_cfg({0: [2], 2: [1], 1: []})
    tracer = _tracer(high_function)
    assert tracer._get_op_order_key(FakeOp(blocks[2], 3)) < tracer._get_op_order_key(FakeOp(blocks[1], 0))


def test_an_op_without_a_known_point_has_no_key():
    high_function, blocks = fake_cfg({0: []})
    tracer = _tracer(high_function)
    assert tracer._get_op_order_key(None) is None
    assert _tracer(object())._get_op_order_key(FakeOp(blocks[0], 1)) is None


def test_an_op_outside_the_cfg_has_no_key_even_when_the_function_has_an_order():
    """順序のある関数で op の位置だけが分からない: key を推測しない（tracer は LOAD を UNKNOWN にする）。"""

    high_function, _blocks = fake_cfg({0: []})
    tracer = _tracer(high_function)
    assert tracer.program_order() is not None
    assert tracer._get_op_order_key(FakeOp(None, 0)) is None

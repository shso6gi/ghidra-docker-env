# -*- coding: utf-8 -*-

from scripts.function_tracer_pcode.analysis.tracer import PcodeTracer


class _Seqnum:
    def __init__(self, order):
        self._order = order

    def getOrder(self):
        return self._order


class _PcodeOp:
    def __init__(self, *, seq_order=None, op_order=None):
        self._seq_order = seq_order
        self._op_order = op_order

    def getSeqnum(self):
        if self._seq_order is None:
            return None
        return _Seqnum(self._seq_order)

    def getOrder(self):
        return self._op_order


def _tracer():
    return object.__new__(PcodeTracer)


def test_get_op_order_key_prefers_sequence_number_order():
    op = _PcodeOp(seq_order="7", op_order=99)

    assert _tracer()._get_op_order_key(op) == 7


def test_get_op_order_key_falls_back_to_pcode_op_order():
    op = _PcodeOp(seq_order=None, op_order="12")

    assert _tracer()._get_op_order_key(op) == 12


def test_get_op_order_key_returns_none_for_missing_or_invalid_order():
    tracer = _tracer()

    assert tracer._get_op_order_key(None) is None
    assert tracer._get_op_order_key(_PcodeOp(seq_order="bad", op_order="also_bad")) is None

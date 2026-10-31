# -*- coding: utf-8 -*-
"""Ghidra の関数から `ProgramOrder` を作り、P-code op の program point の key を読む（Issue #281 / #285）。

順序の規則（何が何より前か）は `core.program_order` が持つ。この module は Ghidra の object から、その規則への
入力（基本 block の graph、op の block と block の中の位置）を読むだけ。読む API は condition tracker が CFG を
作るときと同じもの（`getBasicBlocks` / `getIndex` / `getOutSize` / `getOut` / `hashCode`）と、op の
`getParent().getIndex()` / `getSeqnum().getOrder()`。

op の key は、読み出し（tracer / expander の LOAD）、書き込み（effect 要約の STORE・呼び出しで入る callee の
effect）、呼び出しの位置（callee の読み出しを移す先）で **同じ関数で同じ** `ProgramOrder` から作る。
"""

from __future__ import annotations

import sys
from typing import Dict, List, Optional, Tuple

from scripts.function_tracer_pcode.core.program_order import ProgramOrder

_PYTHON_READ_ERRORS: Tuple[type, ...] = (AttributeError, TypeError, ValueError, RuntimeError)


def _graph_read_errors() -> Tuple[type, ...]:
    """graph を読むときに「読めない」とみなす例外。

    Ghidra の `PcodeBlock.getOut(i)` は `outofthis.get(i).point` を返す。decode の途中で埋まらなかった辺は
    `null` の要素のまま残るので、読めない辺は `None` ではなく Java の `NullPointerException` になる
    （JPype の `JException`。Python の `RuntimeError` の派生ではない）。範囲外の添字も Java の例外になる。
    どれも順序を保証できないので、key を出さない。
    """

    jpype = sys.modules.get("jpype")
    java_exception = getattr(jpype, "JException", None) if jpype is not None else None
    if isinstance(java_exception, type) and issubclass(java_exception, BaseException):
        return _PYTHON_READ_ERRORS + (java_exception,)
    return _PYTHON_READ_ERRORS


def program_order_for_high_function(high_function) -> Optional[ProgramOrder]:
    """`high_function` の基本 block の graph の順序。graph を読めなければ None（key を出さない）。

    辺を 1 本でも読めなければ（例外・`None`・graph の外の block）、その辺を無視して順序を作ってはいけない:
    無視した辺の先の block が前の block より先に並び得る（review 5）。
    """

    get_blocks = getattr(high_function, "getBasicBlocks", None)
    if not callable(get_blocks):
        return None
    try:
        # 反復だけで読む（condition tracker と同じ読み方。`list()` は長さも読む）
        blocks = []
        for block in get_blocks():
            blocks.append(block)
        index_by_hash: Dict[int, int] = {}
        for block in blocks:
            index_by_hash[int(block.hashCode())] = int(block.getIndex())
        successors: Dict[int, List[int]] = {}
        for block in blocks:
            outs: List[int] = []
            for position in range(int(block.getOutSize())):
                out_block = block.getOut(position)
                if out_block is None:
                    # API 上は起きない（読めない辺は例外になる）が、辺が分からないので順序を保証できない
                    return None
                out_index = index_by_hash.get(int(out_block.hashCode()))
                if out_index is None:
                    # graph の外の block へ辺がある: 順序を保証できない
                    return None
                outs.append(out_index)
            successors[int(block.getIndex())] = outs
    except _graph_read_errors():
        return None
    if not successors:
        return None
    return ProgramOrder(successors)


def op_block_index(pcode_op) -> Optional[int]:
    get_parent = getattr(pcode_op, "getParent", None)
    if not callable(get_parent):
        return None
    try:
        parent = get_parent()
        return None if parent is None else int(parent.getIndex())
    except _graph_read_errors():
        return None


def op_block_position(pcode_op) -> Optional[int]:
    """block の中の op の位置（`SequenceNumber.getOrder()`: block ごとに 0 から数える）。"""

    get_seqnum = getattr(pcode_op, "getSeqnum", None)
    if not callable(get_seqnum):
        return None
    try:
        seqnum = get_seqnum()
        return None if seqnum is None else int(seqnum.getOrder())
    except _graph_read_errors():
        return None


def op_program_key(order: Optional[ProgramOrder], pcode_op, *, block_index: Optional[int] = None) -> Optional[int]:
    """op の program point の key。`block_index` を知っている呼び出し側（block を順に読む effect 要約）は渡す。"""

    if order is None or pcode_op is None:
        return None
    if block_index is None:
        block_index = op_block_index(pcode_op)
    return order.key(block_index, op_block_position(pcode_op))

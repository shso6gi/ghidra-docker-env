# -*- coding: utf-8 -*-
"""Ghidra の基本 block の graph と P-code op の最小の偽物（Issue #281 / #285 の順序の test 用）。

production が読む API だけを持つ: block の `getIndex` / `hashCode` / `getOutSize` / `getOut`、op の
`getParent` / `getSeqnum().getOrder()` / `getMnemonic`、high function の `getBasicBlocks`。
"""

from typing import Dict, List, Sequence


class FakeBlock:
    def __init__(self, index: int):
        self._index = index
        self.outs: List["FakeBlock"] = []

    def getIndex(self):
        return self._index

    def hashCode(self):
        return 1000 + self._index

    def getOutSize(self):
        return len(self.outs)

    def getOut(self, position):
        return self.outs[position]


class FakeSeqnum:
    def __init__(self, order: int, address: int):
        self._order = order
        self._address = address

    def getOrder(self):
        return self._order

    def getTarget(self):
        return FakeAddress(self._address)


class FakeAddress:
    def __init__(self, offset: int):
        self._offset = offset

    def getOffset(self):
        return self._offset


class FakeOp:
    def __init__(self, block: FakeBlock, position: int, *, mnemonic: str = "COPY", address: int = 0x1000):
        self._block = block
        self._seqnum = FakeSeqnum(position, address)
        self._mnemonic = mnemonic

    def getParent(self):
        return self._block

    def getSeqnum(self):
        return self._seqnum

    def getMnemonic(self):
        return self._mnemonic


class FakeHighFunction:
    def __init__(self, blocks: Sequence[FakeBlock]):
        self._blocks = list(blocks)

    def getBasicBlocks(self):
        return list(self._blocks)


def fake_cfg(successors: Dict[int, Sequence[int]]):
    """`{block 番号: [後続の番号]}` から (high function, {番号: block})。"""

    blocks = {index: FakeBlock(index) for index in successors}
    for index, outs in successors.items():
        blocks[index].outs = [blocks[out] for out in outs]
    return FakeHighFunction(blocks.values()), blocks

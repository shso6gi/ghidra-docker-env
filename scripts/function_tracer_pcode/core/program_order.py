# -*- coding: utf-8 -*-
"""1 つの関数の中の program point の順序（Issue #281 / #285）。**読み出しと書き込みの順序の唯一の owner**。

memory の読み出し（`read_order_key` / `ObservedMemoryReadRef.order_key`）と store effect（`StoreEffect.order_key`）
の順序は、consumer が整数の `<` / 並べ替えで比べる:

* 読み出しより前の書き込みを選ぶ: `effect.order_key < read_order_key`（`effect.order_key >= max_order_key` を除く）
* 同じ位置への書き込みのうち最後のものを選ぶ・書き込みを順に再生する: `order_key` で並べる

この比べ方が正しい実行順序の前後関係になるには、**key が関数の CFG の線形拡大**（ある実行で a が b より前に
実行され得るなら key(a) < key(b)）でなければならない。修正前は、読み出しは op の `SequenceNumber.getOrder()`
（基本 block の中の位置。block ごとに 0 から数え直す）、書き込みは `(番地 << 8) | getOrder()` で、単位も意味も
違った（#285）。番地の順は、分岐が前へ飛ぶ配置（後ろの番地の block が先に実行される）では実行順と食い違う。

**key の規則**: 基本 block の graph の強連結成分を縮めた DAG の位相順位（`rank`）と、block の中の位置
（`getOrder()`）を組にした整数 `(rank << 32) | position`。

* 非巡回の部分では線形拡大になる: 同じ block の中は位置の順、別の block は、到達できるなら rank が小さい。
  分岐の別の腕どうし（どちらの実行にも両方は現れない）は任意の順になるが、consumer は書き込みの経路条件で
  食い違いを除く（同じ実行に現れない書き込みの枝は条件が矛盾する）。
* **巡回する成分（loop）の中では順序を保証しない**: 繰り返しの 2 回目は、1 回目の後ろの op の後に実行される。
  成分の外の point とは rank で正しく比べられるが、成分の中どうしは比べられない。巡回する成分の中の書き込みは
  producer が fail-closed にする（`in_cycle` を見て effect 要約を不完全にする）。成分の中の読み出しは、同じ成分に
  書き込みが無ければ、外の書き込みとだけ比べることになるので正しい。

key は同じ関数の中だけで比べられる。関数をまたぐ移送（callee の読み出しを caller の呼び出し位置へ）は
`analysis.effects.call_boundary` が持ち、caller の key を付け直す。

Ghidra の API には触らない（block の graph は呼び出し側が渡す: `analysis.program_points`）。
"""

from __future__ import annotations

import heapq
from typing import Dict, FrozenSet, List, Mapping, Optional, Sequence, Tuple

#: block の中の位置の幅。`getOrder()` はこれ未満でなければならない（超えたら key を出さない）
_POSITION_BITS = 32
_POSITION_LIMIT = 1 << _POSITION_BITS


class ProgramOrder:
    """1 つの関数の基本 block の graph から作った、program point の順序。"""

    __slots__ = ("_rank", "_cyclic_ranks", "_cyclic_blocks")

    def __init__(self, successors: Mapping[int, Sequence[int]]) -> None:
        blocks = sorted({int(block) for block in successors} | {int(s) for out in successors.values() for s in out})
        edges: Dict[int, Tuple[int, ...]] = {
            block: tuple(sorted({int(s) for s in successors.get(block, ())})) for block in blocks
        }
        components = _strongly_connected_components(blocks, edges)
        component_of: Dict[int, int] = {}
        for number, members in enumerate(components):
            for block in members:
                component_of[block] = number
        cyclic_components = {
            number
            for number, members in enumerate(components)
            if len(members) > 1 or any(block in edges[block] for block in members)
        }
        ranks = _topological_ranks(components, component_of, edges)
        self._rank: Dict[int, int] = {block: ranks[component_of[block]] for block in blocks}
        self._cyclic_ranks: FrozenSet[int] = frozenset(ranks[number] for number in cyclic_components)
        self._cyclic_blocks: FrozenSet[int] = frozenset(
            block for block in blocks if component_of[block] in cyclic_components
        )

    def key(self, block_index: Optional[int], position: Optional[int]) -> Optional[int]:
        """block `block_index` の位置 `position` の key。分からなければ None（consumer に推測させない）。"""

        if block_index is None or position is None:
            return None
        rank = self._rank.get(int(block_index))
        if rank is None or not 0 <= int(position) < _POSITION_LIMIT:
            return None
        return (rank << _POSITION_BITS) | int(position)

    def block_in_cycle(self, block_index: int) -> bool:
        return int(block_index) in self._cyclic_blocks

    def in_cycle(self, key: Optional[int]) -> bool:
        """key の point が巡回する成分の中にあるか（その中どうしの前後関係を key は表さない）。"""

        return key is not None and key >= 0 and (key >> _POSITION_BITS) in self._cyclic_ranks

    def may_precede(self, first: Optional[int], second: Optional[int]) -> bool:
        """ある実行で `first` の point が `second` の point より前に実行され得るか（key が無ければ True）。

        非巡回なら key の順。同じ巡回する成分の中なら、繰り返しの次の回があるので順に関係なく True。
        """

        if first is None or second is None:
            return True
        if first < second:
            return True
        return self.in_cycle(first) and (first >> _POSITION_BITS) == (second >> _POSITION_BITS)

    @property
    def has_cycle(self) -> bool:
        return bool(self._cyclic_blocks)


def _strongly_connected_components(
    blocks: Sequence[int],
    edges: Mapping[int, Tuple[int, ...]],
) -> List[Tuple[int, ...]]:
    """Tarjan の強連結成分（再帰しない）。順序は決定的（block 番号の順に始める）。"""

    index: Dict[int, int] = {}
    low: Dict[int, int] = {}
    on_stack: Dict[int, bool] = {}
    stack: List[int] = []
    components: List[Tuple[int, ...]] = []
    counter = 0
    for root in blocks:
        if root in index:
            continue
        work: List[Tuple[int, int]] = [(root, 0)]
        while work:
            block, child = work.pop()
            if child == 0:
                index[block] = low[block] = counter
                counter += 1
                stack.append(block)
                on_stack[block] = True
            successors = edges[block]
            if child < len(successors):
                work.append((block, child + 1))
                target = successors[child]
                if target not in index:
                    work.append((target, 0))
                elif on_stack.get(target):
                    low[block] = min(low[block], index[target])
                continue
            if low[block] == index[block]:
                members = []
                while True:
                    member = stack.pop()
                    on_stack[member] = False
                    members.append(member)
                    if member == block:
                        break
                components.append(tuple(sorted(members)))
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[block])
    return components


def _topological_ranks(
    components: Sequence[Tuple[int, ...]],
    component_of: Mapping[int, int],
    edges: Mapping[int, Tuple[int, ...]],
) -> Dict[int, int]:
    """縮めた DAG の位相順位。同順位の候補は最小の block 番号で選ぶ（決定的）。"""

    successors: Dict[int, set] = {number: set() for number in range(len(components))}
    indegree: Dict[int, int] = {number: 0 for number in range(len(components))}
    for block, targets in edges.items():
        source = component_of[block]
        for target in targets:
            destination = component_of[target]
            if destination != source and destination not in successors[source]:
                successors[source].add(destination)
                indegree[destination] += 1
    ready = [(components[number][0], number) for number, degree in indegree.items() if degree == 0]
    heapq.heapify(ready)
    ranks: Dict[int, int] = {}
    while ready:
        _, number = heapq.heappop(ready)
        ranks[number] = len(ranks)
        for destination in successors[number]:
            indegree[destination] -= 1
            if indegree[destination] == 0:
                heapq.heappush(ready, (components[destination][0], destination))
    return ranks

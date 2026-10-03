# -*- coding: utf-8 -*-
"""壁時計を読まない module の test の間は、GC を今のままにする（Issue #239、`tests/conftest.py`）。

この module は壁時計を読まない（読む呼び出しを source に持たない）。call の間も freeze されず、古い循環は
今と同じく集められる（session の memory を増やさない）。
"""

from __future__ import annotations

import gc
import weakref


class _Node:
    def __init__(self) -> None:
        self.peer = None


def test_a_module_that_does_not_read_the_wall_clock_is_not_frozen():
    assert gc.get_freeze_count() == 0


def test_an_older_cycle_is_collected_during_an_unmeasured_call(older_cycle):
    holder, ref = older_cycle
    holder.clear()
    gc.collect()
    assert ref() is None


import pytest  # noqa: E402


@pytest.fixture
def older_cycle():
    first, second = _Node(), _Node()
    first.peer, second.peer = second, first
    ref = weakref.ref(first)
    holder = [first]
    del first, second
    yield holder, ref

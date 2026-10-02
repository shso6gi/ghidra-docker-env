# -*- coding: utf-8 -*-
"""test の call の間の GC の隔離（Issue #239、`tests/conftest.py::pytest_runtest_call`）。

wall-clock の上限を持つ test は、被測定 code の仕事だけで時間が決まる: call より前から在る object は call の
間の collection の対象にならず、call の中で作った object は今と同じく集められる。GC の状態（有効 / 無効・閾値・
freeze の数）は call の後で元に戻る。
"""

from __future__ import annotations

import ast
import gc
import time
import weakref
from pathlib import Path

import pytest

TESTS_ROOT = Path(__file__).resolve().parents[1]


class _Node:
    def __init__(self) -> None:
        self.peer = None


def _cycle():
    first, second = _Node(), _Node()
    first.peer, second.peer = second, first
    return first, weakref.ref(first)


@pytest.fixture
def gc_state():
    """setup と teardown（call の外）の GC の状態: freeze されておらず、call の前後で同じ。"""

    before = (gc.isenabled(), gc.get_threshold(), gc.get_freeze_count())
    assert before[2] == 0
    yield before
    assert (gc.isenabled(), gc.get_threshold(), gc.get_freeze_count()) == before


def test_objects_made_before_the_call_are_frozen_during_it(gc_state):
    assert gc.get_freeze_count() > 0
    assert (gc.isenabled(), gc.get_threshold()) == gc_state[:2]


def test_a_cycle_made_during_the_call_is_collected_during_it(gc_state):
    strong, ref = _cycle()
    del strong
    gc.collect()
    assert ref() is None


@pytest.fixture
def cycle_made_in_setup():
    strong, ref = _cycle()
    holder = [strong]
    del strong
    yield holder, ref
    holder.clear()
    gc.collect()
    # call の後（unfreeze の後）は集められる
    assert ref() is None


def test_a_cycle_made_before_the_call_is_left_for_after_it(cycle_made_in_setup, gc_state):
    holder, ref = cycle_made_in_setup
    holder.clear()
    gc.collect()
    # call の前から在る object は call の間の collection の対象でない（call の後で集める）
    assert ref() is not None


def test_a_full_collection_during_the_call_does_not_scan_the_older_objects(gc_state):
    """call の中の full collection の時間は、call より前から在る object の数に依らない。"""

    started = time.perf_counter()
    gc.collect()
    during = time.perf_counter() - started
    frozen = gc.get_freeze_count()
    assert frozen > 0
    # 比較: 同じ object を全部辿る collection（freeze を外して測る。測った後で元に戻す）
    gc.unfreeze()
    try:
        started = time.perf_counter()
        gc.collect()
        full = time.perf_counter() - started
    finally:
        gc.freeze()
    assert during <= full


def test_no_test_changes_the_freeze_state_itself():
    """freeze / unfreeze を呼ぶのは conftest の hook だけ（test が呼ぶと hook の復元と食い違う）。"""

    offenders = []
    for path in sorted(TESTS_ROOT.rglob("*.py")):
        if path.name == "conftest.py" and path.parent == TESTS_ROOT:
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if isinstance(node, ast.Attribute) and node.attr in ("freeze", "unfreeze"):
                if isinstance(node.value, ast.Name) and node.value.id == "gc":
                    if path != Path(__file__).resolve():
                        offenders.append(f"{path.relative_to(TESTS_ROOT)}:{node.lineno}")
    assert offenders == []

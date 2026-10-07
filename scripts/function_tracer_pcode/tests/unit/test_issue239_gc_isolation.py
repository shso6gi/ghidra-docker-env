# -*- coding: utf-8 -*-
"""test の call の間の GC の隔離（Issue #239、`tests/conftest.py::pytest_runtest_call`）。

wall-clock の上限を持つ test は、被測定 code の仕事だけで時間が決まる: call より前から在る object は call の
間の collection の対象にならず、call の中で作った object は今と同じく集められる。GC の状態（有効 / 無効・閾値・
freeze の数）は call の後で元に戻る。
"""

from __future__ import annotations

import ast
import gc
import re
import time
import weakref
from pathlib import Path
from typing import Dict, Iterable, Set

import pytest

from scripts.function_tracer_pcode.tests import conftest

TESTS_ROOT = Path(__file__).resolve().parents[1]
UNIT_ROOT = TESTS_ROOT / "unit"


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
    time.perf_counter()  # 壁時計を読む test（hook の対象）
    assert gc.get_freeze_count() > 0
    assert (gc.isenabled(), gc.get_threshold()) == gc_state[:2]


def test_a_cycle_made_during_the_call_is_collected_during_it(gc_state):
    time.perf_counter()  # 壁時計を読む test（hook の対象）
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
    time.perf_counter()  # 壁時計を読む test（hook の対象）
    holder, ref = cycle_made_in_setup
    holder.clear()
    gc.collect()
    # call の前から在る object は call の間の collection の対象でない（call の後で集める）
    assert ref() is not None


def test_a_full_collection_during_the_call_does_not_scan_the_older_objects(gc_state):
    """call の中の full collection が辿るのは、call の中で作った object だけ（前から在る object は永続の世代）。

    時間の大小ではなく構造で確かめる: 最も古い世代に残る object は、freeze した object より桁違いに少ない。
    """

    time.perf_counter()  # 壁時計を読む test（hook の対象）
    gc.collect()
    frozen = gc.get_freeze_count()
    assert frozen > 0
    assert len(gc.get_objects(generation=2)) * 10 < frozen


@pytest.mark.wall_clock
def test_a_marked_test_is_frozen_without_reading_the_clock_in_its_module(gc_state):
    """module の外で時計を読む test（production の時計・別 module の helper）は印で対象にする。"""

    assert gc.get_freeze_count() > 0


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


def _read_clock():
    return time.perf_counter()


def test_a_test_that_reads_the_clock_through_a_module_helper_is_frozen(gc_state):
    _read_clock()
    assert gc.get_freeze_count() > 0


def test_a_test_in_a_clock_module_that_does_not_read_the_clock_is_not_frozen(gc_state):
    assert gc.get_freeze_count() == 0


# ---------------------------------------------------------------------------
# AC3: 壁時計の大小を確かめる test は、どれも共有の仕組み（hook）を通る
# ---------------------------------------------------------------------------

#: 時間の量を表す名前（assert の大小比較の operand に現れれば、壁時計の量と見なす）。GC は測った時間を
#: 長くする方へしか動かさないので、確かめるのは時間の量が比較の **小さい側** に在る assert（上限・二つの量の比）
#: だけ: 下限（`>= 0`・`> 0`・`>= TICK`）は GC で壊れない
_TIMING_NAME = re.compile(r"(elapsed|wall|seconds|duration|delay|perf_counter|monotonic|tick|latency|took)", re.I)
#: 時計を読む呼び出し（その戻り値を入れた局所変数は時間の量）
_CLOCK_CALLS = frozenset({"perf_counter", "perf_counter_ns", "monotonic", "monotonic_ns", "time", "time_ns"})
_ORDER = (ast.Lt, ast.LtE, ast.Gt, ast.GtE)

#: 規則に掛かるが壁時計の大小ではない test（理由つき。規則に掛からなくなれば stale として落ちる）
NOT_WALL_CLOCK: Dict[str, str] = {}


def _identifiers(node: ast.AST) -> Iterable[str]:
    if isinstance(node, (ast.Set, ast.List, ast.Tuple)) and all(isinstance(e, ast.Constant) for e in node.elts):
        return  # 文字列の literal の集まり（`{"poll", "monotonic"} <= called` は時間の量ではない）
    for inner in ast.walk(node):
        if isinstance(inner, ast.Name):
            yield inner.id
        elif isinstance(inner, ast.Attribute):
            yield inner.attr
        elif isinstance(inner, ast.Constant) and isinstance(inner.value, str):
            yield inner.value


def timing_assertions(source: str) -> Set[str]:
    """module の source のうち、壁時計の量を大小で比べる assert を持つ test 関数の名前（同じ module の helper
    が持つものは、それを呼ぶ test 関数へ伝える）。"""

    tree = ast.parse(source)
    functions = [node for node in ast.walk(tree) if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))]
    direct: Set[str] = set()
    calls: Dict[str, Set[str]] = {}
    for function in functions:
        clock_names = set()
        for node in ast.walk(function):
            if isinstance(node, ast.Assign) and isinstance(node.value, ast.Call):
                func = node.value.func
                name = func.attr if isinstance(func, ast.Attribute) else getattr(func, "id", None)
                if name in _CLOCK_CALLS:
                    clock_names.update(target.id for target in node.targets if isinstance(target, ast.Name))
        def timing(operand: ast.AST) -> bool:
            names = set(_identifiers(operand))
            return bool(names & clock_names) or any(_TIMING_NAME.search(name) for name in names)

        for node in ast.walk(function):
            if isinstance(node, ast.Assert) and isinstance(node.test, ast.Compare):
                operands = [node.test.left, *node.test.comparators]
                for index, op in enumerate(node.test.ops):
                    # 小さい側: `a < b` / `a <= b` の a、`a > b` / `a >= b` の b
                    if isinstance(op, (ast.Lt, ast.LtE)):
                        smaller = operands[index]
                    elif isinstance(op, (ast.Gt, ast.GtE)):
                        smaller = operands[index + 1]
                    else:
                        continue
                    if timing(smaller):
                        direct.add(function.name)
        calls.setdefault(function.name, set()).update(
            node.func.id for node in ast.walk(function)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
        )
    found = set(direct)
    changed = True
    while changed:
        changed = False
        for name, called in calls.items():
            if name not in found and called & found:
                found.add(name)
                changed = True
    return {name for name in found if name.startswith("test")}


def _marked(source: str) -> Set[str]:
    """`wall_clock` の印を持つ test 関数の名前（module の `pytestmark` に印があれば全部）。"""

    tree = ast.parse(source)
    module_marked = any(
        isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "pytestmark" for t in node.targets)
        and conftest.WALL_CLOCK_MARKER in set(_identifiers(node.value))
        for node in tree.body
    )
    out = set()
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name.startswith("test"):
            if module_marked or any(conftest.WALL_CLOCK_MARKER in set(_identifiers(d)) for d in node.decorator_list):
                out.add(node.name)
    return out


def unselected_timing_tests(path: Path, source: str) -> Set[str]:
    """壁時計の大小を確かめるのに、hook の対象（印か module の中の時計の閉包）でない test 関数。"""

    selected = _marked(source) | set(conftest._wall_clock_functions(str(path)))
    return {f"{path.name}::{name}" for name in timing_assertions(source) - selected}


def test_every_wall_clock_assertion_goes_through_the_shared_freeze():
    offenders, seen = [], set()
    for path in sorted(UNIT_ROOT.glob("test_*.py")):
        source = path.read_text(encoding="utf-8")
        for key in sorted(unselected_timing_tests(path, source)):
            seen.add(key)
            if key not in NOT_WALL_CLOCK:
                offenders.append(key)
    assert offenders == [], "mark these with @pytest.mark.wall_clock (Issue #239): " + ", ".join(offenders)
    assert sorted(set(NOT_WALL_CLOCK) - seen) == []  # stale exemptions


def test_the_wall_clock_guard_finds_an_unmarked_bound_through_an_outside_clock(tmp_path):
    """陽性の対照: module の外の時計（production の時計・別 module の helper）で測る上限は、印が無ければ見つかる。"""

    source = (
        "from scripts.function_tracer_pcode.core.stage_clock import StageClock\n"
        "def test_outside(clock):\n"
        "    region = clock.snapshot()\n"
        "    assert region['seconds_inclusive'] < 0.05\n"
        "def _bounded(seconds):\n"
        "    assert seconds <= 1.0\n"
        "def test_through_helper():\n"
        "    _bounded(3)\n"
        "def test_not_timing():\n"
        "    assert len([1]) < 2\n"
        "def test_lower_bound_only(clock):\n"
        "    assert clock.snapshot()['seconds'] >= 0.0\n"
        "def test_literal_names():\n"
        "    assert {'poll', 'monotonic'} <= set()\n"
    )
    path = tmp_path / "test_sample.py"
    path.write_text(source)
    assert unselected_timing_tests(path, source) == {"test_sample.py::test_outside", "test_sample.py::test_through_helper"}
    marked = source.replace("def test_outside", "@pytest.mark.wall_clock\ndef test_outside")
    path.write_text(marked)
    assert unselected_timing_tests(path, marked) == {"test_sample.py::test_through_helper"}

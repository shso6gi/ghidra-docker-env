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


#: 実の時計（`time.monotonic`）で動く期限を作る呼び出し: `ShiftedClock`（実の時計に足す test の時計）と、
#: `clock=` を渡さない `DeadlinePolicy`（既定の時計が `time.monotonic`）。短い予算では、GC の一時停止が期限の
#: 結果（窓の長さ・どの backend が走るか）を変える。偽の時計を `clock=` で渡す test は対象でない
_REAL_CLOCK_CALLS = frozenset({"ShiftedClock"})
_REAL_CLOCK_DEFAULTED = frozenset({"DeadlinePolicy"})


def _call_name(node: ast.Call):
    func = node.func
    return func.attr if isinstance(func, ast.Attribute) else getattr(func, "id", None)


def _qualnames(tree: ast.AST) -> Dict[ast.AST, str]:
    """関数の node → `Class.method` / `function` の名前（入れ子の class の中の test を区別する）。"""

    out: Dict[ast.AST, str] = {}

    def visit(node, prefix):
        for child in ast.iter_child_nodes(node):
            if isinstance(child, ast.ClassDef):
                visit(child, prefix + child.name + ".")
            elif isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                out[child] = prefix + child.name
                visit(child, prefix + child.name + ".")

    visit(tree, "")
    return out


def timing_assertions(source: str) -> Set[str]:
    """壁時計に結果が左右される test 関数の名前（`Class.method` の形）。

    * assert の大小比較の小さい側に時間の量がある（上限・二つの量の比）
    * 実の時計で動く期限を作る（`_REAL_CLOCK_CALLS` / `clock=` の無い `_REAL_CLOCK_DEFAULTED`）
    同じ module の helper が持つものは、それを呼ぶ test 関数へ伝える（helper の名前で照合）。
    """

    tree = ast.parse(source)
    names = _qualnames(tree)
    direct: Set[str] = set()
    calls: Dict[str, Set[str]] = {}
    for function, qualname in names.items():
        bare = qualname.rsplit(".", 1)[-1]
        clock_names = set()
        for node in ast.walk(function):
            if isinstance(node, ast.Assign) and isinstance(node.value, ast.Call):
                if _call_name(node.value) in _CLOCK_CALLS:
                    clock_names.update(target.id for target in node.targets if isinstance(target, ast.Name))
        def timing(operand: ast.AST) -> bool:
            found = set(_identifiers(operand))
            return bool(found & clock_names) or any(_TIMING_NAME.search(name) for name in found)

        for node in ast.walk(function):
            if isinstance(node, ast.Call):
                name = _call_name(node)
                if name in _REAL_CLOCK_CALLS or (
                    name in _REAL_CLOCK_DEFAULTED and not any(k.arg == "clock" for k in node.keywords)
                ):
                    direct.add(qualname)
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
                        direct.add(qualname)
        calls.setdefault(qualname, set()).update(
            node.func.id for node in ast.walk(function)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
        )
    found = set(direct)
    changed = True
    while changed:
        changed = False
        found_bare = {name.rsplit(".", 1)[-1] for name in found}
        for qualname, called in calls.items():
            if qualname not in found and called & found_bare:
                found.add(qualname)
                changed = True
    return {name for name in found if name.rsplit(".", 1)[-1].startswith("test")}


def _is_wall_clock_mark(node: ast.AST) -> bool:
    """`pytest.mark.wall_clock`（呼び出しの有無を問わない）か。文字列の中の同じ綴りは数えない。"""

    if isinstance(node, ast.Call):
        node = node.func
    return (
        isinstance(node, ast.Attribute) and node.attr == conftest.WALL_CLOCK_MARKER
        and isinstance(node.value, ast.Attribute) and node.value.attr == "mark"
    )


def _marks(value: ast.AST) -> bool:
    return any(_is_wall_clock_mark(node) for node in ast.walk(value))


def _marked(source: str) -> Set[str]:
    """`wall_clock` の印が効く test 関数（`Class.method` の形）。関数・class の decorator と、module の
    `pytestmark`（注釈つきの代入を含む）。"""

    tree = ast.parse(source)
    module_marked = any(
        (isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "pytestmark" for t in node.targets)
         or isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) and node.target.id == "pytestmark")
        and node.value is not None and _marks(node.value)
        for node in tree.body
    )
    out: Set[str] = set()

    def visit(node, prefix, inherited):
        for child in ast.iter_child_nodes(node):
            if isinstance(child, ast.ClassDef):
                visit(child, prefix + child.name + ".", inherited or any(_marks(d) for d in child.decorator_list))
            elif isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)) and child.name.startswith("test"):
                if module_marked or inherited or any(_marks(d) for d in child.decorator_list):
                    out.add(prefix + child.name)

    visit(tree, "", False)
    return out


def unselected_timing_tests(path: Path, source: str) -> Set[str]:
    """壁時計に結果が左右されるのに、hook の対象でない test 関数（hook と同じ選び方: 印は test ごと、module の
    中の時計の閉包は関数の名前で）。"""

    marked = _marked(source)
    detected = set(conftest._wall_clock_functions(str(path)))
    return {
        f"{path.name}::{name}" for name in timing_assertions(source)
        if name not in marked and name.rsplit(".", 1)[-1] not in detected
    }


def test_every_wall_clock_dependent_test_goes_through_the_shared_freeze():
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
    """陽性の対照: module の外の時計（production の時計・別 module の helper）で測る上限と、実の時計で動く期限の
    test は、印が無ければ見つかる。偽の時計・下限・文字列の literal は対象でない。"""

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
    real_clock = (
        "def _policy(seconds):\n"
        "    return DeadlinePolicy(seconds, margin=0.1)\n"
        "def test_real_clock_deadline():\n"
        "    assert run(_policy(0.3)) in (1, 2)\n"
        "def test_fake_clock_deadline(fake):\n"
        "    assert run(DeadlinePolicy(0.3, clock=fake)) in (1, 2)\n"
        "def test_shifted_clock():\n"
        "    clock = ShiftedClock()\n"
        "class TestGroup:\n"
        "    @pytest.mark.skipif(False, reason='wall_clock')\n"
        "    def test_outside(self, clock):\n"
        "        assert clock.snapshot()['seconds'] < 1.0\n"
    )
    source += real_clock
    path.write_text(source)
    expected = {
        "test_sample.py::test_outside", "test_sample.py::test_through_helper",
        "test_sample.py::test_real_clock_deadline", "test_sample.py::test_shifted_clock",
        "test_sample.py::TestGroup.test_outside",
    }
    assert unselected_timing_tests(path, source) == expected
    # 印は test ごと（同じ名前の別の test は印の無いまま）。文字列の中の綴りは印でない
    marked = source.replace("def test_outside(clock)", "@pytest.mark.wall_clock\ndef test_outside(clock)")
    path.write_text(marked)
    assert unselected_timing_tests(path, marked) == expected - {"test_sample.py::test_outside"}
    # class の decorator と注釈つきの `pytestmark` も印
    grouped = marked.replace("class TestGroup:", "@pytest.mark.wall_clock\nclass TestGroup:")
    assert "test_sample.py::TestGroup.test_outside" not in unselected_timing_tests(path, grouped)
    module = "import pytest\npytestmark: list = [pytest.mark.wall_clock]\n" + source
    assert unselected_timing_tests(path, module) == set()

# -*- coding: utf-8 -*-
"""Issue #242（第 7 回のレビュー）: 比べる側の契約の不変条件を、実装と独立な期待値で確かめる。

期待値はどれも **正直な双子**（同じ形の世界を、callback が基底型の値を返し、scalar の葉が基底型の値で作り直した
もの）に Python の組み込みの演算（`==` / `!=` / `<` / `in` / `sorted` / `hash` / dict・set）を当てた結果。比べるのは
戻り値・例外の型・外の code の呼び出しの記録（method・自分・相手の順の列）・変わる容器の最後の状態・偽る型の hook の
数（0）。

判定不能（`UndecidableComparison`）は、場面の作り方から決まる場合だけ許す（実装の分岐から決めない）:
- 外の code が比較の途中で、比べている値の変わる容器を変えた（記録に `mutate` がある）。
- 外の object が hash で置く位置（set / frozenset の要素・dict の key）にある。
- 双子で外の code が容器を受け取る（偽る側の容器は scalar の subclass の葉を読むと写しになり、identity が双子と違う）。
許すときも、そこまでの呼び出しの記録は双子の記録の先頭と同じ（判定しないことを、余分な外の code の呼び出しの
口実にしない）。

ref の層: 等しい ref は同じ hash で、dict / set の中で同じ値として扱われる（`b in {a}`・集合の大きさ）。判定不能は
gate の通過の根拠にならない（`compare_loop_summaries` の gate に判定不能を差し込むと、結果は必ず `unknown`）。
`decided_equal` の結果の使い方は規則で縛る（新しい使い方は分類しない限り test が落ちる）。
"""

from __future__ import annotations

import ast
import pathlib
import random
from typing import Any, Callable, Dict, List, Optional, Tuple

import pytest

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.live_values import UndecidableComparison
from scripts.function_tracer_pcode.tests.unit.runtime_ref_adversaries import (
    HOOK_CALLS, Callback, Liar, LiarFloat, LiarStr, lie,
)

PACKAGE = pathlib.Path(__file__).resolve().parents[2]


# ---------------------------------------------------------------------------
# 世界: 外の object（`Probe`）と、その呼び出しの記録
# ---------------------------------------------------------------------------


class World:
    """1 つの場面の世界（双子と偽る側で 1 つずつ作る）。`lying` なら外の code の戻り値は値を偽る scalar の subclass。"""

    def __init__(self, lying: bool) -> None:
        self.lying = lying
        self.log: List[Tuple[Any, ...]] = []
        self.calls = 0

    def result(self, value: Any) -> Any:
        if type(value) is bool:
            value = int(value)
        return lie(value) if self.lying else value


class Probe:
    """外の object: 比較・hash の呼び出しを記録し、`mode` の規則で答える。

    - `pure`: 値どうしの結果。
    - `second`: `==` は世界の中の 2 回目の呼び出しだけ真（状態で答えが変わる callback）。
    - `mutate`: 最初の呼び出しで `action`（世界の容器を変える）を行い、あとは `pure`。
    """

    __slots__ = ("world", "tag", "value", "mode", "action", "fired")

    def __init__(self, world: World, tag: str, value: Any, mode: str = "pure", action: Optional[Callable[[], None]] = None):
        self.world = world
        self.tag = tag
        self.value = value
        self.mode = mode
        self.action = action
        self.fired = False

    def _answer(self, operation: str, other: Any) -> Any:
        world = self.world
        world.calls += 1
        world.log.append((operation, self.tag, _tag(other)))
        if self.mode == "mutate" and not self.fired:
            self.fired = True
            world.log.append(("mutate", self.tag))
            self.action()
        if type(other) is Probe:
            other = other.value
        elif not (other is None or type(other) in (int, str, float, bool)):
            return NotImplemented
        if operation == "eq" and self.mode == "second":
            return world.result(world.calls == 2)
        try:
            outcome = {
                "eq": lambda: self.value == other, "ne": lambda: self.value != other,
                "lt": lambda: self.value < other, "le": lambda: self.value <= other,
                "gt": lambda: self.value > other, "ge": lambda: self.value >= other,
            }[operation]()
        except TypeError:
            return NotImplemented
        return world.result(outcome)

    def __eq__(self, other: Any) -> Any:
        return self._answer("eq", other)

    def __ne__(self, other: Any) -> Any:
        return self._answer("ne", other)

    def __lt__(self, other: Any) -> Any:
        return self._answer("lt", other)

    def __le__(self, other: Any) -> Any:
        return self._answer("le", other)

    def __gt__(self, other: Any) -> Any:
        return self._answer("gt", other)

    def __ge__(self, other: Any) -> Any:
        return self._answer("ge", other)

    def __hash__(self) -> Any:
        self.world.log.append(("hash", self.tag))
        return self.world.result(hash(self.value))


def _tag(value: Any) -> Any:
    kind = type(value)
    if kind is Probe:
        return value.tag
    if kind is not bool and kind not in (int, str, float) and isinstance(value, (int, str, float)):
        # 偽る scalar: 基底型の slot で基底型の値にして記録する（hook を呼ばない）
        read = int.__index__ if isinstance(value, int) else float.__float__ if isinstance(value, float) else str.__str__
        return ("leaf", read(value))
    return ("leaf", value) if value is None or type(value) in (int, str, float, bool) else ("other", type(value).__name__)


def _view(value: Any, seen: Optional[set] = None) -> Any:
    """値の形（`Probe` は tag、scalar は基底型の値、容器は種類と中身）。"""

    seen = set() if seen is None else seen
    kind = type(value)
    if kind is Probe:
        return ("probe", value.tag)
    if isinstance(value, (list, tuple, dict, set, frozenset)):
        if id(value) in seen:
            return ("cycle",)
        seen = seen | {id(value)}
        base = next(b for b in (list, tuple, dict, set, frozenset) if isinstance(value, b))
        if base is dict:
            return ("dict", tuple((_view(k, seen), _view(v, seen)) for k, v in dict.items(value)))
        if base in (set, frozenset):
            return (base.__name__, tuple(sorted((repr(_view(item, seen)) for item in base.__iter__(value)))))
        return (base.__name__, tuple(_view(item, seen) for item in base.__iter__(value)))
    return _tag(value)


# ---------------------------------------------------------------------------
# 場面の生成（双子と偽る側は同じ種から同じ形を作る）
# ---------------------------------------------------------------------------

#: hash が等しい exact な int（Python の数の hash: `-1` は `-2`、`2**61 - 1` を法とする）
COLLIDING = (1, 2 ** 61, 2 * (2 ** 61 - 1) + 1, -1, -2)
HASHED_SHAPES = ("set", "frozenset", "dict_key")
SHAPES = ("leaf", "tuple", "list", "dict_value", "nested", "shared") + HASHED_SHAPES
OPERATIONS = ("equal", "unequal", "less", "contains", "sorted", "hash")


class Scene:
    """1 つの場面: 演算・左右の値・世界・場面の作り方から決まる「判定不能を許す」理由。"""

    def __init__(self, seed: int, lying: bool) -> None:
        rng = random.Random(seed)
        self.lying = lying
        self.world = World(False)  # 作る間は正直（set / dict の key の重複の判定を双子と同じにする）
        self.containers: List[Any] = []
        self.foreign_hashed = False
        self.operation = rng.choice(OPERATIONS)
        self.counter = 0
        self.left = self._value(rng, depth=0)
        self.right = self._value(rng, depth=0)
        if self.operation == "contains":
            self.right = self._container(rng, rng.choice(("tuple", "list", "set", "frozenset", "dict_key")))
        if self.operation == "sorted":
            self.right = [self._leaf(rng) for _ in range(rng.randint(2, 5))]
        # 外の code が変える容器（比べる値の中の list / dict）。変える callback は作った後で決める
        mutable = [c for c in self.containers if type(c) in (list, dict)]
        probes = [p for p in self._probes() if p.mode == "pure"]
        if mutable and probes and rng.random() < 0.4:
            target = rng.choice(mutable)
            probe = rng.choice(probes)
            probe.mode = "mutate"
            replacement = self._leaf(rng)
            if type(target) is list and len(target) > 0:
                index = rng.randrange(len(target))
                probe.action = lambda: list.__setitem__(target, index, replacement)
            elif type(target) is list:
                probe.action = lambda: target.append(replacement)
            else:
                probe.action = lambda: dict.__setitem__(target, "late", replacement)
        self.world.lying = lying
        self.world.log.clear()
        self.world.calls = 0

    def _probes(self) -> List[Probe]:
        found: List[Probe] = []
        pending = [self.left, self.right]
        seen = set()
        while pending:
            value = pending.pop()
            if id(value) in seen:
                continue
            seen.add(id(value))
            if type(value) is Probe:
                found.append(value)
            elif type(value) is dict:
                pending.extend(value.keys())
                pending.extend(value.values())
            elif type(value) in (list, tuple, set, frozenset):
                pending.extend(value)
        return found

    def _leaf(self, rng: random.Random, hashed: bool = False) -> Any:
        self.counter += 1
        choice = rng.random()
        value = rng.choice(COLLIDING + (0, 2, "a"))
        if choice < 0.45:
            mode = "second" if rng.random() < 0.25 else "pure"
            return Probe(self.world, f"p{self.counter}", value if type(value) is int else 1, mode)
        if self.lying and choice < 0.75 and not hashed:
            return lie(value)  # scalar の subclass の葉（読みで基底型の値）
        return value

    def _value(self, rng: random.Random, depth: int) -> Any:
        shape = rng.choice(SHAPES if depth < 2 else ("leaf",))
        if shape == "leaf":
            return self._leaf(rng)
        return self._container(rng, shape, depth)

    def _container(self, rng: random.Random, shape: str, depth: int = 0) -> Any:
        count = rng.randint(0, 3)
        if shape == "shared":
            leaf = self._leaf(rng)
            return (leaf, [leaf], leaf)
        if shape == "nested":
            value: Any = [(self._value(rng, depth + 1),), self._value(rng, depth + 1)]
            self.containers.append(value)
            return value
        if shape in ("tuple", "list"):
            items = [self._value(rng, depth + 1) for _ in range(count)]
            value = tuple(items) if shape == "tuple" else items
            if shape == "list":
                self.containers.append(value)
            return value
        if shape == "dict_value":
            value = {f"k{index}": self._value(rng, depth + 1) for index in range(count)}
            self.containers.append(value)
            return value
        leaves = [self._leaf(rng, hashed=True) for _ in range(count)]
        if any(type(leaf) is Probe for leaf in leaves):
            self.foreign_hashed = True
        if shape == "set":
            value = set(leaves)
            self.containers.append(value)
            return value
        if shape == "frozenset":
            return frozenset(leaves)
        value = {leaf: index for index, leaf in enumerate(leaves)}
        self.containers.append(value)
        return value


def _builtin(scene: Scene) -> Any:
    left, right = scene.left, scene.right
    return {
        "equal": lambda: bool(left == right),
        "unequal": lambda: bool(left != right),
        "less": lambda: bool(left < right),
        "contains": lambda: bool(left in right),
        "sorted": lambda: tuple(_view(item) for item in sorted(right)),
        "hash": lambda: hash(left),
    }[scene.operation]


def _contract(scene: Scene) -> Any:
    left, right = scene.left, scene.right
    return {
        "equal": lambda: live_values.equal(left, right),
        "unequal": lambda: live_values.unequal(left, right),
        "less": lambda: live_values.less(left, right),
        "contains": lambda: live_values.contains(right, left),
        "sorted": lambda: tuple(_view(item) for item in live_values.sorted_trees(right)),
        "hash": lambda: live_values.hash_tree(left),
    }[scene.operation]


def _run(operation: Callable[[], Any]) -> Tuple[Any, ...]:
    try:
        return ("value", operation())
    except UndecidableComparison:
        return ("undecidable",)
    except RecursionError:
        return ("raises", "RecursionError")
    except Exception as error:  # noqa: BLE001 - 双子と同じ例外の型を比べる
        return ("raises", type(error).__name__)


def _observe(seed: int) -> Tuple[Dict[str, Any], Dict[str, Any], Scene]:
    twin = Scene(seed, lying=False)
    expected = {"outcome": _run(_builtin(twin))}
    expected["log"] = list(twin.world.log)
    expected["state"] = [_view(c) for c in twin.containers]
    lying = Scene(seed, lying=True)
    HOOK_CALLS.clear()  # 作るとき（偽る scalar の葉）の hook は数えない
    got = {"outcome": _run(_contract(lying))}
    got["hooks"] = dict(HOOK_CALLS)
    got["log"] = list(lying.world.log)
    got["state"] = [_view(c) for c in lying.containers]
    return expected, got, lying


SEEDS = range(4000)


@pytest.mark.parametrize("chunk", range(8))
def test_comparisons_match_the_honest_twin_including_callback_order_and_state(chunk):
    """戻り値・例外・外の code の呼び出しの記録・容器の最後の状態が双子と同じ。判定不能は場面が許すときだけで、
    そのときも記録は双子の記録の先頭（余分な呼び出しをしない）。"""

    undecided = matched = 0
    failures = []
    for seed in SEEDS[chunk::8]:
        expected, got, scene = _observe(seed)
        if got["hooks"]:
            failures.append((seed, "hooks", got["hooks"]))
            continue
        if got["outcome"] == ("undecidable",):
            mutated = any(entry[0] == "mutate" for entry in expected["log"])
            # 双子で外の code が容器を受け取る（偽る側では scalar の subclass の葉を読んだ写しになり得る: identity が違う）
            receives_container = any(
                len(entry) == 3 and type(entry[2]) is tuple and entry[2][0] == "other" for entry in expected["log"]
            )
            allowed = mutated or scene.foreign_hashed or receives_container
            prefix = got["log"] == expected["log"][: len(got["log"])]
            if not (allowed and prefix):
                failures.append((seed, scene.operation, "undecidable", expected, got))
            undecided += 1
            continue
        if got["outcome"] != expected["outcome"] or got["log"] != expected["log"] or got["state"] != expected["state"]:
            failures.append((seed, scene.operation, expected, got))
            continue
        matched += 1
    assert failures == [], failures[:3]
    assert matched > undecided  # 判定する場面が大半（判定不能で逃げていない）


def test_the_scene_generator_reaches_every_ingredient():
    """場面の材料（状態で答える callback・容器を変える callback・hash の衝突・共有・hash で置く外の object）が
    実際に生まれ、判定した場面と判定不能の場面の両方がある（生成の偏りで test が空回りしない）。"""

    seen = {"second": 0, "mutate": 0, "collide": 0, "shared": 0, "hashed": 0, "decided_mutation": 0}
    for seed in SEEDS:
        expected, got, scene = _observe(seed)
        modes = {p.mode for p in scene._probes()}
        seen["second"] += "second" in modes
        seen["mutate"] += any(entry[0] == "mutate" for entry in expected["log"])
        seen["hashed"] += scene.foreign_hashed
        seen["collide"] += any(
            type(p) is Probe and p.value in COLLIDING[1:] for p in scene._probes()
        )
        seen["shared"] += any(
            type(v) is tuple and len(v) == 3 and type(v[1]) is list and v[1] and v[1][0] is v[0]
            for v in (scene.left, scene.right)
        )
        seen["decided_mutation"] += (
            any(entry[0] == "mutate" for entry in expected["log"]) and got["outcome"][0] == "value"
        )
    assert all(count >= 20 for count in seen.values()), seen


# ---------------------------------------------------------------------------
# 反例の固定（第 7 回のレビューの 5 件。旧 head ae2c479b ではどれも落ちる）
# ---------------------------------------------------------------------------


def test_equal_refs_have_equal_hashes_and_one_dict_slot():
    """反例 1: `start_expr` が `Liar(1)` と `1` の `LoopSummaryRef` は等しく、hash も等しい（dict / set で同じ値）。"""

    from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopSummaryRef
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    base = corpus.BASES[LoopSummaryRef]()
    a = LoopSummaryRef(**{**base, "start_expr": Liar(1)})
    b = LoopSummaryRef(**{**base, "start_expr": 1})
    HOOK_CALLS.clear()
    assert a == b
    assert hash(a) == hash(b)
    assert b in {a: "value"}
    assert len({a, b}) == 1
    assert dict(HOOK_CALLS) == {}


def test_a_callback_that_changes_the_next_element_matches_the_twin_or_is_undecided():
    """反例 2: 最初の `__eq__` が右の list の次の要素を 0 から 1 に変えて 1 を返す。Python は False。"""

    def scene(lying):
        world = World(lying)
        right = [0, 0]

        def change():
            right[1] = 1

        left = [Probe(world, "m", 0, "mutate", change), 0]
        right[0] = 0
        return world, left, right

    _world, left, right = scene(False)
    expected = bool(left == right)
    _world, left, right = scene(True)
    HOOK_CALLS.clear()
    outcome = _run(lambda: live_values.equal(left, right))
    assert dict(HOOK_CALLS) == {}
    assert outcome in (("value", expected), ("undecidable",))
    assert outcome != ("value", not expected)


def test_contains_follows_the_builtin_probe_order_under_hash_collisions():
    """反例 5: 同じ hash の int 4 つの set と、2 回目の比較だけ真の callback。組み込みの `in` は True。"""

    items = [1, 2 ** 61, 2 * (2 ** 61 - 1) + 1, 3 * (2 ** 61 - 1) + 1]
    assert len({hash(item) for item in items}) == 1

    def scene(lying):
        world = World(lying)
        return world, Probe(world, "q", 1, "second"), set(items)

    world, probe, box = scene(False)
    expected = probe in box
    expected_log = list(world.log)
    world, probe, box = scene(True)
    world.log.clear()
    HOOK_CALLS.clear()
    assert live_values.contains(box, probe) is expected is True
    assert world.log == expected_log
    assert dict(HOOK_CALLS) == {}


# ---------------------------------------------------------------------------
# ref の層: 等しい ref は同じ hash、dict / set で同じ値（全 class の object の field × 値の組）
# ---------------------------------------------------------------------------


def _field_values() -> List[Tuple[str, Callable[[bool], Any]]]:
    """object の field に置く値（`lying` なら偽る側、そうでなければ双子）。"""

    return [
        ("int", lambda lying: 1),
        ("liar", lambda lying: Liar(1) if lying else 1),
        ("callback", lambda lying: Callback(1, lying)),
        ("callback2", lambda lying: Callback(2, lying)),
        ("tuple_callback", lambda lying: (Callback(1, lying), "x")),
        ("list_callback", lambda lying: [Callback(1, lying), Liar(2) if lying else 2]),
        ("dict_callback", lambda lying: {"k": Callback(1, lying)}),
        ("none", lambda lying: None),
    ]


def _object_fields():
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    for cls in corpus.BASES:
        for name, kind in corpus.field_kinds(cls).items():
            if kind == "object":
                yield pytest.param(cls, name, id=f"{cls.__qualname__}.{name}")


@pytest.mark.parametrize("cls, name", list(_object_fields()))
def test_ref_equality_hash_and_containers_agree_with_the_twin(cls, name):
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    def build(make, lying):
        try:
            return ("built", cls(**{**corpus.BASES[cls](), name: make(lying)}))
        except Exception as error:  # noqa: BLE001 - 構築の例外は双子と同じ型であればよい
            return ("raises", type(error).__name__)

    values = _field_values()
    for (_la, make_a), (_lb, make_b) in [(a, b) for a in values for b in values]:
        ta, tb = build(make_a, False), build(make_b, False)
        HOOK_CALLS.clear()
        la, lb = build(make_a, True), build(make_b, True)
        HOOK_CALLS.clear()
        if ta[0] != "built" or tb[0] != "built":
            assert (la[0], lb[0]) == (ta[0], tb[0])
            continue
        a, b = la[1], lb[1]
        expected = _run(lambda: bool(ta[1] == tb[1]))
        got = _run(lambda: a == b)
        assert got in (expected, ("undecidable",)), (expected, got)
        hashed = _run(lambda: (hash(a), hash(b)))
        if got == ("value", True) and hashed[0] == "value":
            assert hashed[1][0] == hashed[1][1]
            assert b in {a: 1} and a in {b}
            assert len({a, b}) == 1
        elif got == ("value", False) and hashed[0] == "value":
            assert len({a, b}) == 2
        assert dict(HOOK_CALLS) == {}


# ---------------------------------------------------------------------------
# 判定不能は gate の通過の根拠にならない
# ---------------------------------------------------------------------------


def _summaries():
    from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopSummaryRef
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    base = corpus.BASES[LoopSummaryRef]()
    same = (LoopSummaryRef(**base), LoopSummaryRef(**base))
    other = (LoopSummaryRef(**base), LoopSummaryRef(**{**base, "constant_bias": 3}))
    return [("same", same), ("other", other)]


@pytest.mark.parametrize("label, pair", _summaries())
def test_an_undecided_gate_in_the_loop_comparator_ends_in_unknown(monkeypatch, label, pair):
    """`compare_loop_summaries` の比較のどれか 1 つを判定不能にすると（全ての位置で試す）、結果は `unknown`。"""

    from scripts.function_tracer_pcode.core.runtime_refs import loops

    real = loops._decided_equal
    left, right = pair
    calls = []

    def counting(a, b):
        calls.append(1)
        return real(a, b)

    monkeypatch.setattr(loops, "_decided_equal", counting)
    baseline = loops.compare_loop_summaries(left, right)
    total = len(calls)
    assert total >= 1
    for position in range(total):
        seen = []

        def undecided_at(a, b, position=position, seen=seen):
            seen.append(1)
            return None if len(seen) == position + 1 else real(a, b)

        monkeypatch.setattr(loops, "_decided_equal", undecided_at)
        result = loops.compare_loop_summaries(left, right)
        assert result.status == "unknown", (label, position, baseline.status, result)


#: `decided_equal` の結果を、変数に置かずに真偽で読んでよい呼び出しの位置（module, 関数）と、`None`（判定不能）が
#: 主張しない側の枝に入る理由。新しい使い方はここに分類するか、変数に置いて直後に `is None` で抜ける形にする
DIRECT_DECISIONS = {
    ("call_models.py", "__post_init__"): "is not True → raise（受理しない）",
    ("call_arguments.py", "fresh_call_argument_refs_are_side_distinct"): "is False だけ真（違うと保証できない: 偽）",
    ("readonly.py", "_infer_lane_terms_from_witnesses"): "is not True → return ()（lane を推論しない）",
    ("readonly.py", "_scalar_lane_terms"): "is not True → return ()（lane を作らない）",
    ("readonly.py", "_complete_seed_prefix_from_exact_witnesses"): "is not True → return self（補わない）",
}


def _decision_sites():
    for path in sorted((PACKAGE / "core").rglob("*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"))
        parents: Dict[ast.AST, ast.AST] = {}
        for node in ast.walk(tree):
            for child in ast.iter_child_nodes(node):
                parents[child] = node
        for node in ast.walk(tree):
            if not (isinstance(node, ast.Call) and getattr(node.func, "id", None) in ("decided_equal", "_decided_equal")):
                continue
            function = node
            while function in parents and not isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
                function = parents[function]
            yield path, function, node, parents


def test_every_undecided_comparison_exits_before_a_decision():
    """`decided_equal` の結果は (a) 変数に置き、次の文が `if 変数 is None:` で return / raise する、か (b) 分類した
    位置の `is not True` / `is False` の直接の読み（`None` は主張しない枝）。それ以外の使い方は落ちる。"""

    offenders = []
    sites = 0
    for path, function, call, parents in _decision_sites():
        sites += 1
        parent = parents[call]
        if isinstance(parent, ast.Assign) and len(parent.targets) == 1 and isinstance(parent.targets[0], ast.Name):
            name = parent.targets[0].id
            block = parents[parent]
            body = next(
                (getattr(block, field) for field in ("body", "orelse", "finalbody")
                 if parent in getattr(block, field, [])),
                None,
            )
            following = body[body.index(parent) + 1] if body and body.index(parent) + 1 < len(body) else None
            exits = (
                isinstance(following, ast.If)
                and ast.unparse(following.test) == f"{name} is None"
                and isinstance(following.body[-1], (ast.Return, ast.Raise))
            )
            if not exits:
                offenders.append((path.name, function.name, call.lineno, "assigned without an immediate None exit"))
            continue
        key = (path.name, getattr(function, "name", None))
        if key not in DIRECT_DECISIONS:
            offenders.append((path.name, key[1], call.lineno, ast.unparse(parent)[:80]))
    assert offenders == []
    assert sites >= 12
    used = {(path.name, getattr(function, "name", None)) for path, function, _call, _parents in _decision_sites()}
    assert set(DIRECT_DECISIONS) <= used  # 分類が残っていない位置を指さない


# ---------------------------------------------------------------------------
# 例外の状態の写し: 値・型・無い / `None` の別・field 間の共有（identity）を保つ
# ---------------------------------------------------------------------------

#: 例外の field の名前（slot。dunder の名前の slot も状態）
SLOT_NAMES = ("a", "b", "__payload__")
_UNSET_TEXT = "<unset>"


def _render_state(error: BaseException) -> str:
    """field の値の repr と、同じ object を持つ field の位置（identity の関係）を書く `__str__` の本体。"""

    values = [error.args[0] if error.args else _UNSET_TEXT]
    for name in SLOT_NAMES:
        try:
            values.append(object.__getattribute__(error, name))
        except AttributeError:
            values.append(_UNSET_TEXT)
    values.append(getattr(error, "note", _UNSET_TEXT))
    values.append(error.__cause__)
    parts = []
    for index, value in enumerate(values):
        shared = [other for other, item in enumerate(values) if item is value and other != index and item is not None]
        parts.append(f"{index}:{value!r}/{type(value).__name__}/{shared}/{value}")
    return " ".join(parts)


class _Stateful(ValueError):
    __slots__ = SLOT_NAMES  # ValueError は `__dict__` を持つ（`note` はそこへ）

    def __str__(self):
        return _render_state(self)


def _exception_scene(seed: int, lying: bool) -> BaseException:
    rng = random.Random(seed)

    def text(value):
        # 双子の値も毎回新しい object（定数の intern・小さい int の cache が、偽る側に無い共有を作らない）
        return LiarStr(value) if lying else "".join([value, ""])

    def fresh():
        choice = rng.randrange(6)
        if choice == 0:
            return LiarFloat(1.5) if lying else float("1.5")
        if choice == 1:
            return text("pq")
        if choice == 2:
            return (text("tu"), 2)
        if choice == 3:
            return [Liar(3000) if lying else int("3000")]
        if choice == 4:
            return KeyError(text("kl"))
        return (KeyError(text("mn")),)  # 中の例外を持つ容器（共有されると置き換えも共有）

    made: List[Any] = []

    def pick():
        choice = rng.randrange(4)
        if choice == 0 and made:
            return rng.choice(made)  # 共有: 前の field と同じ object
        if choice == 1:
            return None
        value = fresh()
        made.append(value)
        return value

    error = _Stateful(pick())
    for name in SLOT_NAMES:
        state = rng.randrange(3)
        if state:
            object.__setattr__(error, name, pick())
    if rng.randrange(2):
        error.note = pick()
    cause = rng.randrange(3)
    if cause == 1:
        error.__cause__ = None
    elif cause == 2:
        nested = KeyError(pick())
        made.append(nested)
        error.__cause__ = nested
        if rng.randrange(2):
            error.note = nested  # 中の例外の共有
    return error


@pytest.mark.parametrize("chunk", range(4))
def test_exception_copies_keep_values_types_absence_and_sharing(chunk):
    failures = []
    for seed in range(chunk, 1200, 4):
        twin = _exception_scene(seed, lying=False)
        expected = _run(lambda: str(twin))
        lying = _exception_scene(seed, lying=True)
        HOOK_CALLS.clear()
        got = _run(lambda: live_values.exception_text(lying))
        if dict(HOOK_CALLS) or got != expected:
            failures.append((seed, expected, got, dict(HOOK_CALLS)))
    assert failures == [], failures[:3]


def test_a_shared_float_and_a_dunder_slot_are_copied_like_the_twin():
    """反例 4: `args[0]` と slot が同じ float の subclass を共有し、自前の `__payload__` slot を持つ例外。"""

    class Shared(ValueError):
        __slots__ = ("slot", "__payload__")

        def __str__(self):
            return f"{self.args[0] is self.slot} {self.__payload__!r} {self.__payload__}"

    def build(value, payload):
        error = Shared(value)
        error.slot = value
        error.__payload__ = payload
        return error

    expected = str(build(1.5, "p"))
    HOOK_CALLS.clear()
    assert live_values.exception_text(build(LiarFloat(1.5), LiarStr("p"))) == expected == "True 'p' p"
    assert dict(HOOK_CALLS) == {}


def test_the_jvm_shutdown_decision_reads_the_same_text_as_the_twin():
    """反例 4 の消費者: `CallTargetRef.from_function` が API の例外を JVM の停止と読むか（共有に依存する文字列）。"""

    from scripts.function_tracer_pcode.core.call_target import CallTargetRef

    class Shutdown(RuntimeError):
        __slots__ = ("slot",)

        def __str__(self):
            return "JVM is not running" if self.args[0] is self.slot else "other"

    class Function:
        def __init__(self, value):
            self.value = value

        def __getattr__(self, name):
            error = Shutdown(self.value)
            error.slot = self.value
            raise error

    outcomes = []
    for value in (1.5, LiarFloat(1.5)):
        HOOK_CALLS.clear()
        outcomes.append(_run(lambda: type(CallTargetRef.from_function(Function(value))).__name__))
        assert dict(HOOK_CALLS) == {}
    assert outcomes[0] == outcomes[1]


# ---------------------------------------------------------------------------
# 第 7 回の独立 review の反例と、mutation が残した規則（どれも実装と独立な期待値）
# ---------------------------------------------------------------------------


def _undecided_or(expected, operation):
    """結果が双子と同じか判定不能（`UndecidableComparison`）で、偽る型の hook を呼ばない。"""

    HOOK_CALLS.clear()
    got = _run(operation)
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",)), (expected, got)
    return got


def test_a_change_to_a_copied_container_is_never_read_stale():
    """写した list（外の object を持つ）を、前の要素の callback が変える。写しを読み続けると双子と違う相手の callback を
    呼ぶ: 双子と同じ結果か判定不能で、記録は双子の先頭。"""

    def scene(lying):
        world = World(lying)
        right = [0, None]

        def change():
            right[1] = 0  # 写しの中の外の object（`q`）を exact な 0 に替える

        right[1] = Probe(world, "q", 5)
        left = [Probe(world, "m", 0, "mutate", change), 0]
        return world, left, right

    world, left, right = scene(False)
    expected = _run(lambda: bool(left == right))
    expected_log = list(world.log)
    world, left, right = scene(True)
    got = _undecided_or(expected, lambda: live_values.equal(left, right))
    assert world.log == expected_log[: len(world.log)]
    if got == expected:
        assert world.log == expected_log


def test_a_foreign_hash_of_a_trusted_leaf_that_changes_a_container_is_caught_at_the_end():
    """比較の dunder は `object` のもので `__hash__` だけが外の code の葉（包まない）: 組み込みの `in` が直接呼ぶ。
    その `__hash__` が比べている dict を変えたら、双子と同じ結果か判定不能。"""

    def scene(lying):
        box = {"a": [Callback(1, lying)]}

        class Hasher:
            def __hash__(self):
                box["a"] = [Callback(2, lying)]
                return 7

        return box, Hasher()

    box, hasher = scene(False)
    expected = _run(lambda: bool(hasher in box))
    box, hasher = scene(True)
    _undecided_or(expected, lambda: live_values.contains(box, hasher))
    box, hasher = scene(True)
    _undecided_or(_run(lambda: bool(box == {"a": [Callback(1, False)], "b": hash(hasher)})),
                  lambda: live_values.equal(box, {"a": [Callback(1, True)], "b": hash(hasher)}))


def test_contains_on_an_object_that_is_not_a_builtin_container_is_not_answered():
    class Box:
        def __contains__(self, item):
            return Liar(1)

    HOOK_CALLS.clear()
    assert _run(lambda: live_values.contains(Box(), 1)) == ("undecidable",)
    assert dict(HOOK_CALLS) == {}


def test_cyclic_containers_with_lying_callbacks_never_run_hooks():
    left = [Callback(1, True)]
    left.append(left)
    right = [Callback(1, True)]
    right.append(right)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.equal(left, right))
    assert dict(HOOK_CALLS) == {}
    assert got in (("undecidable",), ("raises", "RecursionError"))


@pytest.mark.parametrize("make", [
    lambda lying: slice(Callback(1, lying)),
    lambda lying: __import__("types").MappingProxyType({1: Callback(1, lying)}),
], ids=["slice", "mappingproxy"])
def test_builtin_values_that_compare_what_they_hold_are_not_answered(make):
    """`slice` / `mappingproxy` の比較は C の中で持っている値を比べ、その戻り値を C が真偽で読む（包めない）。"""

    expected = _run(lambda: bool([make(False)] == [make(False)]))
    assert _undecided_or(expected, lambda: live_values.equal([make(True)], [make(True)])) == ("undecidable",)


@pytest.mark.parametrize("make", [
    lambda: (__import__("collections").OrderedDict(a=1, b=2), __import__("collections").OrderedDict(b=2, a=1)),
    lambda: (__import__("collections").Counter(a=1), __import__("collections").Counter(a=1, b=0)),
    lambda: (__import__("collections").deque([1]), [1]),
    lambda: ({1: 2}.keys(), {1}),
    lambda: ({1: 2}.values(), {1: 2}.values()),
    lambda: (type("L", (list,), {"__eq__": lambda self, other: Liar(0)})([1]), [1]),
], ids=["ordereddict", "counter", "deque", "keys_view", "values_view", "list_subclass_eq"])
def test_containers_that_compare_unlike_their_base_are_not_read_as_their_base(make):
    """反例（独立 review 1）: 基底型へ読むと比べ方が変わる容器。双子と同じ結果か判定不能（基底型の答えを出さない）。"""

    left, right = make()
    expected = _run(lambda: bool([left] == [right]))
    left, right = make()
    _undecided_or(expected, lambda: live_values.equal([left], [right]))
    _undecided_or(_run(lambda: bool(make()[1] in [make()[0]])), lambda: live_values.contains([make()[0]], make()[1]))


def test_a_list_subclass_without_its_own_comparison_is_compared_like_the_twin():
    plain = type("Plain", (list,), {})
    assert live_values.equal([plain([1, Liar(2)])], [[1, 2]]) is True


def test_foreign_code_receives_the_original_container_not_a_copy():
    """反例（独立 review 2）: 外の `__eq__` の相手は双子と同じ object（写しでも包みでもない）。"""

    seen = []
    box = [Callback(2, True)]

    class Recorder:
        def __eq__(self, other):
            seen.append((other is box, type(other).__name__))
            return False

        __hash__ = object.__hash__

    HOOK_CALLS.clear()
    assert live_values.equal([Recorder()], [box]) is False
    assert seen == [(True, "list")]
    assert dict(HOOK_CALLS) == {}


def test_a_ref_subclass_with_its_own_equality_is_called_first_like_python():
    """反例（独立 review 5）: 右が左の型の subclass で `__eq__` を持つと、Python は右を先に呼ぶ。"""

    from scripts.function_tracer_pcode.core.runtime_refs import LocationBaseRef

    calls = []

    class Child(LocationBaseRef):
        def __eq__(self, other):
            calls.append("child")
            return True

        __hash__ = LocationBaseRef.__hash__

    base = LocationBaseRef(kind="parameter", parameter_index=0)
    child = Child(kind="parameter", parameter_index=1)
    expected = (bool([base] == [child]), bool(base == child), bool(child in [base]))
    expected_calls = list(calls)
    calls.clear()
    got = (live_values.equal([base], [child]), live_values.equal(base, child), live_values.contains([base], child))
    assert got == expected == (True, True, True)
    assert calls == expected_calls


def test_location_refs_that_are_equal_hash_alike():
    """`LocationBaseRef.__eq__` は storage の名前（`storage_space`）を比べない: hash も読まない。"""

    from scripts.function_tracer_pcode.core.runtime_refs import LocationBaseRef

    a = LocationBaseRef(kind="storage", storage_space_id=1, storage_space="ram", storage_offset=8, storage_size=4)
    b = LocationBaseRef(kind="storage", storage_space_id=1, storage_space="RAM", storage_offset=8, storage_size=4)
    assert a == b
    assert hash(a) == hash(b)
    assert len({a, b}) == 1


def test_cyclic_and_container_shared_exception_states_are_copied_like_the_twin():
    """反例（独立 review 6）と mutation: 閉路の状態（自分を持つ slot・`__context__` の環）と、中の例外を持つ容器の共有。"""

    class Looped(ValueError):
        __slots__ = ("me", "pair", "again")

        def __str__(self):
            return f"{self.args[0]!r} {self.me is self} {self.pair is self.again} {self.pair}"

    def build(text):
        error = Looped(text)
        error.me = error
        shared = (KeyError(text),)
        error.pair = shared
        error.again = shared
        other = KeyError(text)
        error.__context__ = other
        other.__context__ = error
        return error

    expected = str(build("".join(["a", "b"])))
    HOOK_CALLS.clear()
    assert live_values.exception_text(build(LiarStr("ab"))) == expected
    assert dict(HOOK_CALLS) == {}


def test_the_exception_copy_check_rejects_a_lost_sharing():
    """写しの確かめ（防御: 写しが正しければ到達しない）が、field 間の共有を失った写しを拒む。"""

    shared = [1]
    error = ValueError(shared)
    error.note = shared
    fields = live_values._exception_fields(error, ValueError)
    items = live_values._exception_instance_dict(error)
    clone = ValueError([1])
    clone.note = [1]
    copied = live_values._exception_fields(clone, ValueError)
    state_items = live_values._exception_instance_dict(clone)
    assert not live_values._exception_state_matches(error, clone, fields, ValueError, copied, items, state_items)
    good = ValueError(shared)
    good.note = shared
    assert live_values._exception_state_matches(
        error, good, fields, ValueError, live_values._exception_fields(good, ValueError), items,
        live_values._exception_instance_dict(good),
    )


# ---------------------------------------------------------------------------
# 第 7 回の 2 巡目の独立 review の反例
# ---------------------------------------------------------------------------


def test_a_replaced_element_reusing_a_freed_id_is_still_seen_as_a_change():
    """反例: callback が元の list の要素を外して捨て、同じ番地に作られた別の値を置く（`id` の再利用）。"""

    def scene(lying):
        left = [1, None, Liar(5) if lying else 5]

        class Swap:
            def __eq__(self, other):
                left[2] = None
                left[2] = Liar(6) if lying else 6
                return True

            __hash__ = object.__hash__

        left[1] = Swap()
        return left, [1, Callback(0, lying), 5]

    left, right = scene(False)
    expected = _run(lambda: bool(left == right))
    left, right = scene(True)
    _undecided_or(expected, lambda: live_values.equal(left, right))


def test_sorting_guards_the_original_containers():
    """反例: 並べる要素の list（scalar の subclass の葉: 読むと写る）を、並べる途中の callback が変える。"""

    log = []

    def scene(lying):
        held = [Liar(1) if lying else 1]

        class Grow:
            def __lt__(self, other):
                log.append("lt")
                held.append(Liar(5) if lying else 5)
                return True

            def __gt__(self, other):
                log.append("gt")
                held.append(Liar(5) if lying else 5)
                return False

            __hash__ = object.__hash__

        return [held, Grow(), [1, 2]], held

    items, held = scene(False)
    expected = _run(lambda: (tuple(_view(item) for item in sorted(items)), _view(held)))
    expected_log, log[:] = list(log), []
    items, held = scene(True)
    HOOK_CALLS.clear()
    got = _run(lambda: (tuple(_view(item) for item in live_values.sorted_trees(items)), _view(held)))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",)), (expected, got)
    assert log == expected_log[: len(log)]
    if got == ("undecidable",):
        assert _view(held) == _view([1] + [5] * (len(held) - 1))  # 双子と同じ回数だけ変えた（余分な呼び出しが無い）


@pytest.mark.parametrize("foreign_inside", [False, True], ids=["read_copy", "copy_of_a_read_copy"])
def test_foreign_code_never_receives_a_read_copy(foreign_inside):
    """反例: scalar の subclass の葉が容器の写しを作らせると、外の `__eq__` は双子の容器と別の object を受け取る:
    判定しない（外の code の呼び出しの前に）。写しが外の葉を持ち、包むためにさらに写しても同じ。"""

    seen = []

    def scene(lying):
        held = [Liar(7) if lying else 7] + ([Callback(1, lying)] if foreign_inside else [])

        class Holder:
            def __eq__(self, other):
                seen.append(other is held)
                return False

            __hash__ = object.__hash__

        return [Holder()], [held]

    left, right = scene(False)
    expected = _run(lambda: bool(left == right))
    expected_seen, seen[:] = list(seen), []
    left, right = scene(True)
    got = _undecided_or(expected, lambda: live_values.equal(left, right))
    assert seen == (expected_seen if got == expected else [])


@pytest.mark.parametrize("make", [
    lambda lying: __import__("types").SimpleNamespace(a=Liar(1) if lying else 1),
    lambda lying: list[Liar(1) if lying else 1],
], ids=["simplenamespace", "generic_alias"])
def test_standard_library_values_that_compare_what_they_hold_are_not_answered(make):
    expected = _run(lambda: bool([make(False)] == [make(False)]))
    assert _undecided_or(expected, lambda: live_values.equal([make(True)], [make(True)])) == ("undecidable",)


def test_an_undecided_intrinsic_comparison_is_not_retried_without_cases():
    """`_intrinsic_values_match` は判定不能（`TypeError` の subclass）を、引数を減らした比べ直しで一致にしない。"""

    from scripts.function_tracer_pcode.proof.strategies import pairwise_solver_proven_rewrite as rewrite

    class Strategy:
        def _intrinsic_runtime_values_equivalent(self, left, right, left_case=None, right_case=None):
            if left_case is not None:
                raise UndecidableComparison("undecided")
            return True

    class Case:
        value_expr = object()

    assert rewrite._intrinsic_values_match(Strategy(), Case(), Case()) is False


# ---------------------------------------------------------------------------
# mutation が残した規則（判定する側の scope・確かめの長さ・登録した比較の相手）
# ---------------------------------------------------------------------------


def _undecidable_binding_summary(**changes):
    from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopSummaryRef, LoopVariableIdentityRef
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    ref = LoopVariableIdentityRef(role="i", varnode_key=(Callback(1, True),), binder_ordinal=0)
    return LoopSummaryRef(**{**corpus.BASES[LoopSummaryRef](), "guard_constraints": (ref,), **changes})


def test_an_undecidable_binding_ends_the_loop_comparison_in_unknown():
    """束縛の文脈の key が判定できない summary（`varnode_key` に外の object）: 比べる側は「key が無い」として後の gate
    （side effect の profile の違い → incompatible）へ進まず unknown。key を読む他の消費者には従来どおり `None`。"""

    from scripts.function_tracer_pcode.core.runtime_refs import loops
    from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopSideEffectProfileRef

    left = _undecidable_binding_summary()
    right = _undecidable_binding_summary(
        side_effect_profile=LoopSideEffectProfileRef(profile="pure_memory_read", memory_reads=True, effect_count=1)
    )
    HOOK_CALLS.clear()
    result = loops.compare_loop_summaries(left, right)
    assert result.status == "unknown"
    assert result.reason == "loop summary keys are not comparable by builtin code"
    assert loops.loop_summary_method_b_key(left) is None
    assert dict(HOOK_CALLS) == {}


def test_an_element_moved_between_copied_lists_is_a_change():
    """要素が写した list の間を移っても `id` の連結は同じ: 長さの列も確かめる。"""

    def scene(lying):
        world = World(lying)
        first = [None, Probe(world, "x", 3)]
        second = [Probe(world, "y", 4)]

        def move():
            second.insert(0, list.pop(first))

        first[0] = Probe(world, "m", 1, "mutate", move)
        return world, [first, second], [[1, 3], [4]]

    world, left, right = scene(False)
    expected = _run(lambda: bool(left == right))
    expected_log = list(world.log)
    world, left, right = scene(True)
    _undecided_or(expected, lambda: live_values.equal(left, right))
    assert world.log == expected_log[: len(world.log)]


def test_registered_comparisons_compare_with_the_wrapped_value():
    """登録した比較は包みでなく元の値と比べる: 左の型の subclass でない `LocationBaseRef` の subclass（自前の `__eq__`）
    と、同じ field の ref は等しい（双子と同じ）。"""

    from scripts.function_tracer_pcode.core.runtime_refs import LocationBaseRef

    calls = []

    class Plain(LocationBaseRef):
        pass

    class Other(LocationBaseRef):
        def __eq__(self, other):
            calls.append("other")
            return NotImplemented

        __hash__ = LocationBaseRef.__hash__

    plain = Plain(kind="parameter", parameter_index=0)
    other = Other(kind="parameter", parameter_index=0)
    expected = (bool([plain] == [other]), list(calls))
    calls.clear()
    assert (live_values.equal([plain], [other]), list(calls)) == expected
    assert expected[0] is True


def test_the_copy_check_sees_an_element_moving_between_lists_in_either_order():
    """確かめの読み（白箱）: 要素が list の間を移っても `id` の連結が同じになる並びの両方で、変化と読む。"""

    x = object()
    for order in ("ab", "ba"):
        first, second = [object(), x], [object()]
        frame = live_values._CopyFrame([first, second] if order == "ab" else [second, first])
        assert frame.unchanged()
        if order == "ab":
            second.insert(0, list.pop(first))  # [a, x] + [b] → [a] + [x, b]
        else:
            first.insert(0, list.pop(second))  # [b] + [a, x] → [] + [b, a, x]
        assert not frame.unchanged(), order


# ---------------------------------------------------------------------------
# 第 7 回の 3 巡目の独立 review の反例
# ---------------------------------------------------------------------------


class _Color(__import__("enum").Enum):
    RED = 1


@pytest.mark.parametrize("make", [
    lambda lying: {_Color.RED: Liar(1) if lying else 1},
    lambda lying: {_Color.RED, Liar(1) if lying else 1},
    lambda lying: ({_Color.RED: [Liar(1) if lying else 1]},),
], ids=["dict_key", "set_element", "nested"])
def test_a_value_that_cannot_be_read_is_undecidable_not_a_plain_type_error(make):
    """反例（3 巡目 C1）: 読めない値（不活性でない key・要素と scalar の subclass の葉: 作り直せない）は、比べる側の
    契約が許す `UndecidableComparison` で答える（素の `TypeError` は `decided_equal` を抜け、呼ぶ側の別の経路に入る）。"""

    from scripts.function_tracer_pcode.core.runtime_refs._reading import decided_equal

    expected = _run(lambda: bool(make(False) == make(False)))
    left, right = make(True), make(True)  # 作るときの hash（set の要素）は数えない
    got = _undecided_or(expected, lambda: live_values.equal(left, right))
    if got == ("undecidable",):
        assert decided_equal(make(True), make(True)) is None
    for operation in (
        lambda: live_values.unequal(make(True), make(True)),
        lambda: live_values.contains((make(True),), make(True)),
        lambda: live_values.sorted_trees([make(True)]),
        lambda: live_values.inert_key(make(True)),
    ):
        outcome = _run(operation)
        assert outcome[0] in ("value", "undecidable"), outcome


def test_an_opaque_value_compared_with_itself_takes_the_identity_shortcut():
    """不透明な葉（`slice`）も、組み込みの容器の比較の identity の近道は双子と同じ（比較が走るときだけ判定しない）。"""

    value = slice(Callback(1, True))
    HOOK_CALLS.clear()
    assert live_values.equal((value,), (value,)) is True
    assert live_values.contains([value], value) is True
    assert dict(HOOK_CALLS) == {}


def test_foreign_code_never_receives_the_opaque_wrapper():
    """外の葉と不透明な葉の比較: 外の `__eq__` に包みを渡さない（双子は元の値を渡す）。渡す前に判定しない。"""

    seen = []

    class Recorder:
        def __eq__(self, other):
            seen.append(type(other).__name__)
            return NotImplemented

        __hash__ = object.__hash__

    expected = _run(lambda: bool([Recorder()] == [slice(Callback(1, False))]))
    expected_seen, seen[:] = list(seen), []
    got = _undecided_or(expected, lambda: live_values.equal([Recorder()], [slice(Callback(1, True))]))
    assert seen == (expected_seen if got == expected else expected_seen[: len(seen)])
    assert "_Opaque" not in seen


# ---------------------------------------------------------------------------
# 費用の修正（owner の要素ごとの比較・葉どうしの直接の比較）の等価性
# ---------------------------------------------------------------------------


def test_owner_equality_keeps_the_tuple_identity_shortcut():
    """owner の `==` は組み込みの tuple の `==` と同じく、同じ object の要素を比べない（同じ NaN の field は等しい）。"""

    from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopSummaryRef
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    nan = float("nan")
    base = corpus.BASES[LoopSummaryRef]()
    a = LoopSummaryRef(**{**base, "start_expr": nan})
    b = LoopSummaryRef(**{**base, "start_expr": nan})
    c = LoopSummaryRef(**{**base, "start_expr": float("nan")})
    assert (a == b, a == c) == ((nan,) == (nan,), (nan,) == (float("nan"),)) == (True, False)


def test_a_leaf_comparison_inside_an_outer_comparison_checks_the_outer_copies():
    """外側の比較が写した list の要素の ref の `==`（葉どうしの直接の比較）で、外の code が外側の list を変える。
    外側が古い写しを読み続けて双子に無い外の code を呼ばない（双子と同じか、記録が双子の先頭の判定不能）。"""

    from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopSummaryRef
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    base = corpus.BASES[LoopSummaryRef]()

    def scene(lying):
        world = World(lying)
        left = [None, None]

        def change():
            left[1] = 7

        left[0] = LoopSummaryRef(**{**base, "start_expr": Probe(world, "m", 1, "mutate", change)})
        left[1] = Probe(world, "x", 7)
        right = [LoopSummaryRef(**{**base, "start_expr": Probe(world, "n", 1)}), Probe(world, "y", 7)]
        world.log.clear()
        return world, left, right

    world, left, right = scene(False)
    expected = _run(lambda: bool(left == right))
    expected_log = list(world.log)
    world, left, right = scene(True)
    _undecided_or(expected, lambda: live_values.equal(left, right))
    assert world.log == expected_log[: len(world.log)]


def test_opaque_leaves_compared_directly_are_not_answered():
    expected = _run(lambda: bool(slice(Callback(1, False)) == slice(Callback(1, False))))
    assert _undecided_or(
        expected, lambda: live_values.equal(slice(Callback(1, True)), slice(Callback(1, True)))
    ) == ("undecidable",)

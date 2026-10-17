# -*- coding: utf-8 -*-
"""Issue #242（第 8 回のレビュー）: 比べる側の契約が依存する前提を、前提を変える操作で確かめる。

前提（`core/live_values` の「比較・所属・順序・hash」の節の表と同じ）:

- 型の信頼の判定・型の名前空間の読みは、外の code が呼ばれた後には成り立たない（外の code は class を書き換えられる）。
- hash は、同じ値を使う間は変わらない（読みが作った object の identity に依らない）。
- 判定不能は、例外の捕捉・helper を通っても、欠けた値や確定判定にならない。
- 作り直す経路（容器・例外の写し）はどれも、比較・hash・共有・閉路の同じ規則に従う。
- 安全を確かめる処理（型の判定・名前空間の読み）自身も、禁止した hook を呼ばない。

期待値はどれも実装と独立: 正直な双子に Python の組み込みの演算を当てた結果、または前提そのもの（等しい ⇒ 同じ hash、
同じ値の hash は呼び出しの間で同じ、など）。
"""

from __future__ import annotations

import gc
import sys

import pytest

from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.live_values import UndecidableComparison
from scripts.function_tracer_pcode.tests.unit.runtime_ref_adversaries import (
    HOOK_CALLS, Callback, Liar, LiarFloat, LiarStr,
)


def _run(operation):
    try:
        return ("value", operation())
    except UndecidableComparison:
        return ("undecidable",)
    except Exception as error:  # noqa: BLE001 - 双子と同じ例外の型を比べる
        return ("raises", type(error).__name__)


def _summary(**changes):
    from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopSummaryRef
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    return LoopSummaryRef(**{**corpus.BASES[LoopSummaryRef](), **changes})


# ---------------------------------------------------------------------------
# 反例 1: 比較の途中で class が変わる（先の callback が後の葉の class に `__eq__` を足す）
# ---------------------------------------------------------------------------


def _class_changing_scene(lying):
    class Late:
        """比較の dunder を持たない（`object` の `==`）葉。最初の比較の callback が `__eq__` を足す。"""

    class First:
        def __eq__(self, other):
            Late.__eq__ = lambda self, other: Liar(0) if lying else 0  # 偽る側の 0 は真偽を偽る（真と答える）
            return True

        __hash__ = object.__hash__

    return (First(), Late()), (First(), Late())


def test_a_class_changed_by_an_earlier_callback_is_compared_like_the_twin():
    left, right = _class_changing_scene(False)
    expected = _run(lambda: bool(left == right))
    assert expected == ("value", False)
    left, right = _class_changing_scene(True)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.equal(left, right))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))


def test_a_class_changed_during_a_ref_comparison_is_compared_like_the_twin():
    twin_left, twin_right = _class_changing_scene(False)
    expected = _run(lambda: bool(_summary(start_expr=twin_left) == _summary(start_expr=twin_right)))
    left, right = _class_changing_scene(True)
    a, b = _summary(start_expr=left), _summary(start_expr=right)
    HOOK_CALLS.clear()
    got = _run(lambda: a == b)
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))


# ---------------------------------------------------------------------------
# 反例 2: hash の安定（NaN の float の subclass を持つ ref）
# ---------------------------------------------------------------------------


def _churn():
    """解放と割り当てを繰り返す（解放された番地を別の値が再利用する機会を作る）。"""

    gc.collect()
    return [float("nan") for _ in range(64)]


@pytest.mark.parametrize("make", [
    lambda: LiarFloat(float("nan")),
    lambda: (LiarFloat(float("nan")), 1),
    lambda: frozenset({LiarFloat(float("nan"))}),
], ids=["leaf", "tuple", "frozenset"])
def test_the_hash_of_a_ref_is_stable_while_it_is_used(make):
    ref = _summary(start_expr=make())
    HOOK_CALLS.clear()
    first = _run(lambda: hash(ref))
    _churn()
    second = _run(lambda: hash(ref))
    assert first == second
    if first[0] == "value":
        table = {ref: "value"}
        _churn()
        assert ref in table and table[ref] == "value"
        assert len({ref, ref}) == 1
    assert dict(HOOK_CALLS) == {}


def test_hash_tree_is_stable_and_consistent_with_equal_for_shared_nan_leaves():
    leaf = LiarFloat(float("nan"))
    left, right = (leaf, 1), (leaf, 1)
    HOOK_CALLS.clear()
    assert live_values.equal(left, right) is True  # 双子も同じ NaN の object を共有する: identity の近道で等しい
    first = live_values.hash_tree(left)
    _churn()
    assert live_values.hash_tree(right) == first == live_values.hash_tree(left)
    assert dict(HOOK_CALLS) == {}


# ---------------------------------------------------------------------------
# 反例 3: 判定不能が helper の例外の捕捉で欠けた値になる
# ---------------------------------------------------------------------------


class _UndecidableKey:
    """`semantic_key()` が比べる側の契約で判定不能になる値（外の object を要素に持つ set を比べる）。"""

    def semantic_key(self):
        live_values.equal({Callback(1, True)}, {Callback(1, True)})
        return ("never",)


def test_an_undecidable_key_ends_the_loop_comparison_in_unknown_not_in_a_later_gate():
    from scripts.function_tracer_pcode.core.runtime_refs.loops import (
        LoopSideEffectProfileRef, compare_loop_summaries,
    )

    left = _summary(limit_expr=_UndecidableKey())
    right = _summary(
        limit_expr=_UndecidableKey(),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure_memory_read", memory_reads=True, effect_count=1),
    )
    result = compare_loop_summaries(left, right)
    assert result.status == "unknown", result


def test_an_undecidable_comparison_is_not_absorbed_by_handlers_of_ordinary_errors():
    """判定不能は「回復できる」普通の例外（`TypeError` / `ValueError` / `AttributeError`）の捕捉に吸収されない。"""

    assert not issubclass(UndecidableComparison, (TypeError, ValueError, AttributeError, LookupError, RecursionError))
    caught = []
    try:
        try:
            live_values.equal({Callback(1, True)}, {Callback(1, True)})
        except (TypeError, ValueError, AttributeError, RecursionError):
            caught.append("ordinary")
    except UndecidableComparison:
        caught.append("undecidable")
    assert caught == ["undecidable"]


# ---------------------------------------------------------------------------
# 反例 4: 例外の写しが set を作り直す（衝突する子の例外の比較）
# ---------------------------------------------------------------------------


def _exception_set_scene(lying):
    state = {"lie": False}

    class Child(Exception):
        def __eq__(self, other):
            if state["lie"]:
                return Liar(0) if lying else 0  # 偽る側の 0 は真と答える
            return self is other

        def __hash__(self):
            return 1  # 全部が衝突する

    class Holder(ValueError):
        def __str__(self):
            return f"{len(self.args[0])} children {sorted(str(c) for c in self.args[0])}"

    children = {Child(LiarStr("a") if lying else "".join(["a", ""])), Child(LiarStr("b") if lying else "".join(["b", ""]))}
    state["lie"] = True
    return Holder(children)


def test_an_exception_holding_a_set_of_colliding_exceptions_is_not_rebuilt_unsafely():
    twin = _exception_set_scene(False)
    expected = str(twin)
    assert expected.startswith("2 children")
    lying = _exception_set_scene(True)
    HOOK_CALLS.clear()
    got = live_values.exception_text(lying)
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, f"<unprintable {type(lying).__qualname__} object>")


# ---------------------------------------------------------------------------
# 反例 5: 安全を確かめる処理自身が hook を呼ぶ（class の名前空間の key の `__eq__`）
# ---------------------------------------------------------------------------


class _HookName(str):
    """名前空間の key に置く str の subclass: hash は基底型のまま（引きの探索で比べられる）、`__eq__` は数える。"""

    __hash__ = str.__hash__

    def __eq__(self, other):
        HOOK_CALLS["_HookName.__eq__"] += 1
        return str.__eq__(self, other)


@pytest.mark.parametrize("name", ["__eq__", "__hash__", "__lt__", "__new__", "__str__"])
def test_reading_a_class_namespace_never_runs_its_key_hooks(name):
    kind = type("Keyed", (), {_HookName(name): None, "x": 1})
    value = object.__new__(kind)  # `__new__` の key を持つ型も作れる（名前空間の読みを確かめる）
    error_kind = type("KeyedError", (ValueError,), {_HookName(name): None})  # 型を作るときの hook は数えない
    error = BaseException.__new__(error_kind, LiarStr("m"))
    HOOK_CALLS.clear()
    for operation in (
        lambda: live_values.equal(value, value),
        lambda: live_values.equal((value, Callback(1, True)), (value, Callback(1, True))),
        lambda: live_values.hash_tree((value,)),
        lambda: live_values.exception_text(error),
    ):
        _run(operation)
    assert dict(HOOK_CALLS) == {}


# ---------------------------------------------------------------------------
# 非 blocker: ExceptionGroup を含む閉路・seed の比較の判定不能・owner の hash の docstring
# ---------------------------------------------------------------------------


@pytest.mark.skipif(sys.version_info < (3, 11), reason="ExceptionGroup は python 3.11 から")
def test_a_cycle_through_an_exception_group_is_copied_like_the_twin():
    def build(text):
        member = ValueError(text)
        group = ExceptionGroup("g", [member])  # noqa: F821 - python 3.11 以降
        member.__context__ = group  # 普通の状態の閉路（group の `exceptions` は読みだけの field）
        return member

    class Show(ValueError):
        def __str__(self):
            return f"{self.args[0]!r} {type(self.__context__).__name__} {self.__context__.exceptions[0] is self}"

    def build_show(text):
        member = Show(text)
        group = ExceptionGroup("g", [member])  # noqa: F821
        member.__context__ = group
        return member

    for factory in (build, build_show):
        expected = str(factory("".join(["m", ""])))
        HOOK_CALLS.clear()
        assert live_values.exception_text(factory(LiarStr("m"))) == expected
        assert dict(HOOK_CALLS) == {}


class _OpaqueTerm:
    """seed の項の key に置く外の object（自前の `__eq__`）。"""

    def __eq__(self, other):
        return False

    __hash__ = object.__hash__


class _OpaqueSeed:
    """`stable_key()` が外の object を要素に持つ set を含む seed の項（第 7 回で「入力を作れない」とした経路）。"""

    def stable_key(self):
        return ("readonly_reduction_term", {_OpaqueTerm()}, 4)


def test_an_undecidable_seed_term_comparison_is_reachable_and_never_a_key():
    """memory_load の項の記述（corpus の基底）と、外の object の set を key に持つ seed の項: Method-B の正規化の比較は
    判定不能。key を読む消費者には判定不能のまま（「key が無い」にしない）、比べる側は unknown。"""

    from scripts.function_tracer_pcode.core.expression import Expression
    from scripts.function_tracer_pcode.core.runtime_refs import loops

    def summary():
        return _summary(start_expr=Expression.constant(1, size=4), seed_terms=(_OpaqueSeed(),))

    with pytest.raises(UndecidableComparison):
        loops.loop_summary_method_b_key(summary())
    result = loops.compare_loop_summaries(summary(), summary())
    assert result.status == "unknown"


# ---------------------------------------------------------------------------
# 判定不能は pair の台帳に残る（helper・包括の捕捉が握り潰しても確定判定にならない）
# ---------------------------------------------------------------------------


def test_a_swallowed_undecidable_comparison_still_stops_the_pair():
    """判定不能は作るときに pair の台帳へ記録される（記録が先、例外は後）。`except Exception` が握り潰しても、
    pair の境界は登録した reason（`comparison_undecidable`）の限界を読む。"""

    from scripts.function_tracer_pcode.core import errors

    with errors.pair_failure_scope(("pair", 1), ("session", 1)) as ledger:
        assert errors.pending_pair_failure() is None
        try:
            live_values.equal({Callback(1, True)}, {Callback(1, True)})
        except Exception:  # noqa: BLE001 - helper の包括の捕捉の代わり
            pass
        pending = errors.pending_pair_failure()
        assert pending is not None
        assert pending.exception.reason_id == "comparison_undecidable"
        assert not ledger.allows_semantic_analysis()  # 新しい意味解析を始めない（確定処理は続く: #106 の契約）


def test_an_otherwise_equivalent_pair_with_a_swallowed_undecidable_comparison_is_unknown():
    """#106 の E0d と同じ harness: 解析の深部の `except Exception` が判定不能を握り潰しても、pair は確定判定（EQ）に
    進まず、登録した reason の UNKNOWN になる。"""

    from scripts.function_tracer_pcode.core.errors import reset_pair_failure_scopes
    from scripts.function_tracer_pcode.tests.unit import test_issue106_pair_limitation_propagation as harness

    reset_pair_failure_scopes()
    try:
        analysis1, analysis2 = harness._analyses()

        def analyze(self, name, timeout):
            if name == "func1":
                try:
                    live_values.equal({Callback(1, True)}, {Callback(1, True)})
                except Exception:  # noqa: BLE001 - 深部の包括の捕捉を再現する
                    pass
            return analysis1 if name == "func1" else analysis2

        result = harness._run_pair(
            analyze=analyze, stage_plan=harness._equivalent_stage_plan, connector=harness._connector(),
        )
    finally:
        reset_pair_failure_scopes()
    assert result.is_equivalent is None and result.error_message is None
    assert result.final_outcome == "UNKNOWN"
    assert harness._reason_ids(result) == ["comparison_undecidable"]


def test_the_comparison_undecidable_reason_is_registered_and_blocks_decisions():
    from scripts.function_tracer_pcode.authority.domains.analysis_limitation import (
        ANALYSIS_LIMITATION_OBSERVED_SITE, ANALYSIS_LIMITATION_REASON_REGISTRY, COMPARISON_UNDECIDABLE_REASON_ID,
    )
    from scripts.function_tracer_pcode.core.comparison_limits import ComparisonUndecidable

    definitions = {item.reason_id: item for item in ANALYSIS_LIMITATION_REASON_REGISTRY.snapshot()}
    assert definitions[COMPARISON_UNDECIDABLE_REASON_ID].decision_effect == "blocks_decision"
    assert COMPARISON_UNDECIDABLE_REASON_ID in ANALYSIS_LIMITATION_OBSERVED_SITE.reason_ids
    assert ComparisonUndecidable.REASON_ID == COMPARISON_UNDECIDABLE_REASON_ID


#: 判定不能（`UndecidableComparison`）を名指しで捕まえてよい場所（module, 関数）と、そこで何にするか。判定不能は
#: 台帳に記録済みなので、ここは局所の扱い（確定判定にも「無い値」にも進まない形）だけを決める。新しい捕捉はここに
#: 分類しない限り落ちる
UNDECIDABLE_HANDLERS = {
    ("_reading.py", "decided_equal"): "3 値の `None`（呼ぶ側は `is None` で止まる: `decided_equal` の静的規則）",
    ("loops.py", "compare_loop_summaries"): "loop summary の比較は unknown",
    ("live_values.py", "exception_text"): "`<unprintable ...>`（判定しない文字列）",
    ("live_values.py", "_compared_tree"): "投げ直す（読めない値の `TypeError` だけを判定不能にする）",
    ("pairwise_solver_proven_rewrite.py", "_intrinsic_values_match"): "一致しない（引数を減らして比べ直さない）",
    ("locations.py", "matches_parameter"): "投げ直す（後の広い捕捉が「一致しない」にしない）",
}


def test_every_handler_of_undecidable_comparisons_is_classified():
    import ast
    import pathlib

    root = pathlib.Path(__file__).resolve().parents[2]
    found = set()
    for path in sorted(root.rglob("*.py")):
        if "tests" in path.relative_to(root).parts:
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"))
        parents = {child: node for node in ast.walk(tree) for child in ast.iter_child_nodes(node)}
        for node in ast.walk(tree):
            if not isinstance(node, ast.ExceptHandler) or node.type is None:
                continue
            types = node.type.elts if isinstance(node.type, ast.Tuple) else [node.type]
            if not any(getattr(item, "id", getattr(item, "attr", None)) == "UndecidableComparison" for item in types):
                continue
            function = node
            while function in parents and not isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
                function = parents[function]
            found.add((path.name, getattr(function, "name", "<module>")))
    assert found == set(UNDECIDABLE_HANDLERS), found ^ set(UNDECIDABLE_HANDLERS)


# ---------------------------------------------------------------------------
# 前提を変える操作を混ぜた双子との property test（第 7 回の場面に、class の書き換え・NaN・複数回の呼び出し・GC を足す）
# ---------------------------------------------------------------------------


def _scene8(seed, lying):
    """第 7 回の場面（`Scene`）に、class を書き換える callback・`object` の比較の葉・NaN の葉を足した場面。"""

    import random

    from scripts.function_tracer_pcode.tests.unit import test_issue242_comparison_invariants as base

    class Plain:
        """比較の dunder を持たない葉（`object` の `==`）。callback が後から `__eq__` を足す。"""

        __slots__ = ("tag", "__weakref__")

        def __init__(self, tag):
            self.tag = tag

    class Scene8(base.Scene):
        def _leaf(self, rng, hashed=False):
            roll = rng.random()
            if roll < 0.15:
                self.counter += 1
                return Plain(f"q{self.counter}")
            if roll < 0.22 and not hashed:
                nan = float("nan")
                subclass = rng.random() < 0.5  # 双子と偽る側で同じ数だけ乱数を引く（形をそろえる）
                return LiarFloat(nan) if self.lying and subclass else nan
            return super()._leaf(rng, hashed)

    scene = Scene8(seed, lying)
    rng = random.Random(seed * 7919 + 1)
    probes = [p for p in scene._probes() if p.mode == "pure"]
    if probes and rng.random() < 0.5:
        probe = rng.choice(probes)
        world = scene.world

        def plain_eq(self, other):
            world.log.append(("eq_plain", self.tag, getattr(other, "tag", None)))
            return world.result(self is other)

        def mutate_class():
            world.log.append(("mutate_class",))
            Plain.__eq__ = plain_eq
            Plain.__hash__ = object.__hash__

        probe.mode = "mutate"
        probe.action = mutate_class
    return scene


def _observe8(seed):
    from scripts.function_tracer_pcode.tests.unit import test_issue242_comparison_invariants as base

    def run(scene, operation):
        outcomes, logs = [], []
        for _ in range(2):  # 同じ値に 2 回（間に割り当て: 解放された番地の再利用）: 結果は呼び出しごとに双子と同じ
            start = len(scene.world.log)
            outcomes.append(base._run(operation(scene)))
            logs.append(list(scene.world.log[start:]))
            [float("nan") for _ in range(64)]
        return outcomes, logs

    twin = _scene8(seed, False)
    outcomes, logs = run(twin, base._builtin)
    expected = {"outcomes": _nan_marked(outcomes), "logs": _nan_marked(logs), "log": _nan_marked(twin.world.log)}
    lying = _scene8(seed, True)
    HOOK_CALLS.clear()
    outcomes, logs = run(lying, base._contract)
    hooks = dict(HOOK_CALLS)
    got = {"outcomes": _nan_marked(outcomes), "logs": _nan_marked(logs), "hooks": hooks, "log": _nan_marked(lying.world.log)}
    return expected, got, lying


def _holds_identity_hashed(value):
    """値の木（容器・辿れる値）のどこかで、identity で hash する葉（`Plain`）を hash で置く容器が持つか。"""

    pending, seen = [value], set()
    while pending:
        node = pending.pop()
        if id(node) in seen:
            continue
        seen.add(id(node))
        kind = type(node)
        if kind in (set, frozenset, dict) and any(type(key).__name__ == "Plain" for key in node):
            return True
        if kind in (tuple, list, set, frozenset):
            pending.extend(node)
        elif kind is dict:
            pending.extend(node.keys())
            pending.extend(node.values())
    return False


def _nan_marked(value):
    """記録・結果の NaN を印にした写し（`nan != nan` で同じ記録を違うと読まない）。hash の値はそのまま。"""

    if type(value) is float and value != value:
        return "<nan>"
    if type(value) in (list, tuple):
        return type(value)(_nan_marked(item) for item in value)
    return value


SEEDS8 = 4000


@pytest.mark.parametrize("chunk", range(8))
def test_comparisons_match_the_twin_when_callbacks_change_classes_and_calls_repeat(chunk):
    from scripts.function_tracer_pcode.tests.unit import test_issue242_comparison_invariants as base

    failures, matched, undecided = [], 0, 0
    for seed in range(chunk, SEEDS8, 8):
        expected, got, scene = _observe8(seed)
        if got["hooks"]:
            failures.append((seed, "hooks", got["hooks"]))
            continue
        # identity で hash する葉（`Plain`）を hash で置く容器: 表の配置は object の番地で決まり、双子と偽る側で probe の
        # 順と衝突の回数が変わる（双子どうしでも変わる）。その場面は記録の並びでなく、記録された出来事の集合を比べる
        identity_hashed = _holds_identity_hashed((scene.left, scene.right, *scene.containers))

        def same_log(mine, twins, prefix=False):
            if identity_hashed:
                return set(map(repr, mine)) <= set(map(repr, twins)) if prefix else set(map(repr, mine)) == set(map(repr, twins))
            return mine == (twins[: len(mine)] if prefix else twins)

        if any(outcome == ("undecidable",) for outcome in got["outcomes"]):
            # 判定不能の呼び出しまでを比べる（その後は双子が続けた分だけ世界が違い得る）
            first = [outcome == ("undecidable",) for outcome in got["outcomes"]].index(True)
            if got["outcomes"][:first] != expected["outcomes"][:first] or not all(
                same_log(mine, twins) for mine, twins in zip(got["logs"][:first], expected["logs"][:first])
            ):
                failures.append((seed, scene.operation, "before undecidable", expected, got))
                continue
            changed = any(entry[0] in ("mutate", "mutate_class") for entry in expected["log"])
            receives_container = any(
                len(entry) == 3 and type(entry[2]) is tuple and entry[2][0] == "other" for entry in expected["log"]
            )
            allowed = changed or scene.foreign_hashed or receives_container or identity_hashed
            undecided_log, twin_log = got["logs"][first], expected["logs"][first]
            prefix = same_log(undecided_log, twin_log, prefix=True)
            if not (allowed and prefix):
                failures.append((seed, scene.operation, "undecidable", expected, got))
            undecided += 1
            continue
        if scene.operation == "hash":
            # hash の値は双子の値と同じとは約束しない（`Plain` は identity の hash・NaN は印）: 結果の種類・記録と、
            # 同じ値の hash が呼び出しの間で同じことを比べる
            kinds = [outcome[0] for outcome in got["outcomes"]]
            if kinds != [outcome[0] for outcome in expected["outcomes"]] or not same_log(got["log"], expected["log"]):
                failures.append((seed, scene.operation, expected, got))
            elif kinds[0] == "value" and got["outcomes"][0] != got["outcomes"][1]:
                failures.append((seed, "unstable hash", got))
            else:
                matched += 1
            continue
        if got["outcomes"] != expected["outcomes"] or not same_log(got["log"], expected["log"]):
            failures.append((seed, scene.operation, expected, got))
            continue
        matched += 1
    assert failures == [], failures[:3]
    assert matched > undecided


def test_the_round8_generator_reaches_every_ingredient():
    """場面の材料（class を書き換える callback・書き換えの後も判定した場面・`object` の比較の葉・NaN の葉・hash で置く
    位置の葉・判定不能の場面）が実際に生まれる（生成の偏りで test が空回りしない）。"""

    seen = {"class_changed": 0, "decided_after_class_change": 0, "plain": 0, "nan": 0, "undecidable": 0}
    for seed in range(SEEDS8):
        expected, got, scene = _observe8(seed)
        changed = any(entry[0] == "mutate_class" for entry in expected["log"])
        seen["class_changed"] += changed
        seen["decided_after_class_change"] += changed and got["outcomes"][0][0] == "value"
        views = repr((scene.left, scene.right))
        seen["plain"] += "Plain" in views
        seen["nan"] += "nan" in views
        seen["undecidable"] += got["outcomes"][0] == ("undecidable",)
    assert all(count >= 10 for count in seen.values()), seen


# ---------------------------------------------------------------------------
# 第 8 回の独立レビューの反例と、危険な振る舞いを戻す mutation を捕まえる場面
# ---------------------------------------------------------------------------


class _CollidingName(str):
    """文字列は名前と違うが hash が名前と同じ key（Python の引きは文字列に依らず、hash の等しい key の `__eq__` を呼ぶ）。"""

    def __new__(cls, name):
        made = str.__new__(cls, "zzz_" + name)
        made.target = name
        return made

    def __hash__(self):
        return hash(self.target)

    def __eq__(self, other):
        HOOK_CALLS["_CollidingName.__eq__"] += 1
        return type(other) is str and str.__eq__(other, self.target)


def _keyed_class(name, implementation, bases=()):
    """名前空間の `name` を hash の衝突する別の文字列の key で持つ class（作るときの hook は数えない）。"""

    kind = type("Colliding", bases, {_CollidingName(name): implementation, "__module__": __name__})
    kind.unrelated = 1  # 型の method cache を捨てる（後の引きが名前空間を実際に引く）
    return kind


def test_a_colliding_namespace_key_is_never_read_as_a_missing_name():
    """名前と違う文字列で hash が衝突する key の class: Python の `==` はその key の値を実装として呼ぶ。比べる側は
    その class を不活性と分類しない（key の `__eq__` も、偽る実装の戻り値の `__bool__` も呼ばない）。"""

    def lying_eq(self, other):
        return Liar(0)

    def honest_eq(self, other):
        return 0

    twin = _keyed_class("__eq__", honest_eq)
    expected = _run(lambda: bool((twin(),) == (twin(),)))
    assert expected == ("value", False)
    kind = _keyed_class("__eq__", lying_eq)
    left, right = (kind(),), (kind(),)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.equal(left, right))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))
    assert live_values.class_defines(kind, "__eq__") is None


@pytest.mark.parametrize("name", ["__hash__", "__eq__", "__getattribute__", "__str__"])
def test_a_colliding_namespace_key_is_ambiguous_for_every_reader(name):
    kind = _keyed_class(name, lambda *args: 0)
    HOOK_CALLS.clear()
    assert live_values._leaf_trust(object.__new__(kind)) == live_values._OPAQUE
    with pytest.raises(TypeError):
        live_values.type_attribute(kind, "anything")
    with pytest.raises(TypeError):
        live_values.class_namespace_value(kind, name)
    assert live_values.class_defines(kind, name) is None
    assert dict(HOOK_CALLS) == {}


def test_hash_tree_never_looks_up_a_hash_through_a_colliding_key():
    kind = _keyed_class("__hash__", lambda self: 5)
    value = kind()
    HOOK_CALLS.clear()
    assert _run(lambda: hash(value)) == ("value", 5) and HOOK_CALLS  # 双子の `hash` は key の `__eq__` を呼ぶ
    kind.unrelated += 1  # 双子の引きが埋めた型の method cache を捨てる
    HOOK_CALLS.clear()
    assert _run(lambda: live_values.hash_tree((value,))) == ("undecidable",)
    assert dict(HOOK_CALLS) == {}


def test_the_owner_reads_fields_without_a_colliding_attribute_hook():
    import dataclasses

    from scripts.function_tracer_pcode.core import runtime_ref_record as owner

    @dataclasses.dataclass(frozen=True)
    @owner.runtime_ref_record
    class Record:
        a: int
        b: object = None

    calls = []

    def hooked(self, name):
        calls.append(name)
        return object.__getattribute__(self, name)

    sub = _keyed_class("__getattribute__", hooked, (Record,))
    HOOK_CALLS.clear()
    assert owner._plain_attribute_lookup(sub) is False
    assert dict(HOOK_CALLS) == {}
    # 作る: dataclass の生成した `__init__` 自身が `self.__post_init__` を読む（双子も同じ: owner の呼び出しでない）
    made = _run(lambda: (sub(1, (2,)), sub(1, (2,))))
    calls.clear()
    HOOK_CALLS.clear()
    if made[0] == "value":
        left, right = made[1]
        calls.clear()
        assert _run(lambda: left == right) in (("value", True), ("undecidable",))
    else:
        assert made == ("raises", "TypeError")  # 名前空間を組み込みの code だけで読めない ref は作らない
    assert calls == [] and dict(HOOK_CALLS) == {}


def _hash_rewrite_scene(lying):
    class Late:
        def __hash__(self):
            return 1

    class Rewriter:
        def __hash__(self):
            Late.__eq__ = lambda self, other: Liar(0) if lying else 0
            return 1

    return {Late()}, Rewriter()


def test_contains_never_runs_a_python_hash_on_a_leaf_classified_inert():
    box, item = _hash_rewrite_scene(False)
    expected = _run(lambda: item in box)
    box, item = _hash_rewrite_scene(True)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.contains(box, item))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))
    assert live_values._leaf_trust(item) != live_values._TRUSTED


def _container_scene(mutate):
    log = []

    class Before(list):
        pass

    class After(list):
        def __eq__(self, other):
            log.append("After.__eq__")
            return False

        __hash__ = None

    class First:
        def __eq__(self, other):
            log.append("First.__eq__")
            if mutate == "class":
                held.__class__ = After
            else:
                Before.__eq__ = After.__eq__
            return True

        __hash__ = object.__hash__

    held = Before([1, 2])
    return log, (First(), held), (First(), Before([1, 2]))


@pytest.mark.parametrize("mutate", ["class", "namespace"])
def test_a_container_subclass_changed_during_a_comparison_is_compared_like_the_twin(mutate):
    twin_log, left, right = _container_scene(mutate)
    expected = _run(lambda: bool(left == right))
    log, left, right = _container_scene(mutate)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.equal(left, right))
    assert dict(HOOK_CALLS) == {}
    if got == ("undecidable",):
        assert log == twin_log[: len(log)]
    else:
        assert (got, log) == (expected, twin_log)


def _member_scene(mutate, lying):
    from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopSummaryRef

    class Member(LoopSummaryRef):
        """中身を足さない ref の subclass（比較は登録した ref の比較: hash で置く位置に包まずに置く）。"""

    class Changed(Member):
        def __eq__(self, other):
            return Liar(1) if lying else 1

        __hash__ = LoopSummaryRef.__hash__

    base = _summary()
    fields = {name: getattr(base, name) for name in base.__dataclass_fields__}
    left_member, right_member = Member(**fields), Member(**fields)

    class First:
        def __eq__(self, other):
            if mutate == "class":
                object.__setattr__(left_member, "__class__", Changed)
                object.__setattr__(right_member, "__class__", Changed)
            else:
                Member.__eq__ = Changed.__eq__
            return True

        __hash__ = object.__hash__

    return (First(), frozenset({left_member})), (First(), frozenset({right_member}))


@pytest.mark.parametrize("mutate", ["class", "namespace"])
def test_a_hashed_member_changed_during_a_comparison_is_compared_like_the_twin(mutate):
    left, right = _member_scene(mutate, False)
    expected = _run(lambda: bool(left == right))
    left, right = _member_scene(mutate, True)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.equal(left, right))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))


def _read_copy_scene():
    log = []

    class Late:
        """最初の分類は不活性（`object` の比較）。先の callback が外の `__eq__` を足す。"""

    class First:
        def __eq__(self, other):
            Late.__eq__ = lambda self, other: (log.append(type(other[0]).__name__), True)[1]
            return True

        __hash__ = object.__hash__

    return log, (First(), Late()), (First(), [Liar(1)])


def test_a_leaf_reclassified_after_a_callback_never_receives_a_read_copy():
    """分類の memo は外の code の後に捨てる: 後の葉の class が外の code になったら、`exact_tree` の写し（基底型の値の
    list）を渡さない（双子の外の code は元の list を受け取る）。"""

    twin_log, left, right = _read_copy_scene()
    expected = _run(lambda: bool(left == right))
    assert twin_log == ["Liar"]
    log, left, right = _read_copy_scene()
    got = _run(lambda: live_values.equal(left, right))
    if got == ("undecidable",):
        assert log == []
    else:
        assert (got, log) == (expected, twin_log)


def _foreign_function():
    # 外の code（package の外の file 名）。method・`__call__`・staticmethod のどれとしても呼べる
    return eval(compile("lambda self=None, *args: 'FOREIGN'", "<foreign>", "eval"))  # noqa: S307


def _trusted_function():
    return lambda self: 1


def _fresh_package_type(build):
    """記録を使わない判定（同じ形の class を新しく作って判定する）。"""

    return live_values.package_type(build())


def test_package_type_follows_a_replaced_namespace_value_even_when_its_id_is_reused():
    """記録した判定は名前空間の値の identity を比べる。記録は値を生かすので、捨てた値の番地を別の値が再利用しても、
    記録したときと同じ状態には見えない。"""

    class Plain:
        """値の型（`__get__` を持たない: 信頼する値）。"""

    class Descriptor:
        __get__ = _foreign_function()  # 読むと外の code を呼ぶ値の型

    kind = type("Holder", (), {"__module__": __name__, "tag": None})
    reused = 0
    for _ in range(64):
        kind.tag = Plain()
        recorded = id(kind.__dict__["tag"])
        assert live_values.package_type(kind) is True
        live_values.package_type(type("Other", (), {}))  # 別の判定（判定の中だけの memo を捨てる）
        kind.tag = None
        kind.tag = Descriptor()
        reused += id(kind.__dict__["tag"]) == recorded
        expected = _fresh_package_type(lambda: type("Holder", (), {"__module__": __name__, "tag": Descriptor()}))
        assert expected is False
        assert live_values.package_type(kind) is expected
    # 記録が値を生かすので番地は再利用されない（生かさなければ再利用され、古い判定に見える）
    assert reused == 0


def test_a_judgement_that_reused_a_recorded_judgement_depends_on_what_that_one_read():
    """入れ子の型の判定を記録から使った判定は、その記録が依る class（値の型）にも依る。"""

    class Marker:
        pass

    class Inner:
        tag = Marker()

    assert live_values.package_type(Inner) is True  # 記録（依存: `Marker`）

    class Outer:
        inner = Inner

    assert live_values.package_type(Outer) is True  # `Inner` は記録から使う
    Marker.__get__ = _foreign_function()
    expected = _fresh_package_type(lambda: type("Outer", (), {"__module__": __name__, "inner": Inner}))
    assert expected is False
    assert live_values.package_type(Inner) is False
    assert live_values.package_type(Outer) is expected


def test_package_type_follows_classes_its_judgement_read():
    class Marker:
        pass

    class Holder:
        tag = Marker()

    assert live_values.package_type(Holder) is True
    Marker.__get__ = _foreign_function()  # 値の型が descriptor になる: `Holder().tag` が外の code を呼ぶ
    marker = Holder.__dict__["tag"]
    expected = _fresh_package_type(lambda: type("Holder", (), {"__module__": __name__, "tag": marker}))
    assert expected is False
    assert live_values.package_type(Holder) is expected

    class Inner:
        x = 1

    class Outer:
        inner = Inner

    assert live_values.package_type(Outer) is True
    Inner.f = _foreign_function()
    expected = _fresh_package_type(lambda: type("Outer", (), {"__module__": __name__, "inner": Inner}))
    assert expected is False
    assert live_values.package_type(Outer) is expected


def test_dataclass_facts_follow_the_field_table():
    import dataclasses

    @dataclasses.dataclass
    class Data:
        a: int
        b: int

    value = Data(1, 2)
    assert live_values.dataclass_field_names(value) == ("a", "b")
    del Data.__dataclass_fields__["b"]
    assert live_values.dataclass_field_names(value) == tuple(item.name for item in dataclasses.fields(value))


@pytest.mark.parametrize("change", ["compare_flag", "replaced_table"])
@pytest.mark.parametrize("when", ["before_first_use", "after_first_use"])
def test_the_owner_fixes_the_field_table_at_first_use(when, change):
    """owner の `==` / `hash` / 写し方は class ごとに最初の使用で固定した field の表で決まる（dataclass の生成した
    `__eq__` が class を作るときの表で固定されるのと同じ）。後で表（`Field.compare`・表そのもの）が変わっても、同じ ref
    の比べ方と hash は変わらない（dict に置いた ref を引ける）。固定より前の変更は、固定する表になる（その前に
    instance は無い: 2 つの表で比べた ref は無い）。"""

    import dataclasses

    from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_record

    @dataclasses.dataclass(frozen=True)
    @runtime_ref_record
    class Owned:
        a: int
        b: int

    def change_table():
        if change == "replaced_table":
            Owned.__dataclass_fields__ = {k: v for k, v in Owned.__dataclass_fields__.items() if k != "b"}
        else:
            Owned.__dataclass_fields__["b"].compare = False

    if when == "before_first_use":
        change_table()
        left, right = Owned(1, 2), Owned(1, 3)
        assert left == right and hash(left) == hash(right) == hash(left)  # 変えた後の表（`b` を比べない）で固定
        return
    held, other = Owned(1, 2), Owned(1, 3)
    table = {held: "value"}
    before = hash(held)
    assert held != other
    change_table()
    _churn()
    assert hash(held) == before and held in table and table[held] == "value"
    assert held != other and Owned(1, 2) == held and hash(Owned(1, 2)) == before


def test_the_owner_never_runs_metaclass_hooks_of_a_ref_class():
    import dataclasses

    from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_record

    log = []

    class Meta(type):
        def __getattribute__(cls, name):
            log.append(("getattribute", name))
            return type.__getattribute__(cls, name)

        def __eq__(cls, other):
            log.append(("eq",))
            return type.__eq__(cls, other)

        def __hash__(cls):
            log.append(("hash",))
            return type.__hash__(cls)

    @dataclasses.dataclass(frozen=True)
    @runtime_ref_record
    class Hooked(metaclass=Meta):
        a: int
        b: object = None

    log.clear()
    values = [Hooked(1, (2,)) for _ in range(3)]
    construction = list(log)
    log.clear()
    outcomes = [values[0] == values[1], hash(values[0]) == hash(values[1]), repr(values[2])]
    assert outcomes[:2] == [True, True]
    owner_calls = [entry for entry in log if entry != ("getattribute", "__call__")]
    assert owner_calls == [], owner_calls
    assert [entry for entry in construction if entry[0] != "getattribute" or entry[1] not in ("__call__",)] == []


def test_contains_never_looks_up_the_hash_of_a_wrapped_item_through_a_colliding_key():
    """`contains` の探す値（包み）は組み込みの `in` が hash する: その hash の引きも key の hook を呼ばない。"""

    kind = _keyed_class("__hash__", lambda self: 1)
    item = kind()
    HOOK_CALLS.clear()
    assert _run(lambda: item in {1}) == ("value", False) and HOOK_CALLS  # 双子の `in` は key の `__eq__` を呼ぶ
    for box in ({1}, frozenset({1}), {1: 2}):
        kind.unrelated += 1  # 前の引きが埋めた型の method cache を捨てる
        HOOK_CALLS.clear()
        assert _run(lambda: live_values.contains(box, item)) == ("undecidable",)
        assert dict(HOOK_CALLS) == {}


def test_the_owner_never_reads_the_truth_of_a_foreign_field_flag():
    """`Field.compare` / `repr` が組み込みの `bool` でない（真偽の読みが外の code を呼ぶ）表は読まない。"""

    import dataclasses

    from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_record

    @dataclasses.dataclass(frozen=True)
    @runtime_ref_record
    class Flagged:
        a: int
        b: int

    Flagged.__dataclass_fields__["b"].compare = Liar(1)  # 真偽の読みが数えられる
    HOOK_CALLS.clear()
    assert live_values.dataclass_field_specs(Flagged) is None
    assert _run(lambda: Flagged(1, 2)) == ("raises", "TypeError")
    assert dict(HOOK_CALLS) == {}


def test_opening_a_pair_scope_never_runs_identity_code_and_never_shares_a_ledger_by_a_lie():
    """pair の scope を開くときの identity の比較は値の code を呼ばない（台帳の lock を持ったまま・持たずに、どちらでも）。
    偽る `__eq__` を持つ別の identity は同じ pair にならない（台帳を共有しない: 失敗が pair の間で漏れない）。組み込みの
    scalar と tuple の identity は値で比べる（再入）。"""

    import threading

    from scripts.function_tracer_pcode.core import errors

    calls = []

    class Identity:
        def __eq__(self, other):
            calls.append("eq")
            return Liar(1)  # 偽る: 等しいと答える

        __hash__ = object.__hash__

    outcome = []

    def open_nested():
        with errors.pair_failure_scope(Identity(), "session") as outer:
            with errors.pair_failure_scope(Identity(), "session") as inner:
                outcome.append(inner is outer)
        with errors.pair_failure_scope(("pair", 1), "session") as outer:
            with errors.pair_failure_scope(("pair", 1), "session") as inner:
                outcome.append(inner is outer)

    HOOK_CALLS.clear()
    worker = threading.Thread(target=open_nested, daemon=True)
    worker.start()
    worker.join(10)
    assert not worker.is_alive(), "the ledger lock was re-entered by the same thread"
    assert outcome == [False, True]
    assert calls == [] and dict(HOOK_CALLS) == {}


def test_contains_is_undecided_when_the_hash_of_the_item_changes_the_copied_mapping():
    """`contains` の探す値の hash（外の code）が、写した dict の元を変えた: 写しを引き続けると、双子に無い外の code の
    呼び出し（写しにだけ残った key との比較）が起きる。hash の直後に判定しない（外の code の呼び出しは双子の先頭）。"""

    def scene():
        log = []
        box = {1: Callback(2, False)}  # 値が外の object: dict は写して値を包む

        class Item:
            def __hash__(self):
                log.append("hash")
                box.pop(1, None)  # 元から key を外す（写しには残る）
                return hash(1)

            def __eq__(self, other):
                log.append("eq")
                return other == 1

        return log, box, Item()

    twin_log, box, item = scene()
    expected = _run(lambda: item in box)
    assert (expected, twin_log) == (("value", False), ["hash"])
    log, box, item = scene()
    got = _run(lambda: live_values.contains(box, item))
    assert got in (expected, ("undecidable",))
    assert log == twin_log[: len(log)]


def test_an_instance_dict_with_a_colliding_key_is_not_read():
    """instance の `__dict__` に hash の衝突する組み込みでない `str` の key があれば、属性を読まない（Python の読みは
    その key の `__eq__` を呼ぶ: どの値か決めない）。"""

    class Holder:
        pass

    holder = Holder()
    holder.__dict__["plain"] = 1
    holder.__dict__[_CollidingName("other")] = 2
    HOOK_CALLS.clear()
    with pytest.raises(TypeError):
        live_values.attribute(holder, "other")
    with pytest.raises(TypeError):
        live_values.instance_state(holder, "plain")
    assert dict(HOOK_CALLS) == {}


@pytest.mark.parametrize("limit", list(range(600, 2100, 37)))
def test_a_runtime_ref_back_reference_terminates_whatever_the_stack_depth(limit):
    """root を指す runtime ref の見積もりは Python の stack の上限で止まる。上限がどこに当たっても（producer の中か
    walker の中か: 型の事実の確かめの深さで変わる）結果は同じ（`RecursionError` を値の不備にしない）。"""

    from scripts.function_tracer_pcode.core.expression import Expression
    from scripts.function_tracer_pcode.core.semantic_lifecycle import SemanticLifecycle

    previous = sys.getrecursionlimit()
    sys.setrecursionlimit(limit)
    try:
        root = Expression.binary_op("INT_ADD", Expression.parameter("a", 0, size=4), Expression.constant(1, size=4))
        object.__setattr__(root, "runtime_ref", (root, root.operands[0]))
        assert root.freeze() is root
        assert root.lifecycle is SemanticLifecycle.VALIDATED
    finally:
        sys.setrecursionlimit(previous)


def test_rewriting_a_class_namespace_keeps_its_keys_builtin_str():
    """前提（`live_values._STR_KEYED_NAMESPACES`）: 確かめた名前空間の key は書き換えの後も組み込みの `str`。class の
    属性の書き換えは名前を組み込みの `str` にして置く（この interpreter で確かめる: 前提が変われば落ちる）。"""

    class Named(str):
        def __hash__(self):
            HOOK_CALLS["Named.__hash__"] += 1
            return str.__hash__(self)

        def __eq__(self, other):
            HOOK_CALLS["Named.__eq__"] += 1
            return str.__eq__(self, other)

    class Holder:
        pass

    assert live_values.class_defines(Holder, "__getattribute__") is False  # 確かめた名前空間として覚える
    setattr(Holder, Named("__getattribute__"), lambda self, name: 0)
    type.__setattr__(Holder, Named("added"), 1)
    storage = live_values._unwrapped(type.__dict__["__dict__"].__get__(Holder))
    assert all(type(key) is str for key in dict.__iter__(storage))
    HOOK_CALLS.clear()
    assert live_values.class_defines(Holder, "__getattribute__") is True  # 後から足した hook も読む
    assert dict(HOOK_CALLS) == {}


#: 判定不能を投げ得る比べる側の契約の入口（呼び出しを包む広い捕捉は、先に判定不能を投げ直す）
_CONTRACT_ENTRIES = frozenset({
    "equal", "unequal", "less", "contains", "sorted_trees", "hash_tree", "same", "inert_key", "undecidable",
})


def test_broad_handlers_never_swallow_an_undecidable_comparison_of_the_contract():
    """広い捕捉（`except Exception` / `BaseException` / 裸の `except`）が比べる側の契約の入口の呼び出しを包むなら、同じ
    `try` の先の節で `UndecidableComparison` を投げ直す（判定不能を「一致しない」などの確定判定にしない）。"""

    import ast
    import pathlib

    root = pathlib.Path(__file__).resolve().parents[2]
    broad = {"Exception", "BaseException"}
    offenders = []
    for path in sorted(root.rglob("*.py")):
        if "tests" in path.relative_to(root).parts:
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"))
        # この module で契約の入口を指す名前（`live_values` から import した名前・`live_values` の module の別名の属性）
        entries, modules = set(), set()
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom) and (node.module or "").endswith("live_values"):
                entries |= {alias.asname or alias.name for alias in node.names if alias.name in _CONTRACT_ENTRIES}
            if isinstance(node, ast.ImportFrom) and (node.module or "").endswith(".core"):
                modules |= {alias.asname or alias.name for alias in node.names if alias.name == "live_values"}
        if path.name == "live_values.py":
            entries |= _CONTRACT_ENTRIES
        for node in ast.walk(tree):
            if not isinstance(node, ast.Try):
                continue
            calls = [call for statement in node.body for call in ast.walk(statement) if isinstance(call, ast.Call)]
            if not any(
                (isinstance(call.func, ast.Name) and call.func.id in entries)
                or (
                    isinstance(call.func, ast.Attribute) and call.func.attr in _CONTRACT_ENTRIES
                    and isinstance(call.func.value, ast.Name) and call.func.value.id in modules
                )
                for call in calls
            ):
                continue
            for handler in node.handlers:
                types = (
                    [] if handler.type is None
                    else handler.type.elts if isinstance(handler.type, ast.Tuple) else [handler.type]
                )
                names = {getattr(item, "id", getattr(item, "attr", None)) for item in types}
                if "UndecidableComparison" in names:
                    break  # 先の節が判定不能を扱う（分類は `UNDECIDABLE_HANDLERS`）
                if handler.type is None or names & broad:
                    offenders.append((path.name, node.lineno))
                    break
    assert offenders == []


# ---------------------------------------------------------------------------
# 第 8 回の 2 度目の独立レビュー（8c）の反例
# ---------------------------------------------------------------------------


def _eq_only_pair(lying):
    class EqOnly:
        """`__eq__` だけを持つ型（`!=` は `object.__ne__`: `__eq__` の戻り値の真偽を C が読んで反転する）。"""

        def __eq__(self, other):
            return Liar(0) if lying else 0

        __hash__ = object.__hash__

    return EqOnly(), EqOnly()


@pytest.mark.parametrize("shape", ["leaf", "tuple", "list"])
def test_a_derived_not_equal_never_reads_the_truth_of_a_foreign_eq(shape):
    wrap = {"leaf": lambda value: value, "tuple": lambda value: (value, 1), "list": lambda value: [value]}[shape]
    left, right = _eq_only_pair(False)
    expected = _run(lambda: bool(wrap(left) != wrap(right)))
    left, right = _eq_only_pair(True)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.unequal(wrap(left), wrap(right)))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))


def _keyed_dict_scene(lying, inner):
    class Foreign:
        def __eq__(self, other):
            return Liar(0) if lying else 0

        __hash__ = object.__hash__

    class Key:
        """不活性な object の key（exact な scalar でない: dict の key を写し直せない）。"""

    key = Key()
    return {key: inner(Foreign())}, {key: inner(Foreign())}


@pytest.mark.parametrize("inner", [
    lambda value: [value], lambda value: {1: value}, lambda value: [(value,)], lambda value: (value,),
    lambda value: [[value]],
], ids=["list", "dict", "tuple_in_list", "tuple", "nested_list"])
def test_values_of_a_dict_with_uncopyable_keys_are_never_compared_raw(inner):
    """key を写せない dict の値は包めない（組み込みの code が元のまま比べる）: 値の中の容器も全部辿り、外の code の葉が
    あれば判定しない（偽る戻り値の真偽を C に読ませない: 偽の「等しい」にしない）。"""

    left, right = _keyed_dict_scene(False, inner)
    expected = _run(lambda: bool(left == right))
    left, right = _keyed_dict_scene(True, inner)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.equal(left, right))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))


def test_a_judgement_depends_on_the_class_of_a_recorded_judgement_it_reused():
    """入れ子の型の判定を記録から使った判定は、その記録の key の型（の MRO）にも依る。"""

    class Inner:
        x = 1

    class Outer:
        inner = Inner

    assert live_values.package_type(Inner) is True
    assert live_values.package_type(Outer) is True  # `Inner` は記録から使う
    Inner.f = _foreign_function()
    expected = _fresh_package_type(lambda: type("Outer", (), {"__module__": __name__, "inner": Inner}))
    assert expected is False
    assert live_values.package_type(Outer) is expected


def test_exception_text_never_reads_an_instance_dict_through_a_colliding_key():
    kind = _keyed_class("__dict__", 5, (ValueError,))
    error = ValueError.__new__(kind, LiarStr("m"))
    HOOK_CALLS.clear()
    text = live_values.exception_text(error)
    assert dict(HOOK_CALLS) == {}
    assert text == "<unprintable Colliding object>"


def test_matching_a_parameter_never_turns_an_undecidable_comparison_into_a_mismatch():
    from scripts.function_tracer_pcode.core.runtime_refs.locations import LocationBaseRef

    def opaque():
        return {Callback(1, True)}  # 外の object の set: 比べると判定不能

    ref = LocationBaseRef(kind="parameter", parameter_index=0, owner_program_id=opaque(), owner_entry_offset=5)
    param = {"index": 0, "owner_program_id": opaque(), "owner_entry_offset": 5}
    assert _run(lambda: live_values.equal(param["owner_program_id"], ref.owner_program_id)) == ("undecidable",)
    assert _run(lambda: ref.matches_parameter(param)) == ("undecidable",)


def _reflected_ne_scene(lying):
    class Right:
        """`!=` は `object.__ne__`（反射で呼ばれ、型の `__eq__` の戻り値を C が真偽で読む）。"""

    class Left:
        def __ne__(self, other):
            Right.__eq__ = lambda self, other: Liar(0) if lying else 0  # 反射より前に外の `__eq__` を足す
            return NotImplemented

        __hash__ = object.__hash__

    return Left(), Right()


def test_a_derived_not_equal_called_after_foreign_code_in_the_same_expression_is_not_trusted():
    left, right = _reflected_ne_scene(False)
    expected = _run(lambda: bool(left != right))
    left, right = _reflected_ne_scene(True)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.unequal(left, right))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))


@pytest.mark.parametrize("make", [
    lambda: __import__("collections").OrderedDict({1: 2}).keys(),
    lambda: (__import__("collections").OrderedDict({1: 2}).items(), 1),
], ids=["odict_view", "odict_view_in_tuple"])
def test_a_value_exact_tree_refuses_with_a_plain_error_is_undecidable_for_every_entry(make):
    """`exact_tree` が素の `TypeError` で読まない値（`OrderedDict` の view: 反復が key を hash する）は、比べる側の契約の
    どの入口でも判定不能（素の `TypeError` は `decided_equal` を抜けて呼ぶ側の別の経路に入る）。"""

    with pytest.raises(TypeError):
        live_values.exact_tree(make())
    for operation in (
        lambda: live_values.equal(make(), make()),
        lambda: live_values.unequal(make(), make()),
        lambda: live_values.contains((make(),), make()),
        lambda: live_values.inert_key(make()),
        lambda: live_values.hash_tree(make()),
    ):
        assert _run(operation) == ("undecidable",)


def test_a_registered_comparison_called_by_a_set_probe_keeps_python_order_and_partner():
    """`contains` の探す値（包み）を set / dict の key の元の ref（包まない: hash で置く位置）と比べると、組み込みの code
    は元の ref の登録した比較に包みを渡す。登録した比較は包みを元の値に戻して比べ（双子と同じ相手）、包みの値が自分の型の
    subclass なら Python の subclass 優先の順を保つ。"""

    from scripts.function_tracer_pcode.core.runtime_refs import LocationBaseRef

    calls = []

    class Child(LocationBaseRef):
        def __eq__(self, other):
            calls.append("child")
            return True

        __hash__ = LocationBaseRef.__hash__

    class Other(LocationBaseRef):
        def __eq__(self, other):
            calls.append("other")
            return NotImplemented

        __hash__ = LocationBaseRef.__hash__

    for kind in (Child, Other):
        base = LocationBaseRef(kind="parameter", parameter_index=0)
        probe = kind(kind="parameter", parameter_index=0)
        assert hash(base) == hash(probe)
        for box in ({base}, frozenset({base}), {base: 1}):
            calls.clear()
            expected = (_run(lambda: probe in box), list(calls))
            calls.clear()
            got = (_run(lambda: live_values.contains(box, probe)), list(calls))
            assert got == expected == (("value", True), expected[1]), (kind.__name__, box)


def test_a_derived_not_equal_against_a_scalar_never_reads_the_truth_of_a_foreign_eq():
    left, _ = _eq_only_pair(False)
    expected = _run(lambda: bool(left != 1))
    left, _ = _eq_only_pair(True)
    HOOK_CALLS.clear()
    for operation in (lambda: live_values.unequal(left, 1), lambda: live_values.unequal(1, left)):
        assert _run(operation) in (expected, ("undecidable",))
    assert dict(HOOK_CALLS) == {}


def _ref_classes():
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    return sorted(corpus.BASES, key=lambda kind: kind.__qualname__)


@pytest.mark.parametrize("kind", _ref_classes(), ids=lambda kind: kind.__qualname__)
def test_production_refs_in_hashed_positions_are_compared_like_the_twin(kind):
    """回帰（第 8 回 8c）: 製品の ref（登録した `__eq__` と `__hash__`）は set / frozenset の要素・dict の key に包まずに
    置け、比べる側の契約は判定不能にせず双子と同じに答える（hash の分類を足したときに ref の `__hash__` を外の code に
    数えて、ref を持つ set を全部判定不能にした退行を捕まえる）。"""

    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    left, right = kind(**corpus.BASES[kind]()), kind(**corpus.BASES[kind]())
    assert live_values._leaf_trust(left) == live_values._CALLS
    for make in (lambda ref: {ref}, lambda ref: frozenset({ref}), lambda ref: {ref: 1}, lambda ref: (frozenset({ref}), 1)):
        expected = _run(lambda: bool(make(left) == make(right)))
        if expected[0] == "raises":  # hash できない ref（双子も作れない）
            assert _run(lambda: live_values.equal(make(left), make(right))) == expected
            return
        assert _run(lambda: live_values.equal(make(left), make(right))) == expected
        assert _run(lambda: live_values.equal(make(left), make(left))) == ("value", True)
    for box in ({left}, {left: 1}):
        assert _run(lambda: live_values.contains(box, right)) == _run(lambda: right in box)
        assert _run(lambda: live_values.contains(box, left)) == ("value", True)


# ---------------------------------------------------------------------------
# 第 8 回の 3 度目の独立レビュー（8d）の反例
# ---------------------------------------------------------------------------


def _explicit_ne_pair(lying, how):
    class Base:
        pass

    class Leaf(Base if how == "inherit" else object):
        __hash__ = object.__hash__

        def __eq__(self, other):
            return Liar(0) if lying else 0

    if how == "explicit":
        Leaf.__ne__ = object.__ne__  # `object.__ne__` そのものを置いても、`!=` は `__eq__` の戻り値の真偽を C が読む
    else:
        Base.__ne__ = object.__ne__
    return Leaf(), Leaf()


@pytest.mark.parametrize("how", ["explicit", "inherit"])
def test_an_explicit_object_ne_is_a_derived_not_equal(how):
    left, right = _explicit_ne_pair(False, how)
    expected = _run(lambda: bool(left != right))
    left, right = _explicit_ne_pair(True, how)
    HOOK_CALLS.clear()
    for operation in (lambda: live_values.unequal(left, right), lambda: live_values.unequal(left, 1)):
        assert _run(operation) in (expected, ("undecidable",))
    assert dict(HOOK_CALLS) == {}



@pytest.mark.parametrize("how", ["own", "inherit"])
def test_an_inherited_ne_is_the_types_own_not_equal(how):
    """MRO の上の class が持つ `__ne__` はその型の `!=` の実装（`_resolved_comparison` は MRO を `object` の手前まで辿る）:
    自分の class に `__ne__` を持たない型も、`!=` が `__eq__` の戻り値の真偽を C で読む型と数えない（判定する）。"""

    def ne(self, other):
        return True

    def eq(self, other):
        return False

    class Base:
        pass

    class Leaf(Base):
        __hash__ = object.__hash__

    (Leaf if how == "own" else Base).__ne__ = ne
    Leaf.__eq__ = eq
    assert live_values._resolved_comparison(Leaf, "__ne__") is ne
    for operation in (lambda: live_values.unequal(Leaf(), 1), lambda: live_values.unequal(1, Leaf())):
        assert _run(operation) != ("undecidable",)

@pytest.mark.parametrize("kind", _ref_classes(), ids=lambda kind: kind.__qualname__)
def test_production_refs_are_decided_by_not_equal(kind):
    """回帰（8d C6）: 製品の ref どうしの `!=`（登録した `__eq__` から `object.__ne__` が作る）は判定する（双子と同じ）。"""

    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    left, right = kind(**corpus.BASES[kind]()), kind(**corpus.BASES[kind]())
    assert _run(lambda: live_values.unequal(left, right)) == _run(lambda: bool(left != right))
    assert _run(lambda: live_values.unequal(left, left)) == ("value", False)


def test_a_registered_comparison_that_declines_after_foreign_code_is_undecidable():
    """登録した比較が外の code を呼んだ後に `NotImplemented` を返すと、反射で後から呼ばれる相手の実装は外の code が書き
    換えた型のもの: 判定しない（登録した比較は外の code の前に断る）。"""

    @live_values.trusted_comparison
    def late_decline(self, other):
        live_values.equal(Callback(1, False), Callback(1, False))  # 外の code（契約の包みを通る）
        return NotImplemented

    class Registered:
        __eq__ = late_decline
        __hash__ = object.__hash__

    assert _run(lambda: live_values.equal(Registered(), 1)) == ("undecidable",)


def test_a_subclass_sharing_the_field_table_compares_with_the_parents_fixed_table():
    """自分の表を持たない subclass は親と同じ表を使う: 親の最初の使用で固定した表で比べる（後で `Field` を書き換えても、
    親と子が別の表で比べない）。class の表を差し替えても、その class の固定は変わらない。"""

    import dataclasses

    from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_record

    @dataclasses.dataclass(frozen=True)
    @runtime_ref_record
    class Parent:
        a: int
        b: int

    first, second = Parent(1, 2), Parent(1, 3)
    assert first != second
    Parent.__dataclass_fields__["b"].compare = False

    class Child(Parent):
        pass

    assert Child(1, 2) != Child(1, 3) and first != second
    assert hash(Child(1, 2)) == hash(Parent(1, 2))


def test_ledger_classification_never_reads_a_foreign_class_attribute():
    """台帳の分類（限界・内部エラーの判定）と JSON の producer の失敗の判定は、例外の型そのもので読む（`isinstance` は
    型が違うと値の `__class__` を読む: 外の code が property にして偽れる）。"""

    from scripts.function_tracer_pcode.core import errors, json_encoding

    calls = []

    class Lying(RuntimeError):
        @property
        def __class__(self):
            calls.append("__class__")
            return errors.AnalysisLimitation

    class LyingRecursion(ValueError):
        @property
        def __class__(self):
            calls.append("__class__")
            return RecursionError

    error = Lying("x")
    assert errors.classify_failure_kind(error) == errors.classify_failure_kind(RuntimeError("x"))
    walker = json_encoding._Walk.__new__(json_encoding._Walk)
    walker.reject = lambda message: (_ for _ in ()).throw(ValueError("rejected: " + message))
    with pytest.raises(ValueError, match="rejected"):
        walker.producer_failed(LyingRecursion("x"))
    assert calls == []


# ---------------------------------------------------------------------------
# 第 8 回の 4 度目の独立レビュー（8e）の反例
# ---------------------------------------------------------------------------


def _enum_scene(lying):
    from enum import Enum

    class Color(Enum):
        RED = 1

    class Plain:
        pass

    held = Plain()

    class Name(str):
        def __hash__(self):
            Plain.__eq__ = lambda self, other: Liar(0) if lying else 0  # 名前の hash（外の code）が class を書き換える
            return object.__hash__(held)

    object.__setattr__(Color.RED, "_name_", Name("RED"))
    return {held}, Color.RED


def test_an_enum_whose_name_is_not_a_builtin_str_is_not_inert():
    """`Enum.__hash__` は `hash(self._name_)`: 名前が `str` の subclass なら、その hash（外の code）が組み込みの code の
    中で走る。そういう member は不活性でない（名前は値ごとに使う時点で確かめる）。"""

    box, item = _enum_scene(False)
    expected = _run(lambda: item in box)
    box, item = _enum_scene(True)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.contains(box, item))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))
    assert live_values._leaf_trust(item) != live_values._TRUSTED


def test_an_enum_with_its_own_name_stays_inert():
    """回帰: 普通の enum member（名前は組み込みの `str`）は不活性のまま（比べても hash しても Python の code を呼ばない）。"""

    from enum import Enum

    class Color(Enum):
        RED = 1

    assert live_values._leaf_trust(Color.RED) == live_values._TRUSTED
    assert live_values.equal({Color.RED: 1}, {Color.RED: 1}) is True


def _buffer_scene(lying):
    class Plain:
        def __buffer__(self, flags):
            Plain.__eq__ = lambda self, other: Liar(0) if lying else 0  # `bytearray` の `==` が読む buffer（外の code）
            raise TypeError("no buffer")

    return Plain()


@pytest.mark.parametrize("operation", ["equal", "unequal", "contains"])
def test_a_bytearray_never_compares_against_foreign_buffer_code_unwrapped(operation):
    run = {
        "equal": lambda value, f: f((bytearray(),), (value,)),
        "unequal": lambda value, f: f((bytearray(),), (value,)),
        "contains": lambda value, f: f([bytearray()], value),
    }[operation]
    twin = {"equal": lambda a, b: bool(a == b), "unequal": lambda a, b: bool(a != b), "contains": lambda a, b: b in a}
    contract = {"equal": live_values.equal, "unequal": live_values.unequal, "contains": live_values.contains}
    expected = _run(lambda: run(_buffer_scene(False), twin[operation]))
    HOOK_CALLS.clear()
    got = _run(lambda: run(_buffer_scene(True), contract[operation]))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))


def test_the_registered_comparison_wrapper_never_runs_a_metaclass_subclass_check():
    import dataclasses

    from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_record

    calls = []

    @dataclasses.dataclass(frozen=True)
    @runtime_ref_record
    class Record:
        a: int

    class Meta(type):
        def __subclasscheck__(cls, sub):
            calls.append("subclasscheck")
            return type.__subclasscheck__(cls, sub)

    class Hooked(Record, metaclass=Meta):
        pass

    member = Hooked(1)

    class Probe:
        def __hash__(self):
            return hash(member)

        def __eq__(self, other):
            return False

    calls.clear()
    expected = _run(lambda: Probe() in {member})
    twin_calls = list(calls)
    calls.clear()
    got = _run(lambda: live_values.contains({member}, Probe()))
    assert calls == [] == twin_calls
    assert got in (expected, ("undecidable",))


def _in_place_scene(lying):
    """key を写せない dict の値の list（組み込みの code が元のまま比べる）へ、登録した比較の中の外の code が分類して
    いない葉を足す。"""

    result = (lambda value: Liar(int(value))) if lying else (lambda value: int(value))

    class Key:
        pass

    key = Key()
    left, right = [], []

    class Late:
        __hash__ = object.__hash__

        def __eq__(self, other):
            return result(False)  # 偽る側は 0 を真と読ませる

    class Foreign:
        __hash__ = object.__hash__

        def __eq__(self, other):
            left.append(Late())
            right.append(Late())
            return result(True)

    @live_values.trusted_comparison
    def registered(self, other):
        return live_values.equal(Foreign(), Foreign())

    class Registered:
        __eq__ = registered
        __hash__ = object.__hash__

    left.append(Registered())
    right.append(Registered())
    return {key: left}, {key: right}


def test_a_container_compared_in_place_is_watched_while_foreign_code_runs():
    left, right = _in_place_scene(False)
    expected = _run(lambda: bool(left == right))
    left, right = _in_place_scene(True)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.equal(left, right))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))


# ---------------------------------------------------------------------------
# 第 8 回の 5 度目の独立レビュー（8f: 信頼の判定と cache の全数の監査）の反例
# ---------------------------------------------------------------------------


def _renamed_builtin_scene(lying):
    class Renamed:
        __eq__ = object.__getattribute__  # 組み込みの実装を別の名前の下に置く: `==` が属性の読み（property）になる
        __hash__ = object.__hash__

        @property
        def foo(self):
            return Liar(1) if lying else True

    return Renamed()


def test_a_builtin_implementation_under_another_dunder_name_is_not_inert():
    value = _renamed_builtin_scene(False)
    expected = _run(lambda: bool((value,) == ("foo",)))
    value = _renamed_builtin_scene(True)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.equal((value,), ("foo",)))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))
    assert live_values._leaf_trust(value) != live_values._TRUSTED


def _enum_lookup_scene(lying):
    import enum

    log = []

    class Key:
        pass

    held = Key()

    class Color(enum.Enum):
        RED = 1

        def __getattribute__(self, name):  # `Enum.__hash__` の `self._name_` の読みを外の code にする
            if name == "_name_":
                log.append("getattribute")
                Key.__eq__ = lambda self, other: Liar(1) if lying else True
                return hash(held)
            return object.__getattribute__(self, name)

    return {held}, Color.RED, log


def test_an_enum_hash_read_through_a_foreign_lookup_is_not_inert():
    box, item, twin_log = _enum_lookup_scene(False)
    expected = _run(lambda: item in box)
    box, item, log = _enum_lookup_scene(True)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.contains(box, item))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))
    assert log == twin_log[: len(log)]


def _ref_descriptor_scene(lying):
    import dataclasses

    from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_record

    @dataclasses.dataclass(frozen=True)
    @runtime_ref_record
    class Record:
        a: int
        b: int

    armed = []

    class Key:
        pass

    # ref の subclass の field の descriptor（package の外の code: 登録した比較の中で読まれ、class を書き換えて戻す）
    source = (
        "class Field:\n"
        "    def __set_name__(self, owner, name):\n"
        "        self.name = '_' + name\n"
        "    def __set__(self, obj, value):\n"
        "        obj.__dict__[self.name] = value\n"
        "    def __get__(self, obj, owner=None):\n"
        "        if obj is None:\n"
        "            return self\n"
        "        if armed:\n"
        "            if lying:\n"
        "                class Restore(int):\n"
        "                    def __bool__(self):\n"
        "                        del Key.__eq__\n"
        "                        return False\n"
        "                Key.__eq__ = lambda self, other: Restore(1)\n"
        "            else:\n"
        "                Key.__eq__ = lambda self, other: True\n"
        "        return obj.__dict__[self.name]\n"
    )
    namespace = {"armed": armed, "lying": lying, "Key": Key}
    exec(compile(source, "<foreign>", "exec"), namespace)  # noqa: S102 - 外の code（package の外の file 名）

    class Sub(Record):
        a = namespace["Field"]()

    left = {Record(0, 0): (Sub(1, 2), Key())}
    right = {Record(0, 0): (Sub(1, 2), Key())}
    armed.append(True)
    return left, right


def test_a_ref_subclass_whose_fields_run_foreign_code_is_not_a_registered_comparison():
    """登録した比較（ref の `==`）を継承しても、field を外の code の descriptor にした subclass は登録した比較の分類に
    ならない（実装が読む `self.a` が外の code: その code が class を書き換えて後で戻しても、偽の答えにしない）。"""

    left, right = _ref_descriptor_scene(False)
    expected = _run(lambda: bool(left == right))
    left, right = _ref_descriptor_scene(True)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.equal(left, right))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))
    member = next(iter(left.values()))[0]
    assert live_values._leaf_trust(member) == live_values._FOREIGN


def test_a_flag_member_without_a_name_stays_inert():
    """回帰（8g）: `Flag` の 0・合成の member は名前が `None`（`hash(None)` は自己完結）: 不活性のまま。"""

    import enum

    class Bits(enum.Flag):
        A = 1
        B = 2

    for member in (Bits(0), Bits.A | Bits.B, Bits.A):
        assert live_values._leaf_trust(member) == live_values._TRUSTED
        assert live_values.contains({member}, member) is True
        assert live_values.equal({member: 1}, {member: 1}) is True


def test_registered_comparisons_in_a_large_set_stay_linear():
    """回帰（8g）: 登録した比較を要素ごとに呼ぶ set / dict の比較は、要素ごとに進行中の比較の容器を読み直さない。
    作業量で数える（時間でなく `_CopyFrame._read` の呼び出しの数）。"""

    from scripts.function_tracer_pcode.core.runtime_refs.pcode import PcodeOpRef

    counts = []
    original = live_values._CopyFrame._read

    def counted(self):
        counts.append(1)
        return original(self)

    for size in (100, 400):
        left = {PcodeOpRef(address_offset=index) for index in range(size)}
        right = {PcodeOpRef(address_offset=index) for index in range(size)}
        counts.clear()
        live_values._CopyFrame._read = counted
        try:
            assert live_values.equal((left, [1]), (right, [1])) is True
        finally:
            live_values._CopyFrame._read = original
        assert len(counts) <= 4, (size, len(counts))


def test_lookup_facts_follow_the_names_they_read():
    """名前の引きだけで決まる型の事実（`builtin_hashed_scalar`・`_dict_holder`・組み込みの振る舞い）の記録は、計算が
    引いた名前を引くたびに確かめる: 後から足した・差し替えた・消した名前、`__bases__` の書き換えで古い記録を使わない。"""

    class Text(str):
        pass

    class Other(str):
        def __eq__(self, other):
            return True

        __hash__ = str.__hash__

    value = Text("x")
    assert live_values.builtin_hashed_scalar(value) is True
    Text.__eq__ = lambda self, other: True  # 足した名前
    assert live_values.builtin_hashed_scalar(value) is False
    del Text.__eq__  # 消した名前
    assert live_values.builtin_hashed_scalar(value) is True

    class Base(str):
        pass

    class Leaf(Base):
        pass

    leaf = Leaf("y")
    assert live_values.builtin_hashed_scalar(leaf) is True
    Leaf.__bases__ = (Other,)  # MRO の書き換え
    assert live_values.builtin_hashed_scalar(leaf) is False

    class Holder:
        pass

    holder = Holder()
    holder.field = 1
    assert live_values.instance_state(holder, "field") == 1
    Holder.__dict__  # noqa: B018 - 読むだけ
    Holder.field = property(lambda self: 2)  # 名前空間を書き換えても instance の状態の読みは同じ規則で読み直す
    assert live_values.instance_state(holder, "field") == 1

    class Seq(list):
        pass

    assert live_values.builtin_sequence(Seq([1])) is True
    Seq.__iter__ = lambda self: iter(())  # 足した名前: 組み込みの振る舞いでない
    assert live_values.builtin_sequence(Seq([1])) is False


def _uncopied_list_scene(lying):
    """写さなかった list（要素が exact な scalar だけ: 組み込みの code が元のまま比べる）へ、先の外の code が分類して
    いない葉を足す。"""

    left_list, right_list = [1], [1]

    class Late:
        __hash__ = object.__hash__

        def __eq__(self, other):
            return Liar(0) if lying else 0

    class First:
        __hash__ = object.__hash__

        def __eq__(self, other):
            left_list.append(Late())
            right_list.append(Late())
            return True

    return (First(), left_list), (First(), right_list)


def test_a_list_compared_in_place_is_watched_even_when_it_was_not_copied():
    left, right = _uncopied_list_scene(False)
    expected = _run(lambda: bool(left == right))
    left, right = _uncopied_list_scene(True)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.equal(left, right))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))


def test_a_fact_computed_over_an_undecidable_namespace_is_not_recorded():
    """組み込みでない key の名前空間に当たった計算（答えは「確かめられない」）は記録しない: その key は `delattr` で後から
    消せる（消した後は確かめられる）。"""

    class Name(str):
        def __hash__(self):
            return str.__hash__(self)

        def __eq__(self, other):
            return str.__eq__(self, other)

    kind = type("Keyed", (int,), {Name("zz"): 1})
    value = kind(1)
    assert live_values.builtin_hashed_scalar(value) is False
    delattr(kind, "zz")
    assert live_values.builtin_hashed_scalar(value) is True


def test_a_judgement_depending_on_a_class_sees_a_replaced_value_there():
    """依存の class（判定が読んだ、key の型の MRO の外の class: 入れ子の型）の名前空間の、既にある名前の値を外の code に
    差し替えると、記録した判定を使わない（名前の集合は同じ: 値の identity で確かめる）。"""

    class Inner:
        f = _trusted_function()

    class Outer:
        inner = Inner

    assert live_values.package_type(Outer) is True
    Inner.f = _foreign_function()
    expected = _fresh_package_type(lambda: type("Outer", (), {"__module__": __name__, "inner": Inner}))
    assert expected is False
    assert live_values.package_type(Outer) is expected


def _enum_memo_scene(lying):
    from enum import Enum

    class Color(Enum):
        RED = 1
        BLUE = 2

    class Left(Enum):
        X = 1

    class Right(Enum):
        X = 1  # 名前が同じ: hash が等しい別の object（比べると `Left.__eq__` を呼ぶ）

    armed = []

    class Name(str):
        def __hash__(self):
            if armed:
                Left.__eq__ = lambda self, other: Liar(0) if lying else 0  # 名前の hash（外の code）が class を書き換える
            return str.__hash__(self)

    object.__setattr__(Color.BLUE, "_name_", Name("BLUE"))
    box = {(Right.X, Color.BLUE, Color.RED)}
    armed.append(True)
    return box, (Left.X, Color.BLUE, Color.RED)


def test_members_of_one_enum_are_classified_one_by_one():
    """同じ enum の member でも、名前が組み込みの `str` でない member は不活性でない: 型ごとに分類を覚えない（先に分類した
    普通の member の分類を使い回さない）。"""

    box, item = _enum_memo_scene(False)
    expected = _run(lambda: item in box)
    box, item = _enum_memo_scene(True)
    HOOK_CALLS.clear()
    got = _run(lambda: live_values.contains(box, item))
    assert dict(HOOK_CALLS) == {}
    assert got in (expected, ("undecidable",))


# ---------------------------------------------------------------------------
# 第 9 回: 判定が読んだ値の状態（型・組み込みの descriptor の中身）と、NaN の hash
# ---------------------------------------------------------------------------


def test_package_type_follows_the_class_of_a_namespace_value():
    """反例（第 9 回 P1）: 名前空間の値の identity が同じでも、その `__class__` を外の descriptor の型にすれば、記録した
    判定を使わない（判定は値の型を読む）。"""

    class Plain:
        pass

    class Descriptor:
        __get__ = _foreign_function()

    class Holder:
        tag = Plain()

    assert live_values.package_type(Holder) is True
    Holder.__dict__["tag"].__class__ = Descriptor
    expected = _fresh_package_type(lambda: type("Holder", (), {"__module__": __name__, "tag": Holder.__dict__["tag"]}))
    assert expected is False
    assert live_values.package_type(Holder) is expected


@pytest.mark.parametrize("kind", ["property", "property_subclass", "staticmethod", "classmethod"])
def test_package_type_follows_a_descriptor_reinitialised_in_place(kind):
    """組み込みの descriptor（`property` / `staticmethod` / `classmethod`）は `__init__` を呼び直すと中身を差し替えられる
    （identity は同じ）: 記録した判定はその中身も確かめる。"""

    def trusted(*args):
        return 1

    make = {
        "property": property,
        "property_subclass": live_values.readable_property,  # package の property の subclass（heap type）
        "staticmethod": staticmethod,
        "classmethod": classmethod,
    }[kind]

    class Holder:
        attr = make(trusted)

    assert live_values.package_type(Holder) is True
    descriptor = Holder.__dict__["attr"]
    type(descriptor).__init__(descriptor, _foreign_function())
    expected = _fresh_package_type(lambda: type("Holder", (), {"__module__": __name__, "attr": descriptor}))
    assert expected is False
    assert live_values.package_type(Holder) is expected


def test_a_ref_field_read_through_a_descriptor_swapped_in_after_judgement_is_not_trusted():
    """反例（第 9 回 P1 の end-to-end）: ref の class の属性の値の class を判定の後で外の descriptor にしても、ref は登録した
    比較の分類のまま比べられない（記録した `package_type` を使わない）。"""

    from scripts.function_tracer_pcode.core.runtime_refs.locations import AddressValueRef

    left, right = AddressValueRef(address_offset=1), AddressValueRef(address_offset=2)
    held = object.__new__(type("Plain", (), {"__module__": __name__}))
    original = AddressValueRef.__dict__.get("symbol_name", _MISSING_ATTR)
    try:
        type.__setattr__(AddressValueRef, "probe_value", held)
        assert live_values._leaf_trust(left) == live_values._CALLS  # 判定を記録する
        namespace = {}
        exec(compile("class Field:\n    def __get__(self, obj, owner=None):\n        return 1\n", "<foreign>", "exec"), namespace)
        held.__class__ = namespace["Field"]
        assert live_values._leaf_trust(left) == live_values._FOREIGN
        HOOK_CALLS.clear()
        assert _run(lambda: live_values.equal({1: left}, {1: right})) in (("value", False), ("undecidable",))
        assert dict(HOOK_CALLS) == {}
    finally:
        type.__delattr__(AddressValueRef, "probe_value")
        assert AddressValueRef.__dict__.get("symbol_name", _MISSING_ATTR) is original


_MISSING_ATTR = object()


class _NanPartner:
    """float の NaN `n` と等しく、hash は `hash(n)` の外の object（main の dataclass の `==` / hash と整合する）。"""

    def __init__(self, nan):
        self.nan = nan

    def __eq__(self, other):
        return other is self.nan or other is self

    def __hash__(self):
        return hash(self.nan)


def test_equal_refs_with_a_nan_and_a_value_equal_to_it_hash_alike():
    """反例（第 9 回 P2）: `a == b` が真なら同じ hash（dict / set で同じ値）。NaN の hash を固定の印にすると、NaN と
    等しいと言う外の object（hash は `hash(n)`）を持つ ref と食い違う。"""

    from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopSummaryRef
    from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus

    nan = float("nan")
    base = corpus.BASES[LoopSummaryRef]()  # 他の field は同じ object を共有する
    left = LoopSummaryRef(**{**base, "start_expr": nan})
    right = LoopSummaryRef(**{**base, "start_expr": _NanPartner(nan)})
    assert _run(lambda: left == right) == ("value", True)  # main の dataclass の `==` と同じ（`_NanPartner` が等しいと言う）
    assert hash(left) == hash(right)
    assert right in {left: "value"} and left in {right: "value"}
    assert live_values.equal((nan, 1), (_NanPartner(nan), 1)) is True
    assert live_values.hash_tree((nan, 1)) == live_values.hash_tree((_NanPartner(nan), 1))


def test_nan_leaves_hash_by_the_leaf_as_held():
    """NaN の葉の hash は持っている葉の identity（exact な float はその hash、scalar の subclass の NaN は基底型の slot の
    hash）: 呼び出しの間で同じで、読みが作る写しの identity に依らない。"""

    held = LiarFloat(float("nan"))
    value = (held, 1)
    first = live_values.hash_tree(value)
    _churn()
    assert live_values.hash_tree(value) == first == live_values.hash_tree((held, 1))
    assert first == hash((float.__hash__(held), 1)) or first == live_values.hash_tree(value)
    nan = float("nan")
    assert live_values.hash_tree((nan, 1)) == hash((nan, 1))


def test_a_nan_leaf_reads_to_the_same_object_every_time():
    """同じ元の NaN の葉（scalar の subclass）は、いつ読んでも同じ写し（`exact_tree`・key・比べる・hash で同じ振る舞い:
    双子は 1 つの写しを持つ）。別の元の葉は別の写し。元の葉が消えると記録も消える。"""

    held = LiarFloat(float("nan"))
    first = live_values.exact_tree((held, 1))
    _churn()
    second = live_values.exact_tree((held, 1))
    assert first[0] is second[0] and type(first[0]) is float
    assert live_values.inert_key((held,)) == live_values.inert_key((held,))  # 同じ object の NaN: identity で等しい
    table = {live_values.inert_key((held,)): "value"}
    assert table[live_values.inert_key((held,))] == "value"
    other = LiarFloat(float("nan"))
    assert live_values.exact_tree(other) is not live_values.exact_tree(held)
    assert live_values.equal((held,), (held,)) is True and live_values.equal((held,), (other,)) is False
    assert live_values.hash_tree((held,)) == live_values.hash_tree((held,))
    count = len(live_values._NAN_COPIES)
    del held, first, second, table
    _churn()
    assert len(live_values._NAN_COPIES) < count


def test_json_protocols_follow_a_replaced_method():
    """JSON の protocol の記録（`_record_protocol`）は引くたびに引いた名前を確かめる: 型の method を別の package の関数に
    差し替えれば、差し替えた関数を使う。"""

    from scripts.function_tracer_pcode.core import json_encoding

    def first(self):
        return iter(())

    def second(self):
        return iter(())

    kind = type("Record", (), {"__module__": __name__, "json_items": first})
    assert json_encoding._record_protocol(kind, "json_items") is first
    kind.json_items = second
    assert json_encoding._record_protocol(kind, "json_items") is second


def test_dataclass_field_names_follow_the_class_of_a_field():
    """dataclass の field の表の `Field` は heap type: `__class__` を変えた `Field` は `dataclasses.fields` と同じ規則で
    扱う（記録した名前を使わない）。"""

    import dataclasses

    @dataclasses.dataclass
    class Data:
        a: int
        b: int

    value = Data(1, 2)
    assert live_values.dataclass_field_names(value) == ("a", "b")

    class Other(dataclasses.Field):
        __slots__ = ()

    Data.__dataclass_fields__["b"].__class__ = Other
    assert live_values.dataclass_field_names(value) == live_values._dataclass_field_names(Data)


def test_package_type_follows_a_dynamic_class_attribute_accessor():
    import types

    def trusted(self):
        return 1

    class Holder:
        attr = types.DynamicClassAttribute(trusted)

    assert live_values.package_type(Holder) is True
    Holder.__dict__["attr"].fget = _foreign_function()  # instance の属性: identity は同じ
    expected = _fresh_package_type(lambda: type("Holder", (), {"__module__": __name__, "attr": Holder.__dict__["attr"]}))
    assert live_values.package_type(Holder) is expected


def test_a_class_whose_metatype_is_type_cannot_rewrite_its_dict_entry():
    """前提（`_fixed_dict_entries` / `_DICT_HOLDERS`）: metaclass が `type` の class の名前空間の `__dict__` の entry は
    作った後に書けも消せもせず、class の metaclass も `type` から変えられない（CPython の振る舞い: 3.10 / 3.12）。"""

    class Base:
        pass

    class Kind(Base):
        pass

    before = (dict(Base.__dict__).get("__dict__"), dict(Kind.__dict__).get("__dict__", live_values._MISSING_DUNDER))
    for klass in (Base, Kind):
        for operation in (
            lambda: setattr(klass, "__dict__", property(lambda self: {})),
            lambda: type.__setattr__(klass, "__dict__", None),
            lambda: delattr(klass, "__dict__"),
            lambda: type.__delattr__(klass, "__dict__"),
        ):
            with pytest.raises(AttributeError):
                operation()

    class Meta(type):
        pass

    with pytest.raises(TypeError):
        Kind.__class__ = Meta
    assert type(Kind) is type
    after = (dict(Base.__dict__).get("__dict__"), dict(Kind.__dict__).get("__dict__", live_values._MISSING_DUNDER))
    assert after[0] is before[0] and after[1] is before[1]
    assert live_values._fixed_dict_entries(live_values._TYPE_MRO.__get__(Kind))


def test_instance_state_follows_a_base_that_holds_the_dict_after_bases_change():
    """`_dict_holder` の記録は MRO の tuple が同じ間だけ: `__bases__` を書き換えて `__dict__` を持つ class が変われば、
    読む descriptor も今の MRO のものになる（記録した descriptor の class が MRO に無いまま読まない）。"""

    class First:
        pass

    class Second:
        pass

    class Kind(First):
        pass

    value = Kind()
    value.probe = "kept"
    assert live_values.instance_state(value, "probe") == "kept"
    Kind.__bases__ = (Second,)
    assert live_values._TYPE_MRO.__get__(Kind) == (Kind, Second, object)
    assert live_values.instance_state(value, "probe") == "kept"
    assert live_values._dict_holder(Kind).__objclass__ in live_values._TYPE_MRO.__get__(Kind)


def test_instance_state_follows_a_dict_entry_written_through_a_metaclass():
    """metaclass が `__dict__` を descriptor でない値で持つ class は、`setattr` が class の名前空間へ `__dict__` を書く:
    記録しない（`_fixed_dict_entries` が偽）。読みは今の名前空間に従う（書いた後は組み込みの descriptor が無い）。"""

    Meta = type("Meta", (type,), {"__dict__": None})
    Kind = Meta("Kind", (), {})
    value = Kind()
    object.__setattr__(value, "probe", "kept")
    assert not live_values._fixed_dict_entries(live_values._TYPE_MRO.__get__(Kind))
    assert live_values.instance_state(value, "probe") == "kept"
    setattr(Kind, "__dict__", property(lambda self: {"probe": "fake"}))
    assert "__dict__" in live_values._TYPE_DICT.__get__(Kind)
    assert live_values._dict_holder_of(Kind) is None
    assert live_values.instance_state(value, "probe", "absent") == "absent"


def test_a_lookup_fact_used_inside_another_passes_its_reads_on():
    """`lookup_fact` の記録を別の `lookup_fact` の計算の途中で使えば、使った記録の読みは外の記録の読みでもある: 内の
    計算が読んだ名前を書き換えれば、外の記録も計算し直す（外が古い答えを返さない）。"""

    inner_table = live_values.LookupFactTable()
    outer_table = live_values.LookupFactTable()
    kind = type("Kind", (), {"marker": "first"})

    def inner(klass):
        return live_values.type_attribute(klass, "marker")

    def outer(klass):
        return ("outer", live_values.lookup_fact(inner_table, klass, inner, klass))

    assert live_values.lookup_fact(inner_table, kind, inner, kind) == "first"  # 内の記録を先に作る（外の計算では使うだけ）
    assert live_values.lookup_fact(outer_table, kind, outer, kind) == ("outer", "first")
    kind.marker = "second"
    assert live_values.lookup_fact(outer_table, kind, outer, kind) == ("outer", "second")
    assert live_values.lookup_fact(inner_table, kind, inner, kind) == "second"


def test_type_attribute_follows_bases_and_namespace_changes_through_the_mro_record():
    """`_PLAIN_MROS` の記録は MRO の tuple が同じ間だけ・名前空間の storage を直接引く: 名前空間の書き換えと
    `__bases__` の書き換えのどちらにも `inspect.getattr_static` と同じ値を返す。"""

    import inspect

    class First:
        marker = "first"

    class Second:
        marker = "second"

    class Kind(First):
        pass

    def expected(name):
        return inspect.getattr_static(Kind, name, None)

    for _ in range(2):  # 2 回目は記録から引く
        assert live_values.type_attribute(Kind, "marker") == expected("marker") == "first"
    First.marker = "rewritten"
    assert live_values.type_attribute(Kind, "marker") == expected("marker") == "rewritten"
    Kind.__bases__ = (Second,)
    assert live_values.type_attribute(Kind, "marker") == expected("marker") == "second"
    Kind.marker = "own"
    assert live_values.type_attribute(Kind, "marker") == expected("marker") == "own"
    del Kind.marker
    assert live_values.type_attribute(Kind, "marker") == expected("marker") == "second"
    assert live_values.type_attribute(Kind, "__repr__") is expected("__repr__") is object.__dict__["__repr__"]


def test_json_protocols_are_judged_again_by_the_next_walk():
    """walk の中の protocol の記録（監査済みの区間の記録）は最も外の walk の間だけ: walk が終われば捨てる
    （例外で終わっても）。次の walk は書き換えた型を今の状態で判定する（外の code が package の型の名前空間へ foreign な
    関数を入れれば、その型を record として辿らない）。"""

    from scripts.function_tracer_pcode.core import json_encoding
    from scripts.function_tracer_pcode.core.json_encoding import JsonValueRejected, RESULT_JSON_POLICY

    def items(self):
        yield "a", 1

    kind = type("Record", (), {"__module__": __name__, "json_items": items})
    assert RESULT_JSON_POLICY.prepare(kind()).value() == {"a": 1}
    assert live_values.region_cache(json_encoding._PROTOCOL_SLOT) is None
    foreign = eval("lambda self: iter(())", {})  # package の外の code（`<string>`）
    kind.json_items = foreign
    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare(kind()).value()
    assert live_values.region_cache(json_encoding._PROTOCOL_SLOT) is None
    kind.json_items = items
    assert RESULT_JSON_POLICY.prepare([kind(), kind()]).value() == [{"a": 1}, {"a": 1}]
    assert live_values.region_cache(json_encoding._PROTOCOL_SLOT) is None


def test_a_walk_forgets_protocols_after_running_code_outside_the_audited_roots():
    """walk の protocol の記録は、J19 の監査の root でない package の code（値の中の package の generator・identity key の
    method）を進めた後には使わない: その code が型を書き換えれば、walk の残りは書き換えた型を今の状態で判定する。"""

    from scripts.function_tracer_pcode.core import json_encoding
    from scripts.function_tracer_pcode.core.json_encoding import JsonValueRejected, RESULT_JSON_POLICY

    def items(self):
        yield "a", 1

    kind = type("Record", (), {"__module__": __name__, "json_items": items})
    foreign = eval("lambda self: iter(())", {})

    def rewriting():
        yield kind()
        kind.json_items = foreign  # 監査の root でない package の code が型を書き換える
        yield kind()

    with pytest.raises(JsonValueRejected):
        RESULT_JSON_POLICY.prepare([kind(), rewriting()]).value()
    assert live_values.region_cache(json_encoding._PROTOCOL_SLOT) is None
    kind.json_items = items

    class Keyed:
        def stable_key(self):
            kind.json_items = foreign
            return ("keyed",)

    # identity key の method（#194 の owner の code）を呼んだ後は記録を捨てる
    try:
        with live_values.audited_region():
            assert json_encoding._record_protocols(kind)[0] is items
            assert json_encoding.identity_key_of(Keyed()) == (True, ("keyed",))
            assert json_encoding._record_protocols(kind)[0] is None
    finally:
        kind.json_items = items


def test_protocol_scopes_are_opened_only_by_audited_roots():
    """`live_values.audited_region`（監査済みの区間: 型の protocol の判定を区間の間 1 度にする）を開ける場所は、walk と J19 の監査の
    entry root の本体だけ（scope の中で走る package の code は監査が live な値に許した操作だけをする: 記録の前提）。
    新しい場所で開けるなら、その関数を監査の root に足す。"""

    import ast
    import pathlib

    from scripts.function_tracer_pcode.tests.unit import _live_flow_audit as audit

    allowed = {(module, qual) for module, qual, _params in audit.ENTRY_ROOTS}
    allowed.add(("core.json_encoding", "_Walk.run"))
    root = pathlib.Path(__file__).resolve().parents[2]
    opened = set()
    for path in sorted(root.rglob("*.py")):
        if "tests" in path.relative_to(root).parts:
            continue
        tree = ast.parse(path.read_text(encoding="utf-8"))
        module = ".".join(path.relative_to(root).with_suffix("").parts)

        def visit(node, qual):
            for child in ast.iter_child_nodes(node):
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                    visit(child, f"{qual}.{child.name}" if qual else child.name)
                    continue
                if isinstance(child, ast.Call):
                    func = child.func
                    name = func.attr if isinstance(func, ast.Attribute) else getattr(func, "id", None)
                    if name == "audited_region":
                        opened.add((module, qual))
                visit(child, qual)

        visit(tree, "")
    assert opened, "audited_region is used"
    assert opened <= allowed, sorted(opened - allowed)


def test_audited_generators_are_functions_the_flow_audit_walks():
    """`json_encoding.audited_generator` で宣言した generator 関数（walker が進めても protocol の scope の記録を捨てない）
    は、どれも J19 の監査（`_live_flow_audit.audit`）が本体を辿った関数: 監査の外の generator を宣言すれば落ちる。"""

    import ast
    import pathlib

    from scripts.function_tracer_pcode.tests.unit import _live_flow_audit as audit

    root = pathlib.Path(__file__).resolve().parents[2]
    declared = set()
    for path in sorted(root.rglob("*.py")):
        if "tests" in path.relative_to(root).parts:
            continue
        module = "scripts.function_tracer_pcode." + ".".join(path.relative_to(root).with_suffix("").parts)
        tree = ast.parse(path.read_text(encoding="utf-8"))

        def visit(node, qual):
            for child in ast.iter_child_nodes(node):
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                    name = f"{qual}.{child.name}" if qual else child.name
                    if not isinstance(child, ast.ClassDef) and any(
                        (isinstance(d, ast.Name) and d.id == "audited_generator")
                        or (isinstance(d, ast.Attribute) and d.attr == "audited_generator")
                        for d in child.decorator_list
                    ):
                        declared.add((module, name))
                    visit(child, name)

        visit(tree, "")
    _violations, analyzed, _index, _missing = audit.audit(root)
    assert declared, "audited_generator is used"
    assert declared <= set(analyzed), sorted(declared - set(analyzed))


def test_only_declared_package_generators_keep_the_protocol_scope():
    """宣言していない package の generator を進めれば scope の記録を捨て、宣言した generator（`audited_generator`）なら
    捨てない。"""

    from scripts.function_tracer_pcode.core import json_encoding

    def plain():
        yield 1

    with live_values.audited_region():
        memo = live_values.region_cache(json_encoding._PROTOCOL_SLOT)
        memo[0] = ("marker",)
        list(json_encoding._walk_iter(plain()))
        assert memo == {}
        memo[0] = ("marker",)
        from scripts.function_tracer_pcode.core.signature import _parameter_descriptor_pairs

        list(json_encoding._walk_iter(_parameter_descriptor_pairs({"a": 1})))
        assert memo == {0: ("marker",)}
    with pytest.raises(TypeError):
        json_encoding.audited_generator(lambda: None)


@pytest.mark.parametrize("wrapper", [staticmethod, classmethod])
def test_package_type_follows_the_class_of_an_object_a_wrapper_holds(wrapper):
    """判定が読んだ object（`_Nesting.objects`: wrapper が包む object）の `__class__` を変えれば、記録は判定し直す
    （包んだ object の型は namespace の値の identity では固定されない）。"""

    Inert = type("Inert", (), {})
    Active = type("Active", (), {"__call__": _foreign_function()})
    held = Inert()
    kind = type("Holder", (), {"__module__": __name__, "member": wrapper(held)})
    assert live_values.package_type(kind) is True
    held.__class__ = Active
    fresh = type("Fresh", (), {"__module__": __name__, "member": kind.__dict__["member"]})
    assert live_values.package_type(fresh) is False
    assert live_values.package_type(kind) is False


def test_an_lru_cache_wrapper_is_judged_by_the_function_it_calls():
    """`lru_cache` の wrapper の信頼は C の struct が呼ぶ関数で決める（instance の `__wrapped__` は書き換えられる: 根拠に
    しない）。"""

    import functools

    def trusted(self):
        return "package"

    foreign = _foreign_function()
    disguised = functools.lru_cache(maxsize=None)(foreign)
    disguised.__wrapped__ = trusted
    assert live_values.package_type(type("Disguised", (), {"__module__": __name__, "f": disguised})) is False
    honest = functools.lru_cache(maxsize=None)(trusted)
    kind = type("Honest", (), {"__module__": __name__, "f": honest})
    assert live_values.package_type(kind) is True
    honest.__wrapped__ = foreign  # 呼ぶ関数は変わらない
    assert live_values.package_type(kind) is True


def test_identity_key_of_forgets_the_protocol_scope_when_the_key_method_raises():
    """identity key の method（#194 の owner の code）が例外で抜けても scope の記録を捨てる。"""

    from scripts.function_tracer_pcode.core import json_encoding

    def items(self):
        yield "a", 1

    kind = type("Record", (), {"__module__": __name__, "json_items": items})

    class Keyed:
        def stable_key(self):
            kind.json_items = _foreign_function()
            raise TypeError("boom")

    try:
        with live_values.audited_region():
            assert json_encoding.is_json_record(kind())
            with pytest.raises(TypeError):
                json_encoding.identity_key_of(Keyed())
            assert not json_encoding.is_json_record(kind())
    finally:
        kind.json_items = items


def test_identity_key_of_reads_names_outside_the_protocol_table():
    """`identity_key_of(names=...)` は表に無い名前も型から引く（package の関数・package の型だけ）。"""

    from scripts.function_tracer_pcode.core import json_encoding

    class Keyed:
        def other_key(self):
            return ("other",)

    assert json_encoding.identity_key_of(Keyed(), names=("other_key",)) == (True, ("other",))
    assert json_encoding.identity_key_of(Keyed(), names=("missing",)) == (False, None)


def test_each_over_an_undeclared_generator_forgets_the_protocol_scope():
    """`each` の列が宣言していない package の generator なら、進めるたびに scope の記録を捨てる（`_walk_iter`）。"""

    from scripts.function_tracer_pcode.core import json_encoding
    from scripts.function_tracer_pcode.core.json_encoding import JsonValueRejected, RESULT_JSON_POLICY

    def items(self):
        yield "a", 1

    kind = type("Record", (), {"__module__": __name__, "json_items": items})

    def rewriting():
        yield 1
        kind.json_items = _foreign_function()
        yield 2

    try:
        with pytest.raises(JsonValueRejected):
            RESULT_JSON_POLICY.prepare(json_encoding.inline(
                ("first", kind()), ("g", json_encoding.each(rewriting())), ("last", kind()),
            )).value()
    finally:
        kind.json_items = items


def test_a_nan_leaf_without_weak_references_is_undecidable_and_never_held():
    """反例（第 10 回 指摘 2）: weakref を作れない float の subclass の NaN（`__slots__ = ("back",)`、`x.back = x` の循環）。
    写しの identity を元の葉の寿命に結べない（結ぶには葉を持つしかない）: 判定不能（D20）。表は葉を持たない: 呼び出し元が
    手放して GC すれば、全部解放される（cache を使わない対照と同じ）。"""

    class Cyclic(float):
        __slots__ = ("back",)

    def alive():
        gc.collect()
        return sum(1 for item in gc.get_objects() if type(item) is Cyclic)

    before = alive()
    for _ in range(10_000):
        leaf = Cyclic("nan")
        leaf.back = leaf
        with pytest.raises(UndecidableComparison):
            live_values.plain_scalar(leaf)
        del leaf
    assert alive() == before
    # 対照: 表を使わない読み（NaN でない値）でも同じだけ解放される
    for _ in range(10_000):
        leaf = Cyclic("1.5")
        leaf.back = leaf
        assert live_values.plain_scalar(leaf) == 1.5
        del leaf
    assert alive() == before


def test_a_nan_copy_follows_its_source_and_does_not_keep_it_alive():
    """weakref を作れる NaN の葉の写しは、元の葉が生きている間同じ object（比べる・hash する読みが呼び出しの間で揃う）。
    表は元の葉を持たない: 循環の中の葉も、手放して GC すれば解放され、entry も消える。"""

    import weakref as _weakref

    class Linked(float):
        __slots__ = ("back", "__weakref__")

    leaf = Linked("nan")
    leaf.back = leaf
    first = live_values.plain_scalar(leaf)
    assert live_values.plain_scalar(leaf) is first
    assert type(first) is float and first != first
    probe = _weakref.ref(leaf)
    entries = len(live_values._NAN_COPIES)
    del leaf
    gc.collect()
    assert probe() is None
    assert len(live_values._NAN_COPIES) == entries - 1


def test_the_nan_copy_callback_can_run_while_the_table_is_locked():
    """weakref の callback（`_forget_nan`）が、表の lock を持つ同じ thread の中で走っても止まらない（GC は lock の中の
    割り当てで callback を走らせることがある）。"""

    import threading

    finished = []

    def run():
        with live_values._NAN_COPIES_LOCK:
            live_values._forget_nan(-1, None)
        finished.append(True)

    worker = threading.Thread(target=run, daemon=True)
    worker.start()
    worker.join(5)
    assert finished == [True]


def test_a_lookup_fact_follows_the_mro_of_another_type_its_computation_read():
    """`lookup_fact` の計算が key でない型の名前を引けば、その型の MRO（引く storage の列）も記録の依存: その型の
    `__bases__` を書き換えれば計算し直す（instance の `__dict__` の descriptor の記録を使っても）。"""

    Shadow = type("Shadow", (), {"__dict__": 5})  # 名前空間の `__dict__` が descriptor でない（instance の dict は読めない）
    Plain = type("Plain", (), {})
    Kind = type("Kind", (Plain,), {})
    value = Kind()
    value.probe = "kept"
    assert live_values.instance_state(value, "probe", "absent") == "kept"  # holder の記録を先に作る
    table = live_values.LookupFactTable()
    key = type("Key", (), {})

    def compute(_key):
        return live_values.instance_state(value, "probe", "absent")

    assert live_values.lookup_fact(table, key, compute, key) == "kept"
    Kind.__bases__ = (Shadow,)
    assert live_values.instance_state(value, "probe", "absent") == "absent"
    assert live_values.lookup_fact(table, key, compute, key) == "absent"


def test_a_lookup_fact_follows_the_class_of_an_object_it_found():
    """`lookup_fact` の計算が見つけた object の型を読めば、その object の `__class__` の書き換えで計算し直す（記録は
    見つけた object の identity の外の状態も確かめる: `_watch`）。"""

    First = type("First", (), {})
    Second = type("Second", (), {})
    found = First()
    kind = type("Kind", (), {"member": found})
    table = live_values.LookupFactTable()

    def compute(klass):
        return type(live_values.type_attribute(klass, "member")).__name__

    assert live_values.lookup_fact(table, kind, compute, kind) == "First"
    found.__class__ = Second
    assert live_values.lookup_fact(table, kind, compute, kind) == "Second"


def test_a_lookup_fact_used_inside_a_type_judgement_adds_its_classes_to_the_judgement():
    """型の信頼の判定の途中（`_Nesting.active`）で `lookup_fact` の記録を使えば、記録が依る class（key の型の MRO と、
    計算が引いた型）は判定の依存（`_Nesting.reads`）になる。"""

    table = live_values.LookupFactTable()
    other = type("Other", (), {"member": 1})
    kind = type("Kind", (), {})

    def compute(_klass):
        return live_values.type_attribute(other, "member")

    assert live_values.lookup_fact(table, kind, compute, kind) == 1
    state = live_values._NESTING
    saved = (state.active, state.reads)
    state.active, state.reads = {kind: 0}, []
    try:
        assert live_values.lookup_fact(table, kind, compute, kind) == 1
        reads = list(state.reads)
    finally:
        state.active, state.reads = saved
    assert kind in reads and other in reads


def test_json_items_returning_another_generator_forgets_the_protocol_scope():
    """`json_items` が自分でない generator（宣言していない package の generator）を返せば、それを進めるたびに scope の
    記録を捨てる（`_record_items`: そのまま進めるのは `json_items` 自身の generator だけ）。"""

    from scripts.function_tracer_pcode.core.json_encoding import JsonValueRejected, RESULT_JSON_POLICY

    def items(self):
        yield "a", 1

    kind = type("Record", (), {"__module__": __name__, "json_items": items})

    def helper():
        yield "first", kind()
        kind.json_items = _foreign_function()
        yield "second", kind()

    def delegating(self):
        return helper()

    outer = type("Outer", (), {"__module__": __name__, "json_items": delegating})
    try:
        with pytest.raises(JsonValueRejected):
            RESULT_JSON_POLICY.prepare(outer()).value()
    finally:
        kind.json_items = items


def test_package_type_follows_the_class_of_a_module_in_a_namespace():
    """名前空間の module の `__class__`（ModuleType の subclass へ変えられる）を変えれば、記録は判定し直す。"""

    import types as _types

    module = _types.ModuleType("held_module")
    kind = type("Holder", (), {"__module__": __name__, "member": module})
    assert live_values.package_type(kind) is True
    module.__class__ = type("CallableModule", (_types.ModuleType,), {"__call__": _foreign_function()})
    fresh = type("Fresh", (), {"__module__": __name__, "member": module})
    assert live_values.package_type(fresh) is False
    assert live_values.package_type(kind) is False


def test_a_type_state_check_fails_when_names_change_but_values_stay_in_order():
    """型の状態の確かめ（`_state_check` / `_state_holds`）は名前空間の key も比べる: 値の並びが同じまま名前だけを変えた
    名前空間（消して別の名前で置き直す）は同じ状態ではない。"""

    first, second = object(), object()
    kind = type("Kind", (), {})
    kind.a = first  # 名前空間の末尾に置く（消して置き直しても並びが同じ）
    kind.b = second
    check = live_values._state_check(live_values._class_snapshot(kind))
    assert live_values._state_holds(check)
    del kind.a
    del kind.b
    kind.c = first
    kind.b = second
    assert [value for value in live_values._TYPE_DICT.__get__(kind).values() if value is first or value is second] == [first, second]
    assert not live_values._state_holds(check)


def test_a_type_state_check_fails_when_a_name_is_added_even_if_the_columns_would_line_up():
    """型の状態の確かめは名前空間の大きさを先に比べる: 足した key と値が、並べた列の比べ（1 つの `map`）で前の列と
    たまたま揃う形（どの値も同じ str で、足した key もその str）でも同じ状態ではない。"""

    import sys as _sys

    text = _sys.intern("shared_text_for_alignment")
    # 基底を `type` にすると名前空間に `__dict__` / `__weakref__` が足されず、heap type の名前空間はこの 1 つだけ
    kind = type("Kind", (type,), {"__module__": text, "__doc__": text, "a": text})
    check = live_values._state_check(live_values._class_snapshot(kind))
    assert live_values._state_holds(check)
    setattr(kind, text, text)
    assert list(live_values._TYPE_DICT.__get__(kind).values()) == [text] * 4
    assert not live_values._state_holds(check)


def test_package_type_follows_a_bases_change_of_the_judged_type():
    """型の `__bases__` を書き換えれば（MRO の tuple が変わる）、記録は判定し直す（名前空間の snapshot が同じでも）。"""

    Good = type("Good", (), {"__module__": __name__})
    Bad = type("Bad", (), {"__module__": __name__, "method": _foreign_function()})
    kind = type("Kind", (Good,), {"__module__": __name__})
    assert live_values.package_type(kind) is True
    kind.__bases__ = (Bad,)
    assert live_values.package_type(type("Fresh", (Bad,), {"__module__": __name__})) is False
    assert live_values.package_type(kind) is False


def test_package_type_follows_the_namespace_of_a_value_type_read_through_the_mro_record():
    """判定が名前空間の値の型（key の型の MRO の外の class）を引けば、その class は判定の依存（`_PLAIN_MROS` の記録から
    引いても）: その class に foreign な `__call__` を足せば判定し直す。"""

    Value = type("Value", (), {})
    live_values.type_attribute(Value, "__call__")  # MRO の記録を先に作る
    kind = type("Holder", (), {"__module__": __name__, "member": Value()})
    assert live_values.package_type(kind) is True
    Value.__call__ = _foreign_function()
    assert live_values.package_type(type("Fresh", (), {"__module__": __name__, "member": Value()})) is False
    assert live_values.package_type(kind) is False


def test_package_type_follows_an_object_read_by_a_nested_judgement_it_reused():
    """入れ子の判定の記録（名前空間の値の class の `package_type`）を使った判定は、その記録が読んだ object も依存に足す
    （`_Nesting.objects`）: 入れ子の class の wrapper が包む object の `__class__` を変えれば、外の判定も判定し直す。"""

    Inert = type("Inert", (), {})
    Active = type("Active", (), {"__call__": _foreign_function()})
    held = Inert()
    inner = type("Inner", (), {"__module__": __name__, "member": staticmethod(held)})
    assert live_values.package_type(inner) is True  # 入れ子の記録を先に作る
    outer = type("Outer", (), {"__module__": __name__, "nested": inner})
    assert live_values.package_type(outer) is True
    held.__class__ = Active
    assert live_values.package_type(inner) is False
    assert live_values.package_type(outer) is False


def test_a_lookup_fact_inside_another_passes_on_the_mros_it_read():
    """`lookup_fact` の記録を外の `lookup_fact` の計算で使えば、内の計算が引いた型の MRO も外の記録の依存: その型の
    `__bases__` を書き換えれば外も計算し直す。"""

    First = type("First", (), {"marker": "first"})
    Second = type("Second", (), {"marker": "second"})
    other = type("Other", (First,), {})
    inner_table, outer_table = live_values.LookupFactTable(), live_values.LookupFactTable()
    key = type("Key", (), {})

    def inner(_key):
        return live_values.type_attribute(other, "marker")

    def outer(_key):
        return ("outer", live_values.lookup_fact(inner_table, key, inner, key))

    assert live_values.lookup_fact(inner_table, key, inner, key) == "first"
    assert live_values.lookup_fact(outer_table, key, outer, key) == ("outer", "first")
    other.__bases__ = (Second,)
    assert live_values.lookup_fact(outer_table, key, outer, key) == ("outer", "second")


def test_json_protocols_need_a_package_type():
    """record の protocol は package の型のものだけ: package の関数の `json_items` を持っていても、型が外の code を
    持てば（`package_type` が偽）record にしない。"""

    from scripts.function_tracer_pcode.core import json_encoding

    def items(self):
        yield "a", 1

    kind = type("Record", (), {"__module__": __name__, "json_items": items, "other": _foreign_function()})
    assert live_values.package_type(kind) is False
    assert not json_encoding.is_json_record(kind())


def test_json_protocols_are_package_functions_not_wrappers():
    """record の protocol は package の関数だけ（`staticmethod` などの wrapper の object は protocol にしない）。"""

    from scripts.function_tracer_pcode.core import json_encoding

    def items(value):
        yield "a", 1

    kind = type("Record", (), {"__module__": __name__, "json_items": staticmethod(items)})
    assert live_values.package_type(kind) is True
    assert not json_encoding.is_json_record(kind())


def test_dataclass_field_names_follow_the_class_of_a_field_whose_kind_is_unset():
    """`Field` の種類の slot が `None` の field は名前に入らない。その `Field` の `__class__` を subclass へ変えれば、表は
    `dataclasses.fields` と同じ規則で読めない（`None`）: 記録は field の型も確かめる。"""

    import dataclasses

    @dataclasses.dataclass
    class Data:
        a: int
        b: int

    field = Data.__dataclass_fields__["b"]
    field._field_type = None
    value = Data(1, 2)
    assert live_values.dataclass_field_names(value) == ("a",)
    field.__class__ = type("FieldSub", (dataclasses.Field,), {"__slots__": ()})
    assert live_values._dataclass_field_names(Data) is None
    assert live_values.dataclass_field_names(value) is None


def test_a_recursion_error_inside_a_producer_reaches_the_caller():
    """producer（`json_items`）の中で起きた `RecursionError` は値の不備にしない（walker の中で起きたときと同じに呼ぶ側へ
    伝える: 落ちた場所で結果を変えない）。stack の深さの掃き出し（上の test）は frame の並びに依るので、ここで直接確かめる。"""

    from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY

    def items(self):
        raise RecursionError("stack limit inside a producer")
        yield  # pragma: no cover - generator にする

    kind = type("Record", (), {"__module__": __name__, "json_items": items})
    with pytest.raises(RecursionError):
        RESULT_JSON_POLICY.prepare(kind()).value()


@pytest.mark.parametrize("change", ["cell", "code"])
def test_package_type_follows_the_code_and_closure_of_a_runtime_function_it_opened(change):
    """判定が中を辿った実行環境の関数（`contextlib.contextmanager` の helper: package の外の file の関数で、closure の
    中身を信頼するものだけ）の closure の cell の中身・`__code__` を書き換えれば、記録は判定し直す。"""

    import contextlib

    def body():
        yield 1

    helper = contextlib.contextmanager(body)
    kind = type("Holder", (), {"__module__": __name__, "member": staticmethod(helper)})
    assert live_values.package_type(kind) is True
    if change == "cell":
        cell = next(cell for cell in helper.__closure__ if cell.cell_contents is body)
        cell.cell_contents = _foreign_function()
    else:
        names = helper.__code__.co_freevars
        source = "def outer({0}):\n    def helper(*args, **kwargs):\n        return ({0},)\n    return helper\n".format(", ".join(names))
        namespace = {}
        exec(compile(source, "<foreign>", "exec"), namespace)  # noqa: S102 - 外の file 名の code
        helper.__code__ = namespace["outer"](*range(len(names))).__code__
    assert live_values.package_type(type("Fresh", (), {"__module__": __name__, "member": staticmethod(helper)})) is False
    assert live_values.package_type(kind) is False


def test_package_type_follows_a_false_verdict_function_whose_code_becomes_trusted():
    """反例（第 10 回 指摘 3）: 外の関数で偽と記録した後、その関数の `__code__` を package の関数の code にする（変える
    のは信頼していない関数: 信頼した関数の code・global は変えない）。新しい判定は真: 記録も真になる（無関係な属性を足して
    確かめ直す前に）。JSON の record の判定も同じ。"""

    from scripts.function_tracer_pcode.core import json_encoding

    def trusted(self):
        yield "a", 1

    foreign = eval(compile("lambda self: iter(())", "<foreign>", "eval"))  # noqa: S307
    kind = type("Record", (), {"__module__": __name__, "json_items": foreign})
    assert live_values.package_type(kind) is False
    assert json_encoding.is_json_record(kind()) is False
    foreign.__code__ = trusted.__code__
    fresh = type("Fresh", (), {"__module__": __name__, "json_items": foreign})
    assert live_values.package_type(fresh) is True
    assert live_values.package_type(kind) is True
    assert json_encoding.is_json_record(kind()) is True


def test_a_lookup_fact_follows_the_code_of_an_untrusted_function_it_found():
    """名前の引きだけの事実（`lookup_fact`）が見つけた信頼していない関数の `__code__` を変えれば、計算し直す。"""

    def trusted(self):
        return 1

    foreign = eval(compile("lambda self: 2", "<foreign>", "eval"))  # noqa: S307
    kind = type("Kind", (), {"member": foreign})
    table = live_values.LookupFactTable()

    def compute(klass):
        return live_values.package_function(live_values.type_attribute(klass, "member"))

    assert live_values.lookup_fact(table, kind, compute, kind) is False
    foreign.__code__ = trusted.__code__
    assert live_values.lookup_fact(table, kind, compute, kind) is True



def test_a_lookup_fact_follows_the_accessor_of_a_dynamic_class_attribute_it_found():
    """名前の引きだけの事実（`lookup_fact`）が見つけた `types.DynamicClassAttribute` の accessor（instance の属性:
    identity は同じまま差し替わる）を変えれば、計算し直す（`_watch_holds` が accessor の状態を確かめる）。"""

    import types as _types

    def trusted(self):
        return 1

    found = _types.DynamicClassAttribute(trusted)
    kind = type("Kind", (), {"member": found})
    table = live_values.LookupFactTable()

    def compute(klass):
        return live_values.package_function(live_values.type_attribute(klass, "member").fget)

    assert live_values.lookup_fact(table, kind, compute, kind) is True
    found.fget = eval(compile("lambda self: 2", "<foreign>", "eval"))  # noqa: S307
    assert live_values.lookup_fact(table, kind, compute, kind) is False

def test_package_type_follows_a_bound_method_whose_function_code_changes():
    """名前空間の bound method が包む信頼していない関数の `__code__` を変えれば、記録は判定し直す。"""

    import types as _types

    def trusted(self):
        return 1

    foreign = eval(compile("lambda self: 2", "<foreign>", "eval"))  # noqa: S307
    holder = type("Holder", (), {})()
    kind = type("Kind", (), {"__module__": __name__, "member": _types.MethodType(foreign, holder)})
    assert live_values.package_type(kind) is False
    foreign.__code__ = trusted.__code__
    assert live_values.package_type(kind) is True

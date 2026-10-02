# -*- coding: utf-8 -*-
"""witness は本体が読むものから導く（Issue #219 PR-219-B、C-RS1 / C-RS5、レビュー 3）。

保証: 同じ safe witness なら、その時点の通常の build と、全 field・fingerprint・参照の保持の意味・予算の
成功 / 失敗と種類が一致する。ここで確かめるのは、fingerprint の codec と保持（`create`）が読む状態:

* codec は set の要素を表現の順に並べる（enum の member の名前で順が変わる）
* codec は dataclass・`stable_key` を持つ object・record の **今の** 状態を読む（同じ object でも状態が
  変われば fingerprint が変わる）
* 入力の型が自分で「witness の token だ」と宣言しても、token として扱わない（token は再利用の owner が
  発行する型だけ）

store を温めてから入力を変え、field の等しさと fingerprint の等しさを別々に確かめる。oracle は
`_snapshot_oracle`（production の witness・正規化を使わない）。
"""

from __future__ import annotations

import dataclasses
import enum
import random
from typing import Any, Callable, List

import pytest

from scripts.function_tracer_pcode.core.budget_policy import BudgetPolicy, budget_policy_scope
from scripts.function_tracer_pcode.core.errors import pair_failure_scope, reset_pair_failure_scopes
from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot
from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import snapshot_reuse_metrics, snapshot_reuse_scope
from scripts.function_tracer_pcode.tests.unit import _snapshot_oracle as oracle
from scripts.function_tracer_pcode.tests.unit.test_issue219_witness_fidelity import _analysis, _closed_root, _with_values

_RAW_BUILD = AnalysisSnapshot.__dict__["_build_from_function_analysis"].__func__
WHERE = ["analysis_scope_key", "return_abi_facts"]


@pytest.fixture(autouse=True, params=["hash", "collide"])
def _witness_hash_mode(request, monkeypatch):
    """`collide` は witness の hash を定数にして、比べ方（`_same`）だけで決めさせる（hash の衝突で誤らない）。"""

    if request.param == "collide":
        from scripts.function_tracer_pcode.proof.obligations import snapshot_reuse

        monkeypatch.setattr(snapshot_reuse, "_hash", lambda value, retained=False: 0)
    yield request.param


@pytest.fixture(autouse=True)
def _clean_ledger_stack():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


# ---------------------------------------------------------------------------
# 材料: 受理される値の種類（enum・dataclass・protocol 型・自己宣言の marker）
# ---------------------------------------------------------------------------


class Level(enum.IntEnum):
    A = 1
    Z = 2


class Mode(str, enum.Enum):
    A = "a"
    Z = "z"


class Plain(enum.Enum):
    A = ("a", 1)
    Z = ("z", 2)


@dataclasses.dataclass
class Box:
    value: Any


@dataclasses.dataclass(frozen=True)
class FrozenBox:
    value: Any


@dataclasses.dataclass
class Marked:
    """自分で witness の token だと宣言する入力（宣言を信じてはいけない）。"""

    value: Any
    __snapshot_witness_token__ = True


@dataclasses.dataclass(unsafe_hash=True)
class ValueHashBox:
    """変わり得る、値で等しく値で hash する object（`==` も hash も別の object を区別しない）。"""

    value: Any


@dataclasses.dataclass(eq=False)
class HashableBox:
    """変わり得る、hashable な object（identity で hash する）。"""

    value: Any


class Keyed:
    """`stable_key` を持つ object（codec は key を読む）。"""

    def __init__(self, key: Any) -> None:
        self.key = key

    def stable_key(self):
        return ("keyed", self.key)


class Record:
    """`json_items` を持つ record（codec は表現を作って読む）。"""

    def __init__(self, value: Any) -> None:
        self.value = value

    def json_items(self):
        yield "value", self.value


def _with_field(base: Any, where: str, value: Any) -> Any:
    if where == "analysis_scope_key":
        return dataclasses.replace(base, analysis_scope_key=("scope", value))
    return dataclasses.replace(base, return_abi_facts={"probe": value})


def _warm_change_and_compare(make: Callable[[], Any], change: Callable[[Any], None], where: str):
    """store を温めてから値を（in place で）変え、同じ解析の再利用の結果と同じ時点の通常の build を比べる。

    返すのは (field の違い, fingerprint の違い, hit したか)。
    """

    value = make()
    analysis = _with_field(_analysis([_closed_root()]), where, value)
    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        oracle.outcome(lambda: AnalysisSnapshot.from_function_analysis(analysis))
        change(value)
        reused = oracle.outcome(lambda: AnalysisSnapshot.from_function_analysis(analysis))
        hits = snapshot_reuse_metrics()["counts"].get("hits", 0)
        built = oracle.outcome(lambda: _RAW_BUILD(AnalysisSnapshot, analysis))
    problems = oracle.outcome_problems(reused, built)
    fingerprints = (
        oracle.fingerprint_problems(reused[1], built[1]) if reused[0] == built[0] == "ok" else []
    )
    return problems, fingerprints, hits


# ---------------------------------------------------------------------------
# レビュー 3 の反例（修正前に落ちる）
# ---------------------------------------------------------------------------


@pytest.fixture
def restore_enum_names():
    saved = {member: member._name_ for cls in (Level, Mode) for member in list(cls.__members__.values())}
    yield
    for member, name in saved.items():
        member._name_ = name


@pytest.mark.parametrize("where", WHERE)
@pytest.mark.parametrize("enum_class", [Level, Mode], ids=["IntEnum", "StrEnum"])
def test_an_enum_member_renamed_after_warming_changes_the_codec_order_and_is_rebuilt(where, enum_class, restore_enum_names):
    def rename(_value):
        enum_class.A._name_ = "zz"

    problems, fingerprints, _hits = _warm_change_and_compare(lambda: frozenset({enum_class.A, enum_class.Z}), rename, where)
    assert fingerprints == [] and problems == []


@pytest.mark.parametrize("where", WHERE)
def test_a_self_declared_token_is_not_trusted_and_its_change_is_rebuilt(where):
    def change(value):
        value.value = 2

    problems, fingerprints, _hits = _warm_change_and_compare(lambda: Marked(1), change, where)
    assert fingerprints == [] and problems == []


# ---------------------------------------------------------------------------
# codec が今の状態を読む object の変更（同じ object でも fingerprint が変わる）
# ---------------------------------------------------------------------------


def _state_changes():
    def set_box(value):
        value.value = 2

    def set_key(value):
        value.key = 2

    def set_record(value):
        value.value = 2

    def set_inner(value):
        value[0].value = 2

    return {
        "mutable_dataclass": (lambda: Box(1), set_box),
        "stable_key_object": (lambda: Keyed(1), set_key),
        "json_record": (lambda: Record(1), set_record),
        "dataclass_in_tuple": (lambda: (Box(1),), set_inner),
        "dataclass_in_list": (lambda: [Box(1)], set_inner),
        "hashable_in_frozenset": (lambda: _single(frozenset({HashableBox(1)})), lambda v: setattr(next(iter(v)), "value", 2)),
        "frozen_dataclass_inner_list": (lambda: FrozenBox([1]), lambda v: v.value.append(2)),
        "plain_enum_member": (lambda: Plain.A, lambda v: None),
    }


def _single(value):
    return value


@pytest.mark.parametrize("where", WHERE)
@pytest.mark.parametrize("name", sorted(_state_changes()))
def test_a_state_change_the_codec_or_retention_reads_is_never_served_stale(where, name):
    make, change = _state_changes()[name]
    problems, fingerprints, _hits = _warm_change_and_compare(make, change, where)
    assert fingerprints == [] and problems == []


# ---------------------------------------------------------------------------
# 正しい再利用を拒まない（精度）と、oracle が正しい共有を違いとしないこと
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("where", WHERE)
@pytest.mark.parametrize(
    "make",
    [lambda: frozenset({Level.A, Level.Z}), lambda: Box(1), lambda: FrozenBox((1, 2)), lambda: Keyed((1,)), lambda: Record("r"),
     lambda: (float("nan"), [1])],
    ids=["enum_set", "dataclass", "frozen_dataclass", "stable_key", "record", "nan_and_list"],
)
def test_an_unchanged_value_is_reused_and_matches_the_body(where, make):
    problems, fingerprints, hits = _warm_change_and_compare(make, lambda _value: None, where)
    assert problems == [] and fingerprints == []
    # 受理されて snapshot になる値なら、変わっていない同じ解析は hit する
    if problems == [] and hits == 0:
        with budget_policy_scope(BudgetPolicy()):
            analysis = _with_field(_analysis([_closed_root()]), where, make())
            assert oracle.outcome(lambda: _RAW_BUILD(AnalysisSnapshot, analysis))[0] == "raised", "an accepted value never hit"


@pytest.mark.parametrize("where", WHERE)
@pytest.mark.parametrize(
    "make",
    [lambda: Box(1), lambda: HashableBox(1), lambda: Record(1), lambda: Keyed(1), lambda: Marked(1), lambda: (Box(1),),
     lambda: frozenset({HashableBox(1)}), lambda: frozenset({ValueHashBox(1)})],
    ids=["dataclass", "hashable", "record", "stable_key", "marked", "dataclass_in_tuple", "hashable_in_frozenset",
         "value_hashed_in_frozenset"],
)
def test_an_equal_but_other_mutable_object_is_another_retained_value(where, make):
    """snapshot は object を参照のまま置く（`snapshot_id` の要素・`deep_freeze` の葉）: 内容が等しくても別の object
    なら別の snapshot（後でその object が変われば snapshot も変わる）。"""

    prime = _with_field(_analysis([_closed_root()]), where, make())
    target = _with_field(prime, where, make())
    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        oracle.outcome(lambda: AnalysisSnapshot.from_function_analysis(prime))
        reused = oracle.outcome(lambda: AnalysisSnapshot.from_function_analysis(target))
        built = oracle.outcome(lambda: _RAW_BUILD(AnalysisSnapshot, target))
    assert oracle.outcome_problems(reused, built) == []


@pytest.mark.parametrize("seeds", [(1, 2), (1, 1)], ids=["other_constant", "equal_constant"])
def test_another_closed_root_is_another_token(seeds):
    """closed な root は token（同じ object であること）で比べる: 別の root は、内容が同じでも hit しない
    （hash が衝突しても `_same` が区別する）。"""

    from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import snapshot_reuse_metrics

    prime = _analysis([_closed_root(seeds[0])])
    target = _with_values(prime, [_closed_root(seeds[1])])
    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        oracle.outcome(lambda: AnalysisSnapshot.from_function_analysis(prime))
        reused = oracle.outcome(lambda: AnalysisSnapshot.from_function_analysis(target))
        built = oracle.outcome(lambda: _RAW_BUILD(AnalysisSnapshot, target))
        assert snapshot_reuse_metrics()["counts"].get("hits", 0) == 0
    assert oracle.outcome_problems(reused, built) == []


@dataclasses.dataclass(frozen=True)
class Effect:
    """効果要約の代わり（frozen な dataclass。codec が field を写す）。"""

    members: Any


_ORDERED_BY_THE_CODEC = {
    "set_of_closed": lambda root: frozenset({root}),
    "set_of_tuple_of_closed": lambda root: frozenset({("tag", root), ("other", 1)}),
    "set_mixed": lambda root: frozenset({root, "plain", 3}),
    "record_key_of_closed": lambda root: {Record(root): 1},
    "list_of_closed": lambda root: [root],
}


@pytest.mark.parametrize("enabled", [True, False], ids=["memo_on", "kill_switch"])
@pytest.mark.parametrize("where", ["effect_summary", *WHERE])
@pytest.mark.parametrize("name", sorted(_ORDERED_BY_THE_CODEC))
def test_a_closed_value_the_codec_must_order_is_built_like_the_body(where, name, enabled, monkeypatch):
    """codec が並べる位置（set の要素・mapping の key）の closed な値: token の並びは codec に分からないので、
    witness は作れず本体へ回る（通常の build と同じ snapshot・同じ例外。内部エラーにしない）。"""

    from scripts.function_tracer_pcode.proof.obligations import snapshot_reuse

    monkeypatch.setattr(snapshot_reuse, "_SNAPSHOT_REUSE_ENABLED", enabled)
    root = _closed_root()
    value = _ORDERED_BY_THE_CODEC[name](root)
    base = _analysis([root])
    if where == "effect_summary":
        analysis = dataclasses.replace(base, effect_summary=Effect(value))
    else:
        analysis = _with_field(base, where, value)
    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        first = oracle.outcome(lambda: AnalysisSnapshot.from_function_analysis(analysis))
        again = oracle.outcome(lambda: AnalysisSnapshot.from_function_analysis(analysis))
        built = oracle.outcome(lambda: _RAW_BUILD(AnalysisSnapshot, analysis))
    assert oracle.outcome_problems(first, built) == []
    assert oracle.outcome_problems(again, built) == []


def test_the_oracle_accepts_correct_sharing_and_rejects_wrong_sharing():
    shared = HashableBox(1)
    assert oracle.retained_equal(frozenset({shared, 1}), frozenset({shared, 1}))
    assert oracle.retained_equal(("s", frozenset({shared})), ("s", frozenset({shared})))
    assert not oracle.retained_equal(frozenset({shared}), frozenset({HashableBox(1)}))
    lst = [1]
    assert oracle.retained_equal(("s", lst), ("s", lst))
    assert not oracle.retained_equal(("s", lst), ("s", [1]))
    nan = float("nan")
    assert oracle.retained_equal((nan,), (nan,))
    assert not oracle.retained_equal((nan,), (float("nan"),))
    # snapshot の field に参照で置かれた object: 同じ object なら同じ、等しい別の object なら違い
    base = _analysis([_closed_root()])
    box = Box(1)
    with budget_policy_scope(BudgetPolicy()):
        first = _RAW_BUILD(AnalysisSnapshot, _with_field(base, "return_abi_facts", box))
        again = _RAW_BUILD(AnalysisSnapshot, _with_field(base, "return_abi_facts", box))
        other = _RAW_BUILD(AnalysisSnapshot, _with_field(base, "return_abi_facts", Box(1)))
    assert oracle.snapshot_problems(first, again) == []
    assert oracle.snapshot_problems(first, other) != []
    # mapping の反復の順（`deep_freeze` は挿入の順を保つ）と key の型も違い
    with budget_policy_scope(BudgetPolicy()):
        ordered = _RAW_BUILD(AnalysisSnapshot, _with_field(base, "return_abi_facts", {"a": 1, "b": 2}))
        reordered = _RAW_BUILD(AnalysisSnapshot, _with_field(base, "return_abi_facts", {"b": 2, "a": 1}))
        int_key = _RAW_BUILD(AnalysisSnapshot, _with_field(base, "return_abi_facts", {1: "v"}))
        enum_key = _RAW_BUILD(AnalysisSnapshot, _with_field(base, "return_abi_facts", {Level.A: "v"}))
    assert oracle.snapshot_problems(ordered, reordered) != []
    assert oracle.snapshot_problems(int_key, enum_key) != []


@pytest.mark.parametrize("where", WHERE)
def test_a_rebuilt_frozenset_around_the_same_mutable_object_is_reused(where):
    shared = HashableBox(1)
    prime = _with_field(_analysis([_closed_root()]), where, frozenset({shared}))
    target = _with_field(prime, where, frozenset({shared}))
    with pair_failure_scope(("pair", 1), None), budget_policy_scope(BudgetPolicy()), snapshot_reuse_scope():
        first = oracle.outcome(lambda: AnalysisSnapshot.from_function_analysis(prime))
        reused = oracle.outcome(lambda: AnalysisSnapshot.from_function_analysis(target))
        built = oracle.outcome(lambda: _RAW_BUILD(AnalysisSnapshot, target))
    assert oracle.outcome_problems(reused, built) == []
    assert first[0] == reused[0]


# ---------------------------------------------------------------------------
# property: 種類 × 入れ子 × 共有 × 状態変更
# ---------------------------------------------------------------------------


def _leaf(rng: random.Random, pool: List[Any]) -> Any:
    if pool and rng.random() < 0.3:
        return rng.choice(pool)
    pick = rng.randrange(12)
    value = (
        lambda: rng.randrange(3), lambda: rng.choice((0.0, -0.0, 1.0)), lambda: float("nan"), lambda: rng.choice(("a", "b")),
        lambda: rng.choice((True, False, None)), lambda: rng.choice(list(Level)), lambda: rng.choice(list(Mode)),
        lambda: rng.choice(list(Plain)), lambda: Box(rng.randrange(3)), lambda: Marked(rng.randrange(3)),
        lambda: Keyed(rng.randrange(3)), lambda: Record(rng.randrange(3)),
    )[pick]()
    pool.append(value)
    return value


def _hashable(value: Any) -> bool:
    try:
        hash(value)
        return True
    except TypeError:
        return False


def _value(rng: random.Random, pool: List[Any], depth: int) -> Any:
    if depth <= 0 or rng.random() < 0.3:
        return _leaf(rng, pool)
    kind = rng.randrange(5)
    items = [_value(rng, pool, depth - 1) for _ in range(rng.randrange(0, 3))]
    if kind == 0:
        return tuple(items)
    if kind == 1:
        return list(items)
    if kind == 2:
        return {"k%d" % index: item for index, item in enumerate(items)}
    if kind == 3:
        return frozenset(item for item in items if _hashable(item))
    return Box(items)


def _mutate(rng: random.Random, pool: List[Any]) -> None:
    """生成した値の中の、変わり得る object の状態を変える（それぞれ確率 1/2。何も変えないこともある）。

    enum の member が値の中にあれば、確率 1/2 で名前を変える（codec の set の並び順が変わり得る）。
    """

    for item in pool:
        if rng.random() < 0.5:
            continue
        # 大きさを変えない変更（1 桁の整数を別の 1 桁へ）: byte の量では区別できない違い
        if isinstance(item, Keyed):
            item.key = _other_digit(rng, item.key)
        elif isinstance(item, (Box, Marked, Record)):
            item.value = _other_digit(rng, item.value)
    members = [item for item in pool if isinstance(item, (Level, Mode))]
    if members and rng.random() < 0.5:
        target = rng.choice(members)
        target._name_ = "Y" if target._name_ != "Y" else "B"


def _other_digit(rng: random.Random, current: Any) -> Any:
    choices = [digit for digit in range(10) if digit != current]
    return rng.choice(choices)


@pytest.mark.parametrize("seed", range(300))
def test_random_kinds_with_changes_after_warming_follow_the_body(seed, restore_enum_names):
    rng = random.Random(seed)
    pool: List[Any] = []
    where = rng.choice(WHERE)
    problems, fingerprints, _hits = _warm_change_and_compare(
        lambda: _value(rng, pool, rng.randrange(1, 4)), lambda _value: _mutate(rng, pool), where,
    )
    assert fingerprints == [], (seed, fingerprints)
    assert problems == [], (seed, problems)

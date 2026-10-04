# -*- coding: utf-8 -*-
"""snapshot の再利用の token の権限（Issue #219 PR-219-B レビュー 5）。

保証:

* token（`ElidedSemanticValue`）を扱えるのは、単一の読みが自分の hook で置いた token を、その読みの内部の
  witness の凍結が受け取るときだけ。
* 通常の codec の入口（`SnapshotFingerprintCodec.freeze` / `digest` / `AnalysisSnapshot.create`）は、呼ぶ側の
  文脈（読みの最中・入力の code の中・入れ子・例外の後）によらず token を拒む（main と同じ `TypeError`）。
* 入力が作った token（同じ型の object）は、読みが置いた token ではない: どこに現れても main と同じに扱う。

oracle は `test_issue219_single_read` と同じ（同じ factory から作った別の初期状態を mode ごとに用意し、同じ手順を
流して、受理・例外・読みの回数と順・全 field・fingerprint を比べる）。producer は入力の code が走る入口
（`stable_key`・`json_items`）から通常の codec・再利用の入口へ入る。ここの値はすべて closed か pending でない
（C-RS2 の sealing の差は入らない）。
"""

from __future__ import annotations

import contextvars
import enum
import random
import threading
from typing import Any, List

import pytest

from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core import json_encoding
from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY
from scripts.function_tracer_pcode.core.budget_policy import (
    NO_SUBSTITUTION,
    LeafSubstitution,
    active_serialization_work,
    substituting_leaves,
)
from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot, SnapshotFingerprintCodec
from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import ElidedSemanticValue, snapshot_reuse_scope
from scripts.function_tracer_pcode.tests.unit import test_issue219_single_read as oracle
from scripts.function_tracer_pcode.tests.unit._publication import published
from scripts.function_tracer_pcode.tests.unit.test_issue219_single_read import (  # noqa: F401 - fixtures
    _clean_ledger_stack,
    _witness_hash_mode,
)


def _closed() -> Expression:
    return published(Expression.binary_op(
        "INT_ADD", Expression.parameter("b", 1, size=4), Expression.constant(3, size=4)))


def _attempt(call) -> Any:
    """入力の code が例外を捕まえて、結果を自分の値に使う（受理されたか・拒まれたか・その文面）。"""

    try:
        out = call()
    except (TypeError, ValueError) as failure:
        return ("rejected", type(failure).__name__, str(failure))
    return ("accepted", type(out).__name__)


class _Recorder:
    """入力の code が見たものを記録する（手順の後の状態として mode の間で比べる）。"""

    def __init__(self) -> None:
        self.calls: List[Any] = []

    def observe(self) -> Any:
        return tuple(self.calls)


class FreezesToken(_Recorder):
    """`stable_key` が通常の `freeze` に token を渡し、捕まえた結果を key に使う（レビュー 5 の反例）。"""

    def stable_key(self):
        seen = _attempt(lambda: SnapshotFingerprintCodec.freeze(ElidedSemanticValue(_closed())))
        self.calls.append(seen)
        return ("freezes_token", len(self.calls), seen)


class DigestsToken(FreezesToken):
    """`stable_key` が通常の `digest` に token を含む値を渡す。"""

    def stable_key(self):
        seen = _attempt(lambda: SnapshotFingerprintCodec.digest(("x", ElidedSemanticValue(_closed()))))
        self.calls.append(seen)
        return ("digests_token", len(self.calls), seen)


class CreatesWithToken(FreezesToken):
    """`stable_key` が `AnalysisSnapshot.create` に token を含む field を渡す。"""

    def stable_key(self):
        seen = _attempt(lambda: AnalysisSnapshot.create(("id",), {"v": ElidedSemanticValue(_closed())}))
        self.calls.append(seen)
        return ("creates_with_token", len(self.calls), seen)


class ReturnsToken(FreezesToken):
    """`stable_key` が token そのものを key として返す（入力が作った token は読みが置いた token ではない）。"""

    def stable_key(self):
        self.calls.append("returned")
        return ElidedSemanticValue(_closed())


class RaisesFromCodec(FreezesToken):
    """`stable_key` が token を通常の codec に渡し、例外を捕まえずに上げる（例外の後の復帰）。"""

    def stable_key(self):
        self.calls.append("raising")
        SnapshotFingerprintCodec.freeze(ElidedSemanticValue(_closed()))
        return ("unreachable_in_main",)


class NestedSnapshot(FreezesToken):
    """`stable_key` が再利用の入口（`from_function_analysis`）へ再入し、その fingerprint を key に使う。"""

    def __init__(self) -> None:
        super().__init__()
        self.inner = oracle.State(["plain"], pending=False).analysis

    def stable_key(self):
        seen = _attempt(lambda: AnalysisSnapshot.from_function_analysis(self.inner).semantic_fingerprint)
        self.calls.append(seen)
        return ("nested", len(self.calls), seen[0])


class WalksWithActiveWork(_Recorder):
    """`json_items` が今の直列化の作業量で closed な値を LEGACY に作る（入れ子の walk は token を受け取らない）。"""

    def json_items(self):
        work = active_serialization_work()
        built = RESULT_JSON_POLICY.materialize(_closed(), budget=work) if work is not None else None
        seen = ("token" if isinstance(built, ElidedSemanticValue) else type(built).__name__)
        self.calls.append(seen)
        yield "built", seen


class FreezesTokenFromJsonItems(_Recorder):
    """`json_items`（意味の view の walk の中）が通常の `freeze` に token を渡す。"""

    def json_items(self):
        seen = _attempt(lambda: SnapshotFingerprintCodec.freeze(ElidedSemanticValue(_closed())))
        self.calls.append(seen)
        yield "seen", seen


class WalksInAnotherThread(_Recorder):
    """`json_items` が今の作業量を別の thread へ渡し、そこで closed な値を LEGACY に作る（別 thread の walk は
    外側の walk の中に見えない: 置き換えの許可は作業量の object に付いていてはならない）。"""

    def json_items(self):
        work = active_serialization_work()
        holder: List[Any] = []

        def build() -> None:
            try:
                holder.append(RESULT_JSON_POLICY.materialize(_closed(), budget=work))
            except Exception as failure:  # noqa: BLE001 - test oracle: record what the thread saw
                holder.append(failure)

        thread = threading.Thread(target=build)
        thread.start()
        thread.join()
        built = holder[0] if holder else None
        seen = "token" if isinstance(built, ElidedSemanticValue) else type(built).__name__
        self.calls.append(seen)
        yield "built", seen


class _Mine(LeafSubstitution):
    """入力の code が自分で効かせる置き換え（式の葉を文字列に置く）。"""

    __slots__ = ()

    def __leaf_substitute__(self, leaf, size):
        return "mine" if type(leaf) is Expression else NO_SUBSTITUTION


class ArmsItsOwnSubstitution(_Recorder):
    """`json_items` が公開の `substituting_leaves` で自分の置き換えを効かせ、作った値を記録する（読みの置き換えが
    入れ子の呼び出しを拒んだり、入力の置き換えと混ざったりしない）。"""

    def json_items(self):
        work = active_serialization_work()
        seen = _attempt_value(lambda: _arm_and_build(work))
        self.calls.append(seen)
        yield "seen", seen


def _arm_and_build(work: Any) -> Any:
    with substituting_leaves(work, _Mine()):
        built = RESULT_JSON_POLICY.materialize(_closed(), budget=work)
    return "token" if isinstance(built, ElidedSemanticValue) else repr(built)[:60]


def _attempt_value(call) -> Any:
    try:
        return ("value", call())
    except (TypeError, ValueError) as failure:
        return ("rejected", type(failure).__name__, str(failure))


class WalksInAFreshContext(_Recorder):
    """`json_items` が同じ thread の新しい `contextvars.Context` で closed な値を LEGACY に作る（外側の walk の中に
    見えない walk。置き換えは、それを claim した読みの walk だけが使う: レビュー 5 の監査の反例 A）。"""

    def json_items(self):
        built = contextvars.Context().run(json_encoding.materialize, _closed())
        seen = "token" if isinstance(built, ElidedSemanticValue) else type(built).__name__
        self.calls.append(seen)
        yield "built", seen


class OpensItsOwnScope(NestedSnapshot):
    """`stable_key` が自分で再利用の scope を開き、その中で再入する（入れ子の scope は外側の読みに影響しない）。"""

    def stable_key(self):
        with snapshot_reuse_scope():
            seen = _attempt(lambda: AnalysisSnapshot.from_function_analysis(self.inner).semantic_fingerprint)
        self.calls.append(seen)
        return ("own_scope", len(self.calls), seen[0])


PRODUCERS = {
    "walks_in_a_fresh_context": WalksInAFreshContext,
    "opens_its_own_scope": OpensItsOwnScope,
    "walks_in_another_thread": WalksInAnotherThread,
    "arms_its_own_substitution": ArmsItsOwnSubstitution,
    "freezes_token": FreezesToken,
    "digests_token": DigestsToken,
    "creates_with_token": CreatesWithToken,
    "returns_token": ReturnsToken,
    "raises_from_codec": RaisesFromCodec,
    "nested_snapshot": NestedSnapshot,
    "walks_with_active_work": WalksWithActiveWork,
    "freezes_token_from_json_items": FreezesTokenFromJsonItems,
}


@pytest.fixture(autouse=True)
def _producers(monkeypatch):
    for name, factory in PRODUCERS.items():
        monkeypatch.setitem(oracle.PRODUCERS, name, factory)
    yield


def _factory(producer: str, where: str):
    def factory() -> oracle.State:
        state = oracle.State(["plain", producer], pending=False)
        value = state.analysis.return_abi_facts["p1"]
        if where == "analysis_scope_key":
            state.analysis.return_abi_facts.pop("p1")
            state.analysis.analysis_scope_key = ("scope", value)
        return state
    return factory


@pytest.mark.parametrize("producer", sorted(PRODUCERS))
@pytest.mark.parametrize("where", ["return_abi_facts", "analysis_scope_key"])
def test_input_code_that_calls_the_codec_sees_the_same_answer_as_main(producer, where, monkeypatch):
    """入力の code の入口（`stable_key` / `json_items`）から通常の codec・再利用の入口へ入る: on / off / main で
    受理・例外・読みの回数と順・全 field・fingerprint が同じ。2 回目の呼び出しは 1 回目の後の状態から（例外の後の
    復帰と hit の経路を含む）。"""

    steps = [("call", "canonical"), ("call", "canonical"), ("mutate", "mutate_plain"), ("call", "canonical")]
    oracle._compare(_factory(producer, where), steps, monkeypatch)


def test_a_token_the_input_made_in_the_snapshot_id_is_rejected_as_in_main(monkeypatch):
    """入力が作った token が `snapshot_id` に直接ある（`stable_key` を経ない）: main と同じ `TypeError`。"""

    def factory() -> oracle.State:
        state = oracle.State(["plain"], pending=False)
        state.analysis.binary_id = ElidedSemanticValue(_closed())
        return state

    steps = [("call", "canonical"), ("call", "canonical")]
    oracle._compare(factory, steps, monkeypatch)


def test_after_a_read_the_normal_codec_rejects_a_token_in_every_mode(monkeypatch):
    """読みが例外で抜けた後も、同じ thread の通常の codec は token を拒む（共有の許可が残らない）。"""

    for mode in ("on", "off"):
        state = _factory("raises_from_codec", "analysis_scope_key")()
        monkeypatch.setattr(oracle.snapshot_reuse, "_SNAPSHOT_REUSE_ENABLED", mode == "on")
        with oracle.pair_failure_scope(("pair", 1), None), oracle.budget_policy_scope(oracle.BudgetPolicy()), \
                oracle.snapshot_reuse_scope():
            with pytest.raises(TypeError):
                AnalysisSnapshot.from_function_analysis(state.analysis)
        with pytest.raises(TypeError, match="opaque object ElidedSemanticValue"):
            SnapshotFingerprintCodec.freeze(ElidedSemanticValue(_closed()))


@pytest.mark.parametrize("seed", range(40))
def test_random_combinations_of_input_code_have_the_same_answers_as_main(seed, monkeypatch):
    """token・codec・再入・入れ子・別 thread・例外の producer と、副作用のある既存の producer を混ぜ、置き場所
    （意味の view / `snapshot_id`）と手順（生成経路・入れ子の直列化・書き換え）を無作為に組む。"""

    rng = random.Random(1000 + seed)
    pool = sorted(PRODUCERS) + ["counting", "counting_key", "writes_note", "plain"]
    chosen = rng.sample(pool, rng.randint(1, 3))
    in_id = [name for name in chosen if rng.random() < 0.5]

    def factory() -> oracle.State:
        state = oracle.State(["plain"] + chosen, pending=False)
        moved = tuple(state.analysis.return_abi_facts.pop("p%d" % (1 + chosen.index(name))) for name in in_id)
        if moved:
            state.analysis.analysis_scope_key = ("scope", moved)
        return state

    oracle._compare(factory, oracle._random_steps(rng), monkeypatch)


# ---------------------------------------------------------------------------
# レビュー 5 の独立した監査の反例
# ---------------------------------------------------------------------------


class SmugglesWhatItBuilt(_Recorder):
    """`json_items` が新しい context で作った値を、読みが view の後に読む `analysis_scope_key` へ置く（反例 A2: 置いた
    token が `snapshot_id` に入れば、展開されずに返る）。"""

    def __init__(self) -> None:
        super().__init__()
        self.target: Any = None

    def json_items(self):
        built = contextvars.Context().run(json_encoding.materialize, _closed())
        self.calls.append(type(built).__name__)
        if self.target is not None:
            self.target.analysis_scope_key = ("scope", built)
        yield "seen", 1


def test_a_value_built_in_a_fresh_context_and_kept_in_the_snapshot_id_is_the_same_as_main(monkeypatch):
    monkeypatch.setitem(oracle.PRODUCERS, "smuggles", SmugglesWhatItBuilt)

    def factory() -> oracle.State:
        state = oracle.State(["plain", "smuggles"], pending=False)
        state.analysis.return_abi_facts["p1"].target = state.analysis
        return state

    oracle._compare(factory, [("call", "canonical"), ("call", "canonical")], monkeypatch)


class _Leaves(LeafSubstitution):
    __slots__ = ()

    def __leaf_substitute__(self, leaf, size):
        return "mine" if type(leaf) is Expression else NO_SUBSTITUTION


class LeavesItsSubstitutionArmed(_Recorder):
    """`json_items` が generator の中で置き換えを効かせ、generator を途中で止めたまま返す（`with` が LIFO で
    抜けない: 反例 B）。読みの `with` が抜けても、外すのは自分の entry だけ。"""

    def __init__(self) -> None:
        super().__init__()
        self.held: Any = None

    def json_items(self):
        work = active_serialization_work()

        def armed():
            with substituting_leaves(work, _Leaves()):
                yield 1

        self.held = armed()
        next(self.held)
        self.calls.append("armed")
        yield "armed", 1


class HoldsAClosedValue(_Recorder):
    """LEGACY の表現に closed な式を持つ record（`snapshot_id` の中で codec が作る）。"""

    def json_items(self):
        self.calls.append("read")
        yield "e", _closed()


def test_a_substitution_left_armed_by_a_suspended_generator_behaves_as_in_main(monkeypatch):
    monkeypatch.setitem(oracle.PRODUCERS, "leaves_armed", LeavesItsSubstitutionArmed)
    monkeypatch.setitem(oracle.PRODUCERS, "holds_closed", HoldsAClosedValue)

    def factory() -> oracle.State:
        state = oracle.State(["plain", "leaves_armed", "holds_closed"], pending=False)
        state.analysis.analysis_scope_key = ("scope", state.analysis.return_abi_facts.pop("p2"))
        return state

    oracle._compare(factory, [("call", "canonical")], monkeypatch)


class SwapsTheFunctionRef(_Recorder):
    """`json_items`（`function_ref` より後に読まれる）が、`function_ref` を同じ値を包む **新しい** 入力の
    `ElidedSemanticValue` に置き換える（反例: witness が型で token を見分けると、別の object を同じと見て hit し、
    前の呼び出しの object を返す）。"""

    def __init__(self) -> None:
        super().__init__()
        self.target: Any = None
        self.inner = object()
        self.made: List[Any] = []

    def json_items(self):
        token = ElidedSemanticValue(self.inner)
        self.made.append(token)
        self.target.function_ref = token
        # 意味の値は呼び出しの間で同じ（witness の残りは等しい: 違いは `function_ref` の object だけ）
        yield "swapped", 1


@pytest.mark.parametrize("mode", ["on", "off", "main"])
def test_an_input_object_of_the_token_type_is_compared_by_identity_not_as_a_token(mode, monkeypatch):
    """各呼び出しが返す `diagnostic_refs["function_ref"]` は、その呼び出しの読みが見た object（main と同じ）。"""

    monkeypatch.setattr(oracle.snapshot_reuse, "_SNAPSHOT_REUSE_ENABLED", mode == "on")
    state = oracle.State(["plain"], pending=False)
    analysis = state.analysis
    original = analysis.function_ref
    producer = SwapsTheFunctionRef()
    producer.target = analysis
    analysis.return_abi_facts["p9"] = producer
    seen = []
    with oracle.pair_failure_scope(("pair", 1), None), oracle.budget_policy_scope(oracle.BudgetPolicy()), \
            oracle.snapshot_reuse_scope():
        for _ in range(3):
            analysis.function_ref = original
            snapshot = (AnalysisSnapshot._build_from_function_analysis(analysis) if mode == "main"
                        else AnalysisSnapshot.from_function_analysis(analysis))
            seen.append(producer.made.index(snapshot.diagnostic_refs["function_ref"]))
        counts = oracle.snapshot_reuse_metrics().get("counts", {})
    # 1 回の呼び出しで `json_items` は 2 回走る（view の walk と codec）: main でも返るのは各呼び出しの 1 つ目
    assert seen == [0, 2, 4]
    assert counts.get("hits", 0) == 0


class SetsTheSameFunctionRef(_Recorder):
    """`SwapsTheFunctionRef` と同じ置き場所・同じ意味の値で、毎回 **同じ** object を置く（陽性の対照）。"""

    def __init__(self, same: Any) -> None:
        super().__init__()
        self.target: Any = None
        self.same = same

    def json_items(self):
        self.target.function_ref = self.same
        yield "swapped", 1


def test_the_same_function_ref_object_does_hit_so_the_identity_test_can_fail():
    """陽性の対照: 同じ object を毎回置けば on は hit する（上の test は hit し得る形で、hit しないことを確かめている）。"""

    state = oracle.State(["plain"], pending=False)
    analysis = state.analysis
    same = ElidedSemanticValue(object())
    producer = SetsTheSameFunctionRef(same)
    producer.target = analysis
    analysis.return_abi_facts["p9"] = producer
    original = analysis.function_ref
    with oracle.pair_failure_scope(("pair", 1), None), oracle.budget_policy_scope(oracle.BudgetPolicy()), \
            oracle.snapshot_reuse_scope():
        for _ in range(3):
            analysis.function_ref = original
            snapshot = AnalysisSnapshot.from_function_analysis(analysis)
            assert snapshot.diagnostic_refs["function_ref"] is same
        counts = oracle.snapshot_reuse_metrics()["counts"]
    assert counts["hits"] == 2


class _Unencodable(enum.Enum):
    """値が JSON にできない（`frozenset`）enum: codec の写しは通るが、fingerprint の JSON にできない。"""

    SET = frozenset({1})


def test_a_value_the_fingerprint_json_cannot_write_raises_the_same_error_as_main(monkeypatch):
    def factory() -> oracle.State:
        state = oracle.State(["plain"], pending=False)
        state.analysis.analysis_scope_key = ("scope", _Unencodable.SET)
        return state

    oracle._compare(factory, [("call", "canonical")], monkeypatch)

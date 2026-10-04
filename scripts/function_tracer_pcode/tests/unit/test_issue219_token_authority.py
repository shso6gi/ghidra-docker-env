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

from typing import Any, List

import pytest

from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY
from scripts.function_tracer_pcode.core.budget_policy import active_serialization_work
from scripts.function_tracer_pcode.proof.obligations.snapshot import AnalysisSnapshot, SnapshotFingerprintCodec
from scripts.function_tracer_pcode.proof.obligations.snapshot_reuse import ElidedSemanticValue
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


PRODUCERS = {
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

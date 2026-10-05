# -*- coding: utf-8 -*-
"""意味の view を直接呼んでよいかの判定（`snapshot._view_returns_its_walk`、Issue #219 PR-219-B レビュー 6）。

単一の読みは、view が owner の定義のままなら `_materialize` を直接呼び、置き換えをその walk へ引数で渡す。
直接呼ぶ経路が飛ばす引き当て（`getattr` の view・`self._materialize`・`RESULT_JSON_POLICY.materialize`）の
どれかを置き換えると、main とは違う呼び出しになる・置き換えが owner の外の code へ渡る。各置き換えで、
on / off / main の全 field・fingerprint・入力の code の観測が同じで、置き換えた code が置き換え（hook）を
受け取らないことを確かめる。置き換えは「main と違う値を返す」ので、判定を外せば on / off が main と食い違う。
"""

from __future__ import annotations

from typing import Any, List

import pytest

from scripts.function_tracer_pcode.core import analysis as analysis_module
from scripts.function_tracer_pcode.core import json_encoding
from scripts.function_tracer_pcode.core.budget_policy import LeafSubstitution
from scripts.function_tracer_pcode.tests.unit import test_issue219_single_read as oracle
from scripts.function_tracer_pcode.tests.unit.test_issue219_single_read import (  # noqa: F401 - fixtures
    _clean_ledger_stack,
    _witness_hash_mode,
)

FunctionReturnAnalysis = analysis_module.FunctionReturnAnalysis
ORIGINAL_VIEW = FunctionReturnAnalysis.__dict__["semantic_snapshot_dict"]
ORIGINAL_MATERIALIZE = FunctionReturnAnalysis.__dict__["_materialize"]
STEPS = [("call", "canonical"), ("call", "canonical"), ("mutate", "mutate_plain"), ("call", "canonical")]


def _marked(fields: Any) -> Any:
    out = dict(fields)
    out["function_name"] = "replaced-view"
    return out


def _view(self):
    return _marked(ORIGINAL_VIEW(self))


def _materialize(self, *, include_derived_proof: bool, leaf_substitution: Any = None):
    assert leaf_substitution is None, "a replaced _materialize must never receive the read's hook"
    return _marked(ORIGINAL_MATERIALIZE(self, include_derived_proof=include_derived_proof))


def _factory() -> oracle.State:
    return oracle.State(["plain"], pending=False)


def test_the_unreplaced_view_is_called_directly_with_the_hook(monkeypatch):
    """陽性対照: 何も置き換えなければ、on は view の walk に hook を渡す（下の test が判定で止まったことの対照）。"""

    seen: List[bool] = []
    original = json_encoding.JsonEncodingPolicy.__dict__["materialize"]
    from scripts.function_tracer_pcode.proof.obligations import snapshot

    real = snapshot._view_returns_its_walk

    def spy(analysis, view):
        seen.append(real(analysis, view))
        return seen[-1]

    monkeypatch.setattr(snapshot, "_view_returns_its_walk", spy)
    assert json_encoding.JsonEncodingPolicy.__dict__["materialize"] is original
    oracle._compare(_factory, STEPS, monkeypatch)
    assert seen and all(seen)


@pytest.mark.parametrize("where", ["instance", "class"])
@pytest.mark.parametrize("name", ["semantic_snapshot_dict", "_materialize"])
def test_a_replaced_view_is_not_called_directly(name, where, monkeypatch):
    replacement = _view if name == "semantic_snapshot_dict" else _materialize
    if where == "class":
        monkeypatch.setattr(FunctionReturnAnalysis, name, replacement)
        factory = _factory
    else:
        def factory() -> oracle.State:
            state = _factory()
            state.analysis.__dict__[name] = replacement.__get__(state.analysis)
            return state
    oracle._compare(factory, STEPS, monkeypatch)


def test_a_replaced_attribute_lookup_is_not_skipped(monkeypatch):
    """class の `__getattribute__` を置き換えると、main の `getattr` は置き換えた view を返す（直接呼べば飛ばす）。"""

    base = object.__getattribute__

    def lookup(self, name):
        value = base(self, name)
        if name == "semantic_snapshot_dict":
            return lambda: _marked(value())
        return value

    monkeypatch.setattr(FunctionReturnAnalysis, "__getattribute__", lookup)
    oracle._compare(_factory, STEPS, monkeypatch)


@pytest.mark.parametrize("how", ["class_method", "rebound_policy"])
def test_a_replaced_walk_entry_never_receives_the_hook(how, monkeypatch):
    """`_materialize` が引く walk の入口を置き換えると、置き換えた code は hook を受け取らない（main と同じ呼び出し）。"""

    received: List[str] = []
    original = json_encoding.JsonEncodingPolicy.__dict__["materialize"]

    def entry(self, source, *, budget=None, counted=False, leaf_substitution=None):
        received.append(type(leaf_substitution).__name__)
        if isinstance(leaf_substitution, LeafSubstitution):
            # 受け取った hook で token を作れてしまう（判定が外れたときの反例）
            leaf_substitution.__placed_values__()
        return _marked(original(self, source, budget=budget, counted=counted))

    if how == "class_method":
        monkeypatch.setattr(json_encoding.JsonEncodingPolicy, "materialize", entry)
    else:
        class _Policy(json_encoding.JsonEncodingPolicy):
            materialize = entry

        monkeypatch.setattr(analysis_module, "RESULT_JSON_POLICY", _Policy())
    oracle._compare(_factory, STEPS, monkeypatch)
    assert received and set(received) == {"NoneType"}

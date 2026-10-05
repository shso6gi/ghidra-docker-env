# -*- coding: utf-8 -*-
"""置いた token を token として扱う **位置** の規則（Issue #219 PR-219-B、レビュー 6）。

単一の読みの置き換えが token を置くのは、意味の view の walk の葉だけ。だから token として凍結・比較・展開して
よいのは意味の値（`semantic_fields` / `retained_form` の `held_fields`）の位置だけで、`snapshot_id`・診断の参照
（`diagnostic_refs`）に同じ object が現れても、置いた object だという理由で token として扱わない:

* `frozen_fingerprint_payload` は `snapshot_id` を許可無しで凍結する（置いた token も opaque として拒む）。token が
  無い入力では `_freeze_unmetered(fingerprint_payload(...))` と同じ値・同じ例外
* 再利用の witness は（hash を定数にした `collide` でも: 比べ方だけで決まる）`parts`（`snapshot_id` の digest・診断の参照を含む）を token を見ずに比べ、`fields` でだけ
  token を「同じ値の token」として比べる（陽性対照: `fields` の token は別 object でも同じ値なら等しい）
"""

from __future__ import annotations

from typing import Any

import pytest

from scripts.function_tracer_pcode.core.budget_policy import BudgetPolicy, budget_policy_scope, serialization_scope
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY
from scripts.function_tracer_pcode.proof.obligations import snapshot_reuse as reuse
from scripts.function_tracer_pcode.proof.obligations.snapshot import (
    SNAPSHOT_EXTRACTION_SCHEMA_VERSION,
    SnapshotFingerprintCodec,
    fingerprint_payload,
    frozen_fingerprint_payload,
    placed_tokens_of,
)
from scripts.function_tracer_pcode.tests.unit._publication import published
from scripts.function_tracer_pcode.tests.unit.test_issue219_single_read import (  # noqa: F401 - fixtures
    _witness_hash_mode,
)


def _closed(value: int = 3) -> Expression:
    return published(Expression.binary_op(
        "INT_ADD", Expression.parameter("b", 1, size=4), Expression.constant(value, size=4)))


class _Record:
    def __init__(self, **fields: Any) -> None:
        self.fields = fields

    def json_items(self):
        yield from self.fields.items()


def _placed(expr: Expression):
    """読みの hook に walk 1 回で token を置かせる（hook・置いた token・許可）。"""

    hook = reuse._ReadHook(elide=True)
    with budget_policy_scope(BudgetPolicy()):
        with serialization_scope(site="t", target_parts=("t",)) as work:
            built = RESULT_JSON_POLICY.materialize(_Record(e=expr), budget=work, leaf_substitution=hook)
    token = built["e"]
    assert type(token) is reuse.ElidedSemanticValue
    placed = placed_tokens_of(hook)
    assert placed.holds(token)
    return hook, token, placed


def _outcome(call) -> Any:
    try:
        return ("value", call())
    except (TypeError, ValueError) as failure:
        return ("rejected", type(failure).__name__, str(failure))


@pytest.mark.parametrize("identity, fields", [
    (("fn", 1), {"a": 1, "b": [1, 2.5, None]}),
    ({"k": (1, 2)}, {"nested": {"x": "y"}}),
    (("fn", object()), {"a": 1}),
    (("fn", 1), {"bad": object()}),
    (("fn", frozenset({1, 2})), {"s": {3, 4}}),
])
def test_the_positional_freeze_equals_the_plain_codec_without_tokens(identity, fields):
    expected = _outcome(lambda: SnapshotFingerprintCodec._freeze_unmetered(
        fingerprint_payload(identity, fields, SNAPSHOT_EXTRACTION_SCHEMA_VERSION)))
    _hook, _token, placed = _placed(_closed())
    for capability in (None, placed):
        assert _outcome(lambda: frozen_fingerprint_payload(
            identity, fields, SNAPSHOT_EXTRACTION_SCHEMA_VERSION, capability)) == expected


def test_a_placed_token_in_the_snapshot_id_is_rejected_like_any_opaque_value():
    _hook, token, placed = _placed(_closed())
    stranger = reuse.ElidedSemanticValue(token.value)
    placed_in_id = _outcome(lambda: frozen_fingerprint_payload(
        ("fn", token), {"a": 1}, SNAPSHOT_EXTRACTION_SCHEMA_VERSION, placed))
    unplaced_in_id = _outcome(lambda: frozen_fingerprint_payload(
        ("fn", stranger), {"a": 1}, SNAPSHOT_EXTRACTION_SCHEMA_VERSION, placed))
    assert placed_in_id[:2] == ("rejected", "TypeError") and placed_in_id == unplaced_in_id
    # 陽性対照: 意味の値の位置では、置いた token は写しにそのまま置かれる（置いていない同じ型の object は拒む）
    frozen = frozen_fingerprint_payload(("fn", 1), {"e": token}, SNAPSHOT_EXTRACTION_SCHEMA_VERSION, placed)
    assert frozen[2] == (("e", token),)
    assert _outcome(lambda: frozen_fingerprint_payload(
        ("fn", 1), {"e": stranger}, SNAPSHOT_EXTRACTION_SCHEMA_VERSION, placed))[:2] == ("rejected", "TypeError")


def test_the_witness_compares_placed_tokens_only_in_the_semantic_fields():
    expr = _closed()
    _hook_a, token_a, placed_a = _placed(expr)
    _hook_b, token_b, placed_b = _placed(expr)
    assert token_a is not token_b and token_a.value is token_b.value
    # 陽性対照: 意味の値の位置なら、別の読みが置いた同じ値の token は同じ（hit し得る）
    assert reuse._Witness(("p",), (token_a,), placed_a) == reuse._Witness(("p",), (token_b,), placed_b)
    # `parts`（snapshot_id の digest・診断の参照の位置）では token として見ない: 別 object は別
    assert reuse._Witness((token_a,), (), placed_a) != reuse._Witness((token_b,), (), placed_b)
    assert reuse._Witness((reuse._Retained((token_a,)),), (), placed_a) != reuse._Witness(
        (reuse._Retained((token_b,)),), (), placed_b)
    # 置いていない token は意味の値の位置でも token ではない
    stranger = reuse.ElidedSemanticValue(expr)
    assert reuse._Witness(("p",), (token_a,), placed_a) != reuse._Witness(("p",), (stranger,), placed_b)

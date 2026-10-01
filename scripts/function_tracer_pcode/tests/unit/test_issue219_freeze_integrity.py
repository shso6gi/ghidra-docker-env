# -*- coding: utf-8 -*-
"""凍結が commit する状態の整合と、runtime ref の表現の写しの契約（Issue #219 PR-219-A、review round 4）。

凍結の途中では、意味値が抱える生 object の code（runtime ref の `stable_key` / `semantic_key`、
record の `json_items`、宣言型の問い合わせ…）が走り得る。その code が凍結中の値を書き換えたり、
凍結・公開へ入り直したりしても、

* commit する意味 field・snapshot・digest・closure・LEGACY 表現は同じ状態を述べる（食い違う
  状態を VALIDATED として commit しない）
* runtime ref の表現の写しは有限の量と時間で止まり、元の容器と alias を残さず、描画と見積りが
  同じ表現を扱う
* ref の表現を作れないことは凍結の失敗にならない（従来の経路へ戻す）。作るときの失敗は、
  従来どおり直列化したときに同じ型で出る（握り潰さない）

ことを、実際の凍結・直列化・snapshot の経路で確かめる。
"""

from __future__ import annotations

import dataclasses
import signal
from typing import Any

import pytest

from scripts.function_tracer_pcode.core import semantic_freeze
from scripts.function_tracer_pcode.core.errors import FrozenExpressionError, reset_pair_failure_scopes
from scripts.function_tracer_pcode.core.expression import Expression, ExpressionType, estimate_legacy_dict_bytes
from scripts.function_tracer_pcode.core.json_encoding import RESULT_JSON_POLICY, JsonEncodingPolicy, raw
from scripts.function_tracer_pcode.core.render_output import utf8_length
from scripts.function_tracer_pcode.core.semantic_freeze import freeze_expression
from scripts.function_tracer_pcode.core.semantic_lifecycle import serialization_closed
from scripts.function_tracer_pcode.core.semantic_projection import canonical_value_key
from scripts.function_tracer_pcode.core.semantic_snapshot import semantic_projection
from scripts.function_tracer_pcode.tests.unit.test_issue219_serialization_closed import _snapshot_fingerprint_of


@pytest.fixture(autouse=True)
def _clean_ledger_stack():
    reset_pair_failure_scopes()
    yield
    reset_pair_failure_scopes()


def _closed(expr: Expression) -> bool:
    """closed の答え（表現の写しを確定させる入口があればそれを通す）。"""

    seal = getattr(semantic_freeze, "seal_serialization", None)
    return seal(expr) if seal is not None else serialization_closed(expr)


def _written(value: Any) -> int:
    return utf8_length(JsonEncodingPolicy.dumps(RESULT_JSON_POLICY, value))


class _Alarm:
    """有限の時間で止まることを確かめる（止まらなければ test を失敗させる）。"""

    def __init__(self, seconds: int) -> None:
        self.seconds = seconds

    def __enter__(self):
        def _expired(*_args):
            raise AssertionError(f"did not stop within {self.seconds}s")

        self._previous = signal.signal(signal.SIGALRM, _expired)
        signal.alarm(self.seconds)
        return self

    def __exit__(self, *_exc):
        signal.alarm(0)
        signal.signal(signal.SIGALRM, self._previous)


# ---------------------------------------------------------------------------
# 1. callback が凍結中の値を書き換える・入り直す
# ---------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True)
class _HolderRef:
    """表現・identity を作る code が、自分を抱える式（`holder`）を書き換える ref。"""

    key: Any = 0

    def holder(self):
        return self.__dict__.get("_holder")


@dataclasses.dataclass(frozen=True)
class _JsonItemsMutatesTheHolder(_HolderRef):
    def json_items(self):
        node = self.holder()
        if node is not None:
            node.value = 2
        yield "key", self.key


@dataclasses.dataclass(frozen=True)
class _StableKeyMutatesTheHolder(_HolderRef):
    def stable_key(self):
        node = self.holder()
        if node is not None:
            node.value = 2
        return ("holder", self.key)


@dataclasses.dataclass(frozen=True)
class _StableKeyMutatesTheHolderInPlace(_HolderRef):
    """属性の protocol を通らない書き換え（構築中の式の `operands` の list へ足す）。"""

    def stable_key(self):
        node = self.holder()
        if node is not None:
            operands = node.__dict__["operands"]
            if type(operands) is list:
                operands.append(Expression.constant(9, size=4))
        return ("holder", self.key)


@dataclasses.dataclass(frozen=True)
class _StableKeyReentersFreeze(_HolderRef):
    """identity を作る途中で、自分を抱える式を凍結・公開へ入り直させる ref。"""

    def stable_key(self):
        node = self.holder()
        if node is not None:
            from scripts.function_tracer_pcode.core.semantic_freeze import publish

            publish(node)
        return ("holder", self.key)


def _holding(ref_type, *, kind=ExpressionType.CONSTANT, value: Any = 1) -> Expression:
    ref = ref_type(1)
    expr = Expression(kind, value=value, size=4, runtime_ref=ref)
    object.__setattr__(ref, "_holder", expr)
    return expr


def _holding_a_parent(ref_type) -> Expression:
    leaf = Expression.constant(1, size=4)
    parent = Expression.binary_op("INT_ADD", leaf, Expression.constant(2, size=4))
    ref = ref_type(1)
    object.__setattr__(ref, "_holder", parent)
    # 子の ref の code が親（同じ凍結の中の値）を書き換える
    leaf.__dict__["runtime_ref"] = ref
    return parent


def _holding_a_child(ref_type) -> Expression:
    """親の ref の code が、先に派生値を作り終えた子（同じ凍結の中の値）を書き換える。"""

    leaf = Expression.constant(1, size=4)
    ref = ref_type(1)
    object.__setattr__(ref, "_holder", leaf)
    return Expression(ExpressionType.UNARY_OP, operator="INT_NEGATE", operands=[leaf], size=4, runtime_ref=ref)


_CALLBACKS = {
    "stable_key_of_a_parent_mutates_a_child": lambda: _holding_a_child(_StableKeyMutatesTheHolder),
    "json_items_mutates_the_holder": lambda: _holding(_JsonItemsMutatesTheHolder),
    "stable_key_mutates_the_holder": lambda: _holding(_StableKeyMutatesTheHolder),
    "stable_key_of_a_child_mutates_the_parent": lambda: _holding_a_parent(_StableKeyMutatesTheHolder),
    "stable_key_mutates_operands_in_place": lambda: _holding_a_parent(_StableKeyMutatesTheHolderInPlace),
    "stable_key_reenters_publication": lambda: _holding(_StableKeyReentersFreeze),
}


def _consistent(expr: Expression) -> None:
    """VALIDATED な値の意味 field・snapshot・closure・LEGACY 表現が同じ状態を述べる。"""

    from scripts.function_tracer_pcode.core.semantic_snapshot import ordered_semantic_edges

    pending = [expr]
    seen = set()
    while pending:
        node = pending.pop()
        if id(node) in seen:
            continue
        seen.add(id(node))
        assert node.is_frozen
        snapshot = semantic_projection(node)
        if node.expr_type is not ExpressionType.PHI:
            assert snapshot.canonical_value == canonical_value_key(node.value), "snapshot describes another value"
            # 表現が描く子（`operands`）と、digest・snapshot が数えた子（辺）が同じ
            edge_children = tuple(edge.child for edge in ordered_semantic_edges(node) if edge.child is not None)
            assert tuple(node.operands) == edge_children, "the drawn children are not the ones the digests describe"
        for edge in ordered_semantic_edges(node):
            if edge.child is not None:
                # 検証済みの値から検証されていない値へ辿れない
                assert edge.child.is_frozen, "a validated node reaches an unvalidated child"
                pending.append(edge.child)
    if _closed(expr):
        before = expr.to_dict()
        assert expr.to_dict() == before


@pytest.mark.parametrize("label", sorted(_CALLBACKS))
def test_a_callback_during_freeze_never_commits_a_state_its_derived_values_do_not_describe(label):
    """凍結中の callback の書き換え・入り直しは、拒まれるか、整合した状態だけが commit される。"""

    expr = _CALLBACKS[label]()
    try:
        freeze_expression(expr)
    except FrozenExpressionError:
        # 書き換えを内部バグとして拒んだ: 何も commit していない
        assert expr.is_frozen is False
        return
    _consistent(expr)
    if expr.is_frozen and _closed(expr):
        fingerprint = _snapshot_fingerprint_of(expr)
        assert _snapshot_fingerprint_of(expr) == fingerprint


def test_a_validated_value_ignores_a_ref_that_tries_to_mutate_it_when_serialized():
    """凍結後の直列化で ref の code が値を書き換えようとしても、値は動かない（凍結済みの拒否）。"""

    expr = _holding(_JsonItemsMutatesTheHolder)
    try:
        freeze_expression(expr)
    except FrozenExpressionError:
        return
    try:
        expr.to_dict()
    except FrozenExpressionError:
        pass
    assert expr.value == 1
    _consistent(expr)


# ---------------------------------------------------------------------------
# 2. ref の表現を作れない・作ると失敗する
# ---------------------------------------------------------------------------


def _raising(exception_type):
    @dataclasses.dataclass(frozen=True)
    class _Raises:
        key: int = 0

        def json_items(self):
            raise exception_type("the ref cannot be serialized")
            yield  # pragma: no cover

    _Raises.__module__ = __name__
    _Raises.__qualname__ = f"_Raises{exception_type.__name__}"
    return _Raises


_FAILURES = {exc.__name__: exc for exc in (OSError, AssertionError, KeyError, RuntimeError, TypeError, ZeroDivisionError)}


@pytest.mark.parametrize("name", sorted(_FAILURES))
def test_a_ref_that_fails_to_serialize_never_fails_freeze_and_keeps_its_failure(name):
    """表現を作れない ref は凍結を失敗させない。直列化したときの失敗は未凍結の値と同じ型。"""

    ref_type = _raising(_FAILURES[name])
    live = Expression.unknown("u", runtime_ref=ref_type())
    frozen = Expression.unknown("u", runtime_ref=ref_type())

    freeze_expression(frozen)

    assert frozen.is_frozen
    with pytest.raises(Exception) as live_failure:
        live.to_dict()
    with pytest.raises(Exception) as frozen_failure:
        frozen.to_dict()
    assert type(frozen_failure.value) is type(live_failure.value)


# ---------------------------------------------------------------------------
# 3. 表現の写しは有限・alias なし・描画と見積りが同じ表現
# ---------------------------------------------------------------------------


_SHARED: list = []


@dataclasses.dataclass(frozen=True)
class _MutatesAYieldedContainer:
    """先に yield した容器を、後の yield の前に書き換える（walker が数えた後で中身が変わる）。"""

    key: int = 0

    def json_items(self):
        items = [1, 2]
        yield "items", raw(items)
        items.extend(range(10))
        yield "after", self.key


@dataclasses.dataclass(frozen=True)
class _HugeRawContainer:
    """yield した容器を walker が数えた後で大きくする（表現は約 129 kB、数えた量は数 byte）。"""

    key: int = 0

    def json_items(self):
        items: list = ["x"]
        yield "items", raw(items)
        items.extend("x" * 1000 for _ in range(128))
        yield "after", self.key


@dataclasses.dataclass(frozen=True)
class _SelfReferentialRawContainer:
    key: int = 0

    def json_items(self):
        items: list = [1]
        items.append(items)
        yield "items", raw(items)


@dataclasses.dataclass(frozen=True)
class _BytesLeaf:
    key: int = 0

    def json_items(self):
        yield "data", raw(b"abc")


def test_a_container_changed_after_it_was_yielded_is_copied_as_drawn():
    expr = Expression.unknown("u", runtime_ref=_MutatesAYieldedContainer())
    live = Expression.unknown("u", runtime_ref=_MutatesAYieldedContainer())
    freeze_expression(expr)

    first = expr.to_dict()
    assert first == live.to_dict()
    if _closed(expr):
        # 写しは元の容器と alias を持たない: 出力を書き換えても次の出力は動かない
        first["runtime_ref"]["items"].append(99)
        assert expr.to_dict() == live.to_dict()
        assert estimate_legacy_dict_bytes(expr, work=None) == _written(expr.to_dict())


def test_a_copy_never_exceeds_the_capture_limit():
    from scripts.function_tracer_pcode.core.frozen_representation import CAPTURE_MAX_BYTES

    expr = Expression.unknown("u", runtime_ref=_HugeRawContainer())
    freeze_expression(expr)

    assert _written(expr.to_dict()["runtime_ref"]) > CAPTURE_MAX_BYTES
    assert _closed(expr) is False
    assert expr.to_dict() == Expression.unknown("u", runtime_ref=_HugeRawContainer()).to_dict()


def _outcome(call):
    try:
        return ("ok", call())
    except Exception as exc:  # noqa: BLE001 - 未凍結の値と同じ結果かを比べるため、型だけを残す
        return ("raised", type(exc))


def test_a_self_referential_representation_stops_and_is_not_captured():
    expr = Expression.unknown("u", runtime_ref=_SelfReferentialRawContainer())
    live = Expression.unknown("u", runtime_ref=_SelfReferentialRawContainer())
    with _Alarm(20):
        freeze_expression(expr)
        assert _closed(expr) is False
        # 写さなかった ref は従来どおり描く（未凍結の値と同じ結果: ここでは閉路の拒否）
        live_outcome = _outcome(live.to_dict)
        frozen_outcome = _outcome(expr.to_dict)
    assert frozen_outcome[0] == live_outcome[0]
    if live_outcome[0] == "raised":
        assert frozen_outcome[1] is live_outcome[1]


def test_draw_and_estimate_use_the_same_representation_for_a_bytes_leaf():
    """見積りと描画は同じ表現を扱う（完成した表現を raw ref として読み直さない）。"""

    live = Expression.unknown("u", runtime_ref=_BytesLeaf())
    frozen = Expression.unknown("u", runtime_ref=_BytesLeaf())
    freeze_expression(frozen)

    assert frozen.to_dict() == live.to_dict()
    assert estimate_legacy_dict_bytes(frozen, work=None) == estimate_legacy_dict_bytes(live, work=None)

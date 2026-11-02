# -*- coding: utf-8 -*-
"""MEMORY を作り直すとき、出口の値の主張（`PostStateValueRef`）を出口の読み出しの主張に変えない（Issue #284）。

出口の値に具体化した MEMORY（`_attach_materialized_post_state_value_ref`）は、元の読み出しの番地を operand に持つ:
`*p = *q; *q = 7; return *p;` の `*p` の出口の値は、時点 t の `*q` の読み出し（番地 `q`）に
`PostStateValueRef(P)` を付けた node になる。post-state の書き換え（`rewrite_loads_from_effects` など）は MEMORY を
`_memory_expr_with_runtime_location` で作り直し、`_merge_memory_runtime_ref` がこの主張を `CanonicalLocation(P)`
（出口の状態の読み出し）に変えていた。lowering は出口の状態の読み出しを番地（`q`）の位置の出口の値に置き換えるので、
値が「t の `*q`」から「出口の `*q`」（= 7）に変わる（偽 EQ / 偽 NOT_EQ の形）。
"""

from scripts.function_tracer_pcode.analysis.effects import post_state
from scripts.function_tracer_pcode.analysis.effects.expression_forms import _impl__merge_memory_runtime_ref
from scripts.function_tracer_pcode.analysis.effects.models import StoreEffect
from scripts.function_tracer_pcode.core import Expression
from scripts.function_tracer_pcode.core.runtime_refs import (
    CanonicalLocation,
    LocationBaseRef,
    ObservedMemoryReadRef,
    PostStateReadRef,
    PostStateSnapshotRef,
    PostStateValueRef,
)
from scripts.function_tracer_pcode.core.semantic_freeze import publish

PARAMETERS = [{"name": "p", "index": 0, "size": 8}, {"name": "q", "index": 1, "size": 8}]
READ_Q, STORE_P, STORE_Q = 100, 200, 300


def _parameter(name, index):
    return Expression.parameter(name, index, "int *", None, 8, runtime_ref=LocationBaseRef.parameter(name, index=index))


def _location(name, index):
    return CanonicalLocation(base_ref=LocationBaseRef.parameter(name, index=index), offset=0, size=4, steps=())


P = _location("p", 0)
Q = _location("q", 1)


def _read_q():
    return Expression.memory(
        _parameter("q", 1), size=4, read_order_key=READ_Q, runtime_ref=ObservedMemoryReadRef(order_key=READ_Q)
    )


def _effects():
    # f(p, q) { *p = *q; *q = 7; return *p; }
    return [
        StoreEffect(location=P, value=_read_q(), conditions=[], order_key=STORE_P),
        StoreEffect(location=Q, value=Expression.constant(7, 4), conditions=[], order_key=STORE_Q),
    ]


def _materialized_exit_value_of_p():
    """`*p` の出口の値: 時点 READ_Q の `*q`（番地は `q` のまま）に P の出口の値の主張を付けたもの。"""

    return Expression.memory(
        _parameter("q", 1),
        size=4,
        read_order_key=READ_Q,
        runtime_ref=PostStateValueRef(location=P, snapshot_ref=PostStateSnapshotRef.function_return()),
    )


def _lowered_smt(expr, effects):
    lowered = post_state._impl_lower_post_state_expression_for_smt_if_needed(expr, [], effects, PARAMETERS)
    return publish(lowered).to_smt()


def test_rewriting_a_materialized_exit_value_keeps_its_value_claim():
    """負例（修正前に落ちる）: 書き換えた後も出口の値の主張のままで、出口の状態の読み出しにならない。"""

    effects = _effects()
    rewritten = post_state._impl_rewrite_loads_from_effects(
        _materialized_exit_value_of_p(), [], effects, PARAMETERS, max_order_key=READ_Q
    )

    assert isinstance(rewritten.runtime_ref, PostStateValueRef)
    assert rewritten.runtime_ref.location == P
    assert post_state._impl__expression_is_materialized_post_state_value(rewritten)
    assert post_state._impl__expression_symbolic_post_state_location_ref(rewritten) is None


def test_rewriting_a_materialized_exit_value_does_not_change_its_lowered_value():
    """負例（修正前に落ちる）: 値は時点 READ_Q の `*q`（入口の `*q`）。修正前は lowering で出口の `*q`（7）になった。"""

    effects = _effects()
    materialized = _materialized_exit_value_of_p()
    rewritten = post_state._impl_rewrite_loads_from_effects(materialized, [], effects, PARAMETERS, max_order_key=READ_Q)

    expected = publish(_read_q()).to_smt()
    assert _lowered_smt(materialized, effects) == expected
    assert _lowered_smt(rewritten, effects) == expected


def test_a_materialized_exit_value_read_at_its_own_location_still_becomes_an_exit_state_read():
    """正例（精度）: 番地が主張の位置 L そのもの（`*p` の出口の値を `p` の番地で持つ）なら、これまでどおり L の出口の
    状態の読み出しとして扱い、effect から L の出口の値（時点 READ_Q の `*q`）に解決する。

    store は P への 1 つだけにする（`*q = 7` があると、P と Q が重ならないことを示せない場合に解決を拒むのが
    正しい: #282 の別名の規則）。"""

    effects = _effects()[:1]
    at_own_location = Expression.memory(
        _parameter("p", 0),
        size=4,
        runtime_ref=PostStateValueRef(location=P, snapshot_ref=PostStateSnapshotRef.function_return()),
    )
    rewritten = post_state._impl_rewrite_loads_from_effects(at_own_location, [], effects, PARAMETERS)

    assert publish(rewritten).to_smt() == publish(_read_q()).to_smt()
    assert _lowered_smt(rewritten, effects) == publish(_read_q()).to_smt()


def test_a_genuine_exit_state_read_is_still_lowered_to_the_exit_value():
    """正例: 出口の状態の読み出し（`PostStateReadRef(Q)`）は、これまでどおり出口の値（7）に lowering する。"""

    effects = _effects()
    exit_read = Expression.memory(
        _parameter("q", 1),
        size=4,
        runtime_ref=PostStateReadRef(location=Q, snapshot_ref=PostStateSnapshotRef.function_return()),
    )

    assert _lowered_smt(exit_read, effects) == publish(Expression.constant(7, 4)).to_smt()


def test_merging_a_location_never_turns_a_value_claim_into_a_read_claim():
    value_ref = PostStateValueRef(location=P, snapshot_ref=PostStateSnapshotRef.function_return())

    # 同じ位置: 主張をそのまま保つ
    assert _impl__merge_memory_runtime_ref(value_ref, P) is value_ref
    assert _impl__merge_memory_runtime_ref(value_ref, None) is value_ref
    # 別の位置を求められたら、値の主張も読み出しの主張も付けない（時点つきの読み出しに戻る）
    assert _impl__merge_memory_runtime_ref(value_ref, Q) is None


def test_merging_keeps_the_existing_behaviour_for_read_refs():
    """正例: 読み出しの ref（位置なしの観測・出口の状態の読み出し・ref 無し）の扱いは変えない。"""

    observed = ObservedMemoryReadRef(order_key=READ_Q)
    assert _impl__merge_memory_runtime_ref(observed, None) is observed
    assert _impl__merge_memory_runtime_ref(observed, Q).location == Q

    exit_read = PostStateReadRef(location=Q, snapshot_ref=PostStateSnapshotRef.function_return())
    assert _impl__merge_memory_runtime_ref(exit_read, Q) is exit_read
    assert _impl__merge_memory_runtime_ref(exit_read, P).location == P

    assert _impl__merge_memory_runtime_ref(None, Q) == Q
    assert _impl__merge_memory_runtime_ref(None, None) is None

# -*- coding: utf-8 -*-
"""Issue #242: 入口の引数の束縛（`runtime_ref_entry` / 自前の `__init__`）と、review の反例（3 回目）。

入口の引数は、関数の signature の束縛と同じ対応（位置・キーワード・`*args`・キーワード専用・`**kwargs`、
method なら receiver を含む）で注釈の型規則を当てる。呼び出しの形（位置・キーワード・混在）で結果が変わらない
こと、すべての種類の引数が写されること、包みが元の signature を保つこと、入口の注釈がすべて解決できることを
固定する。readonly の反例は、受理された seed / witness の属性（代わりの型の値）を基底型の値で読むこと。
"""

from __future__ import annotations

import dataclasses
import inspect
import types
import typing
from typing import Any, Optional, Tuple

import pytest

from scripts.function_tracer_pcode.core import runtime_ref_record
from scripts.function_tracer_pcode.core.runtime_ref_record import entry_arguments, runtime_ref_entry
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.runtime_refs.locations import CanonicalLocation, LocationBaseRef, LocationStep
from scripts.function_tracer_pcode.core.runtime_refs.readonly import (
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReductionAccumulatorProof,
)
from scripts.function_tracer_pcode.tests.unit.runtime_ref_adversaries import HOOK_CALLS, Liar, LiarStr, view


# ---------------------------------------------------------------------------
# 自前の `__init__`: 位置・キーワード・混在で同じ結果（review の blocker 1）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "call",
    [
        pytest.param(lambda v: CanonicalLocation(v("stackframe")), id="positional"),
        pytest.param(lambda v: CanonicalLocation(base_param=v("stackframe")), id="keyword"),
        pytest.param(lambda v: CanonicalLocation(v("p"), v(4), size=v(8), steps=(LocationStep("offset", v(4)),)), id="mixed"),
        pytest.param(lambda v: CanonicalLocation(v("p"), v(4), v(8)), id="positional3"),
        pytest.param(lambda v: CanonicalLocation(v(""), offset=v(0)), id="falsy"),
    ],
)
def test_custom_init_binds_every_call_shape_like_its_signature(call):
    def exact(value):
        return value

    def lying(value):
        return {int: Liar, str: LiarStr}[type(value)](value)

    twin = call(exact)
    HOOK_CALLS.clear()
    built = call(lying)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert view(built) == view(twin)


def test_custom_init_keeps_its_signature():
    original = runtime_ref_record._WRAPPERS[CanonicalLocation.__init__]
    assert inspect.signature(CanonicalLocation.__init__) == inspect.signature(original)
    assert CanonicalLocation.__init__.__wrapped__ is original


# ---------------------------------------------------------------------------
# 引数の種類（非 blocker: `*args` の後のキーワード専用の引数を落とさない）
# ---------------------------------------------------------------------------


def _every_kind(a: int, /, b: str, *rest: int, c: bool, d: Optional[int] = None, **more: str):
    return (a, b, rest, c, d, more)


def test_every_parameter_kind_is_mapped():
    entry = runtime_ref_entry(_every_kind)
    HOOK_CALLS.clear()
    result = entry(Liar(1), LiarStr("b"), Liar(2), Liar(3), c=Liar(1), d=Liar(4), x=LiarStr("y"))
    assert HOOK_CALLS == {}
    assert view(result) == view((1, "b", (2, 3), True, 4, {"x": "y"}))
    assert [type(item) for item in result[2]] == [int, int]
    assert result[3] is True
    # 位置専用の名前をキーワードで渡すと `**more` に入る（signature の束縛と同じ）
    assert entry(1, b="b", c=False, a=LiarStr("z"))[5] == {"a": "z"}
    assert type(entry(1, b="b", c=False, a=LiarStr("z"))[5]["a"]) is str


def test_unannotated_and_any_parameters_are_left_alone():
    def function(x, y: Any, z: int):
        return (x, y, z)

    entry = runtime_ref_entry(function)
    lied = Liar(5)
    result = entry(lied, lied, lied)
    assert result[0] is lied and result[1] is lied and type(result[2]) is int


def test_entries_keep_the_signature_annotations_and_wrapped_function():
    entry = runtime_ref_entry(_every_kind)
    assert inspect.signature(entry) == inspect.signature(_every_kind)
    assert entry.__wrapped__ is _every_kind
    assert entry.__annotations__ == _every_kind.__annotations__
    assert entry.__name__ == "_every_kind" and entry.__module__ == __name__
    factory = LocationBaseRef.__dict__["parameter"].__func__
    assert inspect.signature(factory) == inspect.signature(factory.__wrapped__)
    assert list(inspect.signature(LocationBaseRef.parameter).parameters) == ["name", "index", "owner_program_id", "owner_entry_offset"]


def test_entries_must_wrap_plain_functions():
    with pytest.raises(TypeError):
        runtime_ref_entry(classmethod(_every_kind))


def test_every_entry_plan_resolves():
    """入口の注釈はすべて解決できる（最初の呼び出しで例外にならない）。"""

    from scripts.function_tracer_pcode.tests.unit.test_issue242_entry_matrix import _discovered_entry_functions

    functions = _discovered_entry_functions()
    assert functions
    for function in functions:
        plan = runtime_ref_record._entry_plan(function)
        assert len(plan.positional) + len(plan.by_name) + (plan.var_positional is not None) + (plan.var_keyword is not None) >= 1 or not inspect.signature(function).parameters


def test_entry_arguments_rewrites_only_what_changed():
    args = (1, "b")
    kwargs = {"c": True}
    assert entry_arguments(_every_kind, args, kwargs)[0] is args


# ---------------------------------------------------------------------------
# readonly の反例（review の blocker 2）: 受理された seed / witness の属性を基底型の値で読む
# ---------------------------------------------------------------------------


def _term(offset, size):
    return types.SimpleNamespace(
        byte_offset=offset, access_size=size,
        stable_key=lambda: ("readonly_reduction_term", offset, size),
    )


def _witness(count, terms):
    return types.SimpleNamespace(exact_count=count, terms=terms)


def _int(value):
    return value


def _lie(value):
    return Liar(value)


@pytest.mark.parametrize(
    "changes, invoke",
    [
        pytest.param(
            lambda v: dict(seed_terms=(_term(v(0), v(4)), _term(v(4), v(4))), start_index=2, start_offset=8),
            lambda proof: proof.readonly_term_sequence_contract_key(result_size=4),
            id="seed_terms_contract_key",
        ),
        pytest.param(
            lambda v: dict(seed_terms=(_term(v(0), v(0)),), start_index=1, start_offset=4),
            lambda proof: proof.readonly_term_sequence_contract_key(result_size=4),
            id="seed_terms_falsy_size",
        ),
        pytest.param(
            lambda v: dict(
                exact_return_witnesses=(
                    _witness(v(2), (_term(v(0), v(4)), _term(v(4), v(4)))),
                    _witness(v(1), (_term(v(0), v(4)),)),
                ),
                element_size=8, stride=8, index_scale=8,
            ),
            lambda proof: proof.full_terms_for_count_value(1),
            id="exact_witness_prefix",
        ),
        pytest.param(
            lambda v: dict(
                exact_return_witnesses=(_witness(v(0), ()), _witness(v(1), [_term(v(0), v(4))])),
                element_size=8, stride=8, index_scale=8,
            ),
            lambda proof: proof.full_terms_for_count_value(1),
            id="exact_witness_zero_and_list",
        ),
        pytest.param(
            lambda v: dict(lane_terms=[(v(0), v(4)), (v(4), v(4))], stride=8, element_size=8, index_scale=8),
            lambda proof: (proof.loop_var_unit(), proof.loop_body_terms_for_count_value(3)),
            id="lane_terms_list",
        ),
    ],
)
def test_readonly_reads_accepted_seed_and_witness_values_on_base_values(changes, invoke):
    try:
        twin = invoke(_proof_from(changes(_int)))
    except Exception as error:  # 双子が拒む入力は、偽る値でも同じ型の例外（hook は 0 回）
        HOOK_CALLS.clear()
        with pytest.raises(type(error)):
            invoke(_proof_from(changes(_lie)))
        assert HOOK_CALLS == {}
        return
    HOOK_CALLS.clear()
    built = invoke(_proof_from(changes(_lie)))
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert view(built) == view(twin)


def _proof_from(fields):
    base = dict(
        reduction_kind="memory_sum", pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count", count_parameter_index=1,
        limit_expr=Expression.parameter("count", 1, size=4), result_size=4, stride=4, element_size=4, index_scale=4,
    )
    base.update(fields)
    return ReductionAccumulatorProof(**base)


# ---------------------------------------------------------------------------
# 受理した値の reader（`live_values`）
# ---------------------------------------------------------------------------


def test_exact_tree_reads_tuples_and_lists_on_base_values():
    from scripts.function_tracer_pcode.core.live_values import exact_tree

    shared = [Liar(1), (LiarStr("a"), [Liar(2)])]
    HOOK_CALLS.clear()
    result = exact_tree(("k", shared, shared, None))
    assert HOOK_CALLS == {}
    assert view(result) == view(("k", [1, ("a", [2])], [1, ("a", [2])], None))
    assert type(result[1]) is list and type(result[1][1][1][0]) is int
    assert result[1] is result[2]  # 共有は保つ
    exact = ("k", [1, ("a",)])
    assert exact_tree(exact) is exact  # 葉が変わらなければ同じ object
    cyclic = []
    cyclic.append(cyclic)
    assert exact_tree(cyclic) is cyclic
    top = exact_tree([Liar(7), LiarStr("z")])
    assert type(top) is list and [type(item) for item in top] == [int, str] and top == [7, "z"]


def test_ref_layer_items_read_like_tuple_without_subclass_code():
    """`_reading.items` は `tuple(x)` と同じ要素と例外。scalar の subclass は基底型の値で、組み込みの列は基底型の slot で読む。"""

    import collections

    from scripts.function_tracer_pcode.core.runtime_refs._reading import items, optional_items, rows

    HOOK_CALLS.clear()
    element = Liar(1)
    assert items(LiarStr("ab")) == ("a", "b") and items([element])[0] is element  # 要素は変えない（`tuple()` と同じ）
    with pytest.raises(TypeError):
        items(Liar(3))
    with pytest.raises(TypeError):
        items(None)
    assert optional_items(LiarStr("")) == () and optional_items(Liar(0)) == ()
    assert rows([(Liar(1), LiarStr("x"))], 2) == ((1, "x"),)
    with pytest.raises(ValueError):
        rows([(1, 2, 3)], 2)
    assert HOOK_CALLS == {}
    # 組み込みの列でない iterable は置き換える前（`tuple(x)`）と同じく読む
    assert items(iter([1, 2])) == (1, 2) and items(collections.deque([1])) == (1,)
    assert optional_items(x for x in (1, 2)) == (1, 2)
    Pair = collections.namedtuple("Pair", "a b")
    assert items(Pair(1, 2)) == (1, 2) and type(items(Pair(1, 2))) is tuple


# ---------------------------------------------------------------------------
# 独立の敵対的 review（3 回目）の反例: 受理したまま持つ容器・外の object の読み・引数の無い builder・ref でない class
# ---------------------------------------------------------------------------


def _same_without_hooks(build, prepare=None):
    """`build(exact)` と `build(lying)` が同じ結果（型の札つきの view）で、偽る型の code を呼ばない。

    `prepare(v)` を渡すと、入力（偽る値の集合など、作るときに hash する値）は数える前に作り、`build(入力)` を数える。
    """

    if prepare is not None:
        inputs = {}

        def staged(v):
            return build(inputs[v])

        def exact_inputs(value):
            return value

        def lying_inputs(value):
            return {int: Liar, str: LiarStr}[type(value)](value)

        inputs[exact_inputs] = prepare(exact_inputs)
        inputs[lying_inputs] = prepare(lying_inputs)
        return _run_twin(lambda: staged(exact_inputs), lambda: staged(lying_inputs))

    def exact(value):
        return value

    def lying(value):
        return {int: Liar, str: LiarStr}[type(value)](value)

    return _run_twin(lambda: build(exact), lambda: build(lying))


def _run_twin(twin_call, lying_call):
    try:
        twin = twin_call()
    except Exception as error:
        HOOK_CALLS.clear()
        with pytest.raises(type(error)):
            lying_call()
        assert HOOK_CALLS == {}
        return None
    HOOK_CALLS.clear()
    built = lying_call()
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert view(built) == view(twin)
    return built


def test_budget_identity_reads_set_keys_inside_mappings_on_base_values():
    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import ExpansionBudgetTruncation

    built = _same_without_hooks(
        lambda key: ExpansionBudgetTruncation(kind="path_limit", owner_scope_key=key),
        prepare=lambda v: ({frozenset({v("a")}): v("1")},),
    )
    assert built.event_id == ExpansionBudgetTruncation(kind="path_limit", owner_scope_key=({frozenset({"a"}): "1"},)).event_id


@pytest.mark.parametrize("case", ["opcode_list", "mnemonic_tuple", "fresh_binary_id", "budget_surface"])
def test_text_of_accepted_containers_is_read_on_base_values(case):
    from scripts.function_tracer_pcode.core.runtime_refs.call_arguments import AbiArgumentSlotRef, FreshCallArgumentRef
    from scripts.function_tracer_pcode.core.runtime_refs.pcode import PcodeOpRef
    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import ExpansionBudgetTruncation

    builds = {
        "opcode_list": lambda v: PcodeOpRef(address_offset=0x10, opcode=[v("x")]),
        "mnemonic_tuple": lambda v: PcodeOpRef(address_offset=0x10, mnemonic=(v("x"),)),
        "fresh_binary_id": lambda v: FreshCallArgumentRef(
            binary_id=(v("x"),), slot=AbiArgumentSlotRef(ordinal=0), call_site_key=("call", 1, 1), reason="r",
        ),
        "budget_surface": lambda v: ExpansionBudgetTruncation(kind="k", surface=[v("x")]),
    }
    _same_without_hooks(builds[case])


def test_return_ops_with_container_binary_ids_are_ordered_on_base_values():
    from scripts.function_tracer_pcode.core.runtime_refs.pcode import PcodeOpRef

    def op(binary_id, offset):
        return PcodeOpRef(
            address_offset=offset, seq_time=1, seq_order=1, block_index=0, mnemonic="LOAD", binary_id=binary_id,
            function_entry_space="ram", function_entry_offset=0x100, target_space="ram", target_offset=offset,
            opcode=2, local_op_ordinal=0,
        )

    _same_without_hooks(lambda v: _proof_from(dict(return_op_refs=(op((v("B"),), 0x10), op((v("A"),), 0x20)))).return_op_refs)


class _FakeExpr:
    """式のような object（`limit_expr` は注釈が Any）。class の `constant` で定数を作る。"""

    def __init__(self, size):
        self.size = size

    @classmethod
    def constant(cls, value, size):
        return ("const", value, size)


@pytest.mark.parametrize("size", [0, 8])
def test_lowering_reads_the_size_of_an_expression_like_limit_on_base_values(size):
    """引数の無い builder（`lower_to_loop_summary_ref`）が受理した式の属性を読む。"""

    _same_without_hooks(lambda v: _proof_from(dict(limit_expr=_FakeExpr(v(size)))).lower_to_loop_summary_ref())


def test_budget_collector_reads_substitute_records_on_base_values():
    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import ExpansionBudgetCollector, ExpansionBudgetTruncation
    from scripts.function_tracer_pcode.tests.unit.runtime_ref_adversaries import Duck

    base = ExpansionBudgetTruncation(kind="path_limit", label="x")
    other = ExpansionBudgetTruncation(kind="path_limit", label="x", referenced_event_ids=("b", "a"))

    def run(lying):
        collector = ExpansionBudgetCollector()
        collector.record(base)
        collector.record(Duck(other, lying))
        return collector.as_tuple()

    twin = run(False)
    HOOK_CALLS.clear()
    built = run(True)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert view(built) == view(twin)
    assert built[0].referenced_event_ids == ("a", "b")


def test_call_model_candidate_keys_with_set_leaves_are_compared_on_base_values():
    from scripts.function_tracer_pcode.core.runtime_refs.call_models import CallModelCandidateRef

    def build(keys):
        signature, candidate = keys
        return CallModelCandidateRef(
            provider="f", canonical_symbol="g", signature_key=signature, provenance_key=("p",), candidate_key=candidate,
        )

    _same_without_hooks(
        build,
        prepare=lambda v: ((frozenset({v("a")}),), ("call_model_candidate", "f", "g", (frozenset({v("a")}),), ("p",))),
    )


def test_jvm_shutdown_errors_are_recognised_from_the_base_text_of_their_message():
    from scripts.function_tracer_pcode.core.call_target import CallTargetRef

    class Boom:
        def __init__(self, make):
            self.make = make

        def __getattr__(self, name):
            raise RuntimeError(self.make("JVM is not running"))

    def run(make):
        try:
            return CallTargetRef.from_function(Boom(make))
        except Exception as error:  # 双子と同じ扱い（握りつぶすか、同じ型で上げる）
            return type(error).__name__

    twin = run(lambda text: text)
    HOOK_CALLS.clear()
    built = run(LiarStr)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert view(built) == view(twin)


def test_named_tuples_become_builtin_tuples_in_readers_and_tuple_fields():
    """named tuple は reader も owner の tuple の field も組み込みの tuple にする（その型の `_make` / constructor を
    呼ばない: 作り直すときに葉を偽る型へ包み直し得る。review 4 の P1）。意図した差: 型は基底型の tuple になる。"""

    import collections

    from scripts.function_tracer_pcode.core.live_values import exact_tree
    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import ExpansionBudgetTruncation

    Pair = collections.namedtuple("Pair", "left right")
    HOOK_CALLS.clear()
    read = exact_tree(Pair(LiarStr("x"), (Liar(1),)))
    assert HOOK_CALLS == {}
    assert type(read) is tuple and read == ("x", (1,)) and type(read[0]) is str and type(read[1][0]) is int
    built = _same_without_hooks(lambda v: ExpansionBudgetTruncation(kind="k", owner_scope_key=Pair(v("x"), 1)))
    assert type(built.owner_scope_key) is tuple and built.owner_scope_key == ("x", 1)



# ---------------------------------------------------------------------------
# 検査の道具自身（偽る型が数える操作の範囲、view が見分けるもの）
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("liar, base", [(Liar, int), (LiarStr, str)], ids=["int", "str"])
def test_lying_types_count_every_operation_of_their_base(liar, base):
    from scripts.function_tracer_pcode.tests.unit.runtime_ref_adversaries import _NOT_HOOKED

    missing = [
        name for name in dir(base)
        if name not in _NOT_HOOKED and callable(getattr(base, name)) and not isinstance(getattr(base, name), type)
        and name not in vars(liar)
    ]
    assert missing == []
    HOOK_CALLS.clear()
    value = liar(base(1)) if base is int else liar("ab")
    if base is str:
        value.upper()
        value.zfill(4)
        _ = value * 2
    else:
        _ = value ** 2
        _ = value.bit_count()
        _ = round(value)
    assert sum(HOOK_CALLS.values()) >= 3


def test_view_tells_containers_and_instance_state_apart():
    assert view({"a": 1}) != view({"b": 1})
    assert view({"a": 1}) != view({"a": 2})
    assert view(frozenset({"a"})) != view(frozenset({"b"}))
    assert view(b"a") != view(b"b")
    assert view({"a": Liar(1)}) == view({"a": 1})
    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import ExpansionBudgetTruncation

    left = ExpansionBudgetTruncation(kind="k", owner_scope_key=({"x": 1},))
    right = ExpansionBudgetTruncation(kind="k", owner_scope_key=({"x": 2},))
    assert view(left) != view(right)  # field でない状態（`_owner_scope_value` / event id）も見る


# ---------------------------------------------------------------------------
# 独立の敵対的 review（3 回目の 2 巡目）の反例: subclass の method の結果、組み込みの容器の subclass、
# exact な入力の振る舞いの保存
# ---------------------------------------------------------------------------


def test_return_ops_of_subclasses_with_their_own_keys_are_ordered_on_base_values():
    from scripts.function_tracer_pcode.core.runtime_refs.pcode import PcodeOpRef

    def subclass(lying):
        def stable_key(self):
            return ("pcode_op", (LiarStr if lying else str)("x"), (Liar if lying else int)(self.address_offset))

        return type("SubOp", (PcodeOpRef,), {"stable_key": stable_key})

    honest, lying = subclass(False), subclass(True)
    twin = _proof_from(dict(return_op_refs=(honest(address_offset=2), honest(address_offset=1)))).return_op_refs
    refs = (lying(address_offset=2), lying(address_offset=1))
    HOOK_CALLS.clear()
    built = _proof_from(dict(return_op_refs=refs)).return_op_refs
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert [ref.address_offset for ref in built] == [ref.address_offset for ref in twin]


@pytest.mark.parametrize("shape", ["subclass", "duck"])
def test_loop_variable_keys_of_substitutes_are_looked_up_on_base_values(shape):
    from scripts.function_tracer_pcode.core.runtime_refs import loops
    from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopVariableIdentityRef
    from scripts.function_tracer_pcode.tests.unit.runtime_ref_adversaries import Duck

    good = LoopVariableIdentityRef(role="iv", varnode_key=("register", 16, 8), binder_ordinal=0)
    context = loops._loop_variable_binding_context_from_values(good)

    def substitute(lying):
        if shape == "duck":
            return Duck(good, lying)

        def stable_key(self):
            s, i = (LiarStr, Liar) if lying else (str, int)
            return ("loop_variable_identity", s("iv"), i(0), ("register", i(16), i(8)))

        cls = type("SubLV", (LoopVariableIdentityRef,), {"stable_key": stable_key})
        return cls(role="iv", varnode_key=("register", 16, 8))

    twin = loops._loop_object_semantic_key(substitute(False), context) if shape == "subclass" else None
    value = substitute(True)
    HOOK_CALLS.clear()
    built = loops._loop_object_semantic_key(value, context)
    loops._loop_variable_binding_context_from_values(value)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    if twin is not None:
        assert view(built) == view(twin)


@pytest.mark.parametrize("kind", ["OrderedDict", "deque", "defaultdict", "Counter", "scalar"])
def test_diagnostic_keys_read_accepted_origin_values_on_base_values(kind):
    import collections

    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import UnknownValueRef

    makers = {
        "OrderedDict": lambda s, i: collections.OrderedDict({s("a"): i(1)}),
        "deque": lambda s, i: collections.deque([s("a"), i(1)]),
        "defaultdict": lambda s, i: collections.defaultdict(int, {s("a"): i(1)}),
        "Counter": lambda s, i: collections.Counter({s("a"): i(1)}),
        "scalar": lambda s, i: s("x"),
    }
    twin_origin = makers[kind](str, int)
    twin = UnknownValueRef.opaque(reason="r", origin_kind="k", origin_ref=twin_origin).diagnostic_key()
    origin = makers[kind](LiarStr, Liar)
    HOOK_CALLS.clear()
    built = UnknownValueRef.opaque(reason="r", origin_kind="k", origin_ref=origin).diagnostic_key()
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    if kind == "scalar":
        assert view(built) == view(twin)
        return
    # 型の名前は元の型（双子と同じ）。scalar の subclass を持つ容器の `repr` は、写した組み込みの容器の `repr`
    # （元の型で作り直すと外の constructor を呼ぶ: 意図した差 D5）。subclass が無い入力は双子と同じ文字列
    from scripts.function_tracer_pcode.core.live_values import exact_tree

    *head, (label, (tag, module, name, text)) = built
    *twin_head, (twin_label, (twin_tag, twin_module, twin_name, twin_text)) = twin
    assert (head, label, tag, module, name) == (twin_head, twin_label, twin_tag, twin_module, twin_name)
    assert type(text) is str and text == repr(exact_tree(twin_origin)) and twin_text == repr(twin_origin)


@pytest.mark.parametrize(
    "error",
    [KeyError("JVM is not running"), RuntimeError("JVM is not running"), OSError(2, "JVM is not running"), RuntimeError()],
    ids=["key_error", "runtime_error", "os_error", "empty"],
)
def test_jvm_error_text_is_str_of_the_error_for_exact_arguments(error):
    """exact な引数の例外は、置き換える前（`str(error)`）と同じ文字列で判定する（KeyError の repr などを保つ）。"""

    from scripts.function_tracer_pcode.core.call_target import _error_text

    assert _error_text(error) == str(error)


def test_iterable_arguments_keep_accepting_every_iterable():
    """`Iterable` の注釈の引数（`expansion_budget_event_ids` / `ExpansionBudgetCollector.extend`）は、置き換える前
    （`tuple(items or ())`）と同じく generator・`dict` の値・`deque` を受ける。"""

    import collections

    from scripts.function_tracer_pcode.core.runtime_refs.unknowns import (
        ExpansionBudgetCollector,
        ExpansionBudgetTruncation,
        expansion_budget_event_ids,
    )

    records = [ExpansionBudgetTruncation(kind="k", label=str(index)) for index in range(3)]
    expected = expansion_budget_event_ids(records)
    for shape in ((r for r in records), {i: r for i, r in enumerate(records)}.values(), collections.deque(records)):
        assert expansion_budget_event_ids(shape) == expected
    collector = ExpansionBudgetCollector()
    collector.extend(r for r in records)
    assert len(collector) == 3



@pytest.mark.parametrize(
    "make",
    [
        pytest.param(lambda s, i: KeyError(s("JVM is not running")), id="key_error"),
        pytest.param(lambda s, i: RuntimeError(s("JVM is not running")), id="runtime_error"),
        pytest.param(lambda s, i: RuntimeError(s("JVM is not running"), i(2)), id="two_arguments"),
    ],
)
def test_jvm_error_text_reads_lying_arguments_like_str_of_the_twin(make):
    from scripts.function_tracer_pcode.core.call_target import _error_text

    expected = str(make(str, int))
    lying = make(LiarStr, Liar)
    HOOK_CALLS.clear()
    assert _error_text(lying) == expected
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)


def test_cyclic_containers_that_need_a_copy_are_not_read():
    """閉路を持つ容器は、写しが要れば元の容器を指す写しを作らずに `TypeError`（fail-closed）。"""

    from scripts.function_tracer_pcode.core.live_values import exact_tree

    cyclic = [Liar(1)]
    cyclic.append(cyclic)
    with pytest.raises(TypeError):
        exact_tree(cyclic)

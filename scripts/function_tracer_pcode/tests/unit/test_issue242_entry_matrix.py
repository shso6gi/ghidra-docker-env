# -*- coding: utf-8 -*-
"""Issue #242: runtime ref の構築の入口 × 値の消費 × 入力の形の行列（構築の契約の振る舞いの検査）。

入口: 自前の `__init__`・factory（classmethod / staticmethod）・ref から ref を作る method / 関数
（`@runtime_ref_entry`）。直接構築（35 class の生成された `__init__`）は `test_issue242_construction_contract.py`
と golden が持つ。各入口について、基底の引数（`ENTRY_CASES`）の scalar の位置と、入口が読む API の戻り値の
位置に、次の値を 1 つずつ入れる:

- 値を偽る subclass（`int()` は 999、真偽は逆、比較は偽、format は別の文字列）
- 0 / 空文字 / 0.0（偽る subclass と exact の両方: `x or default` の真偽が値に効く）
- `None`（注釈が Optional のとき）
- bool の注釈の位置には JBoolean の代わり（`Liar(1)` / `Liar(0)`）と exact な `True` / `False`

期待: 入口の引数の注釈の型規則（owner の規則。この test は corpus の仕様の写しで独立に計算する）で写した双子から
作った結果と、型の札つきの view で同じになり、偽る型の code の呼び出しが 0 回。双子が例外になる入力は同じ型の
例外になる。結果が偽る値をそのまま持つ（注釈が `Any` の field など owner が写さない位置）ときは、出力（LEGACY の
JSON）は比べない（契約の外）。
"""

from __future__ import annotations

import ast
import dataclasses
import inspect
import json
import typing
from typing import Any, Callable, Dict, List, Optional, Tuple

import pytest

from scripts.function_tracer_pcode.core import call_target as call_target_module
from scripts.function_tracer_pcode.core import runtime_ref_record
from scripts.function_tracer_pcode.core.call_target import CallTargetRef, coerce_call_target_ref
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.json_encoding import materialize
from scripts.function_tracer_pcode.core.runtime_refs import loops as loops_module
from scripts.function_tracer_pcode.core.runtime_refs import unknowns as unknowns_module
from scripts.function_tracer_pcode.core.runtime_refs.locations import (
    CanonicalLocation,
    LocationBaseRef,
    LocationStep,
    ObservedMemoryReadRef,
    PostStateReadRef,
    PostStateSnapshotRef,
)
from scripts.function_tracer_pcode.core.runtime_refs.loops import (
    LoopSideEffectProfileRef,
    LoopSummaryProofObligation,
    LoopSummaryRef,
    LoopTermDescriptorRef,
)
from scripts.function_tracer_pcode.core.runtime_refs.pcode import PcodeOpRef
from scripts.function_tracer_pcode.core.runtime_refs.readonly import (
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReductionAccumulatorProof,
)
from scripts.function_tracer_pcode.core.runtime_refs.unknowns import ExpansionBudgetTruncation, UnknownValueRef
from scripts.function_tracer_pcode.tests.fixtures.runtime_ref_golden import corpus
from scripts.function_tracer_pcode.tests.unit.runtime_ref_adversaries import (
    HOOK_CALLS,
    Liar,
    LiarStr,
    lie,
    view,
)

# ---------------------------------------------------------------------------
# 偽の Ghidra object（API の戻り値は `values` の dict から返す）
# ---------------------------------------------------------------------------


class _Fake:
    def __init__(self, values: Dict[str, Any], **children: Any):
        self._values = values
        self._children = children

    def __getattr__(self, name: str):
        if name in self._children:
            child = self._children[name]
            return lambda *args: child(*args) if callable(child) and not isinstance(child, _Fake) else child
        key = f"{type(self).__name__}.{name}"
        if key in self._values:
            value = self._values[key]
            return lambda *args: value
        raise AttributeError(name)


class FakeSpace(_Fake):
    pass


class FakeAddress(_Fake):
    pass


class FakeProgram(_Fake):
    pass


class FakeExternalLocation(_Fake):
    pass


class FakeFunction(_Fake):
    pass


class FakeSeq(_Fake):
    pass


class FakeBlock(_Fake):
    pass


class FakeVarnode(_Fake):
    pass


class FakePcodeOp(_Fake):
    pass


class _Iterator:
    def __init__(self, items):
        self._items = list(items)

    def hasNext(self):
        return bool(self._items)

    def next(self):
        return self._items.pop(0)


FUNCTION_API = {
    "FakeFunction.getName": "f",
    "FakeFunction.isExternal": True,
    "FakeFunction.isThunk": False,
    "FakeAddress.getOffset": 0x1000,
    "FakeExternalLocation.getLibraryName": "libc",
    "FakeExternalLocation.getOriginalImportedName": "f_orig",
    "FakeProgram.getUniqueProgramID": 7,
}
#: API の戻り値のうち真偽として読まれるもの（双子は bool）
BOOLEAN_API = frozenset({"FakeFunction.isExternal", "FakeFunction.isThunk"})

PCODE_API = {
    "FakePcodeOp.getMnemonic": "LOAD",
    "FakePcodeOp.getOpcode": 2,
    "FakePcodeOp.getNumInputs": 2,
    "FakeSeq.getTime": 1,
    "FakeSeq.getOrder": 2,
    "FakeAddress.getOffset": 0x1000,
    "FakeSpace.getName": "ram",
    "FakeBlock.getIndex": 0,
    "FakeVarnode.getSize": 4,
}


def make_function(values: Dict[str, Any]) -> FakeFunction:
    address = FakeAddress(values)
    program = FakeProgram(values)
    external = FakeExternalLocation(values)
    return FakeFunction(
        values, getEntryPoint=address, getProgram=program, getExternalLocation=external,
        getThunkedFunction=lambda *args: None,
    )


def make_pcode_op(values: Dict[str, Any]) -> FakePcodeOp:
    space = FakeSpace(values)
    address = FakeAddress(values, getAddressSpace=space)
    seq = FakeSeq(values, getTarget=address)
    varnode = FakeVarnode(values)
    op_holder: List[Any] = []
    block = FakeBlock(values, getIterator=lambda: _Iterator(op_holder))
    op = FakePcodeOp(values, getSeqnum=seq, getParent=block, getInput=lambda index: varnode, getOutput=varnode)
    op_holder.append(op)
    return op


# ---------------------------------------------------------------------------
# 入口の表
# ---------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True)
class EntryCase:
    """1 つの入口: `call(kwargs)` が入口を呼ぶ。`base()` は exact な引数。`api` は入口が読む API の戻り値。"""

    entry: Any  # 入口の関数（classmethod / method / 関数。annotation を読むため）
    call: Callable[[Dict[str, Any], Dict[str, Any]], Any]
    base: Callable[[], Dict[str, Any]]
    api: Optional[Dict[str, Any]] = None


def _expr(value: int = 1) -> Expression:
    return Expression.constant(value, size=4)


def _loop_summary() -> LoopSummaryRef:
    return LoopSummaryRef(
        start_expr=_expr(0), limit_expr=_expr(8), step_expr=_expr(1),
        term_descriptor=LoopTermDescriptorRef(kind="memory_load", reduction_kind="sum", location_base_ref=LocationBaseRef.parameter("p", index=0), stride=4, element_size=4, result_size=4),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure_memory_read", memory_reads=True),
    )


def _proof() -> ReductionAccumulatorProof:
    return ReductionAccumulatorProof(
        reduction_kind="memory_sum", pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count", count_parameter_index=1,
        limit_expr=Expression.parameter("count", 1, size=4), result_size=4, stride=4, element_size=4, index_scale=4,
        loop_body_witnesses=(
            ReadonlyReductionWitness(exact_count=1, terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),)),
        ),
    )


def _location() -> CanonicalLocation:
    return CanonicalLocation(base_ref=LocationBaseRef.parameter("p", index=0), offset=4, size=4)


ENTRY_CASES: Dict[str, EntryCase] = {
    "LocationBaseRef.parameter": EntryCase(
        LocationBaseRef.parameter, lambda kw, api: LocationBaseRef.parameter(**kw),
        lambda: dict(name="a", index=1, owner_program_id=7, owner_entry_offset=0x100),
    ),
    "LocationBaseRef.storage": EntryCase(
        LocationBaseRef.storage, lambda kw, api: LocationBaseRef.storage(**kw),
        lambda: dict(space_id=1, space_name="register", offset=8, size=8, storage_identity_key=("register", 8, 8), display_hint="r"),
    ),
    "LocationBaseRef.global_object": EntryCase(
        LocationBaseRef.global_object, lambda kw, api: LocationBaseRef.global_object(**kw),
        lambda: dict(symbol_name="g", size=8, space_name="ram"),
    ),
    "LocationBaseRef.stack_frame": EntryCase(
        LocationBaseRef.stack_frame, lambda kw, api: LocationBaseRef.stack_frame(), lambda: {},
    ),
    "PostStateSnapshotRef.function_return": EntryCase(
        PostStateSnapshotRef.function_return, lambda kw, api: PostStateSnapshotRef.function_return(), lambda: {},
    ),
    "CanonicalLocation.__init__": EntryCase(
        CanonicalLocation.__init__, lambda kw, api: CanonicalLocation(**kw),
        lambda: dict(base_param="p", offset=4, size=4, steps=(LocationStep("offset", 4),)),
    ),
    "CanonicalLocation.__init__#stackframe": EntryCase(
        CanonicalLocation.__init__, lambda kw, api: CanonicalLocation(**kw),
        lambda: dict(base_param="stackframe", offset=4, size=4),
    ),
    "PostStateReadRef.with_location": EntryCase(
        PostStateReadRef.with_location, lambda kw, api: PostStateReadRef(location=_location()).with_location(**kw),
        lambda: dict(location=_location()),
    ),
    "PostStateReadRef.with_snapshot": EntryCase(
        PostStateReadRef.with_snapshot, lambda kw, api: PostStateReadRef(location=_location()).with_snapshot(**kw),
        lambda: dict(snapshot_ref=PostStateSnapshotRef.function_return()),
    ),
    "ObservedMemoryReadRef.with_location": EntryCase(
        ObservedMemoryReadRef.with_location, lambda kw, api: ObservedMemoryReadRef(order_key=3).with_location(**kw),
        lambda: dict(location=_location(), snapshot_ref=None),
    ),
    "ObservedMemoryReadRef.with_snapshot": EntryCase(
        ObservedMemoryReadRef.with_snapshot, lambda kw, api: ObservedMemoryReadRef(order_key=3).with_snapshot(**kw),
        lambda: dict(snapshot_ref=PostStateSnapshotRef.function_return()),
    ),
    "compare_loop_summaries": EntryCase(
        loops_module.compare_loop_summaries, lambda kw, api: loops_module.compare_loop_summaries(**kw),
        lambda: dict(left=_loop_summary(), right=_loop_summary()),
    ),
    "LoopSummaryProofObligation.case_aware_solver_equality": EntryCase(
        LoopSummaryProofObligation.case_aware_solver_equality,
        lambda kw, api: LoopSummaryProofObligation.case_aware_solver_equality(**kw),
        lambda: dict(left=_loop_summary(), right=_loop_summary(), reason="needs_solver"),
    ),
    "PcodeOpRef.from_pcode_op": EntryCase(
        PcodeOpRef.from_pcode_op, lambda kw, api: PcodeOpRef.from_pcode_op(make_pcode_op(api), **kw),
        lambda: dict(binary_id="B1", program_uid=7, function_entry_space="ram", function_entry_offset=0x100),
        api=PCODE_API,
    ),
    "ReductionAccumulatorProof.loop_body_terms_for_count_value": EntryCase(
        ReductionAccumulatorProof.loop_body_terms_for_count_value,
        lambda kw, api: _proof().loop_body_terms_for_count_value(**kw), lambda: dict(count_value=3),
    ),
    "ReductionAccumulatorProof.full_terms_for_count_value": EntryCase(
        ReductionAccumulatorProof.full_terms_for_count_value,
        lambda kw, api: _proof().full_terms_for_count_value(**kw), lambda: dict(count_value=3),
    ),
    "ReductionAccumulatorProof.seed_terms_for_count_value": EntryCase(
        ReductionAccumulatorProof.seed_terms_for_count_value,
        lambda kw, api: _proof().seed_terms_for_count_value(**kw), lambda: dict(count_value=3),
    ),
    "ReductionAccumulatorProof.with_runtime_evidence": EntryCase(
        ReductionAccumulatorProof.with_runtime_evidence,
        lambda kw, api: _proof().with_runtime_evidence(**kw),
        lambda: dict(
            limit_expr=Expression.parameter("count", 1, size=4), result_size=4,
            loop_body_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),)),),
            exact_return_witnesses=(), guard_constraints=(), signed_counter=True,
        ),
    ),
    "normalize_expansion_budget_truncations": EntryCase(
        unknowns_module.normalize_expansion_budget_truncations,
        lambda kw, api: unknowns_module.normalize_expansion_budget_truncations(**kw),
        lambda: dict(items=[ExpansionBudgetTruncation(kind="k", dedup=(3, 2, 2)), ExpansionBudgetTruncation(kind="k", dedup=(3, 2, 2))]),
    ),
    "UnknownValueRef.deferred_call": EntryCase(
        UnknownValueRef.deferred_call, lambda kw, api: UnknownValueRef.deferred_call(**kw),
        lambda: dict(placeholder_name="p", sequence=2),
    ),
    "UnknownValueRef.out_of_scope_call": EntryCase(
        UnknownValueRef.out_of_scope_call, lambda kw, api: UnknownValueRef.out_of_scope_call(**kw),
        lambda: dict(reason="r", display_hint="d"),
    ),
    "UnknownValueRef.budget_exceeded": EntryCase(
        UnknownValueRef.budget_exceeded, lambda kw, api: UnknownValueRef.budget_exceeded(**kw),
        lambda: dict(operation="expand", origin_kind="k"),
    ),
    "UnknownValueRef.opaque": EntryCase(
        UnknownValueRef.opaque, lambda kw, api: UnknownValueRef.opaque(**kw),
        lambda: dict(reason="r", display_hint="d", origin_kind="k"),
    ),
    "UnknownValueRef.phi_circular": EntryCase(
        UnknownValueRef.phi_circular, lambda kw, api: UnknownValueRef.phi_circular(**kw),
        lambda: dict(display_hint="phi"),
    ),
    "ExpansionBudgetTruncation.with_binding": EntryCase(
        ExpansionBudgetTruncation.with_binding,
        lambda kw, api: ExpansionBudgetTruncation(kind="k").with_binding(**kw),
        lambda: dict(surface="return", owner_scope_key=("scope", 1)),
    ),
    "CallTargetRef.from_function": EntryCase(
        CallTargetRef.from_function, lambda kw, api: CallTargetRef.from_function(make_function(api)),
        lambda: {}, api=FUNCTION_API,
    ),
    "CallTargetRef.from_code_address": EntryCase(
        CallTargetRef.from_code_address, lambda kw, api: CallTargetRef.from_code_address(**kw),
        lambda: dict(address_value=0x1000, display_hint="d", program_id=7),
    ),
    "CallTargetRef.from_code_address#address": EntryCase(
        CallTargetRef.from_code_address,
        lambda kw, api: CallTargetRef.from_code_address(FakeAddress(api), **kw),
        lambda: dict(display_hint="d", program_id=7), api={"FakeAddress.getOffset": 0x1000},
    ),
    "CallTargetRef.from_name": EntryCase(
        CallTargetRef.from_name, lambda kw, api: CallTargetRef.from_name(**kw),
        lambda: dict(function_name="f", program_id=7, entry_offset=0x100, is_external=True, library_name="libc",
                     is_thunk=False, thunked_is_external=False, thunked_library_name="libm"),
    ),
    "CallTargetRef.unknown": EntryCase(
        CallTargetRef.unknown, lambda kw, api: CallTargetRef.unknown(**kw), lambda: dict(display_hint="u"),
    ),
    "loop_summary_method_b_key": EntryCase(
        loops_module.loop_summary_method_b_key, lambda kw, api: loops_module.loop_summary_method_b_key(**kw),
        lambda: dict(summary=_loop_summary()),
    ),
    "loop_summary_method_b_key_at_result_size": EntryCase(
        loops_module.loop_summary_method_b_key_at_result_size,
        lambda kw, api: loops_module.loop_summary_method_b_key_at_result_size(**kw),
        lambda: dict(summary=_loop_summary(), result_size=2),
    ),
    "ReductionAccumulatorProof.readonly_term_sequence_contract_key": EntryCase(
        ReductionAccumulatorProof.readonly_term_sequence_contract_key,
        lambda kw, api: _proof().readonly_term_sequence_contract_key(**kw), lambda: dict(result_size=4),
    ),
    "ReadonlyReductionRef.readonly_term_sequence_contract_key": EntryCase(
        ReadonlyReductionRef.readonly_term_sequence_contract_key,
        lambda kw, api: _proof().lower_to_readonly_reduction_ref().readonly_term_sequence_contract_key(**kw),
        lambda: dict(result_size=4),
    ),
    "coerce_call_target_ref": EntryCase(
        coerce_call_target_ref, lambda kw, api: coerce_call_target_ref(**kw),
        lambda: dict(target=CallTargetRef.from_name("f")),
    ),
}


# ---------------------------------------------------------------------------
# 入口の一覧との突き合わせ（新しい入口は表に足さないと落ちる）
# ---------------------------------------------------------------------------


def _discovered_entries() -> set:
    """ref module の入口（`runtime_ref_entry` の関数・method、ref の class の classmethod / staticmethod と自前の `__init__`）。"""

    import importlib
    import pkgutil

    import scripts.function_tracer_pcode.core.runtime_refs as runtime_refs

    modules = [importlib.import_module(f"{runtime_refs.__name__}.{info.name}") for info in pkgutil.iter_modules(runtime_refs.__path__)]
    modules.append(call_target_module)
    found = set()
    for module in modules:
        for name, value in vars(module).items():
            if inspect.isfunction(value) and value.__module__ == module.__name__ and runtime_ref_record.is_runtime_ref_entry(value):
                found.add(name)
            if isinstance(value, type) and value.__module__ == module.__name__ and runtime_ref_record.is_runtime_ref_record(value):
                for attribute, member in value.__dict__.items():
                    if isinstance(member, (classmethod, staticmethod)) or runtime_ref_record.is_runtime_ref_entry(member):
                        found.add(f"{value.__name__}.{attribute}")
                    elif attribute == "__init__" and not getattr(value, "__dataclass_params__").init:
                        found.add(f"{value.__name__}.__init__")
    return found


def test_every_entry_is_in_the_matrix():
    table = {name.split("#", 1)[0] for name in ENTRY_CASES}
    assert _discovered_entries() == table


def test_public_ref_producing_functions_are_entries():
    """引数を持ち、ref を（推移的に）作る公開の関数・method は `runtime_ref_entry`（引数を消費の前に写す）。"""

    from scripts.function_tracer_pcode.tests.unit.runtime_ref_construction_guard import ConstructionGuard

    guard = ConstructionGuard.for_package()
    decorated = set()
    for unit_name in guard.ref_producing_functions():
        module_name, qualified = unit_name.split(":")
        owner, name = qualified.split(".")
        module = next(m for m in guard.modules.values() if m.name.endswith("." + module_name))
        function = module.functions[name] if owner == "None" else module.methods[(owner, name)]
        if any(ast.unparse(d) == "runtime_ref_entry" for d in function.decorator_list):
            decorated.add(unit_name)
    assert sorted(set(guard.ref_producing_functions()) - decorated) == []


# ---------------------------------------------------------------------------
# 行列
# ---------------------------------------------------------------------------


def _original(entry: Any) -> Any:
    function = getattr(entry, "__func__", entry)
    return runtime_ref_record._ENTRY_WRAPPERS.get(function, function)


def _parameter_kinds(entry: Any) -> Dict[str, Tuple[str, bool]]:
    """引数 → (corpus の仕様の分類, Optional か)。"""

    function = _original(entry)
    hints = typing.get_type_hints(function, include_extras=True)
    kinds = {}
    for name in inspect.signature(function).parameters:
        hint = hints.get(name, Any)
        optional = typing.get_origin(hint) is typing.Union and type(None) in typing.get_args(hint)
        kinds[name] = (corpus.field_kind(hint), optional)
    return kinds


def _zero(value: Any) -> Any:
    return {int: 0, str: "", float: 0.0}.get(type(value))


def _argument_variants(case: EntryCase):
    kinds = _parameter_kinds(case.entry)
    for name, value in case.base().items():
        kind, optional = kinds.get(name, ("object", False))
        if type(value) is bool or kind == "bool":
            for label, item in (("jboolean_true", Liar(1)), ("jboolean_false", Liar(0)), ("true", True), ("false", False)):
                yield f"arg:{name}:{label}", name, item, corpus.twin_value(item, "bool" if kind == "bool" else "element")
        elif type(value) in (int, str, float):
            twin_kind = kind if kind in ("int", "str", "float") else "element"
            for label, item in (("lie", lie(value)), ("lie_falsy", lie(_zero(value))), ("falsy", _zero(value))):
                yield f"arg:{name}:{label}", name, item, corpus.twin_value(item, twin_kind)
            if optional:
                yield f"arg:{name}:none", name, None, None
        elif type(value) is tuple and value and kind == "tuple":
            lied = tuple(lie(item) for item in value)
            yield f"arg:{name}:tuple_lie", name, lied, corpus.twin_value(lied, "tuple")
            listed = [lie(item) for item in value]
            yield f"arg:{name}:list_lie", name, listed, [corpus.twin_value(item, "element") for item in listed]


def _api_variants(case: EntryCase):
    for key, value in (case.api or {}).items():
        if key in BOOLEAN_API:
            for label, item, twin in (("jboolean_true", Liar(1), True), ("jboolean_false", Liar(0), False)):
                yield f"api:{key}:{label}", key, item, twin
        else:
            for label, item in (("lie", lie(value)), ("lie_falsy", lie(_zero(value))), ("falsy", _zero(value))):
                yield f"api:{key}:{label}", key, item, corpus.twin_value(item, "element")


def _matrix():
    for case_id, case in ENTRY_CASES.items():
        yield pytest.param(case_id, "exact", None, None, None, id=f"{case_id}:exact")
        for label, name, item, twin in _argument_variants(case):
            yield pytest.param(case_id, "arg", name, item, twin, id=f"{case_id}:{label}")
        for label, key, item, twin in _api_variants(case):
            yield pytest.param(case_id, "api", key, item, twin, id=f"{case_id}:{label}")


def _holds_subclass(value: Any, depth: int = 0) -> bool:
    kind = type(value)
    if value is None or kind in (int, str, bool, float):
        return False
    if isinstance(value, (int, str, float)):
        return not isinstance(value, __import__("enum").Enum)
    if kind in (tuple, list):
        return any(_holds_subclass(item, depth + 1) for item in value)
    if depth < 12 and dataclasses.is_dataclass(value) and not isinstance(value, type):
        return any(_holds_subclass(getattr(value, item.name), depth + 1) for item in dataclasses.fields(value))
    return False


def _outputs(result: Any) -> Any:
    items = result if type(result) in (tuple, list) else (result,)
    out = []
    for item in items:
        if dataclasses.is_dataclass(item) and not isinstance(item, type):
            stable_key = getattr(type(item), "stable_key", None)
            out.append((
                json.dumps(materialize(item), sort_keys=True),
                view(stable_key(item)) if stable_key else None,
            ))
    return out


def _invoke(case: EntryCase, where: str, name: Optional[str], value: Any):
    kwargs = case.base()
    api = dict(case.api or {})
    if where == "arg":
        kwargs[name] = value
    elif where == "api":
        api[name] = value
    return case.call(kwargs, api)


@pytest.mark.parametrize("case_id, where, name, item, twin", list(_matrix()))
def test_entry_builds_the_twin_without_calling_subclass_code(case_id, where, name, item, twin):
    case = ENTRY_CASES[case_id]
    try:
        expected = _invoke(case, where, name, twin)
    except Exception as error:
        HOOK_CALLS.clear()
        with pytest.raises(type(error)):
            _invoke(case, where, name, item)
        assert HOOK_CALLS == {}
        return
    HOOK_CALLS.clear()
    built = _invoke(case, where, name, item)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert view(built) == view(expected)
    if not _holds_subclass(built):
        assert _outputs(built) == _outputs(expected)


def test_reviewed_examples_keep_their_meaning():
    """review で挙がった例（0・空文字・stackframe・JBoolean・format）を名前で固定する。"""

    HOOK_CALLS.clear()
    assert LocationBaseRef.parameter(LiarStr(""), index=Liar(0)).parameter_name is None
    assert LocationBaseRef.parameter(LiarStr("a")).parameter_name == "a"
    assert CanonicalLocation(base_param=LiarStr("stackframe")).base_ref.kind == "stack_frame"
    assert CanonicalLocation(base_param=LiarStr("")).base_ref.parameter_name == "param"
    assert CallTargetRef.from_name(LiarStr("")).function_name is None
    assert UnknownValueRef.opaque(reason=LiarStr("")).reason == "unknown"
    assert UnknownValueRef.budget_exceeded(operation=LiarStr("expand")).reason == "expand_budget_exceeded"
    external = CallTargetRef.from_function(make_function(dict(FUNCTION_API, **{"FakeFunction.isExternal": Liar(1)})))
    assert external.is_external is True and external.library_name == "libc"
    assert external.stable_key() == CallTargetRef.from_function(make_function(FUNCTION_API)).stable_key()
    assert HOOK_CALLS == {}


# ---------------------------------------------------------------------------
# review で見つかった反例（2 回目）。行列の基底の 1 構成では通らない分岐と、guard が信用する位置
# ---------------------------------------------------------------------------


def _summary_with_limit(operands_container, first: int, second: int) -> LoopSummaryRef:
    limit = Expression.binary_op("+", _expr(first), _expr(second))
    limit.__dict__["operands"] = operands_container([_expr(first), _expr(second)])
    return dataclasses.replace(_loop_summary(), limit_expr=limit)


def test_unreadable_operand_containers_do_not_drop_operands():
    import collections

    # 組み込みでない容器の operand を空の列にすると、別の式と等しい key になる（誤った equivalent）
    left = _summary_with_limit(collections.deque, 1, 2)
    right = _summary_with_limit(collections.deque, 7, 9)
    assert loops_module.compare_loop_summaries(left, right).status != "equivalent"
    assert loops_module.loop_summary_method_b_key(left) is None


def test_str_enum_members_keep_their_identity_in_loop_keys():
    import enum

    class Kind(str, enum.Enum):
        A = "a"

    assert loops_module._loop_object_key(Kind.A) == loops_module._loop_object_key("a")
    assert loops_module._loop_object_semantic_key(Kind.A) == loops_module._loop_object_semantic_key("a")


def test_composed_summary_scalars_are_read_through_the_base_slot():
    import types

    from scripts.function_tracer_pcode.core.runtime_refs.loops import ComposedLoopSummaryRef

    def build(bias):
        current = types.SimpleNamespace(term_descriptor=types.SimpleNamespace(result_size=0), constant_bias=bias)
        return ReadonlyReductionRef(
            reduction_kind="sum", pointer_base_ref=LocationBaseRef.parameter("p"), count_parameter_name="n",
            loop_summary=ComposedLoopSummaryRef(prior=None, current=current),
        )

    twin = build(0)
    HOOK_CALLS.clear()
    assert view(build(Liar(0))) == view(twin)
    assert HOOK_CALLS == {}


def test_lane_terms_accepted_as_a_list_are_compared_on_base_values():
    def summary(lanes):
        descriptor = LoopTermDescriptorRef(
            kind="memory_load", reduction_kind="sum", location_base_ref=LocationBaseRef.parameter("p", index=0),
            stride=8, element_size=8, result_size=4, lane_terms=lanes,
        )
        return dataclasses.replace(_loop_summary(), term_descriptor=descriptor, loop_var_unit="scalar_element_index")

    twin = loops_module.compare_loop_summaries(summary(((0, 4), (4, 4))), summary(((0, 4), (4, 4))))
    HOOK_CALLS.clear()
    lied = [(Liar(0), Liar(4)), (Liar(4), Liar(4))]
    result = loops_module.compare_loop_summaries(summary(lied), summary(list(lied)))
    assert HOOK_CALLS == {}
    assert view(result) == view(twin)


def test_return_op_refs_are_ordered_on_base_values():
    def op(binary_id, offset):
        # 全 identity の文脈を持つ op（stable key に binary_id が入る）
        return PcodeOpRef(
            address_offset=offset, seq_time=1, seq_order=1, block_index=0, mnemonic="LOAD", binary_id=binary_id,
            function_entry_space="ram", function_entry_offset=0x100, target_space="ram", target_offset=offset,
            opcode=2, local_op_ordinal=0,
        )

    def proof(left, right):
        # 偽る repr は両方同じ文字列なので、偽った並びは offset で決まり（B が先）、双子の並びは名前で決まる（A が先）
        return dataclasses.replace(_proof(), return_op_refs=(op(left, 0x10), op(right, 0x20)))

    twin = proof("B", "A")
    HOOK_CALLS.clear()
    built = proof(LiarStr("B"), LiarStr("A"))
    assert HOOK_CALLS == {}
    assert view(built.return_op_refs) == view(twin.return_op_refs)


def test_budget_identity_reads_tuple_mapping_keys_on_base_values():
    lied_key = (Liar(1), 2)
    owner = ("s", {lied_key: 3})
    twin = ExpansionBudgetTruncation(kind="k", owner_scope_key=("s", {(1, 2): 3}))
    HOOK_CALLS.clear()
    built = ExpansionBudgetTruncation(kind="k", owner_scope_key=owner)
    assert HOOK_CALLS == {}
    assert built.event_id == twin.event_id


def test_scalar_subclass_in_a_tuple_annotated_field_takes_the_base_type():
    HOOK_CALLS.clear()
    built = ExpansionBudgetTruncation(kind="k", owner_scope_key=LiarStr("x"), referenced_event_ids=LiarStr("ab"))
    location = LocationBaseRef(kind="storage", storage_identity_key=LiarStr("reg"))
    assert HOOK_CALLS == {}
    assert type(built.owner_scope_key) is str and built.referenced_event_ids == ("a", "b")
    assert type(location.storage_identity_key) is str

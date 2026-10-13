# -*- coding: utf-8 -*-
"""Issue #242: runtime ref の構築の入口 × 呼び出しの形 × 受け手 × 入力の形の行列（構築の契約の振る舞いの検査）。

入口: 自前の `__init__`・factory（classmethod / staticmethod）・ref から ref を作る method / 関数
（`@runtime_ref_entry`）。直接構築（35 class の生成された `__init__`）は `test_issue242_construction_contract.py`
と golden が持つ。次の次元を組み合わせる:

- 呼び出しの形: キーワード・位置・混在（signature から作る。`*args` の入口は位置だけ）。引数の束縛と写し方の
  対応のずれ（自前の `__init__` の receiver など）を落とす
- 受け手と分岐: method の入口は受け手の構成を変える（readonly の seed の項・seed の数・exact な witness・lane、
  loop summary の lane・seed）。基底の 1 構成では通らない分岐の読みを通す
- 入力の形（1 つずつ）: 基底の引数（`ENTRY_CASES`）の scalar の位置と入口が読む API の戻り値の位置に、値を偽る
  subclass・0 / 空文字・`None`・bool の位置の JBoolean の代わり
- 入力の形（全体）: すべての scalar を同時に偽る（`lie_all`）、引数と受け手の中の ref を代わりの型（`Duck`）に
  する（`duck`: 偽る代わりの型と、正直な代わりの型の双子）、その両方（`duck_lie_all`）。受理された値の属性・
  method の戻り値を読む経路（guard が「外の値」と扱う位置）を実行する

期待: 双子（入口の引数の注釈の型規則で写した値・正直な代わりの型）から作った結果と、型の札つきの view で
同じになり、偽る型の code の呼び出しが 0 回。双子が例外になる入力は同じ型の例外になる。結果が偽る値をそのまま
持つ（注釈が `Any` の field など owner が写さない位置）ときは、出力（LEGACY の JSON）は比べない（契約の外）。
"""

from __future__ import annotations

import ast
import importlib
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
    LoopBodyEffectRef,
    LoopCaseRef,
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
    callbacks,
    Liar,
    LiarStr,
    disguise,
    lie,
    lie_deep,
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
    """1 つの入口の 1 構成。

    `call(receiver, args, kwargs, api)` が入口を呼ぶ（`args` / `kwargs` は呼び出しの形で `base()` から作る）。
    `receiver` は method の入口の受け手を作る（`None` なら関数・classmethod）。`fixed` は `call` が自分で渡す
    先頭の位置の引数の数（偽の Ghidra object など。receiver を除く）。`api` は入口が読む API の戻り値。
    """

    entry: Any
    call: Callable[[Any, Tuple[Any, ...], Dict[str, Any], Dict[str, Any]], Any]
    base: Callable[[], Dict[str, Any]]
    api: Optional[Dict[str, Any]] = None
    receiver: Optional[Callable[[], Any]] = None
    fixed: int = 0


def _expr(value: int = 1) -> Expression:
    return Expression.constant(value, size=4)


def _descriptor(**changes: Any) -> LoopTermDescriptorRef:
    fields = dict(
        kind="memory_load", reduction_kind="sum", location_base_ref=LocationBaseRef.parameter("p", index=0),
        stride=4, element_size=4, result_size=4,
    )
    fields.update(changes)
    return LoopTermDescriptorRef(**fields)


def _loop_summary(**changes: Any) -> LoopSummaryRef:
    fields = dict(
        start_expr=_expr(0), limit_expr=_expr(8), step_expr=_expr(1), term_descriptor=_descriptor(),
        side_effect_profile=LoopSideEffectProfileRef(profile="pure_memory_read", memory_reads=True),
    )
    fields.update(changes)
    return LoopSummaryRef(**fields)


def _lane_summary() -> LoopSummaryRef:
    return _loop_summary(
        term_descriptor=_descriptor(stride=8, element_size=8, lane_terms=((0, 4), (4, 4))),
        loop_var_unit="scalar_element_index",
    )


def _seeded_summary() -> LoopSummaryRef:
    return _loop_summary(start_expr=_expr(2), seed_terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),))


def _term(offset: int, size: int = 4) -> ReadonlyReductionTermRef:
    return ReadonlyReductionTermRef(byte_offset=offset, access_size=size)


def _proof(**changes: Any) -> ReductionAccumulatorProof:
    fields = dict(
        reduction_kind="memory_sum", pointer_base_ref=LocationBaseRef.parameter("base", index=0),
        count_parameter_name="count", count_parameter_index=1,
        limit_expr=Expression.parameter("count", 1, size=4), result_size=4, stride=4, element_size=4, index_scale=4,
        loop_body_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
    )
    fields.update(changes)
    return ReductionAccumulatorProof(**fields)


#: readonly の入口が分岐で読む受け手の構成（seed の項・seed の数・exact な戻り値の witness・lane）
PROOF_RECEIVERS: Dict[str, Callable[[], ReductionAccumulatorProof]] = {
    "": _proof,
    "#seed_terms": lambda: _proof(seed_terms=(_term(0), _term(4)), start_index=2, start_offset=8),
    "#seed_count": lambda: _proof(seed_term_count=1, start_index=1, start_offset=4),
    "#exact_witnesses": lambda: _proof(
        element_size=8, stride=8, index_scale=8,
        exact_return_witnesses=(
            ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),
            ReadonlyReductionWitness(exact_count=2, terms=(_term(0), _term(4))),
        ),
    ),
    "#lanes": lambda: _proof(
        stride=8, element_size=8, index_scale=8, lane_terms=((0, 4), (4, 4)),
        loop_body_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
    ),
}

def _conditional_summary() -> LoopSummaryRef:
    condition = Expression.parameter("c", 2, size=4)
    effect = LoopBodyEffectRef(kind="conditional_guard", path_condition_sets=((condition,),), guard_constraints=(condition,))
    return _loop_summary(side_effect_profile=LoopSideEffectProfileRef(
        profile="pure_conditional", memory_reads=True, conditional_guards=True, effect_descriptors=(effect,), guard_count=1,
    ))


def _loop_variable_summary() -> LoopSummaryRef:
    from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopVariableIdentityRef

    induction = Expression.variable("i", size=4, runtime_ref=LoopVariableIdentityRef(role="induction", varnode_key=("unique", 0x10, 4)))
    return _loop_summary(limit_expr=Expression.binary_op("+", induction, _expr(1)))


def _counted_case_summary() -> LoopSummaryRef:
    def case() -> LoopCaseRef:
        return LoopCaseRef(
            path_conditions=(), body_effect=LoopBodyEffectRef(kind="accumulator_update"), term_expr=_expr(1),
            case_kind="accumulator_delta", source="counted_loop_update_case",
        )

    return _loop_summary(
        term_descriptor=_descriptor(kind="affine_residue", residue_cases=((2, 0, 1, 0), (2, 1, 1, 0))), cases=(case(), case()),
    )


#: loop summary の入口が分岐で読む構成（lane・seed・式の limit・条件つきの効果・counted loop の場合分け）
SUMMARY_PAIRS: Dict[str, Callable[[], Tuple[LoopSummaryRef, LoopSummaryRef]]] = {
    "": lambda: (_loop_summary(), _loop_summary()),
    "#lanes": lambda: (_lane_summary(), _lane_summary()),
    "#seeded": lambda: (_seeded_summary(), _seeded_summary()),
    "#limit_parameter": lambda: (_loop_summary(limit_expr=Expression.parameter("n", 1, size=4)),) * 2,
    "#limit_binary": lambda: (
        _loop_summary(limit_expr=Expression.binary_op("+", Expression.parameter("n", 1, size=4), _expr(2))),
    ) * 2,
    "#effects": lambda: (_conditional_summary(), _conditional_summary()),
    "#counted_cases": lambda: (_counted_case_summary(), _counted_case_summary()),
    "#loop_variable": lambda: (_loop_variable_summary(), _loop_variable_summary()),
}


def _location() -> CanonicalLocation:
    return CanonicalLocation(base_ref=LocationBaseRef.parameter("p", index=0), offset=4, size=4)


ENTRY_CASES: Dict[str, EntryCase] = {
    "LocationBaseRef.parameter": EntryCase(
        LocationBaseRef.parameter, lambda r, a, kw, api: LocationBaseRef.parameter(*a, **kw),
        lambda: dict(name="a", index=1, owner_program_id=7, owner_entry_offset=0x100),
    ),
    "LocationBaseRef.storage": EntryCase(
        LocationBaseRef.storage, lambda r, a, kw, api: LocationBaseRef.storage(*a, **kw),
        lambda: dict(space_id=1, space_name="register", offset=8, size=8, storage_identity_key=("register", 8, 8), display_hint="r"),
    ),
    "LocationBaseRef.global_object": EntryCase(
        LocationBaseRef.global_object, lambda r, a, kw, api: LocationBaseRef.global_object(*a, **kw),
        lambda: dict(symbol_name="g", size=8, space_name="ram"),
    ),
    "LocationBaseRef.stack_frame": EntryCase(
        LocationBaseRef.stack_frame, lambda r, a, kw, api: LocationBaseRef.stack_frame(*a, **kw), lambda: {},
    ),
    "PostStateSnapshotRef.function_return": EntryCase(
        PostStateSnapshotRef.function_return, lambda r, a, kw, api: PostStateSnapshotRef.function_return(*a, **kw), lambda: {},
    ),
    "CanonicalLocation.__init__": EntryCase(
        CanonicalLocation.__init__, lambda r, a, kw, api: CanonicalLocation(*a, **kw),
        lambda: dict(base_param="p", offset=4, size=4, steps=(LocationStep("offset", 4),)),
    ),
    "CanonicalLocation.__init__#stackframe": EntryCase(
        CanonicalLocation.__init__, lambda r, a, kw, api: CanonicalLocation(*a, **kw),
        lambda: dict(base_param="stackframe", offset=4, size=4),
    ),
    "CanonicalLocation.__init__#base_ref": EntryCase(
        CanonicalLocation.__init__, lambda r, a, kw, api: CanonicalLocation(*a, **kw),
        lambda: dict(offset=4, size=4, base_ref=LocationBaseRef.parameter("p", index=0)),
    ),
    "PostStateReadRef.with_location": EntryCase(
        PostStateReadRef.with_location, lambda r, a, kw, api: r.with_location(*a, **kw),
        lambda: dict(location=_location()), receiver=lambda: PostStateReadRef(location=_location()),
    ),
    "PostStateReadRef.with_snapshot": EntryCase(
        PostStateReadRef.with_snapshot, lambda r, a, kw, api: r.with_snapshot(*a, **kw),
        lambda: dict(snapshot_ref=PostStateSnapshotRef.function_return()), receiver=lambda: PostStateReadRef(location=_location()),
    ),
    "ObservedMemoryReadRef.with_location": EntryCase(
        ObservedMemoryReadRef.with_location, lambda r, a, kw, api: r.with_location(*a, **kw),
        lambda: dict(location=_location(), snapshot_ref=None), receiver=lambda: ObservedMemoryReadRef(order_key=3),
    ),
    "ObservedMemoryReadRef.with_snapshot": EntryCase(
        ObservedMemoryReadRef.with_snapshot, lambda r, a, kw, api: r.with_snapshot(*a, **kw),
        lambda: dict(snapshot_ref=PostStateSnapshotRef.function_return()), receiver=lambda: ObservedMemoryReadRef(order_key=3),
    ),
    "PcodeOpRef.from_pcode_op": EntryCase(
        PcodeOpRef.from_pcode_op, lambda r, a, kw, api: PcodeOpRef.from_pcode_op(make_pcode_op(api), *a, **kw),
        lambda: dict(binary_id="B1", program_uid=7, function_entry_space="ram", function_entry_offset=0x100),
        api=PCODE_API, fixed=1,
    ),
    "ReductionAccumulatorProof.with_runtime_evidence": EntryCase(
        ReductionAccumulatorProof.with_runtime_evidence, lambda r, a, kw, api: r.with_runtime_evidence(*a, **kw),
        lambda: dict(
            limit_expr=Expression.parameter("count", 1, size=4), result_size=4,
            loop_body_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),),
            exact_return_witnesses=(), guard_constraints=(), signed_counter=True,
        ),
        receiver=_proof,
    ),
    # exact な戻り値の witness から scalar の prefix を正規化する分岐
    "ReductionAccumulatorProof.with_runtime_evidence#normalize_prefix": EntryCase(
        ReductionAccumulatorProof.with_runtime_evidence, lambda r, a, kw, api: r.with_runtime_evidence(*a, **kw),
        lambda: dict(
            limit_expr=Expression.parameter("count", 1, size=4), result_size=4, loop_body_witnesses=(),
            exact_return_witnesses=tuple(
                ReadonlyReductionWitness(exact_count=n, terms=tuple(_term(4 * i) for i in range(n))) for n in (1, 2, 3)
            ),
            guard_constraints=(), signed_counter=True,
        ),
        receiver=lambda: _proof(start_index=2, start_offset=8, loop_body_witnesses=()),
    ),
    # lane の受け手で seed の prefix を witness から補う分岐
    "ReductionAccumulatorProof.with_runtime_evidence#complete_seed": EntryCase(
        ReductionAccumulatorProof.with_runtime_evidence, lambda r, a, kw, api: r.with_runtime_evidence(*a, **kw),
        lambda: dict(
            limit_expr=Expression.parameter("count", 1, size=4), result_size=4,
            loop_body_witnesses=(ReadonlyReductionWitness(exact_count=1, terms=(_term(8),)),),
            exact_return_witnesses=(
                ReadonlyReductionWitness(exact_count=1, terms=(_term(0),)),
                ReadonlyReductionWitness(exact_count=2, terms=(_term(0), _term(4))),
            ),
            guard_constraints=(), signed_counter=True,
        ),
        receiver=lambda: _proof(stride=8, element_size=8, index_scale=8, lane_terms=((0, 4), (4, 4)), start_offset=8),
    ),
    "normalize_expansion_budget_truncations": EntryCase(
        unknowns_module.normalize_expansion_budget_truncations,
        lambda r, a, kw, api: unknowns_module.normalize_expansion_budget_truncations(*a, **kw),
        lambda: dict(items=[ExpansionBudgetTruncation(kind="k", dedup=(3, 2, 2)), ExpansionBudgetTruncation(kind="k", dedup=(3, 2, 2))]),
    ),
    "merge_expansion_budget_truncations": EntryCase(
        unknowns_module.merge_expansion_budget_truncations,
        lambda r, a, kw, api: unknowns_module.merge_expansion_budget_truncations(*a, **kw),
        lambda: dict(groups=[
            [ExpansionBudgetTruncation(kind="k", dedup=(3, 2, 2))],
            None,
            (ExpansionBudgetTruncation(kind="k", dedup=(3, 2, 2), referenced_event_ids=("e",)),),
        ]),
    ),
    "UnknownValueRef.deferred_call": EntryCase(
        UnknownValueRef.deferred_call, lambda r, a, kw, api: UnknownValueRef.deferred_call(*a, **kw),
        lambda: dict(placeholder_name="p", sequence=2),
    ),
    "UnknownValueRef.out_of_scope_call": EntryCase(
        UnknownValueRef.out_of_scope_call, lambda r, a, kw, api: UnknownValueRef.out_of_scope_call(*a, **kw),
        lambda: dict(reason="r", display_hint="d"),
    ),
    "UnknownValueRef.budget_exceeded": EntryCase(
        UnknownValueRef.budget_exceeded, lambda r, a, kw, api: UnknownValueRef.budget_exceeded(*a, **kw),
        lambda: dict(operation="expand", origin_kind="k"),
    ),
    "UnknownValueRef.opaque": EntryCase(
        UnknownValueRef.opaque, lambda r, a, kw, api: UnknownValueRef.opaque(*a, **kw),
        lambda: dict(reason="r", display_hint="d", origin_kind="k"),
    ),
    "UnknownValueRef.phi_circular": EntryCase(
        UnknownValueRef.phi_circular, lambda r, a, kw, api: UnknownValueRef.phi_circular(*a, **kw),
        lambda: dict(display_hint="phi"),
    ),
    "ExpansionBudgetTruncation.with_binding": EntryCase(
        ExpansionBudgetTruncation.with_binding, lambda r, a, kw, api: r.with_binding(*a, **kw),
        lambda: dict(surface="return", owner_scope_key=("scope", 1)), receiver=lambda: ExpansionBudgetTruncation(kind="k"),
    ),
    "ExpansionBudgetTruncation.with_binding#bound": EntryCase(
        ExpansionBudgetTruncation.with_binding, lambda r, a, kw, api: r.with_binding(*a, **kw),
        lambda: dict(surface="return", owner_scope_key=("scope", 1)),
        receiver=lambda: ExpansionBudgetTruncation(kind="k", surface="return", owner_scope_key=("scope", 1)),
    ),
    "CallTargetRef.from_function": EntryCase(
        CallTargetRef.from_function, lambda r, a, kw, api: CallTargetRef.from_function(make_function(api), *a, **kw),
        lambda: {}, api=FUNCTION_API, fixed=1,
    ),
    "CallTargetRef.from_code_address": EntryCase(
        CallTargetRef.from_code_address, lambda r, a, kw, api: CallTargetRef.from_code_address(*a, **kw),
        lambda: dict(address_value=0x1000, display_hint="d", program_id=7),
    ),
    "CallTargetRef.from_code_address#address": EntryCase(
        CallTargetRef.from_code_address,
        lambda r, a, kw, api: CallTargetRef.from_code_address(FakeAddress(api), *a, **kw),
        lambda: dict(display_hint="d", program_id=7), api={"FakeAddress.getOffset": 0x1000}, fixed=1,
    ),
    "CallTargetRef.from_name": EntryCase(
        CallTargetRef.from_name, lambda r, a, kw, api: CallTargetRef.from_name(*a, **kw),
        lambda: dict(function_name="f", program_id=7, entry_offset=0x100, is_external=True, library_name="libc",
                     is_thunk=False, thunked_is_external=False, thunked_library_name="libm"),
    ),
    "CallTargetRef.unknown": EntryCase(
        CallTargetRef.unknown, lambda r, a, kw, api: CallTargetRef.unknown(*a, **kw), lambda: dict(display_hint="u"),
    ),
    "coerce_call_target_ref": EntryCase(
        coerce_call_target_ref, lambda r, a, kw, api: coerce_call_target_ref(*a, **kw),
        lambda: dict(target=CallTargetRef.from_name("f")),
    ),
}

for _suffix, _pair in SUMMARY_PAIRS.items():
    ENTRY_CASES.update({
        f"compare_loop_summaries{_suffix}": EntryCase(
            loops_module.compare_loop_summaries, lambda r, a, kw, api: loops_module.compare_loop_summaries(*a, **kw),
            lambda _pair=_pair: dict(zip(("left", "right"), _pair())),
        ),
        f"LoopSummaryProofObligation.case_aware_solver_equality{_suffix}": EntryCase(
            LoopSummaryProofObligation.case_aware_solver_equality,
            lambda r, a, kw, api: LoopSummaryProofObligation.case_aware_solver_equality(*a, **kw),
            lambda _pair=_pair: dict(zip(("left", "right"), _pair()), reason="needs_solver"),
        ),
        f"loop_summary_method_b_key{_suffix}": EntryCase(
            loops_module.loop_summary_method_b_key, lambda r, a, kw, api: loops_module.loop_summary_method_b_key(*a, **kw),
            lambda _pair=_pair: dict(summary=_pair()[0]),
        ),
        f"loop_summary_method_b_key_at_result_size{_suffix}": EntryCase(
            loops_module.loop_summary_method_b_key_at_result_size,
            lambda r, a, kw, api: loops_module.loop_summary_method_b_key_at_result_size(*a, **kw),
            lambda _pair=_pair: dict(summary=_pair()[0], result_size=2),
        ),
    })

for _suffix, _receiver in PROOF_RECEIVERS.items():
    ENTRY_CASES.update({
        f"ReductionAccumulatorProof.loop_body_terms_for_count_value{_suffix}": EntryCase(
            ReductionAccumulatorProof.loop_body_terms_for_count_value,
            lambda r, a, kw, api: r.loop_body_terms_for_count_value(*a, **kw), lambda: dict(count_value=3),
            receiver=_receiver,
        ),
        f"ReductionAccumulatorProof.full_terms_for_count_value{_suffix}": EntryCase(
            ReductionAccumulatorProof.full_terms_for_count_value,
            lambda r, a, kw, api: r.full_terms_for_count_value(*a, **kw), lambda: dict(count_value=1),
            receiver=_receiver,
        ),
        f"ReductionAccumulatorProof.seed_terms_for_count_value{_suffix}": EntryCase(
            ReductionAccumulatorProof.seed_terms_for_count_value,
            lambda r, a, kw, api: r.seed_terms_for_count_value(*a, **kw), lambda: dict(count_value=1),
            receiver=_receiver,
        ),
        f"ReductionAccumulatorProof.readonly_term_sequence_contract_key{_suffix}": EntryCase(
            ReductionAccumulatorProof.readonly_term_sequence_contract_key,
            lambda r, a, kw, api: r.readonly_term_sequence_contract_key(*a, **kw), lambda: dict(result_size=4),
            receiver=_receiver,
        ),
        f"ReadonlyReductionRef.readonly_term_sequence_contract_key{_suffix}": EntryCase(
            ReadonlyReductionRef.readonly_term_sequence_contract_key,
            lambda r, a, kw, api: r.readonly_term_sequence_contract_key(*a, **kw), lambda: dict(result_size=4),
            receiver=lambda _receiver=_receiver: _receiver().lower_to_readonly_reduction_ref(),
        ),
    })


def _collector() -> Any:
    collector = unknowns_module.ExpansionBudgetCollector()
    collector.record(ExpansionBudgetTruncation(kind="k", dedup=(3, 2, 2), referenced_event_ids=("a",)))
    return collector


def _zero_argument(owner: type, name: str, receiver: Callable[[], Any], call: Optional[Callable[[Any], Any]] = None) -> EntryCase:
    """引数の無い method / property（ref を作る読み手）の行: 受け手の構成と代わりの型の variant で走る。"""

    member = owner.__dict__[name]
    function = member.fget if isinstance(member, property) else member
    invoke = call or (lambda r: getattr(r, name) if isinstance(member, property) else getattr(r, name)())
    return EntryCase(function, lambda r, a, kw, api, _invoke=invoke: _invoke(r), lambda: {}, receiver=receiver)


def _composed() -> Any:
    from scripts.function_tracer_pcode.core.runtime_refs.loops import ComposedLoopSummaryRef

    return ComposedLoopSummaryRef(prior=_loop_summary(), current=_lane_summary(), handoff_proof_key=("handoff", 1), source="composed")


def _corpus_instance(cls: type) -> Any:
    return corpus.build(cls, corpus.BASES[cls]())


ENTRY_CASES.update({
    "_loop_summary_term_at_index": EntryCase(
        loops_module._loop_summary_term_at_index, lambda r, a, kw, api: loops_module._loop_summary_term_at_index(*a, **kw),
        lambda: dict(summary=_loop_summary(), index=1),
    ),
    "_loop_summary_term_at_index#lanes": EntryCase(
        loops_module._loop_summary_term_at_index, lambda r, a, kw, api: loops_module._loop_summary_term_at_index(*a, **kw),
        lambda: dict(summary=_lane_summary(), index=3),
    ),
    "_loop_variable_binding_context_from_values": EntryCase(
        loops_module._loop_variable_binding_context_from_values,
        lambda r, a, kw, api: loops_module._loop_variable_binding_context_from_values(*a, **kw),
        lambda: dict(values=[_loop_variable_summary().limit_expr, _expr(2), (_expr(3), [_expr(4)])]),
    ),
    "ExpansionBudgetCollector.record": EntryCase(
        unknowns_module.ExpansionBudgetCollector.record, lambda r, a, kw, api: (r.record(*a, **kw), r.as_tuple())[1],
        lambda: dict(truncation=ExpansionBudgetTruncation(kind="k", dedup=(3, 2, 2), referenced_event_ids=("b",))),
        receiver=_collector,
    ),
    "ExpansionBudgetCollector.extend": EntryCase(
        unknowns_module.ExpansionBudgetCollector.extend, lambda r, a, kw, api: (r.extend(*a, **kw), r.as_tuple())[1],
        lambda: dict(items=[ExpansionBudgetTruncation(kind="k", dedup=(3, 2, 2), referenced_event_ids=("c",)), None]),
        receiver=_collector,
    ),
    "ExpansionBudgetCollector.as_tuple": _zero_argument(unknowns_module.ExpansionBudgetCollector, "as_tuple", _collector),
    "ComposedLoopSummaryRef.side_effect_profile": _zero_argument(loops_module.ComposedLoopSummaryRef, "side_effect_profile", _composed),
    "StateTransitionLoopSummaryRef.semantic_key": _zero_argument(
        loops_module.StateTransitionLoopSummaryRef, "semantic_key", lambda: _corpus_instance(loops_module.StateTransitionLoopSummaryRef),
    ),
    "CountedStateTransitionLoopSummaryRef.semantic_key": _zero_argument(
        loops_module.CountedStateTransitionLoopSummaryRef, "semantic_key",
        lambda: _corpus_instance(loops_module.CountedStateTransitionLoopSummaryRef),
    ),
})
for _suffix, _pair in SUMMARY_PAIRS.items():
    for _name in ("semantic_key", "pairwise_semantic_key"):
        ENTRY_CASES[f"LoopSummaryRef.{_name}{_suffix}"] = _zero_argument(LoopSummaryRef, _name, lambda _pair=_pair: _pair()[0])
for _suffix, _receiver in PROOF_RECEIVERS.items():
    for _name in ("loop_var_unit", "lower_to_loop_summary_ref", "lower_to_readonly_reduction", "lower_to_readonly_reduction_ref", "semantic_key"):
        ENTRY_CASES[f"ReductionAccumulatorProof.{_name}{_suffix}"] = _zero_argument(ReductionAccumulatorProof, _name, _receiver)
    for _name in ("semantic_key", "pairwise_semantic_key"):
        ENTRY_CASES[f"ReadonlyReductionRef.{_name}{_suffix}"] = _zero_argument(
            ReadonlyReductionRef, _name, lambda _receiver=_receiver: _receiver().lower_to_readonly_reduction_ref(),
        )


# ---------------------------------------------------------------------------
# 入口の一覧との突き合わせ（新しい入口は表に足さないと落ちる）
# ---------------------------------------------------------------------------


def _ref_modules() -> list:
    import importlib
    import pkgutil

    import scripts.function_tracer_pcode.core.runtime_refs as runtime_refs

    modules = [importlib.import_module(f"{runtime_refs.__name__}.{info.name}") for info in pkgutil.iter_modules(runtime_refs.__path__)]
    modules.append(call_target_module)
    return modules


def _discovered() -> Dict[str, Any]:
    """ref module の入口（`runtime_ref_entry` の関数・method、ref の class の classmethod / staticmethod と自前の `__init__`）。"""

    found: Dict[str, Any] = {}
    for module in _ref_modules():
        for name, value in vars(module).items():
            if inspect.isfunction(value) and value.__module__ == module.__name__ and runtime_ref_record.is_runtime_ref_entry(value):
                found[name] = value
            if isinstance(value, type) and value.__module__ == module.__name__ and runtime_ref_record.is_runtime_ref_record(value):
                for attribute, member in value.__dict__.items():
                    if isinstance(member, (classmethod, staticmethod)) or runtime_ref_record.is_runtime_ref_entry(member):
                        found[f"{value.__name__}.{attribute}"] = getattr(member, "__func__", member)
                    elif attribute == "__init__" and not getattr(value, "__dataclass_params__").init:
                        found[f"{value.__name__}.__init__"] = member
            elif isinstance(value, type) and value.__module__ == module.__name__:
                # ref でない class（`ExpansionBudgetCollector` など）の入口
                for attribute, member in value.__dict__.items():
                    if runtime_ref_record.is_runtime_ref_entry(member):
                        found[f"{value.__name__}.{attribute}"] = member
    return found


def _discovered_entry_functions() -> list:
    """入口の元の関数（包みの中身）。"""

    return [_original(function) for function in _discovered().values() if runtime_ref_record.is_runtime_ref_entry(function)]


def _ref_producing_callables() -> set:
    from scripts.function_tracer_pcode.tests.unit.runtime_ref_construction_guard import ConstructionGuard

    required = set()
    for label in ConstructionGuard.for_package().ref_producing_functions(with_arguments=False):
        owner, name = label.split(":")[1].split(".")
        required.add(name if owner == "None" else f"{owner}.{name}")
    return required


def test_every_entry_is_in_the_matrix():
    """入口はすべて行列にある。行列の行は入口か、ref を作る呼べる関数（古い名前の行を残さない）。"""

    table = {name.split("#", 1)[0] for name in ENTRY_CASES}
    discovered = set(_discovered())
    assert sorted(discovered - table) == []
    assert sorted(table - discovered - _ref_producing_callables()) == []


def test_every_ref_producing_callable_is_in_the_matrix():
    """ref を作る、外から呼べるすべての関数・method・property（引数の無いもの・ref でない class のものを含む）は
    行列の行を持つ（受け手の構成と代わりの型の variant で実行される）。"""

    table = {name.split("#", 1)[0] for name in ENTRY_CASES}
    assert sorted(_ref_producing_callables() - table) == []


def test_every_entry_wraps_its_arguments():
    """引数を持つ全入口（factory・自前の `__init__` を含む）が、引数を写す包み（`runtime_ref_entry` と同じ束縛）。"""

    def takes_arguments(function: Any) -> bool:
        parameters = list(inspect.signature(_original(function)).parameters)
        return bool(parameters[1:] if parameters[:1] in (["self"], ["cls"]) else parameters)

    assert sorted(
        name for name, function in _discovered().items()
        if takes_arguments(function) and not runtime_ref_record.is_runtime_ref_entry(function)
    ) == []


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
        elif name == "__init__" and runtime_ref_record.is_runtime_ref_entry(
            vars(importlib.import_module(module.name))[owner].__init__
        ):
            decorated.add(unit_name)  # 自前の `__init__` は `runtime_ref_record` が入口と同じ包みにする
    assert sorted(set(guard.ref_producing_functions()) - decorated) == []


# ---------------------------------------------------------------------------
# 行列
# ---------------------------------------------------------------------------


def _original(entry: Any) -> Any:
    function = getattr(entry, "__func__", entry)
    return runtime_ref_record._ENTRY_WRAPPERS.get(function, function)


def _parameters(case: EntryCase) -> List[inspect.Parameter]:
    """呼び出しで渡す引数（receiver と `fixed` を除く）。"""

    function = _original(case.entry)
    parameters = list(inspect.signature(function).parameters.values())
    receiver = parameters and parameters[0].name in ("self", "cls") and "." in function.__qualname__
    return parameters[int(bool(receiver)) + case.fixed:]


def _parameter_kinds(case: EntryCase) -> Dict[str, Tuple[str, bool]]:
    """引数 → (corpus の仕様の分類, Optional か)。"""

    function = _original(case.entry)
    hints = typing.get_type_hints(function, include_extras=True)
    kinds = {}
    for parameter in _parameters(case):
        hint = hints.get(parameter.name, Any)
        optional = typing.get_origin(hint) is typing.Union and type(None) in typing.get_args(hint)
        kinds[parameter.name] = (corpus.field_kind(hint), optional)
    return kinds


def _shapes(case: EntryCase) -> List[str]:
    """呼び出しの形: キーワード・位置（渡せる先頭の引数をすべて位置で）・混在（最初の 1 つだけ位置で）。"""

    parameters = _parameters(case)
    base = case.base()
    positional = [p for p in parameters if p.kind in (p.POSITIONAL_ONLY, p.POSITIONAL_OR_KEYWORD, p.VAR_POSITIONAL)]
    if any(p.kind is p.VAR_POSITIONAL and p.name in base for p in parameters):
        return ["positional"]
    if not positional or positional[0].name not in base:
        return ["keyword"]
    count = 0
    for parameter in positional:
        if parameter.name not in base or parameter.kind is parameter.VAR_POSITIONAL:
            break
        count += 1
    return ["keyword", "positional", "mixed"] if count > 1 else ["keyword", "positional"]


def _arguments(case: EntryCase, shape: str, kwargs: Dict[str, Any]) -> Tuple[Tuple[Any, ...], Dict[str, Any]]:
    """`kwargs`（名前 → 値）を呼び出しの形の `args` / `kwargs` にする。"""

    kwargs = dict(kwargs)
    if shape == "keyword":
        return (), kwargs
    args: List[Any] = []
    for parameter in _parameters(case):
        if parameter.kind is parameter.VAR_POSITIONAL:
            args.extend(kwargs.pop(parameter.name, ()))
            break
        if parameter.kind not in (parameter.POSITIONAL_ONLY, parameter.POSITIONAL_OR_KEYWORD) or parameter.name not in kwargs:
            break
        args.append(kwargs.pop(parameter.name))
        if shape == "mixed":
            break
    return tuple(args), kwargs


def _zero(value: Any) -> Any:
    return {int: 0, str: "", float: 0.0}.get(type(value))


def _argument_variants(case: EntryCase):
    kinds = _parameter_kinds(case)
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


#: 入力全体を変える variant: すべての scalar を偽る / ref を代わりの型（偽る・正直な双子）にする / その両方 /
#: すべての scalar（引数と API の戻り値）を、比較・hash・文字列化の callback が偽る値を返す外の object にする
DEEP_VARIANTS = ("lie_all", "duck", "duck_lie_all", "duck_objects", "callback_all")


def _matrix():
    for case_id, case in ENTRY_CASES.items():
        for shape in _shapes(case):
            yield pytest.param(case_id, shape, "exact", None, None, None, id=f"{case_id}:{shape}:exact")
            for label, name, item, twin in _argument_variants(case):
                yield pytest.param(case_id, shape, "arg", name, item, twin, id=f"{case_id}:{shape}:{label}")
            for label, key, item, twin in _api_variants(case):
                yield pytest.param(case_id, shape, "api", key, item, twin, id=f"{case_id}:{shape}:{label}")
            for variant in DEEP_VARIANTS:
                yield pytest.param(case_id, shape, variant, None, None, None, id=f"{case_id}:{shape}:{variant}")


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
            try:
                legacy = json.dumps(materialize(item), sort_keys=True)
            except Exception as error:  # LEGACY の JSON に写せない ref（tuple の key の dict を持つなど）
                legacy = ("unencodable", type(error).__name__)
            out.append((legacy, view(stable_key(item)) if stable_key else None))
    return out


def _disguised_receiver(receiver: Any, lying: bool, objects: bool = False) -> Any:
    """受け手の ref の field と容器の field（中の ref と scalar）を代わりの型にした受け手（構築の検証も通る）。

    受け手の scalar の field は owner が写すので変えない。
    """

    def eligible(value: Any) -> bool:
        if dataclasses.is_dataclass(value) or type(value) in (tuple, list):
            return True
        return objects and type(value).__module__.startswith("scripts.function_tracer_pcode.") and not callable(value)

    changes = {
        item.name: disguise(getattr(receiver, item.name), lying, objects=objects)
        for item in dataclasses.fields(receiver)
        if item.init and eligible(getattr(receiver, item.name))
    }
    return dataclasses.replace(receiver, **changes) if changes else receiver


def _inputs(case: EntryCase, where: str, name: Optional[str], value: Any, shape: str, *, twin: bool):
    """1 回の呼び出しの (受け手, args, kwargs, api)。`twin` なら deep variant の正直な双子。"""

    kwargs = case.base()
    api = dict(case.api or {})
    receiver = case.receiver() if case.receiver is not None else None
    if where == "arg":
        kwargs[name] = value
    elif where == "api":
        api[name] = value
    elif where in ("lie_all", "duck_lie_all") and not twin:
        kwargs = {key: lie_deep(item) for key, item in kwargs.items()}
        api = {key: (Liar(int(item)) if key in BOOLEAN_API else lie(item)) for key, item in api.items()}
    elif where in ("lie_all", "duck_lie_all") and twin:
        api = {key: (bool(item) if key in BOOLEAN_API else item) for key, item in api.items()}
    elif where == "callback_all":
        # 外の object（Java の object の代わり）: 双子は callback が基底型の値を返す同じ形
        kwargs = {key: callbacks(item, not twin) for key, item in kwargs.items()}
        api = {key: (item if key in BOOLEAN_API else callbacks(item, not twin)) for key, item in api.items()}
    if where in ("duck", "duck_lie_all", "duck_objects"):
        # `duck_objects`: 式・storage など ref 以外の package の object も代わりの型にする（注釈が Any の位置）
        lying = not twin
        objects = where == "duck_objects"
        kwargs = {
            key: disguise(item, lying, objects=objects)
            if dataclasses.is_dataclass(item) or type(item) in (tuple, list) or (objects and type(item).__module__.startswith("scripts.function_tracer_pcode."))
            else item
            for key, item in kwargs.items()
        }
        if receiver is not None and dataclasses.is_dataclass(receiver):
            receiver = _disguised_receiver(receiver, lying, objects)
    args, kwargs = _arguments(case, shape, kwargs)
    return receiver, args, kwargs, api


def _run(case: EntryCase, where: str, name: Optional[str], value: Any, shape: str, *, twin: bool):
    receiver, args, kwargs, api = _inputs(case, where, name, value, shape, twin=twin)
    return case.call(receiver, args, kwargs, api)


@pytest.mark.parametrize("case_id, shape, where, name, item, twin", list(_matrix()))
def test_entry_builds_the_twin_without_calling_subclass_code(case_id, shape, where, name, item, twin):
    case = ENTRY_CASES[case_id]
    deep = where in DEEP_VARIANTS
    try:
        expected = _run(case, where, name, twin if not deep else None, shape, twin=True)
    except Exception as error:
        HOOK_CALLS.clear()
        with pytest.raises(type(error)):
            _run(case, where, name, item, shape, twin=False)
        assert HOOK_CALLS == {}
        return
    HOOK_CALLS.clear()
    built = _run(case, where, name, item, shape, twin=False)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert view(built) == view(expected)
    if not deep and not _holds_subclass(built):
        assert _outputs(built) == _outputs(expected)


def test_call_shapes_are_exercised():
    """位置・混在の呼び出しを持つ入口が十分にある（`_shapes` が黙って全部をキーワードにしない）。"""

    shapes = {case_id: _shapes(case) for case_id, case in ENTRY_CASES.items()}
    assert sum("positional" in s for s in shapes.values()) >= 25
    assert sum("mixed" in s for s in shapes.values()) >= 10
    assert "positional" in shapes["CanonicalLocation.__init__"] and "mixed" in shapes["CanonicalLocation.__init__"]
    assert shapes["merge_expansion_budget_truncations"] == ["positional"]


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


# ---------------------------------------------------------------------------
# loop の key の組み立て（入口が到達する読み手）: 値の種類ごとに、代わりの型（偽る / 正直な双子）で読む
# ---------------------------------------------------------------------------


def _key_values() -> Dict[str, Any]:
    from scripts.function_tracer_pcode.core.runtime_refs.loops import LoopVariableIdentityRef
    from scripts.function_tracer_pcode.core.storage import StorageInfo

    parameter = Expression.parameter("n", 1, size=4)
    storage = StorageInfo(is_register=True, space_name="register", register_name="x0", offset=8, size=8)
    variable = Expression.variable("v", size=4, storage_info=storage)
    loop_variable = Expression.variable("i", size=4, runtime_ref=LoopVariableIdentityRef(role="induction", varnode_key=("unique", 0x10, 4)))
    return {
        "constant": _expr(3),
        "parameter": parameter,
        "parameter_storage": Expression.parameter("s", size=8, storage_info=storage),
        "variable_storage": variable,
        "variable_runtime": loop_variable,
        "binary": Expression.binary_op("+", parameter, _expr(2)),
        "memory": Expression.memory(Expression.binary_op("+", parameter, _expr(4)), size=4, read_order_key=2),
        "phi": Expression.phi([(Expression.binary_op("<", parameter, _expr(1)), _expr(1)), (None, parameter)]),
        "unknown": Expression.unknown("u"),
        "containers": (1, "a", [2, ("b", 3.5)], {"k": 4, "j": (5,)}, b"\x01", True, None),
        "ref": LocationBaseRef.parameter("p", index=0),
        "summary": _loop_summary(limit_expr=parameter),
    }


@pytest.mark.parametrize("builder", ["_loop_object_key", "_loop_object_semantic_key", "_loop_expression_semantic_key"])
@pytest.mark.parametrize("kind", list(_key_values()))
def test_loop_key_builders_read_every_value_kind_on_base_values(builder, kind):
    """式・storage・ref・容器を代わりの型（偽る / 正直な双子）にしても、key は双子と同じで hook は 0 回。"""

    function = getattr(loops_module, builder)
    value = _key_values()[kind]
    context = loops_module._loop_variable_binding_context_from_values(value) if builder != "_loop_object_key" else None
    arguments = () if builder == "_loop_object_key" else (context,)
    twin = function(disguise(value, False, objects=True), *arguments)
    lying = disguise(value, True, objects=True)
    HOOK_CALLS.clear()
    lied = function(lying, *arguments)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert _without_unidentified(view(lied)) == _without_unidentified(view(twin))


def _without_unidentified(value: Any) -> Any:
    """識別できない値（PHI など）の構造 key の process 内の serial と nonce を外した view（呼ぶたびに変わる）。"""

    if type(value) is tuple:
        items = tuple(_without_unidentified(item) for item in value)
        if len(items) == 2 and items[0] == "tuple" and items[1] and items[1][0] == ("str", "exact_tail_unidentified"):
            return ("tuple", items[1][:2])
        return items
    return value


@pytest.mark.parametrize("kind", list(_key_values()))
def test_loop_binding_context_reads_every_value_kind_on_base_values(kind):
    value = _key_values()[kind]
    twin = loops_module._loop_variable_binding_context_from_values(disguise(value, False, objects=True))
    lying = disguise(value, True, objects=True)
    HOOK_CALLS.clear()
    lied = loops_module._loop_variable_binding_context_from_values(lying)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    assert view(lied) == view(twin)


# ---------------------------------------------------------------------------
# 引数の無い読み手（method / property）を全部: 偽る値・代わりの型で作った ref と、双子で作った ref で比べる
# ---------------------------------------------------------------------------


def _zero_argument_members(cls: type) -> List[str]:
    names = []
    for name, member in vars(cls).items():
        if name.startswith("_") and not (name.startswith("__") and name.endswith("__")):
            continue
        if name in ("__init__", "__post_init__", "__setattr__", "__delattr__", "__repr__", "__eq__", "__hash__", "__init_subclass__"):
            continue
        if isinstance(member, property):
            names.append(name)
        elif inspect.isfunction(member):
            parameters = [p for p in inspect.signature(member).parameters.values() if p.default is p.empty and p.kind in (p.POSITIONAL_ONLY, p.POSITIONAL_OR_KEYWORD)]
            if len(parameters) == 1:
                names.append(name)
    return sorted(names)


def _read(instance: Any, name: str) -> Any:
    try:
        value = getattr(instance, name)
        if callable(value) and not isinstance(getattr(type(instance), name, None), property):
            value = value()
        if inspect.isgenerator(value):
            value = list(value)
        return ("value", value)
    except Exception as error:
        return ("raised", type(error).__name__)


@pytest.mark.parametrize("shape", ["leaves", "listed"])
@pytest.mark.parametrize("cls", corpus.REF_CLASSES, ids=lambda cls: cls.__name__)
def test_every_zero_argument_reader_of_a_ref_reads_on_base_values(cls, shape):
    """corpus の基底の入力の、写されない位置（Any・record・list）を偽る値と代わりの型にして作った ref の、引数の無い
    すべての method / property の結果が、双子（正直な代わりの型）から作った ref と同じで、hook は 0 回。

    `listed` は注釈が Any の位置の scalar を 1 要素の list に入れる（受理したまま持つ容器の中の葉を読む経路）。
    """

    kinds = corpus.field_kinds(cls)

    def inputs(lying: bool) -> Dict[str, Any]:
        kwargs = corpus.BASES[cls]()
        out = {}
        for name, value in kwargs.items():
            if kinds.get(name) == "object" or type(value) is list:
                if shape == "listed" and type(value) in (int, str, float):
                    value = [value]
                value = disguise(value, lying, objects=True)
                if lying:
                    value = lie_deep(value)
            out[name] = value
        return out

    twin_inputs, lying_inputs = inputs(False), inputs(True)
    try:
        twin = corpus.build(cls, twin_inputs)
    except Exception as error:
        HOOK_CALLS.clear()
        with pytest.raises(type(error)):
            corpus.build(cls, lying_inputs)
        assert HOOK_CALLS == {}
        return
    HOOK_CALLS.clear()
    built = corpus.build(cls, lying_inputs)
    assert HOOK_CALLS == {}, dict(HOOK_CALLS)
    for name in _zero_argument_members(cls):
        expected = _read(twin, name)
        HOOK_CALLS.clear()
        got = _read(built, name)
        assert HOOK_CALLS == {}, (name, dict(HOOK_CALLS))
        assert view(got) == view(expected), name

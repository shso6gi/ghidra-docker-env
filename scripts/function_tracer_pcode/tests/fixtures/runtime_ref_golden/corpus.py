# -*- coding: utf-8 -*-
"""runtime ref の scalar の正規化（Issue #242）の golden corpus（**変更前と変更後の commit で同じ入力**）。

この module は `core/runtime_refs`・`core/call_target`・`core/expression` しか使わない。正規化の owner
（`core/runtime_ref_record`）には依存しないので、変更前の commit へそのまま持っていっても同じ ref を
組める（`tests/tools/record_runtime_ref_golden.py` が両方の commit でこの corpus を使う）。

- 模擬型: 外の runtime（JPype）の scalar の subclass。subclass の code（`__int__` / `__repr__` / 比較など）
  が呼ばれた回数を `SUBCLASS_CALLS` に数える。値と振る舞いは基底型と同じ（`Weird` と `JBoolean` を除く:
  §4.3 の意図した差 D1 / D2 / D3 の入力）。
- variant: ref の class ごとに、全 field が exact な基底の構築入力（`BASES`）と、scalar の注釈の field
  （int / bool / str / float / tuple）を 1 つずつ模擬型の値に替えた入力。
- 双子（twin）: variant の入力を型規則（計画 v3 §4.3 の表）で写した入力。規則の **仕様** をこの module
  が独立に持つ（`twin_value`）。変更後の ref は入力から作っても双子から作っても同じ観測になること、
  変更前（main）の観測との差は意図した差（`INTENDED_DIFFERENCES`）だけであることを test が確かめる。
"""

from __future__ import annotations

import collections
import dataclasses
import enum
import typing
from typing import Any, Callable, Dict, Iterator, List, Tuple

from scripts.function_tracer_pcode.core.call_target import CallTargetRef
from scripts.function_tracer_pcode.core.expression import Expression
from scripts.function_tracer_pcode.core.runtime_refs.call_arguments import (
    AbiArgumentSlotRef,
    FreshCallArgumentRef,
)
from scripts.function_tracer_pcode.core.runtime_refs.call_models import CallModelCandidateRef
from scripts.function_tracer_pcode.core.runtime_refs.locations import (
    AddressValueRef,
    CanonicalLocation,
    LocationBaseRef,
    LocationStep,
    ObservedMemoryReadRef,
    PostStateReadRef,
    PostStateSnapshotRef,
    PostStateValueRef,
)
from scripts.function_tracer_pcode.core.runtime_refs.loops import (
    ComposedLoopSummaryRef,
    CountedLoopSummaryRef,
    CountedStateTransitionLoopSummaryRef,
    LoopBinderScope,
    LoopBodyEffectRef,
    LoopCaseRef,
    LoopSideEffectProfileRef,
    LoopSummaryComparisonResult,
    LoopSummaryProofObligation,
    LoopSummaryRef,
    LoopTermDescriptorRef,
    LoopVariableIdentityRef,
    StateTransitionLoopSummaryRef,
    _LoopVariableBindingContext,
)
from scripts.function_tracer_pcode.core.runtime_refs.pcode import PcodeBlockRef, PcodeOpRef
from scripts.function_tracer_pcode.core.runtime_refs.readonly import (
    ReadonlyReductionLowering,
    ReadonlyReductionRef,
    ReadonlyReductionTermRef,
    ReadonlyReductionWitness,
    ReductionAccumulatorProof,
)
from scripts.function_tracer_pcode.core.runtime_refs.unknowns import (
    DeferredCallRef,
    ExpansionBudgetTruncation,
    UnknownValueRef,
)

# ---------------------------------------------------------------------------
# 模擬型（JPype の boxed scalar の代わり）
# ---------------------------------------------------------------------------

#: subclass の code が呼ばれた回数（型の名前・method の名前 → 回数）。
SUBCLASS_CALLS: "collections.Counter[str]" = collections.Counter()

#: 数える method（値は基底型の実装に委ねる。`__eq__` / `__hash__` も委ねるので値の等しさは基底型と同じ）。
_INT_METHODS = (
    "__int__", "__index__", "__float__", "__bool__", "__repr__", "__str__", "__format__",
    "__eq__", "__ne__", "__hash__", "__lt__", "__le__", "__gt__", "__ge__",
    "__neg__", "__pos__", "__abs__", "__invert__",
    "__add__", "__radd__", "__sub__", "__rsub__", "__mul__", "__rmul__",
    "__floordiv__", "__rfloordiv__", "__mod__", "__rmod__", "__and__", "__rand__",
    "__or__", "__ror__", "__xor__", "__rxor__", "__lshift__", "__rshift__",
)
_STR_METHODS = (
    "__str__", "__repr__", "__format__", "__eq__", "__ne__", "__hash__", "__lt__", "__le__",
    "__gt__", "__ge__", "__len__", "__iter__", "__getitem__", "__contains__", "__add__",
    "__mod__", "__bool__",
)
_FLOAT_METHODS = (
    "__int__", "__float__", "__bool__", "__repr__", "__str__", "__format__", "__eq__", "__ne__",
    "__hash__", "__lt__", "__le__", "__gt__", "__ge__", "__add__", "__radd__", "__sub__",
    "__mul__", "__neg__",
)


def _counting(base: type, names: Tuple[str, ...]) -> Callable[[type], type]:
    def decorate(cls: type) -> type:
        for name in names:
            if name in cls.__dict__ or not hasattr(base, name):
                continue
            implementation = getattr(base, name)

            def method(self, *args, _name=name, _impl=implementation):
                SUBCLASS_CALLS[f"{type(self).__name__}.{_name}"] += 1
                return _impl(self, *args)

            method.__name__ = name
            setattr(cls, name, method)
        return cls

    return decorate


@_counting(int, _INT_METHODS)
class JInt(int):
    """`jpype.types.JInt` の代わり（値・`repr`・hash・JSON は int と同じ）。"""


class JLong(JInt):
    pass


class JShort(JInt):
    pass


class JByte(JInt):
    pass


@_counting(int, _INT_METHODS)
class Integer(int):
    """`java.lang.Integer` の boxed の値の代わり。"""


Integer.__module__ = "java.lang"


@_counting(int, _INT_METHODS)
class JBoolean(int):
    """`jpype.types.JBoolean` の代わり（int の subclass で、`repr` は `'True'` / `'False'`）。"""

    def __repr__(self) -> str:
        SUBCLASS_CALLS["JBoolean.__repr__"] += 1
        return "True" if int.__index__(self) else "False"

    __str__ = __repr__


@_counting(int, _INT_METHODS)
class Weird(int):
    """独自の `__eq__` / `__hash__` を持つ int の subclass（偶奇だけで比べる。意図した差 D1 の入力）。"""

    def __eq__(self, other: Any) -> bool:
        SUBCLASS_CALLS["Weird.__eq__"] += 1
        if isinstance(other, int):
            return int.__index__(self) % 2 == int.__index__(other) % 2
        return NotImplemented

    def __ne__(self, other: Any) -> bool:
        result = self.__eq__(other)
        return result if result is NotImplemented else not result

    def __hash__(self) -> int:
        SUBCLASS_CALLS["Weird.__hash__"] += 1
        return int.__index__(self) % 2


@_counting(str, _STR_METHODS)
class JString(str):
    """str の subclass（JPype は Java の文字列を `str` で返すが、型規則の行として持つ）。"""


@_counting(float, _FLOAT_METHODS)
class JDouble(float):
    pass


class IE(enum.IntEnum):
    SEVEN = 7
    ONE = 1


class SE(str, enum.Enum):
    SYM = "sym"


# ---------------------------------------------------------------------------
# 型規則の仕様（計画 v3 §4.3 の表。owner の実装とは独立に書く）
# ---------------------------------------------------------------------------


def field_kind(annotation: Any) -> str:
    """field の注釈の分類: ``int`` / ``bool`` / ``str`` / ``float`` / ``tuple`` / ``record`` / ``object``。

    ``record`` は注釈が dataclass の型（ref の class）: 値は object として持つが、scalar の subclass だけは
    基底型の値になる（review 4: その値の属性の読みが subclass の code を呼ばないように）。
    """

    origin = typing.get_origin(annotation)
    args = typing.get_args(annotation)
    if origin is typing.Union:
        rest = [arg for arg in args if arg is not type(None)]
        return field_kind(rest[0]) if len(rest) == 1 else "object"
    if annotation in (int, bool, str, float):
        return annotation.__name__
    if origin is tuple:
        return "tuple"
    if isinstance(annotation, type) and dataclasses.is_dataclass(annotation):
        return "record"
    return "object"


def twin_value(value: Any, kind: str) -> Any:
    """型規則で写した値（exact な値・Enum の member・scalar でない値はそのまま）。"""

    holder = type(value)
    if kind == "object":
        return value
    if kind == "tuple" and issubclass(holder, tuple):
        # tuple の容器（subclass・named tuple を含む: 組み込みの tuple になる）を辿る。葉は注釈によらず値の基底型へ
        return tuple(
            twin_value(item, "tuple" if issubclass(type(item), tuple) else "element") for item in tuple.__iter__(value)
        )
    if kind == "tuple" and type(value) is list:
        return value  # list は辿らない
    if value is None or holder in (int, bool, str, float) or isinstance(value, enum.Enum):
        return value
    if isinstance(value, int):
        return int.__index__(value) != 0 if kind == "bool" else int.__index__(value)
    if isinstance(value, str):
        return str.__str__(value)
    if isinstance(value, float):
        return float.__float__(value)
    return value


def field_kinds(cls: type) -> Dict[str, str]:
    hints = typing.get_type_hints(cls)
    return {item.name: field_kind(hints[item.name]) for item in dataclasses.fields(cls)}


# ---------------------------------------------------------------------------
# 基底の構築入力（全 field が exact な値）
# ---------------------------------------------------------------------------


def _expr(value: int = 1) -> Expression:
    return Expression.constant(value, size=4)


def _param_base() -> LocationBaseRef:
    return LocationBaseRef(kind="parameter", parameter_name="base", parameter_index=0, display_hint="base")


def _pcode_op() -> PcodeOpRef:
    return PcodeOpRef(address_offset=0x1000, seq_time=1, seq_order=2, block_index=0, mnemonic="LOAD",
                      input_sizes=(8,), output_size=4, binary_id="B1", function_entry_offset=0x100)


def _term_descriptor() -> LoopTermDescriptorRef:
    return LoopTermDescriptorRef(kind="memory_load", reduction_kind="sum", location_base_ref=_param_base(),
                                 start_offset=0, stride=4, element_size=4, result_size=4)


def _profile() -> LoopSideEffectProfileRef:
    return LoopSideEffectProfileRef(profile="pure_memory_read", memory_reads=True, effect_count=0)


def _loop_summary() -> LoopSummaryRef:
    return LoopSummaryRef(start_expr=_expr(0), limit_expr=_expr(8), step_expr=_expr(1),
                          term_descriptor=_term_descriptor(), side_effect_profile=_profile())


def _proof() -> ReductionAccumulatorProof:
    return ReductionAccumulatorProof(
        reduction_kind="memory_sum", pointer_base_ref=_param_base(), count_parameter_name="count",
        count_parameter_index=1, limit_expr=_expr(8), result_size=4, stride=4, element_size=4,
        index_scale=4,
    )


def _location() -> CanonicalLocation:
    return CanonicalLocation(base_ref=_param_base(), offset=4, size=4, steps=(LocationStep(kind="offset", value=4),))


BASES: Dict[type, Callable[[], Dict[str, Any]]] = {
    AbiArgumentSlotRef: lambda: dict(ordinal=1, storage_class="gpr", width_bits=64,
                                     storage_identity_key=("register", 8, 8), declared_type_name="int"),
    FreshCallArgumentRef: lambda: dict(binary_id="B1", slot=AbiArgumentSlotRef(ordinal=0),
                                       call_site_key=("call", 4096, 1), reason="call_argument_unrecovered"),
    CallModelCandidateRef: lambda: dict(
        provider="c99_math_catalog_v1", canonical_symbol="sin",
        signature_key=("c99_math_signature_v1", "sin", (("float", 64),), ("float", 64)),
        provenance_key=("external_import_provenance_v1", "import", "libm", ("sin",)),
    ),
    AddressValueRef: lambda: dict(address_offset=0x4000, source="ram", display_hint="g", program_id=7,
                                  space_id=1, space_name="ram", symbol_name="g", block_name=".data",
                                  is_initialized=True, can_read=True, can_write=False, can_execute=False,
                                  is_volatile=False, object_symbol_name="g", object_base_offset=0x4000,
                                  object_size=8),
    LocationBaseRef: lambda: dict(kind="parameter", parameter_name="a", parameter_index=1,
                                  owner_program_id=7, owner_entry_offset=0x100, storage_space_id=1,
                                  storage_space="register", storage_offset=8, storage_size=8,
                                  storage_identity_key=("register", 8, 8), display_hint="a"),
    LocationStep: lambda: dict(kind="offset", value=4),
    CanonicalLocation: lambda: dict(base_ref=_param_base(), offset=4, size=4,
                                    steps=(LocationStep(kind="offset", value=4),)),
    PostStateValueRef: lambda: dict(location=_location(), snapshot_ref=None, source="effect_summary",
                                    state_kind="materialized_final_value"),
    PostStateSnapshotRef: lambda: dict(scope="call", source="effect_summary", epoch="e1", pcode_op_ref=_pcode_op()),
    PostStateReadRef: lambda: dict(location=_location(), snapshot_ref=None, source="effect_summary",
                                   state_kind="symbolic_read"),
    ObservedMemoryReadRef: lambda: dict(order_key=3, location=_location(), snapshot_ref=None,
                                        pcode_op_ref=_pcode_op(), source="observed_load"),
    LoopVariableIdentityRef: lambda: dict(role="iv", varnode_key=("register", 16, 8), binder_ordinal=0),
    _LoopVariableBindingContext: lambda: dict(stable_to_binder={("register", 16, 8): ("iv", 0)}),
    LoopBodyEffectRef: lambda: dict(kind="memory_write", source="loop_body", scope="body", address_space="ram",
                                    location=None, value_expr=None, guard_constraints=("g", 1),
                                    path_condition_sets=(("p", 1),), guard_paths_incomplete=False,
                                    target_ref=None, order_key=2, keyable=True, unkeyable_reason=None),
    LoopSideEffectProfileRef: lambda: dict(profile="pure_memory_read", memory_reads=True, memory_writes=False,
                                           calls=False, escapes=False, conditional_guards=False,
                                           context_memory_writes=False, context_calls=False,
                                           context_escapes=False, context_conditional_guards=False,
                                           effect_count=1, guard_count=0),
    LoopTermDescriptorRef: lambda: dict(kind="memory_load", reduction_kind="sum", location_base_ref=_param_base(),
                                        start_offset=0, stride=4, element_size=4, result_size=4,
                                        residue_cases=((2, 0, 1, 0),), residue_bias_terms=((1, 0, 3),),
                                        lane_terms=((0, 4),)),
    LoopCaseRef: lambda: dict(path_conditions=("c", 1), body_effect=None, term_expr=None, case_kind="body",
                              source="method_b"),
    # `scoped_fields` は 1 要素（複数の str の frozenset の並びは process の hash の seed に依る: golden を決められない）
    LoopBinderScope: lambda: dict(binders=(_expr(5),), scoped_fields=frozenset({"term_expr"})),
    LoopSummaryRef: lambda: dict(start_expr=_expr(0), limit_expr=_expr(8), step_expr=_expr(1),
                                 term_descriptor=_term_descriptor(), seed_terms=(1, 2), seed_term_count=2,
                                 side_effect_profile=_profile(), guard_constraints=("g", 1),
                                 loop_var_unit="index", source="loop", constant_bias=0),
    ComposedLoopSummaryRef: lambda: dict(prior=None, current=None, handoff_proof_key=("handoff", 1),
                                         source="composed"),
    LoopSummaryProofObligation: lambda: dict(proof_kind="loop_equal", left_summary_key=("l", 1),
                                             right_summary_key=("r", 2), relation="equal",
                                             required_evidence=("e1", "e2"), reason="needs_solver"),
    LoopSummaryComparisonResult: lambda: dict(status="unknown", reason="r", proof_obligation=None),
    CountedLoopSummaryRef: lambda: dict(induction_step=1, result_size=4, signed_loop=True,
                                        residue_cases=((2, 0, 1, 0), (2, 1, -1, 0)),
                                        residue_bias_terms=((1, 0, 5),), source="counted"),
    StateTransitionLoopSummaryRef: lambda: dict(state_guard=None, transition_expr=None, result_size=4,
                                                state_size=4, side_effect_profile=_profile(), source="state"),
    CountedStateTransitionLoopSummaryRef: lambda: dict(initial_state=None, start_expr=_expr(0),
                                                       limit_expr=_expr(8), step_expr=_expr(1),
                                                       transition_expr=None, state_placeholder=None,
                                                       side_effect_profile=_profile(), guard_constraints=("g", 1),
                                                       state_size=4, result_size=4, signed_loop=False,
                                                       handoff_proof_key=("handoff", 2), source="counted_state"),
    PcodeOpRef: lambda: dict(address_offset=0x1000, seq_time=1, seq_order=2, block_index=0, mnemonic="LOAD",
                             input_sizes=(8, 4), output_size=4, binary_id="B1", function_entry_space="ram",
                             function_entry_offset=0x100, target_space="ram", target_offset=0x2000, opcode=None,
                             local_op_ordinal=3, program_uid=11),
    PcodeBlockRef: lambda: dict(block_index=2, start_address_offset=0x1000, binary_id="B1",
                                function_entry_space="ram", function_entry_offset=0x100),
    ReadonlyReductionTermRef: lambda: dict(byte_offset=4, access_size=4),
    ReadonlyReductionWitness: lambda: dict(exact_count=1, terms=(ReadonlyReductionTermRef(byte_offset=0, access_size=4),),
                                           count_semantics="exact"),
    ReductionAccumulatorProof: lambda: dict(
        reduction_kind="memory_sum", pointer_base_ref=_param_base(), count_parameter_name="count",
        count_parameter_index=1, limit_expr=_expr(8), result_size=4, stride=4, element_size=4,
        count_parameter_storage_identity_key=("register", 16, 8), start_offset=0, start_index=0,
        index_step=1, index_scale=4, signed_counter=True, seed_term_count=0, lane_terms=((0, 4),),
        constant_bias=0, return_region_value_proven=False, source="readonly",
    ),
    ReadonlyReductionRef: lambda: dict(reduction_kind="memory_sum", pointer_base_ref=_param_base(),
                                       count_parameter_name="count", count_parameter_index=1,
                                       count_parameter_storage_identity_key=("register", 16, 8), stride=4,
                                       element_size=4, result_size=4, start_offset=0, signed_counter=True,
                                       source="readonly", constant_bias=0),
    ReadonlyReductionLowering: lambda: dict(proof=_proof(), loop_summary=_loop_summary(),
                                            readonly_reduction=_proof().lower_to_readonly_reduction_ref(),
                                            lowering_kind="readonly"),
    DeferredCallRef: lambda: dict(caller_program_id=7, caller_entry_offset=0x100, pcode_op_ref=_pcode_op(),
                                  target_ref=None, sequence=2),
    UnknownValueRef: lambda: dict(kind="call_return", reason="r", target_ref=None, deferred_call_ref=None,
                                  origin_kind="call", origin_ref=None, display_hint="u"),
    ExpansionBudgetTruncation: lambda: dict(kind="dedup_case_limit", surface="return", owner_scope_key=("scope", 1),
                                            label="l", pcode_op_ref=None, dedup=(17, 16, 16), paths=(3, 2, 2),
                                            conditions=(5, 4), callee_scope_key=("callee", 2),
                                            referenced_event_ids=("e1",)),
    CallTargetRef: lambda: dict(kind="function", function_name="f", program_id=7, entry_offset=None,
                                address_offset=None, display_hint="f", is_external=True, library_name="libc",
                                is_thunk=False, thunked_is_external=None, thunked_library_name=None),
}

# ---------------------------------------------------------------------------
# variant（field ごとに模擬型の値へ替える）
# ---------------------------------------------------------------------------

#: int の注釈の field に入れる値（全 field）。
INT_VALUES: Tuple[Tuple[str, Callable[[], Any]], ...] = (
    ("jint", lambda: JInt(7)),
    ("jboolean_true", lambda: JBoolean(1)),
    ("jboolean_false", lambda: JBoolean(0)),
    ("weird", lambda: Weird(7)),
    ("intenum", lambda: IE.SEVEN),
    ("exact", lambda: 7),
    ("jstring_digits", lambda: JString("7")),
    ("jdouble", lambda: JDouble(7.0)),
)

#: 代表の field だけに入れる値（JPype の各整数型・`java.lang.Integer`・境界）。
INT_EXTRA_VALUES: Tuple[Tuple[str, Callable[[], Any]], ...] = (
    ("jlong", lambda: JLong(7)),
    ("jshort", lambda: JShort(7)),
    ("jbyte", lambda: JByte(7)),
    ("java_integer", lambda: Integer(7)),
    ("jint_zero", lambda: JInt(0)),
    ("jint_minus_one", lambda: JInt(-1)),
    ("jint_2p31m1", lambda: JInt(2**31 - 1)),
    ("jint_m2p31", lambda: JInt(-(2**31))),
    ("jlong_2p63m1", lambda: JLong(2**63 - 1)),
    ("jlong_m2p63", lambda: JLong(-(2**63))),
    ("jlong_2p64m1", lambda: JLong(2**64 - 1)),
)
INT_EXTRA_FIELDS = frozenset({
    (LocationBaseRef, "parameter_index"),
    (PcodeOpRef, "address_offset"),
    (AddressValueRef, "address_offset"),
    (CallTargetRef, "entry_offset"),
    (CanonicalLocation, "offset"),
})

BOOL_VALUES: Tuple[Tuple[str, Callable[[], Any]], ...] = (
    ("jboolean_true", lambda: JBoolean(1)),
    ("jboolean_false", lambda: JBoolean(0)),
    ("jint_one", lambda: JInt(1)),
    ("exact_true", lambda: True),
    ("exact_one", lambda: 1),
)

STR_VALUES: Tuple[Tuple[str, Callable[[], Any]], ...] = (
    ("jstring", lambda: JString("sym")),
    ("strenum", lambda: SE.SYM),
    ("exact", lambda: "sym"),
    ("jint", lambda: JInt(7)),
)


def _map_tree(value: Any, leaf: Callable[[Any], Any]) -> Any:
    if type(value) is tuple:
        return tuple(_map_tree(item, leaf) for item in value)
    return leaf(value)


def _subclass_leaf(value: Any) -> Any:
    holder = type(value)
    if holder is int:
        return JInt(value)
    if holder is str:
        return JString(value)
    if holder is float:
        return JDouble(value)
    return value


def _boolean_leaf(value: Any) -> Any:
    return JBoolean(1 if value else 0) if type(value) is bool else value


def tuple_values(base_value: Any) -> Iterator[Tuple[str, Callable[[], Any]]]:
    """tuple の注釈の field に入れる値（基底の値の葉を替えた tree と、混ぜた tree）。"""

    if type(base_value) is not tuple:
        return
    subclassed = _map_tree(base_value, _subclass_leaf)
    if subclassed != base_value or any(type(a) is not type(b) for a, b in zip(_leaves(subclassed), _leaves(base_value))):
        yield "subclass_leaves", lambda: _map_tree(base_value, _subclass_leaf)
    # mixin の enum（IntEnum / str の enum）は入れない: `str()` の結果が python の版で違い（3.11 で変わった）、
    # golden が版に依存する。tuple の中の enum の member を保つことは unit test が直接確かめる
    yield "mixed", lambda: (JInt(1), (JBoolean(1), JString("s"), JDouble(1.5)), "x", 2, None, True)


def _leaves(value: Any) -> List[Any]:
    if type(value) is tuple:
        out: List[Any] = []
        for item in value:
            out.extend(_leaves(item))
        return out
    return [value]


@dataclasses.dataclass(frozen=True)
class Variant:
    """1 つの構築入力（`field` が None なら基底）。"""

    case_id: str
    cls: type
    field: Any
    value_label: str
    make_value: Any

    def kwargs(self) -> Dict[str, Any]:
        kwargs = BASES[self.cls]()
        if self.field is not None:
            kwargs[self.field] = self.make_value()
        return kwargs

    def twin_kwargs(self) -> Dict[str, Any]:
        return twin_kwargs_of(self.cls, self.kwargs())


def class_label(cls: type) -> str:
    return f"{cls.__module__.rsplit('.', 1)[-1]}.{cls.__qualname__}"


def variants() -> List[Variant]:
    out: List[Variant] = []
    for cls in BASES:
        label = class_label(cls)
        out.append(Variant(f"{label}|base", cls, None, "base", None))
        base = BASES[cls]()
        for name, kind in field_kinds(cls).items():
            if kind in ("int", "float"):
                values = list(INT_VALUES)
                if (cls, name) in INT_EXTRA_FIELDS:
                    values += list(INT_EXTRA_VALUES)
            elif kind == "bool":
                values = list(BOOL_VALUES)
            elif kind == "str":
                values = list(STR_VALUES)
            elif kind == "tuple":
                values = list(tuple_values(base.get(name, ())))
            else:
                continue
            for value_label, make in values:
                out.append(Variant(f"{label}|{name}|{value_label}", cls, name, value_label, make))
    return out


def build(cls: type, kwargs: Dict[str, Any]) -> Any:
    return cls(**kwargs)


#: ref の class（corpus が網羅する集合。新しい ref の class は `BASES` に足す）。
REF_CLASSES: Tuple[type, ...] = tuple(BASES)

#: `==` の行列を録る ref（意図した差 D1）: (名前, class, 構築入力)。双子も同じ規則で作る。
#: `AddressValueRef` は自分の検証で scalar を写さない class（main では `Weird` の `__eq__` がそのまま残る）。
EQUALITY_PROBES: Tuple[Tuple[str, type, Callable[[], Dict[str, Any]]], ...] = (
    ("param_exact_5", LocationBaseRef, lambda: dict(kind="parameter", parameter_index=5)),
    ("param_jint_5", LocationBaseRef, lambda: dict(kind="parameter", parameter_index=JInt(5))),
    ("param_weird_5", LocationBaseRef, lambda: dict(kind="parameter", parameter_index=Weird(5))),
    ("param_weird_7", LocationBaseRef, lambda: dict(kind="parameter", parameter_index=Weird(7))),
    ("op_exact_4096", PcodeOpRef, lambda: dict(address_offset=4096)),
    ("op_weird_4098", PcodeOpRef, lambda: dict(address_offset=Weird(4098))),
    ("addr_exact_4096", AddressValueRef, lambda: dict(address_offset=4096, source="ram")),
    ("addr_jint_4096", AddressValueRef, lambda: dict(address_offset=JInt(4096), source="ram")),
    ("addr_weird_4096", AddressValueRef, lambda: dict(address_offset=Weird(4096), source="ram")),
    ("addr_weird_4098", AddressValueRef, lambda: dict(address_offset=Weird(4098), source="ram")),
    ("target_exact_true", CallTargetRef, lambda: dict(kind="function", function_name="f", is_external=True,
                                                      library_name="libc")),
    ("target_jboolean_true", CallTargetRef, lambda: dict(kind="function", function_name="f",
                                                         is_external=JBoolean(1), library_name="libc")),
)


def twin_kwargs_of(cls: type, kwargs: Dict[str, Any]) -> Dict[str, Any]:
    kinds = field_kinds(cls)
    return {name: twin_value(value, kinds.get(name, "object")) for name, value in kwargs.items()}

"""Loop-derived references: variable identities, body effects, term descriptors, loop summaries and their comparison keys."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Callable, Dict, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.core.runtime_ref_record import runtime_ref_entry, runtime_ref_key, runtime_ref_record
from scripts.function_tracer_pcode.core.json_encoding import (as_list, bounded_repr, each, inline, is_json_record, mapping_of, materialize, nested, raw, source_converter)
from scripts.function_tracer_pcode.core.live_values import as_bool, as_int, attribute, builtin_items, exact_scalar, exact_tree, is_kind, scalar_bool, scalar_int, scalar_int_or, scalar_text, size, type_module, type_name, attribute_of, method_of
from scripts.function_tracer_pcode.core.runtime_refs._reading import (
    items as _items,
    optional_items as _optional_items,
    optional_rows as _optional_rows,
    rows as _scalar_rows,
)
from scripts.function_tracer_pcode.core.runtime_refs.locations import (
    LocationBaseRef,
)


LoopSummarySolverProver = Callable[["LoopSummaryProofObligation"], "LoopSummaryComparisonResult"]


@dataclass(frozen=True)
@runtime_ref_record
class LoopVariableIdentityRef:
    """Object-derived identity for a synthetic loop placeholder variable."""

    role: str
    varnode_key: Tuple[Any, ...]
    binder_ordinal: int = 0

    @runtime_ref_key
    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        return None

    @runtime_ref_key
    def binder_key(self) -> Tuple[Any, ...]:
        return (
            "loop_variable_binder",
            self.role,
            int(self.binder_ordinal),
        )

    @runtime_ref_key
    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        if not self.varnode_key:
            return None
        return (
            "loop_variable_identity",
            self.role,
            int(self.binder_ordinal),
            exact_tree(self.varnode_key),  # list のまま受理した key の葉も基底型の値で（Issue #242）
        )

    def json_items(self):
        yield "kind", "loop_variable_identity"
        yield "role", self.role
        yield "binder_ordinal", as_int(self.binder_ordinal)
        yield "varnode_key", self.varnode_key

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
@runtime_ref_record
class _LoopVariableBindingContext:
    """Per-summary alpha-renaming context for loop placeholder variables."""

    stable_to_binder: Dict[Tuple[Any, ...], Tuple[Any, ...]]

    @runtime_ref_key
    def semantic_key_for(self, ref: LoopVariableIdentityRef) -> Optional[Tuple[Any, ...]]:
        stable_key = exact_tree(method_of(ref, "stable_key")())  # 代わりの型・subclass の key も基底型の値で引く
        if stable_key is None:
            return None
        binder_key = method_of(self.stable_to_binder, "get")(stable_key)
        if binder_key is None:
            return None
        return ("loop_bound_variable", binder_key)


def _loop_object_key(value: Any) -> Optional[Tuple[Any, ...]]:
    if value is None:
        return ("none",)
    if is_kind(value, bool):
        return ("bool", bool(value))
    if is_kind(value, int):
        return ("int", scalar_int(value))
    if is_kind(value, str):
        return ("str", exact_tree(value))
    if is_kind(value, bytes):
        return ("bytes", bytes.hex(value))
    if is_kind(value, tuple):
        item_keys = tuple(_loop_object_key(item) for item in value)
        if any(item_key is None for item_key in item_keys):
            return None
        return ("tuple", item_keys)
    if is_kind(value, list):
        item_keys = tuple(_loop_object_key(item) for item in value)
        if any(item_key is None for item_key in item_keys):
            return None
        return ("list", item_keys)
    if is_kind(value, dict):
        items = []
        for key, item in value.items():
            key_key = _loop_object_key(key)
            item_key = _loop_object_key(item)
            if key_key is None or item_key is None:
                return None
            items.append((key_key, item_key))
        items.sort()
        return ("dict", tuple(items))
    structural_key = attribute_of(value, "structural_key", None)
    if callable(structural_key):
        try:
            return ("structural", exact_tree(structural_key()))
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
    stable_key = attribute_of(value, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
        if key is None:
            return None
        return ("stable", exact_tree(key))
    return None


@runtime_ref_entry
def _loop_variable_binding_context_from_values(
    *values: Any,
) -> Optional[_LoopVariableBindingContext]:
    stable_to_binder: Dict[Tuple[Any, ...], Tuple[Any, ...]] = {}
    binder_to_stable: Dict[Tuple[Any, ...], Tuple[Any, ...]] = {}
    seen: set[int] = set()

    def visit(item: Any) -> bool:
        if item is None:
            return True
        item_id = id(item)
        if item_id in seen:
            return True
        seen.add(item_id)

        ref = item if is_kind(item, LoopVariableIdentityRef) else attribute_of(item, "runtime_ref", None)
        if is_kind(ref, LoopVariableIdentityRef):
            stable_key = exact_tree(ref.stable_key())
            binder_key = exact_tree(ref.binder_key())
            if stable_key is None:
                return False
            existing_stable = binder_to_stable.get(binder_key)
            if existing_stable is not None and existing_stable != stable_key:
                return False
            existing_binder = stable_to_binder.get(stable_key)
            if existing_binder is not None and existing_binder != binder_key:
                return False
            binder_to_stable[binder_key] = stable_key
            stable_to_binder[stable_key] = binder_key

        expr_type = exact_tree(attribute_of(attribute_of(item, "expr_type", None), "name", None))
        if expr_type == "PHI":
            branches = builtin_items(attribute_of(item, "value", None))
            if branches is None:
                return False  # 読めない容器: 中身を落とさず、束縛の文脈を作らない
            for cond, branch_value in _scalar_rows(branches, 2):
                if cond is not None and not visit(cond):
                    return False
                if not visit(branch_value):
                    return False
            return True

        condition_expr = attribute_of(item, "expression", None)
        if condition_expr is not None and not visit(condition_expr):
            return False

        operands = builtin_items(attribute_of(item, "operands", None))
        if operands is None:
            return False
        for operand in operands:
            if not visit(operand):
                return False

        if is_kind(item, dict):
            for key, dict_value in item.items():
                if not visit(key) or not visit(dict_value):
                    return False
        elif is_kind(item, (tuple, list)):
            for child in item:
                if not visit(child):
                    return False
        return True

    for value in values:
        if not visit(value):
            return None
    return _LoopVariableBindingContext(stable_to_binder=stable_to_binder)


def _loop_object_semantic_key(
    value: Any,
    loop_variable_context: Optional[_LoopVariableBindingContext] = None,
) -> Optional[Tuple[Any, ...]]:
    """Semantic key for proof-oriented loop comparison.

    This intentionally differs from ``_loop_object_key`` for objects whose
    stable identity contains Ghidra ownership metadata.  The key is still fully
    object-centric: it walks expression/runtime objects and never depends on
    rendered strings.
    """

    if value is None:
        return ("none",)
    if is_kind(value, bool):
        return ("bool", bool(value))
    if is_kind(value, int):
        return ("int", scalar_int(value))
    if is_kind(value, str):
        return ("str", exact_tree(value))
    if is_kind(value, bytes):
        return ("bytes", bytes.hex(value))
    if is_kind(value, tuple):
        item_keys = tuple(_loop_object_semantic_key(item, loop_variable_context) for item in value)
        if any(item_key is None for item_key in item_keys):
            return None
        return ("tuple", item_keys)
    if is_kind(value, list):
        item_keys = tuple(_loop_object_semantic_key(item, loop_variable_context) for item in value)
        if any(item_key is None for item_key in item_keys):
            return None
        return ("list", item_keys)
    if is_kind(value, dict):
        items = []
        for key, item in value.items():
            key_key = _loop_object_semantic_key(key, loop_variable_context)
            item_key = _loop_object_semantic_key(item, loop_variable_context)
            if key_key is None or item_key is None:
                return None
            items.append((key_key, item_key))
        items.sort()
        return ("dict", tuple(items))

    if is_kind(value, LoopVariableIdentityRef):
        if loop_variable_context is None:
            return None
        return exact_tree(method_of(loop_variable_context, "semantic_key_for")(value))

    expr_key = _loop_expression_semantic_key(value, loop_variable_context)
    if expr_key is not None:
        return ("expression", expr_key)

    semantic_key = attribute_of(value, "semantic_key", None)
    if callable(semantic_key):
        try:
            key = semantic_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
        if key is not None:
            return ("semantic", exact_tree(key))
        if is_kind(value, LocationBaseRef):
            return None

    storage_identity_key = attribute_of(value, "storage_identity_key", None)
    if callable(storage_identity_key):
        try:
            key = storage_identity_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
        if key is None:
            return None
        return ("storage_identity", exact_tree(key))

    stable_key = attribute_of(value, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
        if key is None:
            return None
        return ("stable", exact_tree(key))
    return None


def _loop_expression_semantic_key(
    value: Any,
    loop_variable_context: Optional[_LoopVariableBindingContext] = None,
) -> Optional[Tuple[Any, ...]]:
    expr_type = attribute_of(value, "expr_type", None)
    expr_type_name = exact_tree(attribute_of(expr_type, "name", None))
    if expr_type_name is None:
        return None

    size = scalar_int(exact_tree(attribute_of(value, "size", 0)) or 0)
    if expr_type_name == "CONSTANT":
        try:
            return ("const", scalar_int(attribute_of(value, "value")), size)
        except (TypeError, ValueError):
            return None
    if expr_type_name == "PARAMETER":
        index = attribute_of(value, "value", None)
        try:
            if index is not None and scalar_int(index) >= 0:
                return ("parameter", scalar_int(index), size)
        except (TypeError, ValueError):
            pass
        storage = attribute_of(value, "storage_info", None)
        storage_key = _loop_object_semantic_key(storage, loop_variable_context) if storage is not None else None
        if storage is not None:
            if storage_key is None:
                return None
            return ("parameter_storage", size, storage_key)
        return None
    if expr_type_name == "VARIABLE":
        storage = attribute_of(value, "storage_info", None)
        storage_key = _loop_object_semantic_key(storage, loop_variable_context) if storage is not None else None
        if storage is not None:
            if storage_key is None:
                return None
            return ("variable_storage", size, storage_key)
        runtime_ref = attribute_of(value, "runtime_ref", None)
        runtime_key = _loop_object_semantic_key(runtime_ref, loop_variable_context) if runtime_ref is not None else None
        if runtime_ref is not None:
            if runtime_key is None:
                return None
            return ("variable_runtime", size, runtime_key)
        return None
    if expr_type_name in ("UNARY_OP", "BINARY_OP", "INTRINSIC", "CALL"):
        operands = builtin_items(attribute_of(value, "operands", None))
        if operands is None:
            return None  # 読めない容器: operand を落とした key で別の式と等しくしない
        operand_keys = tuple(_loop_object_semantic_key(operand, loop_variable_context) for operand in operands)
        if any(operand_key is None for operand_key in operand_keys):
            return None
        return (
            expr_type_name.lower(),
            exact_tree(attribute_of(value, "operator", None)) or exact_tree(attribute_of(value, "name", None)) or "",
            None if attribute_of(value, "opcode", None) is None else scalar_int(attribute_of(value, "opcode")),
            size,
            operand_keys,
        )
    if expr_type_name == "MEMORY":
        operands = builtin_items(attribute_of(value, "operands", None))
        if not operands:
            return None
        address_key = _loop_object_semantic_key(operands[0], loop_variable_context)
        runtime_key = _loop_object_semantic_key(attribute_of(value, "runtime_ref", None), loop_variable_context)
        if address_key is None:
            return None
        return ("memory", size, address_key, runtime_key)
    if expr_type_name == "PHI":
        branches = []
        phi_branches = builtin_items(attribute_of(value, "value", None))
        if phi_branches is None:
            return None
        for condition, branch_value in _scalar_rows(phi_branches, 2):
            if condition is None:
                condition_key = ("none",)
            else:
                condition_expr = attribute_of(condition, "expression", None)
                condition_key = (
                    "condition",
                    _loop_object_semantic_key(condition_expr, loop_variable_context),
                    scalar_bool(attribute_of(condition, "negated", False)),
                )
                if condition_key[1] is None:
                    return None
            value_key = _loop_object_semantic_key(branch_value, loop_variable_context)
            if value_key is None:
                return None
            branches.append((condition_key, value_key))
        return ("phi", size, tuple(branches))
    if expr_type_name == "UNKNOWN":
        runtime_key = _loop_object_semantic_key(attribute_of(value, "runtime_ref", None), loop_variable_context)
        if runtime_key is not None:
            return ("unknown", size, runtime_key)
        return None
    return None


@source_converter
def _loop_object_source(value: Any) -> Any:
    """`_loop_object_to_dict` と同じ値を 1 要素ずつ作らせる source（表現を先に作らない）。

    record（`json_items()` を持つ object）と sized leaf（式）は walker が辿る。それ以外の
    object は旧実装と同じ不透明な表示になる。
    """

    if value is None or is_kind(value, (bool, int, float, str)):
        return value
    if is_kind(value, (tuple, list)):
        return each(value, _loop_object_source)
    if is_kind(value, dict):
        return mapping_of(value, _loop_object_source, stringify_keys=True)
    if is_json_record(value):
        return value
    return inline(
        ("type", type_module(type(value)) + "." + type_name(type(value))),
        ("unkeyable", True),
    )


def _int_or_zero(value: Any) -> int:
    """`int(value or 0)` と同じ値（真偽と整数化は owner の API で読む。live な値の code を呼ばない）。"""

    if type(value) is int:
        return value
    if value is None or not as_bool(value):
        return 0
    return as_int(value)


@source_converter
def _path_conditions_source(path_conditions: Any) -> Any:
    """`path_condition_sets` の 1 経路（条件の列）の出力。"""

    return each(path_conditions, _loop_object_source)


@source_converter
def _residue_case_source(case: Any) -> Any:
    """`residue_cases` の 1 要素 `(modulus, residue, coeff, bias)` の出力（組み込みの tuple / list だけ）。"""

    if (type(case) is tuple or type(case) is list):
        return inline(
            ("modulus", as_int(case[0])),
            ("residue", as_int(case[1])),
            ("coeff", as_int(case[2])),
            ("bias", as_int(case[3])),
        )
    raise TypeError("a residue case is not a builtin tuple / list")


@source_converter
def _residue_bias_term_source(term: Any) -> Any:
    """`residue_bias_terms` の 1 要素 `(modulus, residue, bias_expr)` の出力（組み込みの tuple / list だけ）。"""

    if (type(term) is tuple or type(term) is list):
        bias_expr = term[2]
        return inline(
            ("modulus", as_int(term[0])),
            ("residue", as_int(term[1])),
            ("bias_expr", bias_expr if is_json_record(bias_expr) else bounded_repr(bias_expr)),
        )
    raise TypeError("a residue bias term is not a builtin tuple / list")


@source_converter
def _lane_term_source(lane: Any) -> Any:
    """`lane_terms` の 1 要素 `(offset, size)` の出力（組み込みの tuple / list だけ）。"""

    if (type(lane) is tuple or type(lane) is list):
        return inline(
            ("byte_offset", as_int(lane[0])),
            ("access_size", max(1, _int_or_zero(lane[1]))),
        )
    raise TypeError("a lane term is not a builtin tuple / list")


def _loop_object_to_dict(value: Any) -> Any:
    if value is None or is_kind(value, (bool, int, float, str)):
        return exact_scalar(value)
    if is_kind(value, tuple):
        return [_loop_object_to_dict(item) for item in value]
    if is_kind(value, list):
        return [_loop_object_to_dict(item) for item in value]
    if is_kind(value, dict):
        return {scalar_text(key): _loop_object_to_dict(item) for key, item in value.items()}
    to_dict = attribute_of(value, "to_dict", None)
    if callable(to_dict):
        try:
            return exact_tree(to_dict())
        except (AttributeError, TypeError, ValueError, RecursionError):
            return {
                "type": type_module(type(value)) + "." + type_name(type(value)),
                "unserializable": True,
            }
    return {
        "type": type_module(type(value)) + "." + type_name(type(value)),
        "unkeyable": True,
    }


@dataclass(frozen=True)
@runtime_ref_record
class LoopBodyEffectRef:
    """Object-centric descriptor for one loop-body effect or guard."""

    kind: str
    source: str = "loop_body"
    scope: str = "loop"
    address_space: Any = None
    location: Any = None
    value_expr: Any = None
    guard_constraints: Tuple[Any, ...] = ()
    path_condition_sets: Tuple[Tuple[Any, ...], ...] = ()
    guard_paths_incomplete: bool = False
    target_ref: Any = None
    order_key: Optional[int] = None
    keyable: bool = True
    unkeyable_reason: Optional[str] = None

    @runtime_ref_key
    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        if not self.keyable:
            return None
        if self.guard_paths_incomplete:
            return None
        if (
            self.kind == "memory_write"
            and self.source == "pcode_scan"
            and self.scope == "loop"
            and (self.address_space is None or self.location is None or self.value_expr is None)
        ):
            return None
        address_space_key = _loop_object_key(self.address_space)
        location_key = _loop_object_key(self.location)
        value_key = _loop_object_key(self.value_expr)
        guard_keys = tuple(_loop_object_key(guard) for guard in self.guard_constraints)
        path_keys = tuple(
            tuple(_loop_object_key(condition) for condition in _items(path_conditions))
            for path_conditions in self.path_condition_sets
        )
        target_key = _loop_object_key(self.target_ref)
        if (
            address_space_key is None
            or location_key is None
            or value_key is None
            or target_key is None
            or any(guard_key is None for guard_key in guard_keys)
            or any(any(condition_key is None for condition_key in path_key) for path_key in path_keys)
        ):
            return None
        return (
            "loop_body_effect",
            self.kind,
            self.source,
            self.scope,
            address_space_key,
            location_key,
            value_key,
            guard_keys,
            path_keys,
            bool(self.guard_paths_incomplete),
            target_key,
            None if self.order_key is None else int(self.order_key),
            bool(self.keyable),
        )

    @runtime_ref_key
    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        if not self.keyable or self.guard_paths_incomplete:
            return None
        address_space_key = _loop_object_semantic_key(self.address_space)
        location_key = _loop_object_semantic_key(self.location)
        value_key = _loop_object_semantic_key(self.value_expr)
        guard_keys = tuple(_loop_object_semantic_key(guard) for guard in self.guard_constraints)
        path_keys = tuple(
            tuple(_loop_object_semantic_key(condition) for condition in _items(path_conditions))
            for path_conditions in self.path_condition_sets
        )
        target_key = _loop_object_semantic_key(self.target_ref)
        if (
            address_space_key is None
            or location_key is None
            or value_key is None
            or target_key is None
            or any(guard_key is None for guard_key in guard_keys)
            or any(any(condition_key is None for condition_key in path_key) for path_key in path_keys)
        ):
            return None
        return (
            "loop_body_effect",
            self.kind,
            self.source,
            self.scope,
            address_space_key,
            location_key,
            value_key,
            guard_keys,
            path_keys,
            bool(self.guard_paths_incomplete),
            target_key,
            None if self.order_key is None else int(self.order_key),
            bool(self.keyable),
        )

    def json_items(self):
        yield "kind", "loop_body_effect"
        yield "effect_kind", self.kind
        yield "source", self.source
        yield "scope", self.scope
        yield "address_space", _loop_object_source(self.address_space)
        yield "location", _loop_object_source(self.location)
        yield "value_expr", _loop_object_source(self.value_expr)
        yield "guard_constraints", each(self.guard_constraints, _loop_object_source)
        yield "path_condition_sets", each(
            self.path_condition_sets,
            _path_conditions_source,
        )
        yield "guard_paths_incomplete", as_bool(self.guard_paths_incomplete)
        yield "target_ref", _loop_object_source(self.target_ref)
        yield "order_key", self.order_key
        yield "keyable", as_bool(self.keyable)
        yield "unkeyable_reason", self.unkeyable_reason

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
@runtime_ref_record
class LoopSideEffectProfileRef:
    """Object-centric side-effect profile for a loop summary."""

    profile: str = "pure"
    memory_reads: bool = False
    memory_writes: bool = False
    calls: bool = False
    escapes: bool = False
    conditional_guards: bool = False
    context_memory_writes: bool = False
    context_calls: bool = False
    context_escapes: bool = False
    context_conditional_guards: bool = False
    effect_count: int = 0
    guard_count: int = 0
    effect_descriptors: Tuple[LoopBodyEffectRef, ...] = ()
    context_descriptors: Tuple[LoopBodyEffectRef, ...] = ()

    @runtime_ref_key
    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        effect_keys = tuple(method_of(effect, "stable_key")() for effect in self.effect_descriptors)
        context_effect_keys = tuple(method_of(effect, "stable_key")() for effect in self.context_descriptors)
        if any(effect_key is None for effect_key in effect_keys):
            return None
        if any(effect_key is None for effect_key in context_effect_keys):
            return None
        return (
            "loop_side_effect_profile",
            self.profile,
            bool(self.memory_reads),
            bool(self.memory_writes),
            bool(self.calls),
            bool(self.escapes),
            bool(self.conditional_guards),
            bool(self.context_memory_writes),
            bool(self.context_calls),
            bool(self.context_escapes),
            bool(self.context_conditional_guards),
            int(self.effect_count),
            int(self.guard_count),
            effect_keys,
            context_effect_keys,
        )

    @runtime_ref_key
    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        effect_keys = tuple(method_of(effect, "semantic_key")() for effect in self.effect_descriptors)
        context_effect_keys = tuple(method_of(effect, "semantic_key")() for effect in self.context_descriptors)
        if any(effect_key is None for effect_key in effect_keys):
            return None
        if any(effect_key is None for effect_key in context_effect_keys):
            return None
        return (
            "loop_side_effect_profile",
            self.profile,
            bool(self.memory_reads),
            bool(self.memory_writes),
            bool(self.calls),
            bool(self.escapes),
            bool(self.conditional_guards),
            bool(self.context_memory_writes),
            bool(self.context_calls),
            bool(self.context_escapes),
            bool(self.context_conditional_guards),
            int(self.effect_count),
            int(self.guard_count),
            effect_keys,
            context_effect_keys,
        )

    def requires_effect_proof(self) -> bool:
        profile = (self.profile or "").lower()
        effect_descriptors = tuple(self.effect_descriptors or ())
        context_descriptors = tuple(self.context_descriptors or ())

        def _descriptor_requires_effect_proof(effect: LoopBodyEffectRef) -> bool:
            return exact_tree(attribute_of(effect, "kind", None)) != "conditional_guard"

        if profile not in {"pure", "pure_memory_read", "pure_conditional"}:
            return True
        return bool(
            self.memory_writes
            or self.calls
            or self.escapes
            or self.context_memory_writes
            or self.context_calls
            or self.context_escapes
            or any(_descriptor_requires_effect_proof(effect) for effect in effect_descriptors)
            or any(_descriptor_requires_effect_proof(effect) for effect in context_descriptors)
        )

    def json_items(self):
        yield "kind", "loop_side_effect_profile"
        yield "profile", self.profile
        yield "memory_reads", as_bool(self.memory_reads)
        yield "memory_writes", as_bool(self.memory_writes)
        yield "calls", as_bool(self.calls)
        yield "escapes", as_bool(self.escapes)
        yield "conditional_guards", as_bool(self.conditional_guards)
        yield "context_memory_writes", as_bool(self.context_memory_writes)
        yield "context_calls", as_bool(self.context_calls)
        yield "context_escapes", as_bool(self.context_escapes)
        yield "context_conditional_guards", as_bool(self.context_conditional_guards)
        yield "effect_count", as_int(self.effect_count)
        yield "guard_count", as_int(self.guard_count)
        yield "effect_descriptors", each(self.effect_descriptors)
        yield "context_descriptors", each(self.context_descriptors)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
@runtime_ref_record
class LoopTermDescriptorRef:
    """Object-centric descriptor for the per-iteration term of a loop summary."""

    kind: str
    reduction_kind: str = "sum"
    location_base_ref: Optional[LocationBaseRef] = None
    start_offset: int = 0
    stride: int = 0
    element_size: int = 0
    result_size: int = 0
    residue_cases: Tuple[Tuple[int, int, int, int], ...] = ()
    residue_bias_terms: Tuple[Tuple[int, int, Any], ...] = ()
    lane_terms: Tuple[Tuple[int, int], ...] = ()

    @runtime_ref_key
    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        residue_bias_keys = tuple(
            (
                int(modulus),
                int(residue),
                _loop_object_key(bias_expr),
            )
            for modulus, residue, bias_expr in _scalar_rows(self.residue_bias_terms, 3)
        )
        if any(key[2] is None for key in residue_bias_keys):
            return None
        return (
            "loop_term_descriptor",
            self.kind,
            self.reduction_kind,
            self.location_base_ref.stable_key() if self.location_base_ref is not None else None,
            int(self.start_offset),
            int(self.stride),
            int(self.element_size),
            max(1, int(self.result_size or 0)),
            tuple(
                (
                    int(modulus),
                    int(residue),
                    int(coeff),
                    int(bias),
                )
                for modulus, residue, coeff, bias in _scalar_rows(self.residue_cases, 4)
            ),
            residue_bias_keys,
            tuple((int(offset), max(1, int(size or 0))) for offset, size in _scalar_rows(self.lane_terms, 2)),
        )

    @runtime_ref_key
    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        location_key = self.location_base_ref.semantic_key() if self.location_base_ref is not None else None
        if self.location_base_ref is not None and location_key is None:
            return None
        residue_bias_keys = tuple(
            (
                int(modulus),
                int(residue),
                _loop_object_semantic_key(bias_expr),
            )
            for modulus, residue, bias_expr in _scalar_rows(self.residue_bias_terms, 3)
        )
        if any(key[2] is None for key in residue_bias_keys):
            return None
        return (
            "loop_term_descriptor",
            self.kind,
            self.reduction_kind,
            location_key,
            int(self.start_offset),
            int(self.stride),
            int(self.element_size),
            max(1, int(self.result_size or 0)),
            tuple(
                (
                    int(modulus),
                    int(residue),
                    int(coeff),
                    int(bias),
                )
                for modulus, residue, coeff, bias in _scalar_rows(self.residue_cases, 4)
            ),
            residue_bias_keys,
            tuple((int(offset), max(1, int(size or 0))) for offset, size in _scalar_rows(self.lane_terms, 2)),
        )

    def json_items(self):
        yield "kind", "loop_term_descriptor"
        yield "term_kind", self.kind
        yield "reduction_kind", self.reduction_kind
        yield "start_offset", as_int(self.start_offset)
        yield "stride", as_int(self.stride)
        yield "element_size", as_int(self.element_size)
        yield "result_size", max(1, _int_or_zero(self.result_size))

        yield "residue_cases", each(
            self.residue_cases,
            _residue_case_source,
        )
        yield "residue_bias_terms", each(
            self.residue_bias_terms,
            _residue_bias_term_source,
        )

        yield "lane_terms", each(
            self.lane_terms,
            _lane_term_source,
        )
        if self.location_base_ref is not None:
            yield "location_base_ref", self.location_base_ref

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
@runtime_ref_record
class LoopCaseRef:
    """Path-sensitive loop-body case used by Method-B loop summaries."""

    path_conditions: Tuple[Any, ...] = ()
    body_effect: Any = None
    term_expr: Any = None
    case_kind: str = "body_term"
    source: str = "recurrence_summary"

    @runtime_ref_key
    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        path_keys = tuple(_loop_object_key(condition) for condition in self.path_conditions)
        body_effect_key = _loop_object_key(self.body_effect)
        term_key = _loop_object_key(self.term_expr)
        if (
            any(path_key is None for path_key in path_keys)
            or body_effect_key is None
            or term_key is None
        ):
            return None
        return (
            "loop_case",
            self.case_kind,
            path_keys,
            body_effect_key,
            term_key,
            self.source,
        )

    @runtime_ref_key
    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        path_keys = tuple(_loop_object_semantic_key(condition) for condition in self.path_conditions)
        body_effect_key = _loop_object_semantic_key(self.body_effect)
        term_key = _loop_object_semantic_key(self.term_expr)
        if (
            any(path_key is None for path_key in path_keys)
            or body_effect_key is None
            or term_key is None
        ):
            return None
        return (
            "loop_case",
            self.case_kind,
            path_keys,
            body_effect_key,
            term_key,
            self.source,
        )

    def json_items(self):
        yield "kind", "loop_case"
        yield "case_kind", self.case_kind
        yield "path_conditions", each(self.path_conditions, _loop_object_source)
        yield "body_effect", _loop_object_source(self.body_effect)
        yield "term_expr", _loop_object_source(self.term_expr)
        yield "source", self.source

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


def _bias_key(value: int, result_size: int) -> Tuple[int, int]:
    bits = max(1, scalar_int_or(result_size)) * 8
    return bits, scalar_int(value) % (1 << bits)


def _normalize_storage_identity_key(value: Optional[Tuple[Any, ...]]) -> Optional[Tuple[Any, ...]]:
    if value is None:
        return None
    return exact_tree(_items(value))


def _count_parameter_semantic_identity(
    *,
    count_parameter_index: Optional[int],
    count_parameter_storage_identity_key: Optional[Tuple[Any, ...]],
) -> Optional[Tuple[Any, ...]]:
    identities = _count_parameter_semantic_identities(
        count_parameter_index=count_parameter_index,
        count_parameter_storage_identity_key=count_parameter_storage_identity_key,
    )
    return identities[0] if identities else None


def _count_parameter_semantic_identities(
    *,
    count_parameter_index: Optional[int],
    count_parameter_storage_identity_key: Optional[Tuple[Any, ...]],
) -> Tuple[Tuple[Any, ...], ...]:
    identities = []
    storage_key = _normalize_storage_identity_key(count_parameter_storage_identity_key)
    if storage_key is not None:
        identities.append(("parameter_storage", storage_key))
    if count_parameter_index is not None:
        try:
            index = scalar_int(count_parameter_index)
        except (TypeError, ValueError):
            index = -1
        if index >= 0:
            identities.append(("parameter", index))
    return tuple(identities)


@dataclass(frozen=True)
@runtime_ref_record
class LoopSummaryRef:
    """Unified semantic loop summary shared by all recurrence summaries.

    ``witnesses`` are evidence keyed by the original count/limit surface, not
    proof obligations by themselves. A witness may describe a count value outside
    ``guard_constraints``; consumers must check guard reachability before using
    witnesses to prove equivalence.
    """

    start_expr: Any
    limit_expr: Any
    step_expr: Any
    term_descriptor: LoopTermDescriptorRef
    seed_terms: Tuple[Any, ...] = ()
    seed_term_count: Optional[int] = None
    witnesses: Tuple[Any, ...] = ()
    side_effect_profile: LoopSideEffectProfileRef = LoopSideEffectProfileRef()
    guard_constraints: Tuple[Any, ...] = ()
    cases: Tuple[LoopCaseRef, ...] = ()
    loop_var_unit: str = "element_index"
    source: str = "recurrence_summary"
    constant_bias: int = 0

    def __post_init__(self) -> None:
        result_size = scalar_int_or(getattr(self.term_descriptor, "result_size", 0))
        if result_size <= 0 and scalar_int(self.constant_bias) != 0:
            raise ValueError("LoopSummaryRef.constant_bias requires a positive term result_size")
        result_size = max(1, result_size)
        object.__setattr__(self, "constant_bias", _bias_key(scalar_int(self.constant_bias), result_size)[1])

    @runtime_ref_key
    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        start_key = _loop_object_key(self.start_expr)
        limit_key = _loop_object_key(self.limit_expr)
        step_key = _loop_object_key(self.step_expr)
        seed_terms = tuple(self.seed_terms or ())
        seed_term_count = getattr(self, "seed_term_count", None)
        if seed_terms:
            seed_keys = tuple(_loop_object_key(term) for term in seed_terms)
        elif seed_term_count is not None:
            if int(seed_term_count) < 0:
                return None
            seed_keys = (("seed_term_count", int(seed_term_count)),)
        else:
            seed_keys = ()
        witness_keys = tuple(_loop_object_key(witness) for witness in self.witnesses)
        guard_keys = tuple(_loop_object_key(guard) for guard in self.guard_constraints)
        case_keys = tuple(method_of(case, "stable_key")() for case in self.cases)
        term_descriptor_key = self.term_descriptor.stable_key()
        side_effect_key = self.side_effect_profile.stable_key()
        if (
            start_key is None
            or limit_key is None
            or step_key is None
            or term_descriptor_key is None
            or any(seed_key is None for seed_key in seed_keys)
            or any(witness_key is None for witness_key in witness_keys)
            or any(guard_key is None for guard_key in guard_keys)
            or any(case_key is None for case_key in case_keys)
            or side_effect_key is None
        ):
            return None
        return (
            "loop_summary",
            self.loop_var_unit,
            start_key,
            limit_key,
            step_key,
            term_descriptor_key,
            seed_keys,
            witness_keys,
            side_effect_key,
            guard_keys,
            case_keys,
            self.source,
            _bias_key(int(self.constant_bias), getattr(self.term_descriptor, "result_size", 0)),
        )

    def requires_effect_proof(self) -> bool:
        return scalar_bool(self.side_effect_profile.requires_effect_proof())

    def requires_path_proof(self) -> bool:
        counted_update_cases = []
        for case in tuple(self.cases or ()):
            if exact_tree(attribute_of(case, "source", None)) == "counted_loop_update_case":
                counted_update_cases.append(case)
                continue
            if attribute_of(case, "body_effect", None) is not None:
                return True
            if attribute_of(case, "term_expr", None) is not None:
                return True
        if counted_update_cases and not self._counted_loop_update_cases_are_descriptor_covered(counted_update_cases):
            return True
        return False

    def _counted_loop_update_cases_are_descriptor_covered(self, cases: Sequence[Any]) -> bool:
        if not cases:
            return True
        if exact_tree(getattr(self.term_descriptor, "kind", None)) != "affine_residue":
            return False
        raw_residue_cases = getattr(self.term_descriptor, "residue_cases", ())
        residue_cases = _items(raw_residue_cases) if scalar_bool(raw_residue_cases) else ()
        if not residue_cases:
            return False
        for case in cases:
            if exact_tree(attribute_of(case, "case_kind", None)) != "accumulator_delta":
                return False
            body_effect = attribute_of(case, "body_effect", None)
            if exact_tree(attribute_of(body_effect, "kind", None)) != "accumulator_update":
                return False
            if attribute_of(case, "term_expr", None) is None:
                return False
        residue_keys = []
        for residue_case in residue_cases:
            row = _items(residue_case)
            if len(row) < 4:
                return False
            try:
                modulus = scalar_int(row[0])
                residue = scalar_int(row[1])
            except (TypeError, ValueError):
                return False
            if modulus <= 0 or residue < 0 or residue >= modulus:
                return False
            residue_keys.append((modulus, residue))
        if len(residue_keys) == 1:
            return residue_keys[0] == (1, 0) and len(cases) == 1
        moduli = {modulus for modulus, _residue in residue_keys}
        if len(moduli) != 1:
            return False
        modulus = moduli.pop()
        if len(cases) != modulus:
            return False
        return {residue for _modulus, residue in residue_keys} == set(range(modulus))

    @runtime_ref_key
    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        if self.requires_effect_proof() or self.requires_path_proof():
            return None
        return loop_summary_method_b_key(self)

    @runtime_ref_key
    def pairwise_exact_key(self) -> Optional[Tuple[Any, ...]]:
        if self.requires_effect_proof() or self.requires_path_proof():
            return None
        return self.stable_key()

    @runtime_ref_key
    def pairwise_semantic_key(self) -> Optional[Tuple[Any, ...]]:
        return self.semantic_key()

    def json_items(self):
        yield "kind", "loop_summary"
        yield "loop_var_unit", self.loop_var_unit
        yield "start_expr", _loop_object_source(self.start_expr)
        yield "limit_expr", _loop_object_source(self.limit_expr)
        yield "step_expr", _loop_object_source(self.step_expr)
        yield "term_descriptor", self.term_descriptor
        yield "seed_terms", each(self.seed_terms, _loop_object_source)
        yield "seed_term_count", None if self.seed_term_count is None else as_int(self.seed_term_count)
        yield "witnesses", each(self.witnesses, _loop_object_source)
        yield "side_effect_profile", self.side_effect_profile
        yield "guard_constraints", each(self.guard_constraints, _loop_object_source)
        yield "cases", each(self.cases)
        yield "source", self.source
        yield "constant_bias", as_int(self.constant_bias)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
@runtime_ref_record
class ComposedLoopSummaryRef:
    """Lightweight composition wrapper for sequential loop summaries.

    The wrapper keeps composition identity separate from ``LoopSummaryRef`` while
    projecting the current summary surface for legacy consumers that only need
    guard/term/side-effect shape.
    """

    prior: Any
    current: Any
    handoff_proof_key: Optional[Tuple[Any, ...]] = None
    source: str = "composed_loop_summary"

    @property
    def start_expr(self) -> Any:
        return attribute_of(self.current, "start_expr", None)

    @property
    def limit_expr(self) -> Any:
        return attribute_of(self.current, "limit_expr", None)

    @property
    def step_expr(self) -> Any:
        return attribute_of(self.current, "step_expr", None)

    @property
    def term_descriptor(self) -> Any:
        return attribute_of(self.current, "term_descriptor", None)

    @property
    def seed_terms(self) -> Tuple[Any, ...]:
        return _optional_items(attribute_of(self.current, "seed_terms", ()))

    @property
    def seed_term_count(self) -> Optional[int]:
        # `current` は Any: scalar は基底型の値で返す（読み手が subclass の code を呼ばない。Issue #242）
        return exact_tree(attribute_of(self.current, "seed_term_count", None))

    @property
    def witnesses(self) -> Tuple[Any, ...]:
        return _optional_items(attribute_of(self.current, "witnesses", ()))

    @property
    def side_effect_profile(self) -> LoopSideEffectProfileRef:
        # `current` の属性は owner の API で読む（`__getattr__` / package の外の property を呼ばない）
        profile = attribute(self.current, "side_effect_profile")
        return profile if is_kind(profile, LoopSideEffectProfileRef) else LoopSideEffectProfileRef()

    @property
    def guard_constraints(self) -> Tuple[Any, ...]:
        return _optional_items(attribute_of(self.current, "guard_constraints", ()))

    @property
    def cases(self) -> Tuple[Any, ...]:
        return _optional_items(attribute_of(self.current, "cases", ()))

    @property
    def loop_var_unit(self) -> str:
        return scalar_text(exact_tree(attribute_of(self.current, "loop_var_unit", "element_index")) or "element_index")

    @property
    def constant_bias(self) -> int:
        try:
            return scalar_int_or(attribute_of(self.current, "constant_bias", 0))
        except (TypeError, ValueError):
            return 0

    @runtime_ref_key
    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        prior_key = _loop_object_key(self.prior)
        current_key = _loop_object_key(self.current)
        handoff_key = _loop_object_key(self.handoff_proof_key)
        side_effect_key = self.side_effect_profile.stable_key()
        if prior_key is None or current_key is None or handoff_key is None or side_effect_key is None:
            return None
        return (
            "composed_loop_summary",
            prior_key,
            current_key,
            handoff_key,
            side_effect_key,
            self.source,
        )

    @runtime_ref_key
    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        prior_key = _loop_object_semantic_key(self.prior)
        current_key = _loop_object_semantic_key(self.current)
        handoff_key = _loop_object_semantic_key(self.handoff_proof_key)
        side_effect_key = self.side_effect_profile.stable_key()
        if prior_key is None or current_key is None or handoff_key is None or side_effect_key is None:
            return None
        return (
            "composed_loop_summary",
            prior_key,
            current_key,
            handoff_key,
            side_effect_key,
            self.source,
        )

    @runtime_ref_key
    def pairwise_exact_key(self) -> Optional[Tuple[Any, ...]]:
        return self.stable_key()

    @runtime_ref_key
    def pairwise_semantic_key(self) -> Optional[Tuple[Any, ...]]:
        return self.semantic_key()

    def requires_effect_proof(self) -> bool:
        for summary in (self.prior, self.current):
            requires_effect_proof = attribute_of(summary, "requires_effect_proof", None)
            if callable(requires_effect_proof) and scalar_bool(requires_effect_proof()):
                return True
        return False

    def requires_path_proof(self) -> bool:
        for summary in (self.prior, self.current):
            requires_path_proof = attribute_of(summary, "requires_path_proof", None)
            if callable(requires_path_proof) and scalar_bool(requires_path_proof()):
                return True
        return False

    def json_items(self):
        yield "kind", "composed_loop_summary"
        yield "prior", _loop_object_source(self.prior)
        yield "current", _loop_object_source(self.current)
        yield "handoff_proof_key", _loop_object_source(self.handoff_proof_key)
        yield "side_effect_profile", self.side_effect_profile
        yield "source", self.source

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
@runtime_ref_record
class LoopSummaryProofObligation:
    """Proof obligation emitted when loop-summary equality needs a solver context."""

    proof_kind: str
    left_summary_key: Optional[Tuple[Any, ...]]
    right_summary_key: Optional[Tuple[Any, ...]]
    relation: str
    required_evidence: Tuple[str, ...]
    reason: str

    @classmethod
    @runtime_ref_entry
    def case_aware_solver_equality(
        cls,
        left: "LoopSummaryRef",
        right: "LoopSummaryRef",
        *,
        reason: str,
    ) -> "LoopSummaryProofObligation":
        return cls(
            proof_kind="case_aware_loop_summary_solver_equality",
            left_summary_key=_loop_summary_comparison_key(left),
            right_summary_key=_loop_summary_comparison_key(right),
            relation="loop_summary_value_equality_under_case_guards",
            required_evidence=(
                "guard_partition",
                "transition_or_term_equality",
                "pure_side_effect_profile",
                "width_policy",
            ),
            reason=reason,
        )

    def json_items(self):
        yield "kind", "loop_summary_proof_obligation"
        yield "proof_kind", self.proof_kind
        yield "left_summary_key", self.left_summary_key
        yield "right_summary_key", self.right_summary_key
        yield "relation", self.relation
        yield "required_evidence", self.required_evidence
        yield "reason", self.reason

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


def _loop_summary_comparison_key(summary: Optional["LoopSummaryRef"]) -> Optional[Tuple[Any, ...]]:
    if summary is None:
        return None
    for name in ("pairwise_semantic_key", "semantic_key", "stable_key"):
        key_fn = attribute_of(summary, name, None)
        if not callable(key_fn):
            continue
        try:
            key = key_fn()
        except (AttributeError, TypeError, ValueError, RecursionError):
            key = None
        if key is not None:
            return exact_tree(key)  # 外の method（上書きした key）の結果: 組み込みの木で読む
    return None


@dataclass(frozen=True)
@runtime_ref_record
class LoopSummaryComparisonResult:
    """Tri-state result for the future Method-B loop-summary comparator."""

    status: str
    reason: Optional[str] = None
    proof_obligation: Optional[LoopSummaryProofObligation] = None

    def __post_init__(self) -> None:
        if self.status not in {"equivalent", "different", "incompatible", "unknown"}:
            raise ValueError(f"Unsupported loop summary comparison status: {self.status}")

    def is_equivalent(self) -> Optional[bool]:
        if self.status == "equivalent":
            return True
        if self.status == "different":
            return False
        return None

    def blocks_shortcut(self) -> bool:
        return self.status in {"different", "incompatible"}

    def json_items(self):
        yield "kind", "loop_summary_comparison_result"
        yield "status", self.status
        yield "reason", self.reason
        yield "proof_obligation", self.proof_obligation if self.proof_obligation is not None else None

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@runtime_ref_entry
def compare_loop_summaries(
    left: Optional[LoopSummaryRef],
    right: Optional[LoopSummaryRef],
    *,
    solver_prover: Optional[LoopSummarySolverProver] = None,
) -> LoopSummaryComparisonResult:
    """Compare Method-B loop summaries.

    This central comparator owns the structural gates.  Solver-backed equality
    is supplied as an optional callback because the model layer does not know
    the active return-case guards or SMT runner.
    """

    if left is None or right is None:
        return LoopSummaryComparisonResult("unknown", "missing loop summary")
    left_method_b_key = loop_summary_method_b_key(left)
    right_method_b_key = loop_summary_method_b_key(right)
    if left_method_b_key is not None and right_method_b_key is not None:
        if left_method_b_key == right_method_b_key:
            return LoopSummaryComparisonResult("equivalent", "loop summaries match by semantic seed compensation")
    left_profile = attribute_of(left, "side_effect_profile", None)
    right_profile = attribute_of(right, "side_effect_profile", None)
    if left_profile is not None and right_profile is not None:
        left_shape = (
            exact_tree(attribute_of(left_profile, "profile")),
            scalar_bool(attribute_of(left_profile, "memory_reads")),
            scalar_bool(attribute_of(left_profile, "memory_writes")),
            scalar_bool(attribute_of(left_profile, "calls")),
            scalar_bool(attribute_of(left_profile, "escapes")),
            scalar_bool(attribute_of(left_profile, "conditional_guards")),
            scalar_int(attribute_of(left_profile, "effect_count")),
            scalar_int(attribute_of(left_profile, "guard_count")),
        )
        right_shape = (
            exact_tree(attribute_of(right_profile, "profile")),
            scalar_bool(attribute_of(right_profile, "memory_reads")),
            scalar_bool(attribute_of(right_profile, "memory_writes")),
            scalar_bool(attribute_of(right_profile, "calls")),
            scalar_bool(attribute_of(right_profile, "escapes")),
            scalar_bool(attribute_of(right_profile, "conditional_guards")),
            scalar_int(attribute_of(right_profile, "effect_count")),
            scalar_int(attribute_of(right_profile, "guard_count")),
        )
        if left_shape != right_shape:
            return LoopSummaryComparisonResult("incompatible", "loop side-effect profiles differ")
        left_effect_key = exact_tree(method_of(left_profile, "stable_key")())
        right_effect_key = exact_tree(method_of(right_profile, "stable_key")())
        if left_effect_key is not None and right_effect_key is not None and left_effect_key != right_effect_key:
            return LoopSummaryComparisonResult("incompatible", "loop body effects differ")
    left_cases = _optional_items(attribute_of(left, "cases", ()))
    right_cases = _optional_items(attribute_of(right, "cases", ()))
    if len(left_cases) != len(right_cases):
        return LoopSummaryComparisonResult("incompatible", "loop case counts differ")
    if left_cases or right_cases:
        left_case_keys = tuple(exact_tree(method_of(case, "stable_key")()) for case in left_cases)
        right_case_keys = tuple(exact_tree(method_of(case, "stable_key")()) for case in right_cases)
        if any(case_key is None for case_key in left_case_keys + right_case_keys):
            return LoopSummaryComparisonResult("incompatible", "loop cases are unkeyable")
        if left_case_keys != right_case_keys:
            return LoopSummaryComparisonResult("incompatible", "loop cases differ")
    left_semantic_key = exact_tree(left.pairwise_semantic_key())
    right_semantic_key = exact_tree(right.pairwise_semantic_key())
    if left_semantic_key is not None and right_semantic_key is not None:
        if left_semantic_key == right_semantic_key:
            return LoopSummaryComparisonResult("equivalent", "loop summaries match by semantic key")
    obligation = LoopSummaryProofObligation.case_aware_solver_equality(
        left,
        right,
        reason="loop summary comparator requires case-aware solver proof",
    )
    if solver_prover is not None:
        try:
            proven = solver_prover(obligation)
        except (AttributeError, TypeError, ValueError, RecursionError):
            proven = None
        if is_kind(proven, LoopSummaryComparisonResult):
            if exact_tree(proven.status) in {"equivalent", "different", "incompatible"}:
                return proven
    return LoopSummaryComparisonResult(
        "unknown",
        "loop summary comparator requires case-aware solver proof",
        proof_obligation=obligation,
    )


@runtime_ref_key
@runtime_ref_entry
def loop_summary_method_b_key(summary: Optional[LoopSummaryRef]) -> Optional[Tuple[Any, ...]]:
    """Canonical Method-B key for pure loop summaries.

    The key normalizes a suffix loop whose ``seed_terms`` exactly cover the
    omitted prefix back to the earliest represented start.  This is not a broad
    semantic proof; it is a deterministic object-centric identity for the
    current pure, path-insensitive loop-summary subset.
    """

    if summary is None:
        return None
    if is_kind(summary, ComposedLoopSummaryRef):
        return None
    seed_terms_for_binding = _optional_items(attribute_of(summary, "seed_terms", ()))
    binding_context = _loop_variable_binding_context_from_values(
        attribute_of(summary, "start_expr", None),
        attribute_of(summary, "limit_expr", None),
        attribute_of(summary, "step_expr", None),
        seed_terms_for_binding,
        _optional_items(attribute_of(summary, "witnesses", ())),
        _optional_items(attribute_of(summary, "guard_constraints", ())),
    )
    if binding_context is None:
        return None
    requires_effect_proof = attribute_of(summary, "requires_effect_proof", None)
    if callable(requires_effect_proof) and scalar_bool(requires_effect_proof()):
        return None
    requires_path_proof = attribute_of(summary, "requires_path_proof", None)
    if callable(requires_path_proof) and scalar_bool(requires_path_proof()):
        return None
    start_value = _loop_summary_int_constant(attribute_of(summary, "start_expr", None))
    step_value = _loop_summary_int_constant(attribute_of(summary, "step_expr", None))
    if start_value is None or step_value is None or step_value <= 0:
        return None

    term_descriptor = attribute_of(summary, "term_descriptor", None)
    if term_descriptor is None:
        return None
    if (
        exact_tree(attribute_of(term_descriptor, "kind", None)) == "memory_load"
        and attribute_of(term_descriptor, "location_base_ref", None) is None
    ):
        return None
    term_key = _loop_summary_term_descriptor_semantic_key(
        term_descriptor,
        loop_var_unit=exact_tree(attribute_of(summary, "loop_var_unit", None)),
    )
    if exact_tree(attribute_of(term_descriptor, "kind", None)) == "memory_load" and term_key is None:
        return None
    loop_var_unit_key = exact_tree(attribute_of(summary, "loop_var_unit", None))
    if term_key is not None and len(term_key) > 0 and term_key[0] == "scalar_memory_term_sequence":
        loop_var_unit_key = "scalar_element_index"
    limit_key = _loop_summary_limit_semantic_key(
        attribute_of(summary, "limit_expr", None),
        binding_context,
    )
    side_effect_key = exact_tree(method_of(summary.side_effect_profile, "semantic_key")())
    if limit_key is None or side_effect_key is None:
        return None

    canonical_start = scalar_int(start_value)
    seed_items = builtin_items(attribute_of(summary, "seed_terms", None))
    if seed_items is None:
        return None  # 読めない容器: 中身を落として別の key にしない
    remaining_seed_terms = list(seed_items)
    if not remaining_seed_terms:
        seed_term_count = attribute_of(summary, "seed_term_count", None)
        if (
            seed_term_count is not None
            and scalar_int(seed_term_count) >= 0
            and scalar_int(seed_term_count) == scalar_int(canonical_start)
            and scalar_int(step_value) == 1
        ):
            canonical_start = scalar_int(canonical_start) - scalar_int(seed_term_count)
            remaining_seed_terms = []

    while remaining_seed_terms:
        previous_index = canonical_start - scalar_int(step_value)
        expected_term = _loop_summary_term_at_index(summary, previous_index)
        if expected_term is None:
            break
        expected_key = _loop_object_semantic_key(expected_term, binding_context)
        actual_key = _loop_object_semantic_key(remaining_seed_terms[-1], binding_context)
        if expected_key is None or actual_key is None or expected_key != actual_key:
            break
        remaining_seed_terms.pop()
        canonical_start = previous_index

    seed_keys = tuple(_loop_object_semantic_key(term, binding_context) for term in remaining_seed_terms)
    if any(seed_key is None for seed_key in seed_keys):
        return None
    return (
        "loop_summary_method_b",
        loop_var_unit_key,
        scalar_int(canonical_start),
        limit_key,
        scalar_int(step_value),
        term_key,
        seed_keys,
        _bias_key(
            scalar_int_or(attribute_of(summary, "constant_bias", 0)),
            attribute_of(term_descriptor, "result_size", 0),
        ),
        side_effect_key,
    )


@runtime_ref_key
@runtime_ref_entry
def loop_summary_method_b_key_at_result_size(
    summary: Optional[LoopSummaryRef],
    result_size: int,
) -> Optional[Tuple[Any, ...]]:
    """Projected Method-B key for comparing a wider sum at a narrower width."""

    if summary is None:
        return None
    if is_kind(summary, ComposedLoopSummaryRef):
        return None
    try:
        target_result_size = max(1, scalar_int(result_size))
    except (TypeError, ValueError):
        return None
    term_descriptor = attribute_of(summary, "term_descriptor", None)
    if term_descriptor is None:
        return None
    original_result_size = max(1, scalar_int_or(attribute_of(term_descriptor, "result_size", 0)))
    if target_result_size > original_result_size:
        return None
    if target_result_size == original_result_size:
        return loop_summary_method_b_key(summary)
    if exact_tree(attribute_of(term_descriptor, "kind", None)) != "memory_load":
        return None
    if exact_tree(attribute_of(term_descriptor, "reduction_kind", "sum")) not in ("sum", "memory_sum"):
        return None

    try:
        lane_terms = _optional_rows(attribute_of(term_descriptor, "lane_terms", ()), 2)
    except (TypeError, ValueError):
        return None
    if lane_terms:
        try:
            if any(max(1, scalar_int_or(size)) != target_result_size for _offset, size in lane_terms):
                return None
        except (TypeError, ValueError):
            return None
    else:
        try:
            element_size = max(1, scalar_int_or(attribute_of(term_descriptor, "element_size", 0)))
        except (TypeError, ValueError):
            return None
        if element_size != target_result_size:
            return None

    projected_descriptor = replace(term_descriptor, result_size=target_result_size)
    projected_summary = replace(
        summary,
        term_descriptor=projected_descriptor,
        constant_bias=_bias_key(scalar_int_or(attribute_of(summary, "constant_bias", 0)), target_result_size)[1],
    )
    return loop_summary_method_b_key(projected_summary)


def _loop_summary_int_constant(value: Any) -> Optional[int]:
    if is_kind(value, bool):
        return None
    if is_kind(value, int):
        return scalar_int(value)
    expr_type = attribute_of(value, "expr_type", None)
    if exact_tree(attribute_of(expr_type, "name", None)) == "CONSTANT":
        try:
            return scalar_int(attribute_of(value, "value"))
        except (TypeError, ValueError):
            return None
    return None


def _loop_summary_limit_semantic_key(
    value: Any,
    loop_variable_context: Optional[_LoopVariableBindingContext] = None,
) -> Optional[Tuple[Any, ...]]:
    expr_type = attribute_of(value, "expr_type", None)
    if exact_tree(attribute_of(expr_type, "name", None)) == "PARAMETER":
        storage = attribute_of(value, "storage_info", None)
        storage_key = _loop_object_semantic_key(storage, loop_variable_context) if storage is not None else None
        if storage is not None:
            if storage_key is None:
                return None
            return ("loop_limit_parameter_storage", storage_key)
        index = attribute_of(value, "value", None)
        try:
            if index is not None and scalar_int(index) >= 0:
                return ("loop_limit_parameter", scalar_int(index))
        except (TypeError, ValueError):
            pass
        return None
    return _loop_object_semantic_key(value, loop_variable_context)


def _loop_summary_term_descriptor_semantic_key(
    term_descriptor: LoopTermDescriptorRef,
    *,
    loop_var_unit: Optional[str] = None,
) -> Optional[Tuple[Any, ...]]:
    scalar_key = _loop_summary_scalar_memory_term_key(
        term_descriptor,
        loop_var_unit=loop_var_unit,
    )
    if scalar_key is not None:
        return scalar_key
    return exact_tree(method_of(term_descriptor, "semantic_key")())


def _loop_summary_scalar_memory_term_key(
    term_descriptor: LoopTermDescriptorRef,
    *,
    loop_var_unit: Optional[str] = None,
) -> Optional[Tuple[Any, ...]]:
    loop_var_unit = exact_tree(loop_var_unit)
    if exact_tree(attribute_of(term_descriptor, "kind", None)) != "memory_load":
        return None
    location_base_ref = attribute_of(term_descriptor, "location_base_ref", None)
    if location_base_ref is None:
        return None
    reduction_kind = exact_tree(attribute_of(term_descriptor, "reduction_kind", "sum"))
    result_size = max(1, scalar_int_or(attribute_of(term_descriptor, "result_size", 0)))
    start_offset = scalar_int_or(attribute_of(term_descriptor, "start_offset", 0))
    lane_terms = _optional_rows(attribute_of(term_descriptor, "lane_terms", ()), 2)
    if not lane_terms:
        element_size = scalar_int_or(attribute_of(term_descriptor, "element_size", 0))
        stride = scalar_int_or(attribute_of(term_descriptor, "stride", 0))
        if element_size <= 0 or stride <= 0 or element_size != result_size:
            return None
        location_key = exact_tree(method_of(location_base_ref, "semantic_key")())
        if location_key is None:
            return None
        return (
            "scalar_memory_term_sequence",
            reduction_kind,
            location_key,
            start_offset,
            stride,
            element_size,
            result_size,
        )
    if loop_var_unit != "scalar_element_index":
        return None

    normalized_lanes = sorted(
        (scalar_int(offset), max(1, scalar_int_or(size)))
        for offset, size in lane_terms
    )
    access_sizes = {size for _, size in normalized_lanes}
    if len(access_sizes) != 1:
        return None
    access_size = next(iter(access_sizes))
    if access_size != result_size:
        return None
    offsets = [offset for offset, _ in normalized_lanes]
    if len(set(offsets)) != len(offsets):
        return None
    if len(offsets) == 1:
        scalar_stride = access_size
    else:
        deltas = [right - left for left, right in zip(offsets, offsets[1:])]
        if any(delta <= 0 for delta in deltas):
            return None
        scalar_stride = deltas[0]
        if any(delta != scalar_stride for delta in deltas):
            return None
    if scalar_stride != access_size:
        return None
    descriptor_stride = scalar_int_or(attribute_of(term_descriptor, "stride", 0))
    if descriptor_stride != scalar_stride * len(offsets):
        return None
    expected_offsets = [offsets[0] + index * scalar_stride for index in range(len(offsets))]
    if offsets != expected_offsets:
        return None
    location_key = exact_tree(method_of(location_base_ref, "semantic_key")())
    if location_key is None:
        return None
    return (
        "scalar_memory_term_sequence",
        reduction_kind,
        location_key,
        start_offset + offsets[0],
        scalar_stride,
        access_size,
        result_size,
    )


@runtime_ref_entry
def _loop_summary_term_at_index(summary: LoopSummaryRef, index: int) -> Optional[Any]:
    from scripts.function_tracer_pcode.core.runtime_refs.readonly import (ReadonlyReductionTermRef)
    term_descriptor = attribute_of(summary, "term_descriptor", None)
    if term_descriptor is None:
        return None
    if exact_tree(attribute_of(term_descriptor, "kind", None)) != "memory_load":
        return None
    scalar_key = _loop_summary_scalar_memory_term_key(
        term_descriptor,
        loop_var_unit=exact_tree(attribute_of(summary, "loop_var_unit", None)),
    )
    if scalar_key is not None:
        start_offset = scalar_int(scalar_key[3])
        stride = scalar_int(scalar_key[4])
        access_size = scalar_int(scalar_key[5])
        return ReadonlyReductionTermRef(
            byte_offset=start_offset + scalar_int(index) * stride,
            access_size=access_size,
        )
    element_size = scalar_int_or(attribute_of(term_descriptor, "element_size", 0))
    stride = scalar_int_or(attribute_of(term_descriptor, "stride", 0))
    if element_size <= 0 or stride <= 0:
        return None
    start_offset = scalar_int_or(attribute_of(term_descriptor, "start_offset", 0))
    return ReadonlyReductionTermRef(
        byte_offset=start_offset + scalar_int(index) * stride,
        access_size=element_size,
    )


def _loop_int_expr(value: int, like_expr: Any) -> Any:
    expression_cls = attribute_of(like_expr, "__class__", None)
    constant = attribute_of(expression_cls, "constant", None)
    if callable(constant):
        size = max(1, scalar_int_or(attribute_of(like_expr, "size", 0), 4))
        return exact_scalar(constant(scalar_int(value), size=size))  # 外の factory の結果の葉を写す
    return scalar_int(value)


@dataclass(frozen=True)
@runtime_ref_record
class CountedLoopSummaryRef:
    """Structured identity for a counted scalar loop summary."""

    induction_step: int
    result_size: int
    signed_loop: bool
    residue_cases: Tuple[Tuple[int, int, int, int], ...]
    residue_bias_terms: Tuple[Tuple[int, int, Any], ...] = ()
    source: str = "recurrence_summary"
    loop_summary: Optional[LoopSummaryRef] = None

    @runtime_ref_key
    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        loop_summary_key = self.loop_summary.stable_key() if self.loop_summary is not None else None
        residue_bias_keys = tuple(
            (
                int(modulus),
                int(residue),
                _loop_object_key(bias_expr),
            )
            for modulus, residue, bias_expr in _scalar_rows(self.residue_bias_terms, 3)
        )
        if any(key[2] is None for key in residue_bias_keys):
            return None
        return (
            "counted_loop_summary",
            int(self.induction_step),
            max(1, int(self.result_size or 0)),
            bool(self.signed_loop),
            tuple(
                (
                    int(modulus),
                    int(residue),
                    int(coeff),
                    int(bias),
                )
                for modulus, residue, coeff, bias in _scalar_rows(self.residue_cases, 4)
            ),
            residue_bias_keys,
            self.source,
            loop_summary_key,
        )

    @runtime_ref_key
    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        residue_bias_keys = tuple(
            (
                int(modulus),
                int(residue),
                _loop_object_semantic_key(bias_expr),
            )
            for modulus, residue, bias_expr in _scalar_rows(self.residue_bias_terms, 3)
        )
        if any(key[2] is None for key in residue_bias_keys):
            return None
        if self.loop_summary is not None:
            loop_key = self.loop_summary.semantic_key()
            if loop_key is None:
                return None
            return (
                "counted_loop_summary_loop_semantic",
                int(self.induction_step),
                max(1, int(self.result_size or 0)),
                bool(self.signed_loop),
                tuple(
                    (
                        int(modulus),
                        int(residue),
                        int(coeff),
                        int(bias),
                    )
                    for modulus, residue, coeff, bias in _scalar_rows(self.residue_cases, 4)
                ),
                residue_bias_keys,
                loop_key,
            )
        return (
            "counted_loop_summary_semantic",
            int(self.induction_step),
            max(1, int(self.result_size or 0)),
            bool(self.signed_loop),
            tuple(
                (
                    int(modulus),
                    int(residue),
                    int(coeff),
                    int(bias),
                )
                for modulus, residue, coeff, bias in _scalar_rows(self.residue_cases, 4)
            ),
            residue_bias_keys,
        )

    @runtime_ref_key
    def pairwise_exact_key(self) -> Optional[Tuple[Any, ...]]:
        if self.loop_summary is not None and self.loop_summary.pairwise_exact_key() is None:
            return None
        return self.stable_key()

    @runtime_ref_key
    def pairwise_semantic_key(self) -> Optional[Tuple[Any, ...]]:
        return self.semantic_key()

    def pairwise_requires_guard_equivalence(self) -> bool:
        return True

    def display_name(self) -> str:
        return (
            f"counted_loop(step={as_int(self.induction_step)},"
            f"signed={as_bool(self.signed_loop)},"
            f"cases={size(self.residue_cases)})"
        )

    def json_items(self):
        yield "kind", "counted_loop_summary"
        yield "induction_step", as_int(self.induction_step)
        yield "result_size", max(1, _int_or_zero(self.result_size))
        yield "signed_loop", as_bool(self.signed_loop)

        yield "residue_cases", each(
            self.residue_cases,
            _residue_case_source,
        )
        yield "residue_bias_terms", each(
            self.residue_bias_terms,
            _residue_bias_term_source,
        )

        yield "source", self.source
        yield "loop_summary", self.loop_summary if self.loop_summary is not None else None
        yield "display_name", self.display_name()

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
@runtime_ref_record
class StateTransitionLoopSummaryRef:
    """Object-centric summary for loops whose trip count is driven by state transitions.

    The summary describes the transition system, not a source-level loop name.
    Two summaries can share an SMT function only when their guard/update surface
    and side-effect profile are structurally/semantically identical.
    """

    state_guard: Any
    transition_expr: Any
    result_size: int
    state_size: int
    accumulator_init: Any = None
    accumulator_delta: Any = None
    transition_cases: Any = None
    side_effect_profile: LoopSideEffectProfileRef = LoopSideEffectProfileRef()
    source: str = "state_transition_loop_summary"

    def __post_init__(self) -> None:
        object.__setattr__(self, "result_size", max(1, scalar_int(self.result_size or 0)))
        object.__setattr__(self, "state_size", max(1, scalar_int(self.state_size or 0)))

    @runtime_ref_key
    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        guard_key = _loop_object_key(self.state_guard)
        transition_key = _loop_object_key(
            self.transition_cases if self.transition_cases is not None else self.transition_expr
        )
        init_key = _loop_object_key(self.accumulator_init)
        delta_key = _loop_object_key(self.accumulator_delta)
        side_effect_key = self.side_effect_profile.stable_key()
        if (
            guard_key is None
            or transition_key is None
            or init_key is None
            or delta_key is None
            or side_effect_key is None
        ):
            return None
        return (
            "state_transition_loop_summary",
            guard_key,
            transition_key,
            init_key,
            delta_key,
            side_effect_key,
            int(self.state_size),
            int(self.result_size),
            self.source,
        )

    @runtime_ref_key
    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        binding_context = _loop_variable_binding_context_from_values(
            self.state_guard,
            self.transition_cases if self.transition_cases is not None else self.transition_expr,
            self.accumulator_init,
            self.accumulator_delta,
        )
        if binding_context is None:
            return None
        guard_key = _loop_object_semantic_key(self.state_guard, binding_context)
        transition_key = _loop_object_semantic_key(
            self.transition_cases if self.transition_cases is not None else self.transition_expr,
            binding_context,
        )
        init_key = _loop_object_semantic_key(self.accumulator_init, binding_context)
        delta_key = _loop_object_semantic_key(self.accumulator_delta, binding_context)
        side_effect_key = self._scalar_side_effect_semantic_key(binding_context)
        if (
            guard_key is None
            or transition_key is None
            or init_key is None
            or delta_key is None
            or side_effect_key is None
        ):
            return None
        return (
            "state_transition_loop_summary",
            guard_key,
            transition_key,
            init_key,
            delta_key,
            side_effect_key,
            int(self.state_size),
            int(self.result_size),
            self.source,
        )

    def _scalar_side_effect_semantic_key(
        self,
        binding_context: Optional[_LoopVariableBindingContext] = None,
    ) -> Optional[Tuple[Any, ...]]:
        """Semantic effect key for state-transition summaries.

        Branch guards are part of ``state_guard`` and ``transition_cases`` for this
        summary kind, so CFG-local guard counts must not split otherwise identical
        transition systems.  Non-scalar effects still participate in the key.
        """

        effect_keys = tuple(
            _loop_object_semantic_key(effect, binding_context)
            for effect in _optional_items(getattr(self.side_effect_profile, "effect_descriptors", ()))
        )
        context_keys = tuple(
            _loop_object_semantic_key(effect, binding_context)
            for effect in _optional_items(getattr(self.side_effect_profile, "context_descriptors", ()))
        )
        if any(effect_key is None for effect_key in effect_keys + context_keys):
            return None
        return (
            "state_transition_scalar_effect_profile",
            scalar_bool(getattr(self.side_effect_profile, "memory_reads", False)),
            scalar_bool(getattr(self.side_effect_profile, "memory_writes", False)),
            scalar_bool(getattr(self.side_effect_profile, "calls", False)),
            scalar_bool(getattr(self.side_effect_profile, "escapes", False)),
            scalar_bool(getattr(self.side_effect_profile, "context_memory_writes", False)),
            scalar_bool(getattr(self.side_effect_profile, "context_calls", False)),
            scalar_bool(getattr(self.side_effect_profile, "context_escapes", False)),
            effect_keys,
            context_keys,
        )

    def display_name(self) -> str:
        return f"state_transition_loop(state={as_int(self.state_size)},result={as_int(self.result_size)})"

    def json_items(self):
        yield "kind", "state_transition_loop_summary"
        yield "state_guard", _loop_object_source(self.state_guard)
        yield "transition_expr", _loop_object_source(self.transition_expr)
        yield "transition_cases", _loop_object_source(self.transition_cases)
        yield "accumulator_init", _loop_object_source(self.accumulator_init)
        yield "accumulator_delta", _loop_object_source(self.accumulator_delta)
        yield "side_effect_profile", self.side_effect_profile
        yield "state_size", as_int(self.state_size)
        yield "result_size", as_int(self.result_size)
        yield "source", self.source
        yield "display_name", self.display_name()

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
@runtime_ref_record
class CountedStateTransitionLoopSummaryRef:
    """Summary for counted loops whose scalar state is updated by a transition."""

    initial_state: Any
    start_expr: Any
    limit_expr: Any
    step_expr: Any
    transition_expr: Any
    state_placeholder: Any
    transition_cases: Any = None
    side_effect_profile: LoopSideEffectProfileRef = LoopSideEffectProfileRef()
    guard_constraints: Tuple[Any, ...] = ()
    state_size: int = 0
    result_size: int = 0
    signed_loop: bool = False
    handoff_proof_key: Optional[Tuple[Any, ...]] = None
    source: str = "counted_state_transition_loop_summary"

    def __post_init__(self) -> None:
        object.__setattr__(self, "state_size", max(1, scalar_int(self.state_size or self.result_size or 0)))
        object.__setattr__(self, "result_size", max(1, scalar_int(self.result_size or self.state_size or 0)))

    @runtime_ref_key
    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        init_key = _loop_object_key(self.initial_state)
        start_key = _loop_object_key(self.start_expr)
        limit_key = _loop_object_key(self.limit_expr)
        step_key = _loop_object_key(self.step_expr)
        transition_key = _loop_object_key(
            self.transition_cases if self.transition_cases is not None else self.transition_expr
        )
        placeholder_key = _loop_object_key(self.state_placeholder)
        guard_keys = tuple(_loop_object_key(guard) for guard in self.guard_constraints)
        side_effect_key = self.side_effect_profile.stable_key()
        if (
            init_key is None
            or start_key is None
            or limit_key is None
            or step_key is None
            or transition_key is None
            or placeholder_key is None
            or any(guard_key is None for guard_key in guard_keys)
            or side_effect_key is None
        ):
            return None
        return (
            "counted_state_transition_loop_summary",
            init_key,
            start_key,
            limit_key,
            step_key,
            transition_key,
            placeholder_key,
            side_effect_key,
            guard_keys,
            int(self.state_size),
            int(self.result_size),
            bool(self.signed_loop),
            self.source,
        )

    @runtime_ref_key
    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        binding_context = _loop_variable_binding_context_from_values(
            self.state_placeholder,
            self.transition_cases if self.transition_cases is not None else self.transition_expr,
        )
        if binding_context is None:
            return None
        init_key = _loop_object_semantic_key(self.initial_state, binding_context)
        start_key = _loop_object_semantic_key(self.start_expr, binding_context)
        limit_key = _loop_object_semantic_key(self.limit_expr, binding_context)
        step_key = _loop_object_semantic_key(self.step_expr, binding_context)
        transition_key = _loop_object_semantic_key(
            self.transition_cases if self.transition_cases is not None else self.transition_expr,
            binding_context,
        )
        guard_keys = tuple(_loop_object_semantic_key(guard, binding_context) for guard in self.guard_constraints)
        side_effect_key = self.side_effect_profile.stable_key()
        if (
            init_key is None
            or start_key is None
            or limit_key is None
            or step_key is None
            or transition_key is None
            or any(guard_key is None for guard_key in guard_keys)
            or side_effect_key is None
        ):
            return None
        return (
            "counted_state_transition_loop_summary",
            init_key,
            start_key,
            limit_key,
            step_key,
            transition_key,
            side_effect_key,
            guard_keys,
            int(self.state_size),
            int(self.result_size),
            bool(self.signed_loop),
            self.source,
        )

    def display_name(self) -> str:
        return f"counted_state_transition(state={as_int(self.state_size)},result={as_int(self.result_size)})"

    def json_items(self):
        yield "kind", "counted_state_transition_loop_summary"
        yield "initial_state", _loop_object_source(self.initial_state)
        yield "start_expr", _loop_object_source(self.start_expr)
        yield "limit_expr", _loop_object_source(self.limit_expr)
        yield "step_expr", _loop_object_source(self.step_expr)
        yield "transition_expr", _loop_object_source(self.transition_expr)
        yield "transition_cases", _loop_object_source(self.transition_cases)
        yield "side_effect_profile", self.side_effect_profile
        yield "guard_constraints", _loop_object_source(self.guard_constraints)
        yield "state_size", as_int(self.state_size)
        yield "result_size", as_int(self.result_size)
        yield "signed_loop", as_bool(self.signed_loop)
        yield "handoff_proof_key", _loop_object_source(self.handoff_proof_key)
        yield "source", self.source
        yield "display_name", self.display_name()

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


# Sibling modules reference each other at call time; import them last to avoid cycles.

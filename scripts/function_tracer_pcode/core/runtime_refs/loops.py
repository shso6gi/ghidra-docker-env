"""Loop-derived references: variable identities, body effects, term descriptors, loop summaries and their comparison keys."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Callable, Dict, Optional, Sequence, Tuple
from scripts.function_tracer_pcode.core.json_encoding import (as_list, bounded_repr, each, inline, is_json_record, mapping_of, materialize, nested, raw, source_converter)
from scripts.function_tracer_pcode.core.runtime_refs.locations import (
    LocationBaseRef,
)


LoopSummarySolverProver = Callable[["LoopSummaryProofObligation"], "LoopSummaryComparisonResult"]


@dataclass(frozen=True)
class LoopVariableIdentityRef:
    """Object-derived identity for a synthetic loop placeholder variable."""

    role: str
    varnode_key: Tuple[Any, ...]
    binder_ordinal: int = 0

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        return None

    def binder_key(self) -> Tuple[Any, ...]:
        return (
            "loop_variable_binder",
            self.role,
            int(self.binder_ordinal),
        )

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        if not self.varnode_key:
            return None
        return (
            "loop_variable_identity",
            self.role,
            int(self.binder_ordinal),
            self.varnode_key,
        )

    def json_items(self):
        yield "kind", "loop_variable_identity"
        yield "role", self.role
        yield "binder_ordinal", int(self.binder_ordinal)
        yield "varnode_key", self.varnode_key

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
class _LoopVariableBindingContext:
    """Per-summary alpha-renaming context for loop placeholder variables."""

    stable_to_binder: Dict[Tuple[Any, ...], Tuple[Any, ...]]

    def semantic_key_for(self, ref: LoopVariableIdentityRef) -> Optional[Tuple[Any, ...]]:
        stable_key = ref.stable_key()
        if stable_key is None:
            return None
        binder_key = self.stable_to_binder.get(stable_key)
        if binder_key is None:
            return None
        return ("loop_bound_variable", binder_key)


def _loop_object_key(value: Any) -> Optional[Tuple[Any, ...]]:
    if value is None:
        return ("none",)
    if isinstance(value, bool):
        return ("bool", bool(value))
    if isinstance(value, int):
        return ("int", int(value))
    if isinstance(value, str):
        return ("str", value)
    if isinstance(value, bytes):
        return ("bytes", value.hex())
    if isinstance(value, tuple):
        item_keys = tuple(_loop_object_key(item) for item in value)
        if any(item_key is None for item_key in item_keys):
            return None
        return ("tuple", item_keys)
    if isinstance(value, list):
        item_keys = tuple(_loop_object_key(item) for item in value)
        if any(item_key is None for item_key in item_keys):
            return None
        return ("list", item_keys)
    if isinstance(value, dict):
        items = []
        for key, item in value.items():
            key_key = _loop_object_key(key)
            item_key = _loop_object_key(item)
            if key_key is None or item_key is None:
                return None
            items.append((key_key, item_key))
        items.sort()
        return ("dict", tuple(items))
    structural_key = getattr(value, "structural_key", None)
    if callable(structural_key):
        try:
            return ("structural", structural_key())
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
        if key is None:
            return None
        return ("stable", key)
    return None


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

        ref = item if isinstance(item, LoopVariableIdentityRef) else getattr(item, "runtime_ref", None)
        if isinstance(ref, LoopVariableIdentityRef):
            stable_key = ref.stable_key()
            binder_key = ref.binder_key()
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

        expr_type = getattr(getattr(item, "expr_type", None), "name", None)
        if expr_type == "PHI":
            for cond, branch_value in getattr(item, "value", None) or ():
                if cond is not None and not visit(cond):
                    return False
                if not visit(branch_value):
                    return False
            return True

        condition_expr = getattr(item, "expression", None)
        if condition_expr is not None and not visit(condition_expr):
            return False

        for operand in getattr(item, "operands", None) or ():
            if not visit(operand):
                return False

        if isinstance(item, dict):
            for key, dict_value in item.items():
                if not visit(key) or not visit(dict_value):
                    return False
        elif isinstance(item, (tuple, list)):
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
    if isinstance(value, bool):
        return ("bool", bool(value))
    if isinstance(value, int):
        return ("int", int(value))
    if isinstance(value, str):
        return ("str", value)
    if isinstance(value, bytes):
        return ("bytes", value.hex())
    if isinstance(value, tuple):
        item_keys = tuple(_loop_object_semantic_key(item, loop_variable_context) for item in value)
        if any(item_key is None for item_key in item_keys):
            return None
        return ("tuple", item_keys)
    if isinstance(value, list):
        item_keys = tuple(_loop_object_semantic_key(item, loop_variable_context) for item in value)
        if any(item_key is None for item_key in item_keys):
            return None
        return ("list", item_keys)
    if isinstance(value, dict):
        items = []
        for key, item in value.items():
            key_key = _loop_object_semantic_key(key, loop_variable_context)
            item_key = _loop_object_semantic_key(item, loop_variable_context)
            if key_key is None or item_key is None:
                return None
            items.append((key_key, item_key))
        items.sort()
        return ("dict", tuple(items))

    if isinstance(value, LoopVariableIdentityRef):
        if loop_variable_context is None:
            return None
        return loop_variable_context.semantic_key_for(value)

    expr_key = _loop_expression_semantic_key(value, loop_variable_context)
    if expr_key is not None:
        return ("expression", expr_key)

    semantic_key = getattr(value, "semantic_key", None)
    if callable(semantic_key):
        try:
            key = semantic_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
        if key is not None:
            return ("semantic", key)
        if isinstance(value, LocationBaseRef):
            return None

    storage_identity_key = getattr(value, "storage_identity_key", None)
    if callable(storage_identity_key):
        try:
            key = storage_identity_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
        if key is None:
            return None
        return ("storage_identity", key)

    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            key = stable_key()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return None
        if key is None:
            return None
        return ("stable", key)
    return None


def _loop_expression_semantic_key(
    value: Any,
    loop_variable_context: Optional[_LoopVariableBindingContext] = None,
) -> Optional[Tuple[Any, ...]]:
    expr_type = getattr(value, "expr_type", None)
    expr_type_name = getattr(expr_type, "name", None)
    if expr_type_name is None:
        return None

    size = int(getattr(value, "size", 0) or 0)
    if expr_type_name == "CONSTANT":
        try:
            return ("const", int(getattr(value, "value")), size)
        except (TypeError, ValueError):
            return None
    if expr_type_name == "PARAMETER":
        index = getattr(value, "value", None)
        try:
            if index is not None and int(index) >= 0:
                return ("parameter", int(index), size)
        except (TypeError, ValueError):
            pass
        storage = getattr(value, "storage_info", None)
        storage_key = _loop_object_semantic_key(storage, loop_variable_context) if storage is not None else None
        if storage is not None:
            if storage_key is None:
                return None
            return ("parameter_storage", size, storage_key)
        return None
    if expr_type_name == "VARIABLE":
        storage = getattr(value, "storage_info", None)
        storage_key = _loop_object_semantic_key(storage, loop_variable_context) if storage is not None else None
        if storage is not None:
            if storage_key is None:
                return None
            return ("variable_storage", size, storage_key)
        runtime_ref = getattr(value, "runtime_ref", None)
        runtime_key = _loop_object_semantic_key(runtime_ref, loop_variable_context) if runtime_ref is not None else None
        if runtime_ref is not None:
            if runtime_key is None:
                return None
            return ("variable_runtime", size, runtime_key)
        return None
    if expr_type_name in {"UNARY_OP", "BINARY_OP", "INTRINSIC", "CALL"}:
        operand_keys = tuple(
            _loop_object_semantic_key(operand, loop_variable_context)
            for operand in (getattr(value, "operands", None) or ())
        )
        if any(operand_key is None for operand_key in operand_keys):
            return None
        return (
            expr_type_name.lower(),
            getattr(value, "operator", None) or getattr(value, "name", None) or "",
            None if getattr(value, "opcode", None) is None else int(getattr(value, "opcode")),
            size,
            operand_keys,
        )
    if expr_type_name == "MEMORY":
        operands = getattr(value, "operands", None) or ()
        if not operands:
            return None
        address_key = _loop_object_semantic_key(operands[0], loop_variable_context)
        runtime_key = _loop_object_semantic_key(getattr(value, "runtime_ref", None), loop_variable_context)
        if address_key is None:
            return None
        return ("memory", size, address_key, runtime_key)
    if expr_type_name == "PHI":
        branches = []
        for condition, branch_value in getattr(value, "value", None) or ():
            if condition is None:
                condition_key = ("none",)
            else:
                condition_expr = getattr(condition, "expression", None)
                condition_key = (
                    "condition",
                    _loop_object_semantic_key(condition_expr, loop_variable_context),
                    bool(getattr(condition, "negated", False)),
                )
                if condition_key[1] is None:
                    return None
            value_key = _loop_object_semantic_key(branch_value, loop_variable_context)
            if value_key is None:
                return None
            branches.append((condition_key, value_key))
        return ("phi", size, tuple(branches))
    if expr_type_name == "UNKNOWN":
        runtime_key = _loop_object_semantic_key(getattr(value, "runtime_ref", None), loop_variable_context)
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

    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, (tuple, list)):
        return each(value, _loop_object_source)
    if isinstance(value, dict):
        return mapping_of(value, _loop_object_source, stringify_keys=True)
    if is_json_record(value):
        return value
    return inline(
        ("type", f"{type(value).__module__}.{type(value).__qualname__}"),
        ("unkeyable", True),
    )


def _loop_object_to_dict(value: Any) -> Any:
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, tuple):
        return [_loop_object_to_dict(item) for item in value]
    if isinstance(value, list):
        return [_loop_object_to_dict(item) for item in value]
    if isinstance(value, dict):
        return {str(key): _loop_object_to_dict(item) for key, item in value.items()}
    to_dict = getattr(value, "to_dict", None)
    if callable(to_dict):
        try:
            return to_dict()
        except (AttributeError, TypeError, ValueError, RecursionError):
            return {
                "type": f"{type(value).__module__}.{type(value).__qualname__}",
                "unserializable": True,
            }
    return {
        "type": f"{type(value).__module__}.{type(value).__qualname__}",
        "unkeyable": True,
    }


@dataclass(frozen=True)
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
            tuple(_loop_object_key(condition) for condition in path_conditions)
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

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        if not self.keyable or self.guard_paths_incomplete:
            return None
        address_space_key = _loop_object_semantic_key(self.address_space)
        location_key = _loop_object_semantic_key(self.location)
        value_key = _loop_object_semantic_key(self.value_expr)
        guard_keys = tuple(_loop_object_semantic_key(guard) for guard in self.guard_constraints)
        path_keys = tuple(
            tuple(_loop_object_semantic_key(condition) for condition in path_conditions)
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
            source_converter(lambda path_conditions: each(path_conditions, _loop_object_source)),
        )
        yield "guard_paths_incomplete", bool(self.guard_paths_incomplete)
        yield "target_ref", _loop_object_source(self.target_ref)
        yield "order_key", self.order_key
        yield "keyable", bool(self.keyable)
        yield "unkeyable_reason", self.unkeyable_reason

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
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

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        effect_keys = tuple(effect.stable_key() for effect in self.effect_descriptors)
        context_effect_keys = tuple(effect.stable_key() for effect in self.context_descriptors)
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

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        effect_keys = tuple(effect.semantic_key() for effect in self.effect_descriptors)
        context_effect_keys = tuple(effect.semantic_key() for effect in self.context_descriptors)
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
            return getattr(effect, "kind", None) != "conditional_guard"

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
        yield "memory_reads", bool(self.memory_reads)
        yield "memory_writes", bool(self.memory_writes)
        yield "calls", bool(self.calls)
        yield "escapes", bool(self.escapes)
        yield "conditional_guards", bool(self.conditional_guards)
        yield "context_memory_writes", bool(self.context_memory_writes)
        yield "context_calls", bool(self.context_calls)
        yield "context_escapes", bool(self.context_escapes)
        yield "context_conditional_guards", bool(self.context_conditional_guards)
        yield "effect_count", int(self.effect_count)
        yield "guard_count", int(self.guard_count)
        yield "effect_descriptors", each(self.effect_descriptors)
        yield "context_descriptors", each(self.context_descriptors)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
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

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        residue_bias_keys = tuple(
            (
                int(modulus),
                int(residue),
                _loop_object_key(bias_expr),
            )
            for modulus, residue, bias_expr in self.residue_bias_terms
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
                for modulus, residue, coeff, bias in self.residue_cases
            ),
            residue_bias_keys,
            tuple((int(offset), max(1, int(size or 0))) for offset, size in self.lane_terms),
        )

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
            for modulus, residue, bias_expr in self.residue_bias_terms
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
                for modulus, residue, coeff, bias in self.residue_cases
            ),
            residue_bias_keys,
            tuple((int(offset), max(1, int(size or 0))) for offset, size in self.lane_terms),
        )

    def json_items(self):
        yield "kind", "loop_term_descriptor"
        yield "term_kind", self.kind
        yield "reduction_kind", self.reduction_kind
        yield "start_offset", int(self.start_offset)
        yield "stride", int(self.stride)
        yield "element_size", int(self.element_size)
        yield "result_size", max(1, int(self.result_size or 0))

        yield "residue_cases", each(
            self.residue_cases,
            source_converter(lambda case: inline(
                ("modulus", int(case[0])),
                ("residue", int(case[1])),
                ("coeff", int(case[2])),
                ("bias", int(case[3])),
            )),
        )
        yield "residue_bias_terms", each(
            self.residue_bias_terms,
            source_converter(lambda term: inline(
                ("modulus", int(term[0])),
                ("residue", int(term[1])),
                ("bias_expr", term[2] if is_json_record(term[2]) else bounded_repr(term[2])),
            )),
        )

        yield "lane_terms", each(
            self.lane_terms,
            source_converter(lambda lane: inline(
                ("byte_offset", int(lane[0])),
                ("access_size", max(1, int(lane[1] or 0))),
            )),
        )
        if self.location_base_ref is not None:
            yield "location_base_ref", self.location_base_ref

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
class LoopCaseRef:
    """Path-sensitive loop-body case used by Method-B loop summaries."""

    path_conditions: Tuple[Any, ...] = ()
    body_effect: Any = None
    term_expr: Any = None
    case_kind: str = "body_term"
    source: str = "recurrence_summary"

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
    bits = max(1, int(result_size or 0)) * 8
    return bits, int(value) % (1 << bits)


def _normalize_storage_identity_key(value: Optional[Tuple[Any, ...]]) -> Optional[Tuple[Any, ...]]:
    if value is None:
        return None
    return tuple(value)


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
            index = int(count_parameter_index)
        except (TypeError, ValueError):
            index = -1
        if index >= 0:
            identities.append(("parameter", index))
    return tuple(identities)


@dataclass(frozen=True)
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
        result_size = int(getattr(self.term_descriptor, "result_size", 0) or 0)
        if result_size <= 0 and int(self.constant_bias) != 0:
            raise ValueError("LoopSummaryRef.constant_bias requires a positive term result_size")
        result_size = max(1, result_size)
        object.__setattr__(self, "constant_bias", _bias_key(int(self.constant_bias), result_size)[1])

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
        case_keys = tuple(case.stable_key() for case in self.cases)
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
        return self.side_effect_profile.requires_effect_proof()

    def requires_path_proof(self) -> bool:
        counted_update_cases = []
        for case in tuple(self.cases or ()):
            if getattr(case, "source", None) == "counted_loop_update_case":
                counted_update_cases.append(case)
                continue
            if getattr(case, "body_effect", None) is not None:
                return True
            if getattr(case, "term_expr", None) is not None:
                return True
        if counted_update_cases and not self._counted_loop_update_cases_are_descriptor_covered(counted_update_cases):
            return True
        return False

    def _counted_loop_update_cases_are_descriptor_covered(self, cases: Sequence[Any]) -> bool:
        if not cases:
            return True
        if getattr(self.term_descriptor, "kind", None) != "affine_residue":
            return False
        residue_cases = tuple(getattr(self.term_descriptor, "residue_cases", ()) or ())
        if not residue_cases:
            return False
        for case in cases:
            if getattr(case, "case_kind", None) != "accumulator_delta":
                return False
            body_effect = getattr(case, "body_effect", None)
            if getattr(body_effect, "kind", None) != "accumulator_update":
                return False
            if getattr(case, "term_expr", None) is None:
                return False
        residue_keys = []
        for residue_case in residue_cases:
            if len(residue_case) < 4:
                return False
            try:
                modulus = int(residue_case[0])
                residue = int(residue_case[1])
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

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        if self.requires_effect_proof() or self.requires_path_proof():
            return None
        return loop_summary_method_b_key(self)

    def pairwise_exact_key(self) -> Optional[Tuple[Any, ...]]:
        if self.requires_effect_proof() or self.requires_path_proof():
            return None
        return self.stable_key()

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
        yield "seed_term_count", None if self.seed_term_count is None else int(self.seed_term_count)
        yield "witnesses", each(self.witnesses, _loop_object_source)
        yield "side_effect_profile", self.side_effect_profile
        yield "guard_constraints", each(self.guard_constraints, _loop_object_source)
        yield "cases", each(self.cases)
        yield "source", self.source
        yield "constant_bias", int(self.constant_bias)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
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
        return getattr(self.current, "start_expr", None)

    @property
    def limit_expr(self) -> Any:
        return getattr(self.current, "limit_expr", None)

    @property
    def step_expr(self) -> Any:
        return getattr(self.current, "step_expr", None)

    @property
    def term_descriptor(self) -> Any:
        return getattr(self.current, "term_descriptor", None)

    @property
    def seed_terms(self) -> Tuple[Any, ...]:
        return tuple(getattr(self.current, "seed_terms", ()) or ())

    @property
    def seed_term_count(self) -> Optional[int]:
        return getattr(self.current, "seed_term_count", None)

    @property
    def witnesses(self) -> Tuple[Any, ...]:
        return tuple(getattr(self.current, "witnesses", ()) or ())

    @property
    def side_effect_profile(self) -> LoopSideEffectProfileRef:
        profile = getattr(self.current, "side_effect_profile", None)
        return profile if isinstance(profile, LoopSideEffectProfileRef) else LoopSideEffectProfileRef()

    @property
    def guard_constraints(self) -> Tuple[Any, ...]:
        return tuple(getattr(self.current, "guard_constraints", ()) or ())

    @property
    def cases(self) -> Tuple[Any, ...]:
        return tuple(getattr(self.current, "cases", ()) or ())

    @property
    def loop_var_unit(self) -> str:
        return str(getattr(self.current, "loop_var_unit", "element_index") or "element_index")

    @property
    def constant_bias(self) -> int:
        try:
            return int(getattr(self.current, "constant_bias", 0) or 0)
        except (TypeError, ValueError):
            return 0

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

    def pairwise_exact_key(self) -> Optional[Tuple[Any, ...]]:
        return self.stable_key()

    def pairwise_semantic_key(self) -> Optional[Tuple[Any, ...]]:
        return self.semantic_key()

    def requires_effect_proof(self) -> bool:
        for summary in (self.prior, self.current):
            requires_effect_proof = getattr(summary, "requires_effect_proof", None)
            if callable(requires_effect_proof) and requires_effect_proof():
                return True
        return False

    def requires_path_proof(self) -> bool:
        for summary in (self.prior, self.current):
            requires_path_proof = getattr(summary, "requires_path_proof", None)
            if callable(requires_path_proof) and requires_path_proof():
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
class LoopSummaryProofObligation:
    """Proof obligation emitted when loop-summary equality needs a solver context."""

    proof_kind: str
    left_summary_key: Optional[Tuple[Any, ...]]
    right_summary_key: Optional[Tuple[Any, ...]]
    relation: str
    required_evidence: Tuple[str, ...]
    reason: str

    @classmethod
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
        key_fn = getattr(summary, name, None)
        if not callable(key_fn):
            continue
        try:
            key = key_fn()
        except (AttributeError, TypeError, ValueError, RecursionError):
            key = None
        if key is not None:
            return key
    return None


@dataclass(frozen=True)
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
    left_profile = getattr(left, "side_effect_profile", None)
    right_profile = getattr(right, "side_effect_profile", None)
    if left_profile is not None and right_profile is not None:
        left_shape = (
            left_profile.profile,
            bool(left_profile.memory_reads),
            bool(left_profile.memory_writes),
            bool(left_profile.calls),
            bool(left_profile.escapes),
            bool(left_profile.conditional_guards),
            int(left_profile.effect_count),
            int(left_profile.guard_count),
        )
        right_shape = (
            right_profile.profile,
            bool(right_profile.memory_reads),
            bool(right_profile.memory_writes),
            bool(right_profile.calls),
            bool(right_profile.escapes),
            bool(right_profile.conditional_guards),
            int(right_profile.effect_count),
            int(right_profile.guard_count),
        )
        if left_shape != right_shape:
            return LoopSummaryComparisonResult("incompatible", "loop side-effect profiles differ")
        left_effect_key = left_profile.stable_key()
        right_effect_key = right_profile.stable_key()
        if left_effect_key is not None and right_effect_key is not None and left_effect_key != right_effect_key:
            return LoopSummaryComparisonResult("incompatible", "loop body effects differ")
    left_cases = tuple(getattr(left, "cases", ()) or ())
    right_cases = tuple(getattr(right, "cases", ()) or ())
    if len(left_cases) != len(right_cases):
        return LoopSummaryComparisonResult("incompatible", "loop case counts differ")
    if left_cases or right_cases:
        left_case_keys = tuple(case.stable_key() for case in left_cases)
        right_case_keys = tuple(case.stable_key() for case in right_cases)
        if any(case_key is None for case_key in left_case_keys + right_case_keys):
            return LoopSummaryComparisonResult("incompatible", "loop cases are unkeyable")
        if left_case_keys != right_case_keys:
            return LoopSummaryComparisonResult("incompatible", "loop cases differ")
    left_semantic_key = left.pairwise_semantic_key()
    right_semantic_key = right.pairwise_semantic_key()
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
        if isinstance(proven, LoopSummaryComparisonResult):
            if proven.status in {"equivalent", "different", "incompatible"}:
                return proven
    return LoopSummaryComparisonResult(
        "unknown",
        "loop summary comparator requires case-aware solver proof",
        proof_obligation=obligation,
    )


def loop_summary_method_b_key(summary: Optional[LoopSummaryRef]) -> Optional[Tuple[Any, ...]]:
    """Canonical Method-B key for pure loop summaries.

    The key normalizes a suffix loop whose ``seed_terms`` exactly cover the
    omitted prefix back to the earliest represented start.  This is not a broad
    semantic proof; it is a deterministic object-centric identity for the
    current pure, path-insensitive loop-summary subset.
    """

    if summary is None:
        return None
    if isinstance(summary, ComposedLoopSummaryRef):
        return None
    seed_terms_for_binding = tuple(getattr(summary, "seed_terms", ()) or ())
    binding_context = _loop_variable_binding_context_from_values(
        getattr(summary, "start_expr", None),
        getattr(summary, "limit_expr", None),
        getattr(summary, "step_expr", None),
        seed_terms_for_binding,
        tuple(getattr(summary, "witnesses", ()) or ()),
        tuple(getattr(summary, "guard_constraints", ()) or ()),
    )
    if binding_context is None:
        return None
    requires_effect_proof = getattr(summary, "requires_effect_proof", None)
    if callable(requires_effect_proof) and requires_effect_proof():
        return None
    requires_path_proof = getattr(summary, "requires_path_proof", None)
    if callable(requires_path_proof) and requires_path_proof():
        return None
    start_value = _loop_summary_int_constant(getattr(summary, "start_expr", None))
    step_value = _loop_summary_int_constant(getattr(summary, "step_expr", None))
    if start_value is None or step_value is None or step_value <= 0:
        return None

    term_descriptor = getattr(summary, "term_descriptor", None)
    if term_descriptor is None:
        return None
    if (
        getattr(term_descriptor, "kind", None) == "memory_load"
        and getattr(term_descriptor, "location_base_ref", None) is None
    ):
        return None
    term_key = _loop_summary_term_descriptor_semantic_key(
        term_descriptor,
        loop_var_unit=getattr(summary, "loop_var_unit", None),
    )
    if getattr(term_descriptor, "kind", None) == "memory_load" and term_key is None:
        return None
    loop_var_unit_key = getattr(summary, "loop_var_unit", None)
    if term_key is not None and len(term_key) > 0 and term_key[0] == "scalar_memory_term_sequence":
        loop_var_unit_key = "scalar_element_index"
    limit_key = _loop_summary_limit_semantic_key(
        getattr(summary, "limit_expr", None),
        binding_context,
    )
    side_effect_key = summary.side_effect_profile.semantic_key()
    if limit_key is None or side_effect_key is None:
        return None

    canonical_start = int(start_value)
    remaining_seed_terms = list(getattr(summary, "seed_terms", ()) or ())
    if not remaining_seed_terms:
        seed_term_count = getattr(summary, "seed_term_count", None)
        if (
            seed_term_count is not None
            and int(seed_term_count) >= 0
            and int(seed_term_count) == int(canonical_start)
            and int(step_value) == 1
        ):
            canonical_start = int(canonical_start) - int(seed_term_count)
            remaining_seed_terms = []

    while remaining_seed_terms:
        previous_index = canonical_start - int(step_value)
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
        int(canonical_start),
        limit_key,
        int(step_value),
        term_key,
        seed_keys,
        _bias_key(
            int(getattr(summary, "constant_bias", 0) or 0),
            getattr(term_descriptor, "result_size", 0),
        ),
        side_effect_key,
    )


def loop_summary_method_b_key_at_result_size(
    summary: Optional[LoopSummaryRef],
    result_size: int,
) -> Optional[Tuple[Any, ...]]:
    """Projected Method-B key for comparing a wider sum at a narrower width."""

    if summary is None:
        return None
    if isinstance(summary, ComposedLoopSummaryRef):
        return None
    try:
        target_result_size = max(1, int(result_size))
    except (TypeError, ValueError):
        return None
    term_descriptor = getattr(summary, "term_descriptor", None)
    if term_descriptor is None:
        return None
    original_result_size = max(1, int(getattr(term_descriptor, "result_size", 0) or 0))
    if target_result_size > original_result_size:
        return None
    if target_result_size == original_result_size:
        return loop_summary_method_b_key(summary)
    if getattr(term_descriptor, "kind", None) != "memory_load":
        return None
    if getattr(term_descriptor, "reduction_kind", "sum") not in {"sum", "memory_sum"}:
        return None

    lane_terms = tuple(getattr(term_descriptor, "lane_terms", ()) or ())
    if lane_terms:
        try:
            if any(max(1, int(size or 0)) != target_result_size for _offset, size in lane_terms):
                return None
        except (TypeError, ValueError):
            return None
    else:
        try:
            element_size = max(1, int(getattr(term_descriptor, "element_size", 0) or 0))
        except (TypeError, ValueError):
            return None
        if element_size != target_result_size:
            return None

    projected_descriptor = replace(term_descriptor, result_size=target_result_size)
    projected_summary = replace(
        summary,
        term_descriptor=projected_descriptor,
        constant_bias=_bias_key(int(getattr(summary, "constant_bias", 0) or 0), target_result_size)[1],
    )
    return loop_summary_method_b_key(projected_summary)


def _loop_summary_int_constant(value: Any) -> Optional[int]:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return int(value)
    expr_type = getattr(value, "expr_type", None)
    if getattr(expr_type, "name", None) == "CONSTANT":
        try:
            return int(getattr(value, "value"))
        except (TypeError, ValueError):
            return None
    return None


def _loop_summary_limit_semantic_key(
    value: Any,
    loop_variable_context: Optional[_LoopVariableBindingContext] = None,
) -> Optional[Tuple[Any, ...]]:
    expr_type = getattr(value, "expr_type", None)
    if getattr(expr_type, "name", None) == "PARAMETER":
        storage = getattr(value, "storage_info", None)
        storage_key = _loop_object_semantic_key(storage, loop_variable_context) if storage is not None else None
        if storage is not None:
            if storage_key is None:
                return None
            return ("loop_limit_parameter_storage", storage_key)
        index = getattr(value, "value", None)
        try:
            if index is not None and int(index) >= 0:
                return ("loop_limit_parameter", int(index))
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
    return term_descriptor.semantic_key()


def _loop_summary_scalar_memory_term_key(
    term_descriptor: LoopTermDescriptorRef,
    *,
    loop_var_unit: Optional[str] = None,
) -> Optional[Tuple[Any, ...]]:
    if getattr(term_descriptor, "kind", None) != "memory_load":
        return None
    location_base_ref = getattr(term_descriptor, "location_base_ref", None)
    if location_base_ref is None:
        return None
    reduction_kind = getattr(term_descriptor, "reduction_kind", "sum")
    result_size = max(1, int(getattr(term_descriptor, "result_size", 0) or 0))
    start_offset = int(getattr(term_descriptor, "start_offset", 0) or 0)
    lane_terms = tuple(getattr(term_descriptor, "lane_terms", ()) or ())
    if not lane_terms:
        element_size = int(getattr(term_descriptor, "element_size", 0) or 0)
        stride = int(getattr(term_descriptor, "stride", 0) or 0)
        if element_size <= 0 or stride <= 0 or element_size != result_size:
            return None
        location_key = location_base_ref.semantic_key()
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
        (int(offset), max(1, int(size or 0)))
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
    descriptor_stride = int(getattr(term_descriptor, "stride", 0) or 0)
    if descriptor_stride != scalar_stride * len(offsets):
        return None
    expected_offsets = [offsets[0] + index * scalar_stride for index in range(len(offsets))]
    if offsets != expected_offsets:
        return None
    location_key = location_base_ref.semantic_key()
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


def _loop_summary_term_at_index(summary: LoopSummaryRef, index: int) -> Optional[Any]:
    from scripts.function_tracer_pcode.core.runtime_refs.readonly import (ReadonlyReductionTermRef)
    term_descriptor = getattr(summary, "term_descriptor", None)
    if term_descriptor is None:
        return None
    if getattr(term_descriptor, "kind", None) != "memory_load":
        return None
    scalar_key = _loop_summary_scalar_memory_term_key(
        term_descriptor,
        loop_var_unit=getattr(summary, "loop_var_unit", None),
    )
    if scalar_key is not None:
        start_offset = int(scalar_key[3])
        stride = int(scalar_key[4])
        access_size = int(scalar_key[5])
        return ReadonlyReductionTermRef(
            byte_offset=start_offset + int(index) * stride,
            access_size=access_size,
        )
    element_size = int(getattr(term_descriptor, "element_size", 0) or 0)
    stride = int(getattr(term_descriptor, "stride", 0) or 0)
    if element_size <= 0 or stride <= 0:
        return None
    start_offset = int(getattr(term_descriptor, "start_offset", 0) or 0)
    return ReadonlyReductionTermRef(
        byte_offset=start_offset + int(index) * stride,
        access_size=element_size,
    )


def _loop_int_expr(value: int, like_expr: Any) -> Any:
    expression_cls = getattr(like_expr, "__class__", None)
    constant = getattr(expression_cls, "constant", None)
    if callable(constant):
        size = max(1, int(getattr(like_expr, "size", 0) or 4))
        return constant(int(value), size=size)
    return int(value)


@dataclass(frozen=True)
class CountedLoopSummaryRef:
    """Structured identity for a counted scalar loop summary."""

    induction_step: int
    result_size: int
    signed_loop: bool
    residue_cases: Tuple[Tuple[int, int, int, int], ...]
    residue_bias_terms: Tuple[Tuple[int, int, Any], ...] = ()
    source: str = "recurrence_summary"
    loop_summary: Optional[LoopSummaryRef] = None

    def stable_key(self) -> Optional[Tuple[Any, ...]]:
        loop_summary_key = self.loop_summary.stable_key() if self.loop_summary is not None else None
        residue_bias_keys = tuple(
            (
                int(modulus),
                int(residue),
                _loop_object_key(bias_expr),
            )
            for modulus, residue, bias_expr in self.residue_bias_terms
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
                for modulus, residue, coeff, bias in self.residue_cases
            ),
            residue_bias_keys,
            self.source,
            loop_summary_key,
        )

    def semantic_key(self) -> Optional[Tuple[Any, ...]]:
        residue_bias_keys = tuple(
            (
                int(modulus),
                int(residue),
                _loop_object_semantic_key(bias_expr),
            )
            for modulus, residue, bias_expr in self.residue_bias_terms
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
                    for modulus, residue, coeff, bias in self.residue_cases
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
                for modulus, residue, coeff, bias in self.residue_cases
            ),
            residue_bias_keys,
        )

    def pairwise_exact_key(self) -> Optional[Tuple[Any, ...]]:
        if self.loop_summary is not None and self.loop_summary.pairwise_exact_key() is None:
            return None
        return self.stable_key()

    def pairwise_semantic_key(self) -> Optional[Tuple[Any, ...]]:
        return self.semantic_key()

    def pairwise_requires_guard_equivalence(self) -> bool:
        return True

    def display_name(self) -> str:
        return (
            f"counted_loop(step={int(self.induction_step)},"
            f"signed={bool(self.signed_loop)},"
            f"cases={len(self.residue_cases)})"
        )

    def json_items(self):
        yield "kind", "counted_loop_summary"
        yield "induction_step", int(self.induction_step)
        yield "result_size", max(1, int(self.result_size or 0))
        yield "signed_loop", bool(self.signed_loop)

        yield "residue_cases", each(
            self.residue_cases,
            source_converter(lambda case: inline(
                ("modulus", int(case[0])),
                ("residue", int(case[1])),
                ("coeff", int(case[2])),
                ("bias", int(case[3])),
            )),
        )
        yield "residue_bias_terms", each(
            self.residue_bias_terms,
            source_converter(lambda term: inline(
                ("modulus", int(term[0])),
                ("residue", int(term[1])),
                ("bias_expr", term[2] if is_json_record(term[2]) else bounded_repr(term[2])),
            )),
        )

        yield "source", self.source
        yield "loop_summary", self.loop_summary if self.loop_summary is not None else None
        yield "display_name", self.display_name()

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
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
        object.__setattr__(self, "result_size", max(1, int(self.result_size or 0)))
        object.__setattr__(self, "state_size", max(1, int(self.state_size or 0)))

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
            for effect in getattr(self.side_effect_profile, "effect_descriptors", ()) or ()
        )
        context_keys = tuple(
            _loop_object_semantic_key(effect, binding_context)
            for effect in getattr(self.side_effect_profile, "context_descriptors", ()) or ()
        )
        if any(effect_key is None for effect_key in effect_keys + context_keys):
            return None
        return (
            "state_transition_scalar_effect_profile",
            bool(getattr(self.side_effect_profile, "memory_reads", False)),
            bool(getattr(self.side_effect_profile, "memory_writes", False)),
            bool(getattr(self.side_effect_profile, "calls", False)),
            bool(getattr(self.side_effect_profile, "escapes", False)),
            bool(getattr(self.side_effect_profile, "context_memory_writes", False)),
            bool(getattr(self.side_effect_profile, "context_calls", False)),
            bool(getattr(self.side_effect_profile, "context_escapes", False)),
            effect_keys,
            context_keys,
        )

    def display_name(self) -> str:
        return f"state_transition_loop(state={int(self.state_size)},result={int(self.result_size)})"

    def json_items(self):
        yield "kind", "state_transition_loop_summary"
        yield "state_guard", _loop_object_source(self.state_guard)
        yield "transition_expr", _loop_object_source(self.transition_expr)
        yield "transition_cases", _loop_object_source(self.transition_cases)
        yield "accumulator_init", _loop_object_source(self.accumulator_init)
        yield "accumulator_delta", _loop_object_source(self.accumulator_delta)
        yield "side_effect_profile", self.side_effect_profile
        yield "state_size", int(self.state_size)
        yield "result_size", int(self.result_size)
        yield "source", self.source
        yield "display_name", self.display_name()

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
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
        object.__setattr__(self, "state_size", max(1, int(self.state_size or self.result_size or 0)))
        object.__setattr__(self, "result_size", max(1, int(self.result_size or self.state_size or 0)))

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
        return f"counted_state_transition(state={int(self.state_size)},result={int(self.result_size)})"

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
        yield "state_size", int(self.state_size)
        yield "result_size", int(self.result_size)
        yield "signed_loop", bool(self.signed_loop)
        yield "handoff_proof_key", _loop_object_source(self.handoff_proof_key)
        yield "source", self.source
        yield "display_name", self.display_name()

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


# Sibling modules reference each other at call time; import them last to avoid cycles.

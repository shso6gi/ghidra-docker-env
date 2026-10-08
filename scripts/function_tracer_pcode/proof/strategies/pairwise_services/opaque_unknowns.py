"""Opaque / unsupported unknown evidence extracted from object targets."""

from __future__ import annotations

from typing import Any, List, Optional, Tuple

from scripts.function_tracer_pcode.core.structural import provenance_key_view


def _impl__opaque_unknown_return_object_evidence_from_target(
    self,
    object_target_key: Tuple[Any, ...],
) -> Optional[Tuple[Any, ...]]:
    target = self._normalize_nested_tuple(object_target_key)
    if not isinstance(target, tuple) or len(target) < 4:
        return None
    sides = []
    opaque_refs: List[Any] = []
    seen_refs = set()
    for side in target[2:4]:
        side_tuple = self._normalize_nested_tuple(side)
        if not isinstance(side_tuple, tuple) or len(side_tuple) < 6:
            return None
        side_label = side_tuple[1]
        function_ref = side_tuple[2]
        return_storage = side_tuple[3]
        partition_member = side_tuple[4]
        unresolved_locations = side_tuple[5]
        side_refs = self._opaque_unknown_refs_from_value(
            (partition_member, unresolved_locations)
        )
        for ref in side_refs:
            key = repr(ref)
            if key not in seen_refs:
                seen_refs.add(key)
                opaque_refs.append(ref)
        sides.append(
            (
                "return_side",
                ("side", side_label),
                ("function_ref", function_ref),
                ("return_storage", return_storage),
                ("return_case_origin", partition_member),
                ("unresolved_locations", unresolved_locations),
                ("opaque_unknown_refs", side_refs),
            )
        )
    if not opaque_refs:
        return None
    return (
        "opaque_unknown_return_object_evidence",
        ("opaque_unknown_refs", tuple(sorted(opaque_refs, key=repr))),
        ("return_sides", tuple(sides)),
        ("return_width_policy", tuple(side[3] for side in target[2:4] if isinstance(side, tuple) and len(side) >= 4)),
        ("evidence_status", "object_evidence_collected"),
    )


def _impl__opaque_unknown_refs_from_value(cls, value: Any) -> Tuple[Any, ...]:
    refs: List[Any] = []
    seen = set()

    def visit(node: Any) -> None:
        # provenance key の ref の identity（projection の atom）は owner の読み口で形を読む（Issue #215）
        normalized = provenance_key_view(cls._normalize_nested_tuple(node))
        if isinstance(normalized, tuple):
            if (
                len(normalized) == 2
                and normalized[0] in {"runtime_ref", "unknown_runtime_ref"}
                and isinstance(normalized[1], tuple)
                and len(normalized[1]) >= 2
                and normalized[1][0] == "opaque_unknown"
                and normalized[1][1] == "void"
            ):
                key = repr(normalized)
                if key not in seen:
                    seen.add(key)
                    refs.append(normalized)
            for item in normalized:
                visit(item)
        elif isinstance(normalized, list):
            for item in normalized:
                visit(item)
        elif isinstance(normalized, dict):
            for key, item in normalized.items():
                visit(key)
                visit(item)

    visit(value)
    return tuple(sorted(refs, key=repr))


def _impl__pcode_origin_cross_binary_shape_key(origin_key: Any) -> Optional[Tuple[Any, ...]]:
    if not (isinstance(origin_key, tuple) and origin_key and origin_key[0] == "pcode_op"):
        return None
    if (
        len(origin_key) >= 8
        and isinstance(origin_key[2], tuple)
        and len(origin_key[2]) == 3
        and origin_key[2][0] == "function_entry"
        and isinstance(origin_key[3], tuple)
        and len(origin_key[3]) == 3
        and origin_key[3][0] == "seq_target"
    ):
        try:
            relative_target = int(origin_key[3][2]) - int(origin_key[2][2])
            seq_time = int(origin_key[4])
            seq_order = int(origin_key[5])
            local_op_ordinal = int(origin_key[7])
        except (TypeError, ValueError):
            return None
        return (
            "pcode_op_cross_binary_shape",
            ("function_entry_space", origin_key[2][1]),
            ("target_space", origin_key[3][1]),
            ("relative_target_offset", relative_target),
            ("seq_time", seq_time),
            ("seq_order", seq_order),
            ("opcode", origin_key[6]),
            ("local_op_ordinal", local_op_ordinal),
        )
    if len(origin_key) >= 6:
        return (
            "pcode_op_cross_binary_shape",
            ("address_offset", origin_key[1]),
            ("seq_time", origin_key[2]),
            ("seq_order", origin_key[3]),
            ("block_index", origin_key[4]),
            ("mnemonic", origin_key[5]),
        )
    return None


def _impl__unsupported_ops_include_memory_or_effect(unsupported_ops: set[Any]) -> bool:
    for op in unsupported_ops:
        if not isinstance(op, tuple):
            continue
        rendered = repr(op)
        if any(marker in rendered for marker in ("LOAD", "STORE", "CALL", "INDIRECT", "MULTIEQUAL")):
            return True
    return False


def _impl__unknown_expression_classification_key(self, expr: Any) -> Tuple[str, Tuple[Any, ...]]:
    runtime_ref = getattr(expr, "runtime_ref", None)
    if getattr(runtime_ref, "deferred_call_ref", None) is not None:
        kind = "deferred_call_unknown"
    else:
        raw_kind = getattr(runtime_ref, "kind", None)
        kind = str(raw_kind or "opaque_unknown")
    runtime_key = self._diagnostic_key_or_semantic_key_or_stable_key_or_none(runtime_ref)
    if runtime_key is not None:
        ref_key = ("unknown_runtime_ref", runtime_key)
    else:
        ref_key = ("unknown_expression", self._expression_runtime_object_key(expr))
    return kind, ref_key


def _impl__object_target_contains_void_opaque_unknown(cls, value: Any) -> bool:
    # provenance key の ref の identity（projection の atom）は owner の読み口で形を読む（Issue #215）
    normalized = provenance_key_view(cls._normalize_nested_tuple(value))
    if isinstance(normalized, tuple):
        if (
            len(normalized) >= 2
            and normalized[0] == "opaque_unknown"
            and normalized[1] == "void"
        ):
            return True
        return any(cls._object_target_contains_void_opaque_unknown(item) for item in normalized)
    if isinstance(normalized, list):
        return any(cls._object_target_contains_void_opaque_unknown(item) for item in normalized)
    if isinstance(normalized, dict):
        return any(
            cls._object_target_contains_void_opaque_unknown(key)
            or cls._object_target_contains_void_opaque_unknown(item)
            for key, item in normalized.items()
        )
    return False

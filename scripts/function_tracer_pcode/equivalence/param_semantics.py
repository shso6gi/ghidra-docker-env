# -*- coding: utf-8 -*-
"""Shared parameter semantic-width inference helpers."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Iterable, Optional, Set, Tuple

from ..model import Expression, ExpressionType, FunctionReturnAnalysis, ReadonlyReductionRef, StorageInfo
from ..model.signature import get_declared_type_signedness


SIGNED_COMPARE_OPS = {"INT_SLESS", "INT_SLESSEQUAL"}
UNSIGNED_COMPARE_OPS = {"INT_LESS", "INT_LESSEQUAL"}
TRANSPARENT_UNARY_OPS = {"INT_SEXT", "INT_ZEXT", "CAST", "COPY"}
SIGNEDNESS_PROPAGATING_BINARY_OPS = {"INT_AND", "INT_OR", "INT_XOR"}


@dataclass(frozen=True)
class ParameterSemanticHint:
    """Semantic-width hint inferred from object-level usage evidence."""

    narrow_bits: int
    signedness: str
    signedness_source: str = "explicit"


ParameterIdentityKey = Tuple[object, ...]


def _empty_evidence_entry() -> Dict[str, Any]:
    return {
        "narrow_bits": set(),
        "signed_score": 0,
        "unsigned_score": 0,
        "direct_signed_score": 0,
        "direct_unsigned_score": 0,
        "blocked_compare_signedness": False,
    }


def infer_parameter_semantics(
    analysis: FunctionReturnAnalysis,
) -> Dict[int, ParameterSemanticHint]:
    """Infer per-parameter semantic-width hints from object-level usage evidence."""
    hints, _ = _infer_parameter_semantics_object_keyed(analysis)
    return hints


def infer_parameter_semantics_by_identity(
    analysis: FunctionReturnAnalysis,
) -> Dict[ParameterIdentityKey, ParameterSemanticHint]:
    """Infer semantic-width hints keyed by explicit parameter/storage identity."""
    _, hints_by_identity = _infer_parameter_semantics_object_keyed(analysis)
    return hints_by_identity


def _infer_parameter_semantics_object_keyed(
    analysis: FunctionReturnAnalysis,
) -> Tuple[Dict[int, ParameterSemanticHint], Dict[ParameterIdentityKey, ParameterSemanticHint]]:
    params_by_identity = _build_parameter_metadata_by_identity(analysis)

    evidence: Dict[ParameterIdentityKey, Dict[str, Any]] = {}
    for identity, meta in params_by_identity.items():
        storage_bits = _get_storage_bits(meta)
        if storage_bits is not None:
            _record_width_evidence(evidence, identity, storage_bits)

    for ret_info in analysis.returns or []:
        if ret_info.value is not None:
            _collect_from_expression(ret_info.value, evidence)
        for cond in ret_info.conditions or []:
            expr = getattr(cond, "expression", None)
            if expr is not None:
                _collect_from_expression(expr, evidence)
    for candidate in getattr(analysis, "summary_return_candidates", ()) or ():
        if getattr(candidate, "acceptance_status", None) not in {"accepted", "validated"}:
            continue
        ret_info = getattr(candidate, "return_info", None)
        if ret_info is None:
            continue
        if getattr(ret_info, "value", None) is not None:
            _collect_from_expression(ret_info.value, evidence)
        for cond in getattr(ret_info, "conditions", None) or []:
            expr = getattr(cond, "expression", None)
            if expr is not None:
                _collect_from_expression(expr, evidence)

    evidence_by_index: Dict[int, Dict[str, Any]] = {}
    identities_by_index: Dict[int, Set[ParameterIdentityKey]] = {}
    metadata_by_index: Dict[int, Dict[str, Any]] = {}
    hints: Dict[int, ParameterSemanticHint] = {}
    hints_by_identity: Dict[ParameterIdentityKey, ParameterSemanticHint] = {}
    for identity, param_evidence in evidence.items():
        meta = params_by_identity.get(identity)
        if meta is None:
            continue
        index = meta["index"]
        if index is None:
            hint = _semantic_hint_from_evidence(param_evidence, meta)
            if hint is not None:
                hints_by_identity[identity] = hint
                for descriptor_identity in meta.get("identities", set()):
                    hints_by_identity.setdefault(descriptor_identity, hint)
            continue
        metadata_by_index[index] = meta
        identities_by_index.setdefault(index, set()).add(identity)
        _merge_evidence_entries(
            evidence_by_index.setdefault(index, _empty_evidence_entry()),
            param_evidence,
        )

    for index, param_evidence in evidence_by_index.items():
        meta = metadata_by_index.get(index)
        if meta is None:
            continue
        hint = _semantic_hint_from_evidence(param_evidence, meta)
        if hint is None:
            continue
        hints[index] = hint
        for identity in identities_by_index.get(index, set()):
            hints_by_identity[identity] = hint
        for identity in meta.get("identities", set()):
            hints_by_identity.setdefault(identity, hint)

    return hints, hints_by_identity


def hint_objects_by_name(
    analysis: FunctionReturnAnalysis,
) -> Dict[str, ParameterSemanticHint]:
    """Return semantic hint objects keyed by parameter name."""
    by_index = infer_parameter_semantics(analysis)
    unique_names = _globally_unique_parameter_names(analysis.parameters or [])
    candidates: Dict[str, list[ParameterSemanticHint]] = {}
    for param in analysis.parameters or []:
        index = _normalize_parameter_index(param.get("index"))
        if index is None:
            continue
        hint = by_index.get(index)
        if hint is None:
            continue
        name = param.get("name")
        if not isinstance(name, str) or not name:
            continue
        if name not in unique_names:
            continue
        candidates.setdefault(name, []).append(hint)
    return {
        name: values[0]
        for name, values in candidates.items()
        if len(values) == 1
    }


def _globally_unique_parameter_names(parameters: Iterable[Dict[str, Any]]) -> Set[str]:
    counts: Dict[str, int] = {}
    for param in parameters or []:
        name = param.get("name")
        if isinstance(name, str) and name:
            counts[name] = counts.get(name, 0) + 1
    return {name for name, count in counts.items() if count == 1}


def hint_objects_by_identity(
    analysis: FunctionReturnAnalysis,
) -> Dict[ParameterIdentityKey, ParameterSemanticHint]:
    """Return semantic hint objects keyed by explicit parameter/storage identity."""
    return infer_parameter_semantics_by_identity(analysis)


def parameter_identity_key_from_descriptor(
    param: Dict[str, Any],
) -> Optional[ParameterIdentityKey]:
    """Return the canonical object identity for a parameter descriptor."""
    index = _normalize_parameter_index(param.get("index"))
    if index is not None:
        return ("parameter_index", index)
    storage_key = _storage_identity_key(param.get("storage_info", param.get("storage")))
    if storage_key is not None:
        return ("parameter_storage", storage_key)
    return None


def parameter_identity_key_from_expression(
    expr: Expression,
) -> Optional[ParameterIdentityKey]:
    """Return the canonical object identity for a parameter expression."""
    return _parameter_identity_key_from_expression(expr)


def _collect_from_expression(
    expr: Expression,
    evidence: Dict[ParameterIdentityKey, Dict[str, Any]],
) -> None:
    if expr is None:
        return

    runtime_ref = getattr(expr, "runtime_ref", None)
    if _is_readonly_reduction_ref(runtime_ref):
        _record_readonly_reduction_counter_evidence(runtime_ref, evidence)

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        operand = expr.operands[0]
        refs = _extract_param_reference(operand)
        if refs is not None:
            for identity, narrow_bits in refs.items():
                if narrow_bits is not None:
                    _record_width_evidence(evidence, identity, narrow_bits)
                if expr.operator == "INT_SEXT":
                    _record_signedness_evidence(evidence, identity, signed_score=3)

    elif expr.expr_type == ExpressionType.BINARY_OP:
        if expr.operator == "SUBPIECE":
            refs = _extract_subpiece_reference(expr)
            if refs is not None:
                for identity, narrow_bits in refs.items():
                    _record_width_evidence(evidence, identity, narrow_bits)

        elif expr.operator == "INT_AND":
            refs = _extract_masked_param_reference(expr)
            if refs is not None:
                for identity, narrow_bits in refs.items():
                    _record_width_evidence(evidence, identity, narrow_bits)

        elif expr.operator in SIGNED_COMPARE_OPS | UNSIGNED_COMPARE_OPS:
            _record_compare_signedness(expr, evidence)

    for operand in expr.operands or []:
        _collect_from_expression(operand, evidence)

    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if hasattr(value, "expr_type"):
                _collect_from_expression(value, evidence)
            if cond is not None and hasattr(cond, "expression"):
                _collect_from_expression(cond.expression, evidence)


def _record_readonly_reduction_counter_evidence(
    runtime_ref: ReadonlyReductionRef,
    evidence: Dict[ParameterIdentityKey, Dict[str, Any]],
) -> None:
    identities: Set[ParameterIdentityKey] = set()
    identities_fn = getattr(runtime_ref, "count_parameter_semantic_identities", None)
    if callable(identities_fn):
        try:
            identities.update(
                identity for identity in identities_fn() if isinstance(identity, tuple)
            )
        except Exception:
            pass
    index = _normalize_parameter_index(getattr(runtime_ref, "count_parameter_index", None))
    if index is not None:
        identities.add(("parameter_index", index))
    storage_key = _storage_identity_key(
        getattr(runtime_ref, "count_parameter_storage_identity_key", None)
    )
    if storage_key is not None:
        identities.add(("parameter_storage", storage_key))
    if not identities:
        return
    signed_counter = bool(getattr(runtime_ref, "signed_counter", True))
    for identity in identities:
        _record_signedness_evidence(
            evidence,
            identity,
            signed_score=4 if signed_counter else 0,
            unsigned_score=4 if not signed_counter else 0,
            direct_operand=True,
        )


def _is_readonly_reduction_ref(runtime_ref: Any) -> bool:
    if isinstance(runtime_ref, ReadonlyReductionRef):
        return True
    if runtime_ref is None:
        return False
    return (
        hasattr(runtime_ref, "reduction_kind")
        and (
            hasattr(runtime_ref, "count_parameter_index")
            or hasattr(runtime_ref, "count_parameter_storage_identity_key")
            or hasattr(runtime_ref, "count_parameter_name")
        )
    )


def _record_compare_signedness(
    expr: Expression,
    evidence: Dict[ParameterIdentityKey, Dict[str, Any]],
) -> None:
    if len(expr.operands) != 2:
        return

    score_key = "signed_score" if expr.operator in SIGNED_COMPARE_OPS else "unsigned_score"
    left_refs = _collect_compare_signedness_references(expr.operands[0])
    right_refs = _collect_compare_signedness_references(expr.operands[1])
    left_blocked_refs = _collect_blocked_compare_signedness_references(expr.operands[0])
    right_blocked_refs = _collect_blocked_compare_signedness_references(expr.operands[1])
    left_direct = _is_direct_param_compare_operand(expr.operands[0])
    right_direct = _is_direct_param_compare_operand(expr.operands[1])

    if left_refs and _supports_signedness_inference(expr.operands[1]):
        _record_compare_refs(
            left_refs,
            evidence,
            score_key,
            compare_expr=expr,
            other_operand=expr.operands[1],
            direct_operand=left_direct,
        )
    elif left_blocked_refs and _supports_signedness_inference(expr.operands[1]):
        _record_blocked_compare_signedness(evidence, left_blocked_refs)

    if right_refs and _supports_signedness_inference(expr.operands[0]):
        _record_compare_refs(
            right_refs,
            evidence,
            score_key,
            compare_expr=expr,
            other_operand=expr.operands[0],
            direct_operand=right_direct,
        )
    elif right_blocked_refs and _supports_signedness_inference(expr.operands[0]):
        _record_blocked_compare_signedness(evidence, right_blocked_refs)


def _record_compare_refs(
    refs: Dict[ParameterIdentityKey, Optional[int]],
    evidence: Dict[ParameterIdentityKey, Dict[str, Any]],
    score_key: str,
    *,
    compare_expr: Expression,
    other_operand: Expression,
    direct_operand: bool,
) -> None:
    signed_bonus = _signed_boundary_bonus(compare_expr, other_operand)
    for identity, narrow_bits in refs.items():
        if narrow_bits is not None:
            _record_width_evidence(evidence, identity, narrow_bits)
        _record_signedness_evidence(
            evidence,
            identity,
            signed_score=(2 + signed_bonus) if score_key == "signed_score" else 0,
            unsigned_score=2 if score_key == "unsigned_score" else 0,
            direct_operand=direct_operand,
        )


def _signed_boundary_bonus(
    compare_expr: Expression,
    other_operand: Expression,
) -> int:
    if compare_expr.operator not in SIGNED_COMPARE_OPS:
        return 0
    if other_operand.expr_type != ExpressionType.CONSTANT:
        return 0
    try:
        const_value = int(other_operand.value)
    except Exception:
        return 0
    return 2 if const_value in {0, -1} else 0


def _supports_signedness_inference(expr: Expression) -> bool:
    if expr.expr_type == ExpressionType.CONSTANT:
        return True
    refs = _collect_compare_signedness_references(expr)
    return refs is not None and bool(refs)


def _collect_compare_signedness_references(
    expr: Expression,
) -> Optional[Dict[ParameterIdentityKey, Optional[int]]]:
    """Collect parameter refs whose compare signedness can be attributed directly.

    Unlike the general collector, this intentionally does not cross explicit
    extension/cast nodes. Compare opcode signedness for ``SEXT/ZEXT(param)`` is
    evidence about the widened temporary, not about the leaf parameter object.
    """
    if expr.expr_type == ExpressionType.PARAMETER:
        identity = _parameter_identity_key_from_expression(expr)
        return {identity: None} if identity is not None else None

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        return None

    if expr.expr_type != ExpressionType.BINARY_OP:
        return None

    if expr.operator == "SUBPIECE":
        return _extract_subpiece_reference(expr)

    if expr.operator == "INT_AND":
        return _extract_masked_param_reference(expr)

    if expr.operator not in SIGNEDNESS_PROPAGATING_BINARY_OPS:
        return None

    merged: Dict[ParameterIdentityKey, Optional[int]] = {}
    for operand in expr.operands:
        if operand.expr_type == ExpressionType.CONSTANT:
            continue
        operand_refs = _collect_compare_signedness_references(operand)
        if operand_refs is None:
            return None
        _merge_param_reference_maps(merged, operand_refs)

    return merged


def _collect_blocked_compare_signedness_references(
    expr: Expression,
) -> Optional[Dict[ParameterIdentityKey, Optional[int]]]:
    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        if expr.operator in TRANSPARENT_UNARY_OPS:
            return _collect_param_references(expr.operands[0])
        return None

    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator not in SIGNEDNESS_PROPAGATING_BINARY_OPS:
        return None

    merged: Dict[ParameterIdentityKey, Optional[int]] = {}
    for operand in expr.operands:
        if operand.expr_type == ExpressionType.CONSTANT:
            continue
        operand_refs = _collect_blocked_compare_signedness_references(operand)
        if operand_refs:
            _merge_param_reference_maps(merged, operand_refs)
    return merged or None


def _collect_param_references(
    expr: Expression,
) -> Optional[Dict[ParameterIdentityKey, Optional[int]]]:
    """Collect parameter references from signedness-safe expression shapes.

    The collector is intentionally conservative: it only walks through operators
    whose comparison signedness can be meaningfully propagated to their leaf
    parameters without assuming arithmetic identities.
    """
    if expr.expr_type == ExpressionType.PARAMETER:
        identity = _parameter_identity_key_from_expression(expr)
        return {identity: None} if identity is not None else None

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        if expr.operator in TRANSPARENT_UNARY_OPS:
            return _collect_param_references(expr.operands[0])
        return None

    if expr.expr_type != ExpressionType.BINARY_OP:
        return None

    if expr.operator == "SUBPIECE":
        return _extract_subpiece_reference(expr)

    if expr.operator == "INT_AND":
        return _extract_masked_param_reference(expr)

    if expr.operator not in SIGNEDNESS_PROPAGATING_BINARY_OPS:
        return None

    merged: Dict[ParameterIdentityKey, Optional[int]] = {}
    for operand in expr.operands:
        if operand.expr_type == ExpressionType.CONSTANT:
            continue
        operand_refs = _collect_param_references(operand)
        if operand_refs is None:
            return None
        _merge_param_reference_maps(merged, operand_refs)

    return merged


def _merge_param_reference_maps(
    merged: Dict[ParameterIdentityKey, Optional[int]],
    refs: Dict[ParameterIdentityKey, Optional[int]],
) -> None:
    for identity, narrow_bits in refs.items():
        current = merged.get(identity)
        if current is None:
            merged[identity] = narrow_bits
            continue
        if narrow_bits is None:
            continue
        merged[identity] = min(current, narrow_bits) if current is not None else narrow_bits


def _extract_param_reference(
    expr: Expression,
) -> Optional[Dict[ParameterIdentityKey, Optional[int]]]:
    if expr.expr_type == ExpressionType.PARAMETER:
        identity = _parameter_identity_key_from_expression(expr)
        return {identity: None} if identity is not None else None

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        if expr.operator in TRANSPARENT_UNARY_OPS:
            return _extract_param_reference(expr.operands[0])

    if expr.expr_type == ExpressionType.BINARY_OP:
        if expr.operator == "SUBPIECE":
            return _extract_subpiece_reference(expr)
        if expr.operator == "INT_AND":
            return _extract_masked_param_reference(expr)

    return None


def _is_direct_param_compare_operand(expr: Expression) -> bool:
    if expr.expr_type == ExpressionType.PARAMETER:
        return _parameter_identity_key_from_expression(expr) is not None
    if expr.expr_type == ExpressionType.BINARY_OP:
        if expr.operator == "SUBPIECE":
            return _extract_subpiece_reference(expr) is not None
        if expr.operator == "INT_AND":
            return _extract_masked_param_reference(expr) is not None
    return False


def _extract_subpiece_reference(
    expr: Expression,
) -> Optional[Dict[ParameterIdentityKey, int]]:
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "SUBPIECE":
        return None
    if len(expr.operands) != 2:
        return None

    source, offset = expr.operands
    if offset.expr_type != ExpressionType.CONSTANT or offset.value != 0:
        return None

    source_ref = _extract_param_reference(source)
    if source_ref is None:
        return None

    return {identity: expr.get_bit_width() for identity in source_ref}


def _extract_masked_param_reference(
    expr: Expression,
) -> Optional[Dict[ParameterIdentityKey, int]]:
    if expr.expr_type != ExpressionType.BINARY_OP or expr.operator != "INT_AND":
        return None
    if len(expr.operands) != 2:
        return None

    left, right = expr.operands
    if left.expr_type == ExpressionType.CONSTANT:
        const_expr, other_expr = left, right
    elif right.expr_type == ExpressionType.CONSTANT:
        const_expr, other_expr = right, left
    else:
        return None

    mask_bits = _mask_to_narrow_bits(getattr(const_expr, "value", None))
    if mask_bits is None:
        return None

    ref = _extract_param_reference(other_expr)
    if ref is None:
        return None

    return {identity: mask_bits for identity in ref}


def _mask_to_narrow_bits(value: Any) -> Optional[int]:
    if not isinstance(value, int) or value <= 0:
        return None
    for bits in (8, 16, 32):
        if value == (1 << bits) - 1:
            return bits
    return None


def _record_width_evidence(
    evidence: Dict[ParameterIdentityKey, Dict[str, Any]],
    identity: ParameterIdentityKey,
    narrow_bits: int,
) -> None:
    entry = evidence.setdefault(identity, _empty_evidence_entry())
    if int(narrow_bits) > 0:
        entry["narrow_bits"].add(int(narrow_bits))


def _record_signedness_evidence(
    evidence: Dict[ParameterIdentityKey, Dict[str, Any]],
    identity: ParameterIdentityKey,
    *,
    signed_score: int = 0,
    unsigned_score: int = 0,
    direct_operand: bool = False,
) -> None:
    entry = evidence.setdefault(identity, _empty_evidence_entry())
    entry["signed_score"] += signed_score
    entry["unsigned_score"] += unsigned_score
    if direct_operand:
        entry["direct_signed_score"] += signed_score
        entry["direct_unsigned_score"] += unsigned_score


def _record_blocked_compare_signedness(
    evidence: Dict[ParameterIdentityKey, Dict[str, Any]],
    refs: Dict[ParameterIdentityKey, Optional[int]],
) -> None:
    for identity, narrow_bits in refs.items():
        entry = evidence.setdefault(identity, _empty_evidence_entry())
        entry["blocked_compare_signedness"] = True
        if narrow_bits is not None:
            entry["narrow_bits"].add(int(narrow_bits))


def _resolve_narrow_bits(
    param_evidence: Dict[str, Any],
    declared_bits: int,
) -> Optional[int]:
    candidates = sorted(
        bits for bits in param_evidence.get("narrow_bits", set()) if bits < declared_bits
    )
    if not candidates:
        return None
    return candidates[0]


def _semantic_hint_from_evidence(
    param_evidence: Dict[str, Any],
    meta: Dict[str, Any],
) -> Optional[ParameterSemanticHint]:
    narrow_bits = _resolve_narrow_bits(param_evidence, meta["declared_bits"])
    signedness, signedness_source = _resolve_signedness(
        param_evidence,
        meta["declared_signedness"],
    )
    if signedness is None:
        return None
    assert signedness_source is not None

    if narrow_bits is not None and 0 < int(narrow_bits) < int(meta["declared_bits"]):
        direct_signedness_state = _resolve_direct_signedness(param_evidence)
        if direct_signedness_state == "conflict":
            signedness = "unknown"
            signedness_source = "width_only"
        elif direct_signedness_state in {"signed", "unsigned"}:
            signedness = direct_signedness_state
            signedness_source = "explicit"
        else:
            signedness = "unknown"
            signedness_source = "width_only"

    if not _should_emit_hint(
        param_evidence=param_evidence,
        narrow_bits=narrow_bits,
        declared_bits=meta["declared_bits"],
        signedness=signedness,
        signedness_source=signedness_source,
        declared_signedness=meta["declared_signedness"],
    ):
        return None

    return ParameterSemanticHint(
        narrow_bits=narrow_bits or meta["declared_bits"],
        signedness=signedness,
        signedness_source=signedness_source,
    )


def _merge_evidence_entries(target: Dict[str, Any], source: Dict[str, Any]) -> None:
    target.setdefault("narrow_bits", set()).update(source.get("narrow_bits", set()))
    for key in ("signed_score", "unsigned_score", "direct_signed_score", "direct_unsigned_score"):
        target[key] = int(target.get(key, 0)) + int(source.get(key, 0))
    target["blocked_compare_signedness"] = bool(
        target.get("blocked_compare_signedness", False)
        or source.get("blocked_compare_signedness", False)
    )


def _resolve_signedness(
    param_evidence: Dict[str, Any],
    declared_signedness: Optional[str],
) -> Tuple[Optional[str], Optional[str]]:
    signed_score = int(param_evidence.get("signed_score", 0))
    unsigned_score = int(param_evidence.get("unsigned_score", 0))

    if signed_score > unsigned_score:
        return "signed", "explicit"
    if unsigned_score > signed_score:
        return "unsigned", "explicit"

    if declared_signedness in {"signed", "unsigned"}:
        return declared_signedness, "declared"
    return None, None


def _should_emit_hint(
    *,
    param_evidence: Dict[str, Any],
    narrow_bits: Optional[int],
    declared_bits: int,
    signedness: str,
    signedness_source: str,
    declared_signedness: Optional[str],
) -> bool:
    if narrow_bits is not None and 0 < int(narrow_bits) < int(declared_bits):
        return True

    if signedness_source != "explicit":
        return False

    direct_signed_score = int(param_evidence.get("direct_signed_score", 0))
    direct_unsigned_score = int(param_evidence.get("direct_unsigned_score", 0))
    if direct_signed_score > 0 and direct_unsigned_score > 0:
        return False
    if direct_signed_score == direct_unsigned_score:
        return False

    direct_signedness = "signed" if direct_signed_score > direct_unsigned_score else "unsigned"
    if signedness != direct_signedness:
        return False

    if declared_signedness not in {"signed", "unsigned"}:
        return True
    return signedness != declared_signedness


def _resolve_direct_signedness(param_evidence: Dict[str, Any]) -> Optional[str]:
    direct_signed_score = int(param_evidence.get("direct_signed_score", 0))
    direct_unsigned_score = int(param_evidence.get("direct_unsigned_score", 0))
    if direct_signed_score > 0 and direct_unsigned_score > 0:
        return "conflict"
    if direct_signed_score > 0:
        return "signed"
    if direct_unsigned_score > 0:
        return "unsigned"
    return None


def _get_declared_bits(param: Dict[str, Any]) -> int:
    raw_dt = param.get("data_type_obj")
    if raw_dt is not None and hasattr(raw_dt, "getLength"):
        try:
            return int(raw_dt.getLength()) * 8
        except Exception:
            pass
    return int(param.get("size", 4)) * 8


def _get_storage_bits(
    param_meta: Dict[str, Any],
) -> Optional[int]:
    storage = _coerce_storage_info(param_meta.get("storage"))
    if storage is None:
        return None
    try:
        size_bits = int(storage.size_bits or (storage.size * 8) or 0)
    except Exception:
        return None
    return size_bits if size_bits > 0 else None


def _get_declared_signedness(param: Dict[str, Any]) -> Optional[str]:
    if "is_signed" in param:
        return "signed" if param.get("is_signed", True) else "unsigned"

    raw_dt = param.get("data_type_obj")
    if raw_dt is None:
        return None
    signed = get_declared_type_signedness(
        raw_dt,
        fallback_name=None,
        fallback_signed=True,
    )
    return "signed" if signed else "unsigned"


def _build_parameter_metadata_by_identity(
    analysis: FunctionReturnAnalysis,
) -> Dict[ParameterIdentityKey, Dict[str, Any]]:
    grouped: Dict[ParameterIdentityKey, list[Dict[str, Any]]] = {}
    for param in analysis.parameters or []:
        index = _normalize_parameter_index(param.get("index"))
        descriptor = dict(param)
        if index is not None:
            descriptor["index"] = index
        meta = {
            "index": index,
            "declared_bits": _get_declared_bits(descriptor),
            "declared_signedness": _get_declared_signedness(descriptor),
            "storage": descriptor.get("storage_info", descriptor.get("storage")),
            "identities": set(),
        }
        identities = _parameter_identity_keys_from_descriptor(descriptor)
        if not identities:
            continue
        meta["identities"] = set(identities)
        for identity in identities:
            grouped.setdefault(identity, []).append(meta)

    result: Dict[ParameterIdentityKey, Dict[str, Any]] = {}
    for identity, metas in grouped.items():
        indexed_metas = [meta for meta in metas if meta["index"] is not None]
        if indexed_metas:
            indexes = {meta["index"] for meta in indexed_metas}
            if len(indexes) != 1:
                continue
            result[identity] = indexed_metas[0]
            continue
        if len(metas) != 1:
            continue
        result[identity] = metas[0]
    return result


def _parameter_identity_keys_from_descriptor(
    param: Dict[str, Any],
) -> Set[ParameterIdentityKey]:
    identities: Set[ParameterIdentityKey] = set()
    index = _normalize_parameter_index(param.get("index"))
    if index is not None:
        identities.add(("parameter_index", index))
    storage_key = _storage_identity_key(param.get("storage_info", param.get("storage")))
    if storage_key is not None:
        identities.add(("parameter_storage", storage_key))
    return identities


def _parameter_identity_key_from_expression(
    expr: Expression,
) -> Optional[ParameterIdentityKey]:
    index = _normalize_parameter_index(getattr(expr, "value", None))
    if index is not None:
        return ("parameter_index", index)
    storage_key = _storage_identity_key(getattr(expr, "storage_info", None))
    if storage_key is not None:
        return ("parameter_storage", storage_key)
    return None


def _normalize_parameter_index(value: Any) -> Optional[int]:
    try:
        index = int(value)
    except (TypeError, ValueError):
        return None
    return index if index >= 0 else None


def _storage_identity_key(storage: Optional[object]) -> Optional[Tuple[object, ...]]:
    storage_info = _coerce_storage_info(storage)
    if storage_info is None:
        return None
    return storage_info.storage_identity_key()


def _coerce_storage_info(storage: Optional[object]) -> Optional[StorageInfo]:
    if storage is None:
        return None
    if isinstance(storage, StorageInfo):
        return storage
    if not isinstance(storage, dict):
        return None
    try:
        kind = str(storage.get("kind", "") or storage.get("space_name", "") or "").lower()
        is_register = bool(storage.get("is_register", False)) or kind == "register"
        return StorageInfo(
            is_register=is_register,
            space_name=str(storage.get("space_name") or ("register" if is_register else "")),
            space_id=storage.get("space_id"),
            offset=int(storage.get("offset", 0) or 0),
            size=int(storage.get("size", 0) or 0),
            size_bits=int(storage.get("size_bits", 0) or 0),
            register_name=storage.get("register_name"),
            register_offset=storage.get("register_offset"),
            register_size=storage.get("register_size"),
            register_size_bits=storage.get("register_size_bits"),
            base_register_name=storage.get("base_register_name"),
            base_register_offset=int(storage.get("base_register_offset", 0) or 0),
            base_register_size=int(storage.get("base_register_size", 0) or 0),
            base_register_size_bits=int(storage.get("base_register_size_bits", 0) or 0),
            bit_offset_in_base=int(storage.get("bit_offset_in_base", 0) or 0),
            is_stack_pointer=bool(storage.get("is_stack_pointer", False)),
            is_frame_pointer=bool(storage.get("is_frame_pointer", False)),
        )
    except Exception:
        return None

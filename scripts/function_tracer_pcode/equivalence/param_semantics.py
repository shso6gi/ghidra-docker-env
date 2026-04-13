# -*- coding: utf-8 -*-
"""Shared parameter semantic-width inference helpers."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple

from ..model import Expression, ExpressionType, FunctionReturnAnalysis
from .typing.helpers import get_type_name_from_param, is_unsigned_type


SIGNED_COMPARE_OPS = {"INT_SLESS", "INT_SLESSEQUAL"}
UNSIGNED_COMPARE_OPS = {"INT_LESS", "INT_LESSEQUAL"}
TRANSPARENT_UNARY_OPS = {"INT_SEXT", "INT_ZEXT", "CAST", "COPY"}
SIGNEDNESS_PROPAGATING_BINARY_OPS = {"INT_AND", "INT_OR", "INT_XOR"}


@dataclass(frozen=True)
class ParameterSemanticHint:
    """Semantic-width hint inferred from explicit narrowing patterns."""

    narrow_bits: int
    signedness: str
    signedness_source: str = "explicit"


def infer_parameter_semantics(
    analysis: FunctionReturnAnalysis,
) -> Dict[int, ParameterSemanticHint]:
    """Infer per-parameter semantic-width hints from return/condition expressions."""
    params_by_name: Dict[str, Dict[str, Any]] = {}
    for fallback_index, param in enumerate(analysis.parameters or []):
        name = param.get("name", f"param_{fallback_index}")
        params_by_name[name] = {
            "index": param.get("index", fallback_index),
            "declared_bits": _get_declared_bits(param),
            "declared_signedness": _get_declared_signedness(param),
        }

    evidence: Dict[str, Dict[str, Any]] = {}
    for ret_info in analysis.returns or []:
        if ret_info.value is not None:
            _collect_from_expression(ret_info.value, evidence)
        for cond in ret_info.conditions or []:
            expr = getattr(cond, "expression", None)
            if expr is not None:
                _collect_from_expression(expr, evidence)

    hints: Dict[int, ParameterSemanticHint] = {}
    for param_name, param_evidence in evidence.items():
        meta = params_by_name.get(param_name)
        if meta is None:
            continue

        narrow_bits = _resolve_narrow_bits(param_evidence, meta["declared_bits"])
        if narrow_bits is None or narrow_bits >= meta["declared_bits"]:
            continue

        signedness, signedness_source = _resolve_signedness(
            param_evidence,
            meta["declared_signedness"],
        )
        if signedness is None:
            continue
        assert signedness_source is not None

        hints[meta["index"]] = ParameterSemanticHint(
            narrow_bits=narrow_bits,
            signedness=signedness,
            signedness_source=signedness_source,
        )

    return hints


def hints_by_name(
    analysis: FunctionReturnAnalysis,
) -> Dict[str, Tuple[str, int]]:
    """Return semantic hints keyed by parameter name for existing consumers."""
    by_index = infer_parameter_semantics(analysis)
    result: Dict[str, Tuple[str, int]] = {}
    for fallback_index, param in enumerate(analysis.parameters or []):
        index = param.get("index", fallback_index)
        hint = by_index.get(index)
        if hint is None:
            continue
        name = param.get("name", f"param_{fallback_index}")
        result[name] = (hint.signedness, hint.narrow_bits)
    return result


def hint_objects_by_name(
    analysis: FunctionReturnAnalysis,
) -> Dict[str, ParameterSemanticHint]:
    """Return semantic hint objects keyed by parameter name."""
    by_index = infer_parameter_semantics(analysis)
    result: Dict[str, ParameterSemanticHint] = {}
    for fallback_index, param in enumerate(analysis.parameters or []):
        index = param.get("index", fallback_index)
        hint = by_index.get(index)
        if hint is None:
            continue
        name = param.get("name", f"param_{fallback_index}")
        result[name] = hint
    return result


def _collect_from_expression(
    expr: Expression,
    evidence: Dict[str, Dict[str, Any]],
) -> None:
    if expr is None:
        return

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        operand = expr.operands[0]
        ref = _extract_param_reference(operand)
        if ref is not None:
            param_name, narrow_bits = ref
            if narrow_bits is not None:
                _record_width_evidence(evidence, param_name, narrow_bits)
                if expr.operator == "INT_SEXT":
                    _record_signedness_evidence(evidence, param_name, signed_score=3)

    elif expr.expr_type == ExpressionType.BINARY_OP:
        if expr.operator == "SUBPIECE":
            ref = _extract_subpiece_reference(expr)
            if ref is not None:
                param_name, narrow_bits = ref
                _record_width_evidence(evidence, param_name, narrow_bits)

        elif expr.operator == "INT_AND":
            ref = _extract_masked_param_reference(expr)
            if ref is not None:
                param_name, narrow_bits = ref
                _record_width_evidence(evidence, param_name, narrow_bits)

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


def _record_compare_signedness(
    expr: Expression,
    evidence: Dict[str, Dict[str, Any]],
) -> None:
    if len(expr.operands) != 2:
        return

    score_key = "signed_score" if expr.operator in SIGNED_COMPARE_OPS else "unsigned_score"
    left_refs = _collect_param_references(expr.operands[0])
    right_refs = _collect_param_references(expr.operands[1])

    if left_refs and _supports_signedness_inference(expr.operands[1]):
        _record_compare_refs(left_refs, evidence, score_key)

    if right_refs and _supports_signedness_inference(expr.operands[0]):
        _record_compare_refs(right_refs, evidence, score_key)


def _record_compare_refs(
    refs: Dict[str, Optional[int]],
    evidence: Dict[str, Dict[str, Any]],
    score_key: str,
) -> None:
    for param_name, narrow_bits in refs.items():
        if narrow_bits is not None:
            _record_width_evidence(evidence, param_name, narrow_bits)
        _record_signedness_evidence(
            evidence,
            param_name,
            signed_score=2 if score_key == "signed_score" else 0,
            unsigned_score=2 if score_key == "unsigned_score" else 0,
        )


def _supports_signedness_inference(expr: Expression) -> bool:
    if expr.expr_type == ExpressionType.CONSTANT:
        return True
    refs = _collect_param_references(expr)
    return refs is not None and bool(refs)


def _collect_param_references(
    expr: Expression,
) -> Optional[Dict[str, Optional[int]]]:
    """Collect parameter references from signedness-safe expression shapes.

    The collector is intentionally conservative: it only walks through operators
    whose comparison signedness can be meaningfully propagated to their leaf
    parameters without assuming arithmetic identities.
    """
    if expr.expr_type == ExpressionType.PARAMETER and expr.name:
        return {expr.name: None}

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        if expr.operator in TRANSPARENT_UNARY_OPS:
            return _collect_param_references(expr.operands[0])
        return None

    if expr.expr_type != ExpressionType.BINARY_OP:
        return None

    if expr.operator == "SUBPIECE":
        ref = _extract_subpiece_reference(expr)
        if ref is None:
            return None
        param_name, narrow_bits = ref
        return {param_name: narrow_bits}

    if expr.operator == "INT_AND":
        ref = _extract_masked_param_reference(expr)
        if ref is not None:
            param_name, narrow_bits = ref
            return {param_name: narrow_bits}

    if expr.operator not in SIGNEDNESS_PROPAGATING_BINARY_OPS:
        return None

    merged: Dict[str, Optional[int]] = {}
    for operand in expr.operands:
        if operand.expr_type == ExpressionType.CONSTANT:
            continue
        operand_refs = _collect_param_references(operand)
        if operand_refs is None:
            return None
        _merge_param_reference_maps(merged, operand_refs)

    return merged


def _merge_param_reference_maps(
    merged: Dict[str, Optional[int]],
    refs: Dict[str, Optional[int]],
) -> None:
    for param_name, narrow_bits in refs.items():
        current = merged.get(param_name)
        if current is None:
            merged[param_name] = narrow_bits
            continue
        if narrow_bits is None:
            continue
        merged[param_name] = min(current, narrow_bits) if current is not None else narrow_bits


def _extract_param_reference(
    expr: Expression,
) -> Optional[Tuple[str, Optional[int]]]:
    if expr.expr_type == ExpressionType.PARAMETER and expr.name:
        return expr.name, None

    if expr.expr_type == ExpressionType.UNARY_OP and expr.operands:
        if expr.operator in TRANSPARENT_UNARY_OPS:
            return _extract_param_reference(expr.operands[0])

    if expr.expr_type == ExpressionType.BINARY_OP:
        if expr.operator == "SUBPIECE":
            return _extract_subpiece_reference(expr)
        if expr.operator == "INT_AND":
            return _extract_masked_param_reference(expr)

    return None


def _extract_subpiece_reference(
    expr: Expression,
) -> Optional[Tuple[str, int]]:
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

    param_name, _ = source_ref
    return param_name, expr.get_bit_width()


def _extract_masked_param_reference(
    expr: Expression,
) -> Optional[Tuple[str, int]]:
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

    param_name, _ = ref
    return param_name, mask_bits


def _mask_to_narrow_bits(value: Any) -> Optional[int]:
    if not isinstance(value, int) or value <= 0:
        return None
    for bits in (8, 16, 32):
        if value == (1 << bits) - 1:
            return bits
    return None


def _record_width_evidence(
    evidence: Dict[str, Dict[str, Any]],
    param_name: str,
    narrow_bits: int,
) -> None:
    entry = evidence.setdefault(
        param_name,
        {"narrow_bits": set(), "signed_score": 0, "unsigned_score": 0},
    )
    if int(narrow_bits) > 0:
        entry["narrow_bits"].add(int(narrow_bits))


def _record_signedness_evidence(
    evidence: Dict[str, Dict[str, Any]],
    param_name: str,
    *,
    signed_score: int = 0,
    unsigned_score: int = 0,
) -> None:
    entry = evidence.setdefault(
        param_name,
        {"narrow_bits": set(), "signed_score": 0, "unsigned_score": 0},
    )
    entry["signed_score"] += signed_score
    entry["unsigned_score"] += unsigned_score


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


def _get_declared_bits(param: Dict[str, Any]) -> int:
    raw_dt = param.get("data_type_obj")
    if raw_dt is not None and hasattr(raw_dt, "getLength"):
        try:
            return int(raw_dt.getLength()) * 8
        except Exception:
            pass
    return int(param.get("size", 4)) * 8


def _get_declared_signedness(param: Dict[str, Any]) -> Optional[str]:
    if "is_signed" in param:
        return "signed" if param.get("is_signed", True) else "unsigned"

    type_name = get_type_name_from_param(param)
    if not type_name:
        return None
    return "unsigned" if is_unsigned_type(type_name) else "signed"

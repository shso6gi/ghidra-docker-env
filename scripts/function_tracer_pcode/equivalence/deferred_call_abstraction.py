# -*- coding: utf-8 -*-
"""Relational abstraction for unresolved deferred call returns."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from ..model import Condition, DeferredCallInfo, Expression, ExpressionType, FunctionReturnAnalysis, ReturnInfo
from ..model.structural import expression_key_or_identity
from ..model.runtime_refs import CanonicalLocation, PostStateReadRef, PostStateValueRef


@dataclass(frozen=True)
class AbstractedCallMatch:
    deferred_key1: Tuple[object, ...]
    deferred_key2: Tuple[object, ...]
    summary_name: str
    summary_index: int
    summary_kind: str
    summary_size: int
    match_evidence: Dict[str, Any]


@dataclass
class DeferredCallAbstractionResult:
    analysis1: FunctionReturnAnalysis
    analysis2: FunctionReturnAnalysis
    matches: List[AbstractedCallMatch]

    @property
    def applied(self) -> bool:
        return bool(self.matches)


RecursiveAbstractionResult = DeferredCallAbstractionResult


_PURE_RETURN_CALLS: Mapping[str, Dict[str, Any]] = {
    "sqrt": {
        "return_width_bits": 64,
        "return_type_policy": "fp64",
        "requires_fp_non_nan": True,
        "observes_errno": False,
        "observes_fenv": False,
    },
    "sqrtf": {
        "return_width_bits": 32,
        "return_type_policy": "fp32",
        "requires_fp_non_nan": True,
        "observes_errno": False,
        "observes_fenv": False,
    },
}

_SIDE_EFFECTING_CALLS = {
    "printf",
    "fprintf",
    "sprintf",
    "snprintf",
    "puts",
    "putchar",
    "fputs",
}


def abstract_deferred_calls(
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    assume_fp_non_nan: bool = False,
    observes_errno: bool = False,
    observes_fenv: bool = False,
    debug: bool = False,
) -> DeferredCallAbstractionResult:
    """Replace proven matching deferred call returns with shared summary parameters."""

    analysis1.normalize_deferred_calls()
    analysis2.normalize_deferred_calls()
    deferred1 = list((analysis1.deferred_calls or {}).values())
    deferred2 = list((analysis2.deferred_calls or {}).values())
    if not deferred1 or not deferred2:
        if debug:
            print(
                "[deferred_call_abstraction] no compatible deferred-call matches; "
                f"left_deferred_calls={len(deferred1)} "
                f"right_deferred_calls={len(deferred2)}"
            )
        return DeferredCallAbstractionResult(analysis1=analysis1, analysis2=analysis2, matches=[])

    usage1 = _collect_deferred_call_usage(analysis1)
    usage2 = _collect_deferred_call_usage(analysis2)
    domain_policy = {
        "fp_non_nan": bool(assume_fp_non_nan),
        "observes_errno": bool(observes_errno),
        "observes_fenv": bool(observes_fenv),
    }
    grouped1 = _group_deferred_calls(analysis1, deferred1, usage1, domain_policy)
    grouped2 = _group_deferred_calls(analysis2, deferred2, usage2, domain_policy)

    matches: List[AbstractedCallMatch] = []
    next_rec_summary_index = 10_000
    next_call_summary_index = 20_000

    for key in sorted(set(grouped1) & set(grouped2), key=repr):
        left_infos = grouped1[key]
        right_infos = grouped2[key]
        if len(left_infos) != len(right_infos):
            continue
        summary_kind = key[0]
        for pair_index, (left_info, right_info) in enumerate(zip(left_infos, right_infos)):
            if summary_kind == "self_recursive":
                summary_index = next_rec_summary_index
                summary_name = f"summary_rec_{summary_index}"
                next_rec_summary_index += 1
            else:
                summary_index = next_call_summary_index
                summary_name = f"summary_call_{summary_index}"
                next_call_summary_index += 1
            left_usage = usage1.get(left_info.deferred_call_ref.stable_key(), {})
            right_usage = usage2.get(right_info.deferred_call_ref.stable_key(), {})
            summary_size = _summary_size_for_match(left_info, right_info, left_usage, right_usage, summary_kind)
            if summary_size is None:
                continue
            matches.append(
                AbstractedCallMatch(
                    deferred_key1=left_info.deferred_call_ref.stable_key(),
                    deferred_key2=right_info.deferred_call_ref.stable_key(),
                    summary_name=summary_name,
                    summary_index=summary_index,
                    summary_kind=summary_kind,
                    summary_size=summary_size,
                    match_evidence={
                        "summary_kind": summary_kind,
                        "left": _match_evidence(left_info, left_usage, len(left_infos), domain_policy),
                        "right": _match_evidence(right_info, right_usage, len(right_infos), domain_policy),
                    },
                )
            )

    if not matches:
        if debug:
            _debug_no_deferred_matches(grouped1, grouped2)
        return DeferredCallAbstractionResult(analysis1=analysis1, analysis2=analysis2, matches=[])

    mapping1 = {match.deferred_key1: match for match in matches}
    mapping2 = {match.deferred_key2: match for match in matches}

    transformed1 = _rewrite_analysis_with_abstract_calls(analysis1, mapping1)
    transformed2 = _rewrite_analysis_with_abstract_calls(analysis2, mapping2)
    return DeferredCallAbstractionResult(
        analysis1=transformed1,
        analysis2=transformed2,
        matches=matches,
    )


def abstract_recursive_calls(
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    assume_fp_non_nan: bool = False,
    observes_errno: bool = False,
    observes_fenv: bool = False,
    debug: bool = False,
) -> DeferredCallAbstractionResult:
    return abstract_deferred_calls(
        analysis1,
        analysis2,
        assume_fp_non_nan=assume_fp_non_nan,
        observes_errno=observes_errno,
        observes_fenv=observes_fenv,
        debug=debug,
    )


def _group_deferred_calls(
    analysis: FunctionReturnAnalysis,
    deferred_calls: Sequence[DeferredCallInfo],
    usage: Mapping[Tuple[object, ...], Dict[str, Any]],
    domain_policy: Mapping[str, bool],
) -> Dict[Tuple[Any, ...], List[DeferredCallInfo]]:
    grouped: Dict[Tuple[Any, ...], List[DeferredCallInfo]] = {}
    for info in deferred_calls:
        key = _deferred_call_match_key(analysis, info, usage.get(info.deferred_call_ref.stable_key(), {}), domain_policy)
        if key is None:
            continue
        grouped.setdefault(key, []).append(info)
    return grouped


def _deferred_call_match_key(
    analysis: FunctionReturnAnalysis,
    info: DeferredCallInfo,
    usage: Mapping[str, Any],
    domain_policy: Mapping[str, bool],
) -> Optional[Tuple[Any, ...]]:
    if info is None:
        return None

    recursive_key = _recursive_target_key(analysis, info)
    if recursive_key == ("self_recursive",):
        arg_key = tuple(_argument_key(arg) for arg in (info.arguments or []))
        return ("self_recursive", recursive_key, arg_key)

    return _pure_call_match_key(analysis, info, usage, domain_policy)


def _pure_call_match_key(
    analysis: FunctionReturnAnalysis,
    info: DeferredCallInfo,
    usage: Mapping[str, Any],
    domain_policy: Mapping[str, bool],
) -> Optional[Tuple[Any, ...]]:
    target_name = _normalized_call_name(getattr(info, "target_name", ""))
    if target_name in _SIDE_EFFECTING_CALLS:
        return None
    if getattr(info, "effect_class", None) != "pure_return":
        return None
    policy = _PURE_RETURN_CALLS.get(target_name)
    if policy is None:
        return None
    target_identity_key = _pure_target_identity_key(info)
    if target_identity_key is None:
        return None
    if policy.get("requires_fp_non_nan") and not domain_policy.get("fp_non_nan", False):
        return None
    if domain_policy.get("observes_errno", False) or domain_policy.get("observes_fenv", False):
        return None
    if len(getattr(info, "arguments", []) or []) != 1:
        return None
    if _usage_has_condition_only_reference(usage):
        return None

    usage_width_bits = _usage_return_width_bits(usage)
    expected_width_bits = int(policy["return_width_bits"])
    if usage_width_bits is not None and usage_width_bits != expected_width_bits:
        return None

    guard_key = usage.get("return_case_guard_key")
    if guard_key is None:
        return None

    arg_key = tuple(_pure_analysis_expression_key(analysis, arg) for arg in (info.arguments or []))
    return (
        "pure_call",
        target_name,
        target_identity_key,
        arg_key,
        guard_key,
        expected_width_bits,
        policy["return_type_policy"],
        tuple(sorted(domain_policy.items())),
    )


def _match_evidence(
    info: DeferredCallInfo,
    usage: Mapping[str, Any],
    multiplicity: int,
    domain_policy: Mapping[str, bool],
) -> Dict[str, Any]:
    evidence = dict(getattr(info, "match_evidence", {}) or {})
    width_bits = _usage_return_width_bits(usage)
    if width_bits is None:
        target_name = _normalized_call_name(getattr(info, "target_name", ""))
        policy = _PURE_RETURN_CALLS.get(target_name)
        if policy is not None:
            width_bits = int(policy["return_width_bits"])
    evidence.update(
        {
            "callee_identity": info.target_ref.stable_key(),
            "callee_name": info.target_ref.display_name(),
            "callee_identity_policy": _call_target_identity_policy(info.target_ref),
            "argument_expression_key": tuple(_argument_key(arg) for arg in (info.arguments or [])),
            "active_guard_key": usage.get("active_guard_key"),
            "return_case_guard_key": usage.get("return_case_guard_key"),
            "abi_return_width_bits": width_bits,
            "abi_return_type_policy": _usage_return_type_policy(info, usage),
            "call_site_multiplicity": int(multiplicity),
            "effect_class": getattr(info, "effect_class", "unknown_effect"),
            "domain_policy": dict(domain_policy),
        }
    )
    return evidence


def _usage_return_type_policy(info: DeferredCallInfo, usage: Mapping[str, Any]) -> Optional[str]:
    width = _usage_return_width_bits(usage)
    name = _normalized_call_name(getattr(info, "target_name", ""))
    policy = _PURE_RETURN_CALLS.get(name)
    if width is None and policy is not None:
        return str(policy["return_type_policy"])
    if policy is not None and width == int(policy["return_width_bits"]):
        return str(policy["return_type_policy"])
    return None if width is None else f"bv{width}"


def _usage_return_width_bits(usage: Mapping[str, Any]) -> Optional[int]:
    sizes = usage.get("value_sizes")
    if not sizes:
        return None
    normalized = sorted({int(size) for size in sizes if size is not None and int(size) > 0})
    if len(normalized) != 1:
        return None
    return normalized[0] * 8


def _summary_size_for_match(
    left_info: DeferredCallInfo,
    right_info: DeferredCallInfo,
    left_usage: Mapping[str, Any],
    right_usage: Mapping[str, Any],
    summary_kind: str,
) -> Optional[int]:
    if summary_kind == "pure_call":
        left_policy_size = _pure_return_policy_size(left_info)
        right_policy_size = _pure_return_policy_size(right_info)
        if left_policy_size is None or left_policy_size != right_policy_size:
            return None
        return left_policy_size

    left_sizes = sorted({int(size) for size in left_usage.get("value_sizes", ()) if size})
    right_sizes = sorted({int(size) for size in right_usage.get("value_sizes", ()) if size})
    if len(left_sizes) == 1 and left_sizes == right_sizes:
        return left_sizes[0]
    return 4


def _pure_return_policy_size(info: DeferredCallInfo) -> Optional[int]:
    target_name = _normalized_call_name(getattr(info, "target_name", ""))
    policy = _PURE_RETURN_CALLS.get(target_name)
    if policy is None:
        return None
    width_bits = int(policy.get("return_width_bits") or 0)
    if width_bits <= 0 or width_bits % 8 != 0:
        return None
    return width_bits // 8


def _usage_has_condition_only_reference(usage: Mapping[str, Any]) -> bool:
    value_count = int(usage.get("value_reference_count", 0) or 0)
    condition_count = int(usage.get("condition_reference_count", 0) or 0)
    return value_count == 0 and condition_count > 0


def _collect_deferred_call_usage(
    analysis: FunctionReturnAnalysis,
) -> Dict[Tuple[object, ...], Dict[str, Any]]:
    usage: Dict[Tuple[object, ...], Dict[str, Any]] = {}
    for ret in analysis.returns or []:
        guard_key = _conditions_key(ret.conditions, analysis)
        for key, sizes in _deferred_unknown_sizes(ret.value).items():
            entry = usage.setdefault(key, _empty_usage())
            entry["value_reference_count"] += len(sizes)
            entry["value_sizes"].update(sizes)
            entry["return_case_guard_key"] = _merge_usage_key(entry.get("return_case_guard_key"), guard_key)
            entry["active_guard_key"] = _merge_usage_key(entry.get("active_guard_key"), guard_key)
        for cond in ret.conditions or []:
            for key, sizes in _deferred_unknown_sizes(cond.expression).items():
                entry = usage.setdefault(key, _empty_usage())
                entry["condition_reference_count"] += len(sizes)
                entry["condition_sizes"].update(sizes)
                entry["return_case_guard_key"] = _merge_usage_key(entry.get("return_case_guard_key"), guard_key)
                entry["active_guard_key"] = _merge_usage_key(entry.get("active_guard_key"), guard_key)
    return usage


def _empty_usage() -> Dict[str, Any]:
    return {
        "value_reference_count": 0,
        "condition_reference_count": 0,
        "value_sizes": set(),
        "condition_sizes": set(),
        "return_case_guard_key": None,
        "active_guard_key": None,
    }


def _merge_usage_key(existing: Optional[Tuple[Any, ...]], new_key: Tuple[Any, ...]) -> Optional[Tuple[Any, ...]]:
    if existing is None:
        return new_key
    if existing == new_key:
        return existing
    return ("multiple_guards",)


def _deferred_unknown_sizes(expr: Optional[Expression]) -> Dict[Tuple[object, ...], List[int]]:
    found: Dict[Tuple[object, ...], List[int]] = {}
    if expr is None:
        return found
    if expr.expr_type == ExpressionType.UNKNOWN:
        runtime_ref = getattr(expr, "runtime_ref", None)
        deferred_call_ref = getattr(runtime_ref, "deferred_call_ref", None)
        if hasattr(deferred_call_ref, "stable_key"):
            found.setdefault(deferred_call_ref.stable_key(), []).append(int(expr.size or 0))
    if expr.expr_type == ExpressionType.PHI and expr.value:
        for cond, value in expr.value:
            if cond is not None:
                _merge_found(found, _deferred_unknown_sizes(cond.expression))
            _merge_found(found, _deferred_unknown_sizes(value))
        return found
    for operand in getattr(expr, "operands", ()) or ():
        _merge_found(found, _deferred_unknown_sizes(operand))
    return found


def _merge_found(
    target: Dict[Tuple[object, ...], List[int]],
    source: Mapping[Tuple[object, ...], List[int]],
) -> None:
    for key, sizes in source.items():
        target.setdefault(key, []).extend(sizes)


def _conditions_key(
    conditions: Sequence[Condition],
    analysis: FunctionReturnAnalysis,
) -> Tuple[Any, ...]:
    return tuple(
        (
            "condition",
            _analysis_expression_key(analysis, cond.expression),
            bool(cond.negated),
        )
        for cond in (conditions or [])
    )


def _argument_key(expr: Optional[Expression]) -> Tuple[object, ...]:
    if expr is None:
        return ("none",)
    return _object_centric_expression_key(expr, for_call_target=False)


def _analysis_expression_key(
    analysis: FunctionReturnAnalysis,
    expr: Optional[Expression],
) -> Tuple[object, ...]:
    role_map = _parameter_role_map(analysis)
    return _expression_key_with_parameter_roles(expr, role_map)


def _pure_analysis_expression_key(
    analysis: FunctionReturnAnalysis,
    expr: Optional[Expression],
) -> Tuple[object, ...]:
    role_map = _parameter_size_role_map(analysis)
    return _expression_key_with_parameter_roles(expr, role_map)


def _expression_key_with_parameter_roles(
    expr: Optional[Expression],
    role_map: Mapping[int, Tuple[Any, ...]],
) -> Tuple[object, ...]:
    if expr is None:
        return ("none",)
    if expr.expr_type == ExpressionType.PARAMETER:
        index = expr.value if isinstance(expr.value, int) else -1
        role = role_map.get(int(index))
        if role is not None:
            return role
        return ("parameter", index, int(expr.size or 0))
    if expr.expr_type == ExpressionType.UNARY_OP:
        operand = expr.operands[0] if expr.operands else None
        return (
            "unary",
            expr.operator or "",
            int(expr.size or 0),
            _expression_key_with_parameter_roles(operand, role_map),
        )
    if expr.expr_type == ExpressionType.BINARY_OP:
        left = expr.operands[0] if expr.operands else None
        right = expr.operands[1] if len(expr.operands) > 1 else None
        left_key = _expression_key_with_parameter_roles(left, role_map)
        right_key = _expression_key_with_parameter_roles(right, role_map)
        if (expr.operator or "") in {
            "INT_ADD",
            "INT_MULT",
            "INT_AND",
            "INT_OR",
            "INT_XOR",
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "BOOL_AND",
            "BOOL_OR",
            "BOOL_XOR",
        } and right_key < left_key:
            left_key, right_key = right_key, left_key
        return ("binary", expr.operator or "", int(expr.size or 0), left_key, right_key)
    if expr.expr_type == ExpressionType.PHI and expr.value:
        return (
            "phi",
            int(expr.size or 0),
            tuple(
                (
                    (
                        "condition",
                        _expression_key_with_parameter_roles(cond.expression, role_map),
                        bool(cond.negated),
                    )
                    if cond is not None
                    else ("none",),
                    _expression_key_with_parameter_roles(value, role_map),
                )
                for cond, value in expr.value
            ),
        )
    if getattr(expr, "operands", None):
        return (
            "expr_with_roles",
            expr.expr_type.value if hasattr(expr.expr_type, "value") else str(expr.expr_type),
            expr.operator or "",
            int(expr.size or 0),
            tuple(_expression_key_with_parameter_roles(operand, role_map) for operand in expr.operands),
        )
    return _object_centric_expression_key(expr, for_call_target=False)


def _parameter_role_map(
    analysis: FunctionReturnAnalysis,
) -> Dict[int, Tuple[Any, ...]]:
    buckets: Dict[Tuple[str, int], List[Tuple[int, Dict[str, Any]]]] = {}
    for param in analysis.parameters or []:
        try:
            index = int(param.get("index"))
        except Exception:
            continue
        size = int(param.get("size") or 0)
        type_class = _parameter_type_class(param)
        buckets.setdefault((type_class, size), []).append((index, param))

    roles: Dict[int, Tuple[Any, ...]] = {}
    for (type_class, size), entries in buckets.items():
        for ordinal, (index, _param) in enumerate(sorted(entries, key=lambda item: item[0])):
            roles[index] = ("parameter_role", type_class, size, ordinal)
    return roles


def _parameter_size_role_map(
    analysis: FunctionReturnAnalysis,
) -> Dict[int, Tuple[Any, ...]]:
    buckets: Dict[int, List[Tuple[int, Dict[str, Any]]]] = {}
    for param in analysis.parameters or []:
        try:
            index = int(param.get("index"))
        except Exception:
            continue
        size = int(param.get("size") or 0)
        buckets.setdefault(size, []).append((index, param))

    roles: Dict[int, Tuple[Any, ...]] = {}
    for size, entries in buckets.items():
        for ordinal, (index, _param) in enumerate(sorted(entries, key=lambda item: item[0])):
            roles[index] = ("parameter_size_role", size, ordinal)
    return roles


def _pure_target_identity_key(info: DeferredCallInfo) -> Optional[Tuple[Any, ...]]:
    target_ref = getattr(info, "target_ref", None)
    if target_ref is None or getattr(target_ref, "is_unknown", lambda: True)():
        return None
    if not getattr(target_ref, "is_function", lambda: False)():
        return None
    target_name = _normalized_call_name(getattr(info, "target_name", ""))
    if not target_name:
        return None
    if getattr(target_ref, "is_external", None) is True:
        library_name = str(getattr(target_ref, "library_name", "") or "").lower()
        if not library_name:
            return None
        return ("external_library_function", target_name, library_name)
    if getattr(target_ref, "is_thunk", None) is True and getattr(target_ref, "thunked_is_external", None) is True:
        library_name = str(getattr(target_ref, "thunked_library_name", "") or "").lower()
        if not library_name:
            return None
        return ("external_library_thunk", target_name, library_name)
    return None


def _call_target_identity_policy(target_ref) -> Dict[str, Any]:
    if target_ref is None:
        return {"status": "missing"}
    if getattr(target_ref, "is_unknown", lambda: False)():
        return {"status": "unresolved_target"}
    if getattr(target_ref, "is_external", None) is True:
        if not getattr(target_ref, "library_name", None):
            return {"status": "unscoped_external_library_function_rejected"}
        return {
            "status": "external_library_function",
            "library_name": getattr(target_ref, "library_name", None),
        }
    if getattr(target_ref, "is_thunk", None) is True and getattr(target_ref, "thunked_is_external", None) is True:
        if not getattr(target_ref, "thunked_library_name", None):
            return {"status": "unscoped_external_library_thunk_rejected"}
        return {
            "status": "external_library_thunk",
            "library_name": getattr(target_ref, "thunked_library_name", None),
        }
    if getattr(target_ref, "entry_offset", None) is not None or getattr(target_ref, "address_offset", None) is not None:
        return {"status": "resolved_local_or_plt_address_rejected"}
    if getattr(target_ref, "program_id", None) is not None:
        return {"status": "program_scoped_name_rejected"}
    return {"status": "name_only_target_rejected"}


def _parameter_type_class(param: Mapping[str, Any]) -> str:
    data_type = str(param.get("data_type") or "").lower()
    if "double" in data_type:
        return "fp64"
    if "float" in data_type:
        return "fp32"
    size = int(param.get("size") or 0)
    if size == 8 and ("f" in str(param.get("storage") or "").lower()):
        return "fp64"
    return "int"


def _recursive_target_key(
    analysis: FunctionReturnAnalysis,
    info: DeferredCallInfo,
) -> Optional[Tuple[object, ...]]:
    target_ref = getattr(info, "target_ref", None)
    function_ref = getattr(analysis, "function_ref", None)
    if function_ref is not None and target_ref is not None:
        target_key = target_ref.analysis_key()
        if target_key is not None and target_key == function_ref.analysis_key():
            return ("self_recursive",)
    return None


def _call_target_runtime_display_name(runtime_ref) -> Optional[str]:
    if runtime_ref is None:
        return None

    can_execute = getattr(runtime_ref, "can_execute", None)
    if can_execute is False:
        return None

    for attr in ("symbol_name", "display_hint"):
        value = getattr(runtime_ref, attr, None)
        if isinstance(value, str) and value:
            return value

    display_name = getattr(runtime_ref, "display_name", None)
    if callable(display_name):
        try:
            value = display_name()
        except Exception:
            value = None
        if isinstance(value, str) and value:
            return value
    return None


def _object_centric_expression_key(
    expr: Optional[Expression],
    *,
    for_call_target: bool,
) -> Tuple[object, ...]:
    if expr is None:
        return ("none",)

    if expr.expr_type == ExpressionType.PARAMETER:
        index = expr.value if isinstance(expr.value, int) else -1
        return ("parameter", index, int(expr.size or 0))

    if expr.expr_type == ExpressionType.CONSTANT:
        if for_call_target:
            runtime_ref = getattr(expr, "runtime_ref", None)
            display_name = _call_target_runtime_display_name(runtime_ref)
            if display_name:
                return ("call_target_object", display_name, int(expr.size or 0))
        try:
            value = int(expr.value)
        except Exception:
            value = expr.value
        return ("const", value, int(expr.size or 0))

    if expr.expr_type == ExpressionType.UNKNOWN:
        runtime_ref = getattr(expr, "runtime_ref", None)
        runtime_key = (
            runtime_ref.stable_key()
            if hasattr(runtime_ref, "stable_key")
            else None
        )
        return ("unknown", runtime_key, int(expr.size or 0))

    runtime_ref = getattr(expr, "runtime_ref", None)
    if isinstance(runtime_ref, (CanonicalLocation, PostStateReadRef, PostStateValueRef)):
        stable_key = (
            runtime_ref.stable_key()
            if hasattr(runtime_ref, "stable_key")
            else runtime_ref
        )
        return ("runtime_object", stable_key, int(expr.size or 0))

    if expr.expr_type == ExpressionType.VARIABLE:
        storage_info = getattr(expr, "storage_info", None)
        storage_key = (
            storage_info.storage_identity_key()
            if hasattr(storage_info, "storage_identity_key")
            else None
        )
        return (
            "variable",
            storage_key if storage_key is not None else (expr.name or ""),
            int(expr.size or 0),
        )

    if expr.expr_type == ExpressionType.INTRINSIC:
        operands = getattr(expr, "operands", None) or []
        operand_keys = tuple(
            _object_centric_expression_key(operand, for_call_target=for_call_target)
            for operand in operands
        )
        return (
            "intrinsic",
            getattr(expr, "name", None) or "",
            int(expr.size or 0),
            operand_keys,
        )

    if expr.expr_type == ExpressionType.UNARY_OP:
        operand = expr.operands[0] if expr.operands else None
        return (
            "unary",
            expr.operator or "",
            int(expr.size or 0),
            _object_centric_expression_key(operand, for_call_target=for_call_target),
        )

    if expr.expr_type == ExpressionType.BINARY_OP:
        left = expr.operands[0] if expr.operands else None
        right = expr.operands[1] if len(expr.operands) > 1 else None
        left_key = _object_centric_expression_key(left, for_call_target=for_call_target)
        right_key = _object_centric_expression_key(right, for_call_target=for_call_target)
        if (expr.operator or "") in {
            "INT_ADD",
            "INT_MULT",
            "INT_AND",
            "INT_OR",
            "INT_XOR",
            "INT_EQUAL",
            "INT_NOTEQUAL",
            "BOOL_AND",
            "BOOL_OR",
            "BOOL_XOR",
        } and right_key < left_key:
            left_key, right_key = right_key, left_key
        return (
            "binary",
            expr.operator or "",
            int(expr.size or 0),
            left_key,
            right_key,
        )

    if expr.expr_type == ExpressionType.MEMORY:
        runtime_ref = getattr(expr, "runtime_ref", None)
        if isinstance(runtime_ref, (CanonicalLocation, PostStateReadRef, PostStateValueRef)):
            stable_key = (
                runtime_ref.stable_key()
                if hasattr(runtime_ref, "stable_key")
                else runtime_ref
            )
            return ("memory_runtime_object", stable_key, int(expr.size or 0))
        address = expr.operands[0] if expr.operands else None
        return (
            "memory",
            int(expr.size or 0),
            _object_centric_expression_key(address, for_call_target=for_call_target),
        )

    if expr.expr_type == ExpressionType.PHI and expr.value:
        branches = []
        for cond, value in expr.value:
            if cond is None:
                cond_key = ("none",)
            else:
                cond_key = (
                    "condition",
                    _object_centric_expression_key(
                        cond.expression,
                        for_call_target=for_call_target,
                    ),
                    bool(cond.negated),
                )
            branches.append(
                (
                    cond_key,
                    _object_centric_expression_key(
                        value,
                        for_call_target=for_call_target,
                    ),
                )
            )
        return ("phi", int(expr.size or 0), tuple(branches))

    return (
        "expr",
        expression_key_or_identity(
            expr,
            strip_width_adapters=True,
            collapse_full_masks=True,
            include_memory_read_order=False,
        ),
    )


def _rewrite_analysis_with_abstract_calls(
    analysis: FunctionReturnAnalysis,
    placeholder_mapping: Dict[Tuple[object, ...], AbstractedCallMatch],
) -> FunctionReturnAnalysis:
    cloned = FunctionReturnAnalysis(
        function_name=analysis.function_name,
        entry_point=analysis.entry_point,
        parameters=[dict(param) for param in (analysis.parameters or [])],
        returns=[],
        function_ref=analysis.function_ref,
        return_type=analysis.return_type,
        return_type_obj=analysis.return_type_obj,
        signedness_result=analysis.signedness_result,
        unknown_event_count=analysis.unknown_event_count,
        unknown_event_reasons=list(analysis.unknown_event_reasons),
        analysis_notes=list(analysis.analysis_notes),
        recovered_from_decompiler=analysis.recovered_from_decompiler,
        incomplete_control_flow=analysis.incomplete_control_flow,
        deferred_calls=dict(analysis.deferred_calls),
        effect_summary=analysis.effect_summary,
        comparison_surface=analysis.comparison_surface,
        analysis_scope_key=analysis.analysis_scope_key,
        program_is_big_endian=analysis.program_is_big_endian,
        completed_recovery_proof_ids=tuple(getattr(analysis, "completed_recovery_proof_ids", ()) or ()),
        completed_recovery_proof_evidence=tuple(getattr(analysis, "completed_recovery_proof_evidence", ()) or ()),
        quarantined_recurrence_proposals=tuple(
            getattr(analysis, "quarantined_recurrence_proposals", ()) or ()
        ),
        binary_id=analysis.binary_id,
    )

    existing_indices = {
        int(param.get("index", -1))
        for param in cloned.parameters
        if isinstance(param.get("index", -1), int)
    }

    for match in placeholder_mapping.values():
        if match.summary_index not in existing_indices:
            synthetic_key = (
                "synthetic_recursive_summary"
                if match.summary_kind == "self_recursive"
                else "synthetic_pure_call_summary"
            )
            cloned.parameters.append(
                {
                    "name": match.summary_name,
                    "index": match.summary_index,
                    "size": match.summary_size,
                    "data_type": "int",
                    "is_signed": True,
                    synthetic_key: True,
                    "deferred_call_match_evidence": match.match_evidence,
                }
            )
            existing_indices.add(match.summary_index)

    cloned.parameters.sort(key=lambda param: int(param.get("index", 1 << 20)))
    cloned.returns = [
        ReturnInfo(
            address=ret.address,
            value=_rewrite_expression(ret.value, placeholder_mapping),
            conditions=[
                Condition(
                    _rewrite_expression(cond.expression, placeholder_mapping),
                    cond.negated,
                )
                for cond in ret.conditions
            ],
            branch_index=ret.branch_index,
            pcode_identity=ret.pcode_identity,
            pcode_order=ret.pcode_order,
            pcode_time=ret.pcode_time,
            pcode_op_ref=getattr(ret, "pcode_op_ref", None),
            return_value_pcode_op_refs=tuple(
                getattr(ret, "return_value_pcode_op_refs", ()) or ()
            ),
        )
        for ret in (analysis.returns or [])
    ]

    if placeholder_mapping:
        note = "deferred_call_relational_abstraction"
        if note not in cloned.analysis_notes:
            cloned.analysis_notes.append(note)
        if any(match.summary_kind == "self_recursive" for match in placeholder_mapping.values()):
            legacy_note = "recursive_relational_abstraction"
            if legacy_note not in cloned.analysis_notes:
                cloned.analysis_notes.append(legacy_note)

    cloned.deferred_calls = {
        key: info
        for key, info in cloned.deferred_calls.items()
        if key not in placeholder_mapping
    }
    return cloned


def _rewrite_expression(
    expr: Optional[Expression],
    placeholder_mapping: Dict[Tuple[object, ...], AbstractedCallMatch],
) -> Optional[Expression]:
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.UNKNOWN:
        runtime_ref = getattr(expr, "runtime_ref", None)
        deferred_call_ref = getattr(runtime_ref, "deferred_call_ref", None)
        deferred_key = (
            deferred_call_ref.stable_key()
            if hasattr(deferred_call_ref, "stable_key")
            else None
        )
        if deferred_key in placeholder_mapping:
            match = placeholder_mapping[deferred_key]
            size = expr.size or match.summary_size or 4
            return Expression.parameter(
                match.summary_name,
                index=match.summary_index,
                data_type="int",
                size=size,
            )

    if expr.expr_type == ExpressionType.PHI and expr.value:
        rebuilt_branches = []
        for cond, value in expr.value:
            new_cond = (
                Condition(_rewrite_expression(cond.expression, placeholder_mapping), cond.negated)
                if cond is not None
                else None
            )
            new_value = _rewrite_expression(value, placeholder_mapping)
            rebuilt_branches.append((new_cond, new_value))
        rebuilt = Expression.phi(rebuilt_branches)
        rebuilt.size = expr.size
        return rebuilt

    if not expr.operands:
        return expr

    return Expression(
        expr.expr_type,
        value=expr.value,
        operator=expr.operator,
        operands=[_rewrite_expression(op, placeholder_mapping) for op in expr.operands],
        size=expr.size,
        name=expr.name,
        data_type=expr.data_type,
        data_type_obj=getattr(expr, "data_type_obj", None),
        storage_info=expr.storage_info,
        read_order_key=getattr(expr, "read_order_key", None),
        runtime_ref=getattr(expr, "runtime_ref", None),
        opcode=getattr(expr, "opcode", None),
    )


def _debug_no_deferred_matches(
    grouped1: Mapping[Tuple[Any, ...], List[DeferredCallInfo]],
    grouped2: Mapping[Tuple[Any, ...], List[DeferredCallInfo]],
) -> None:
    left_targets = _target_inventory(grouped1)
    right_targets = _target_inventory(grouped2)
    shared_targets = sorted(set(left_targets) & set(right_targets), key=repr)
    print(
        "[deferred_call_abstraction] no compatible deferred-call matches; "
        f"left_groups={len(grouped1)} right_groups={len(grouped2)} "
        f"shared_targets={len(shared_targets)}"
    )
    for target in shared_targets[:5]:
        left_args = sorted(left_targets.get(target, ()), key=repr)
        right_args = sorted(right_targets.get(target, ()), key=repr)
        print(
            "[deferred_call_abstraction] target-only match with argument mismatch: "
            f"target={_short_debug_key(target)} "
            f"left_arg_keys={_short_debug_key(left_args[:3])} "
            f"right_arg_keys={_short_debug_key(right_args[:3])}"
        )


def _target_inventory(
    grouped: Mapping[Tuple[Any, ...], List[DeferredCallInfo]],
) -> Dict[Tuple[object, ...], Tuple[Tuple[Any, ...], ...]]:
    inventory: Dict[Tuple[object, ...], List[Tuple[Any, ...]]] = {}
    for key in grouped:
        if key[0] == "self_recursive":
            target_key = tuple(key[1])
            arg_key = tuple(key[2])
        elif key[0] == "pure_call":
            target_key = (key[1], key[2])
            arg_key = tuple(key[3])
        else:
            continue
        inventory.setdefault(target_key, []).append(arg_key)
    return {target: tuple(args) for target, args in inventory.items()}


def _short_debug_key(value: object, *, limit: int = 600) -> str:
    text = repr(value)
    if len(text) <= limit:
        return text
    return text[: limit - 3] + "..."


def _normalized_call_name(name: Optional[str]) -> str:
    raw = str(name or "").strip()
    if not raw:
        return ""
    raw = raw.split("@", 1)[0]
    raw = raw.rsplit(".", 1)[-1] if "." in raw else raw
    while raw.startswith("_"):
        raw = raw[1:]
    return raw.lower()

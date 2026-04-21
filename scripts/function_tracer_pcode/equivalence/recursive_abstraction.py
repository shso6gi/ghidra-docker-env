# -*- coding: utf-8 -*-
"""Relational abstraction layer for unresolved recursive call summaries."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from ..model import Condition, DeferredCallInfo, Expression, ExpressionType, FunctionReturnAnalysis, ReturnInfo
from ..model.structural import expression_key_or_identity
from ..model.runtime_refs import CanonicalLocation, PostStateReadRef, PostStateValueRef, UnknownValueRef


@dataclass(frozen=True)
class AbstractedCallMatch:
    deferred_key1: Tuple[object, ...]
    deferred_key2: Tuple[object, ...]
    summary_name: str
    summary_index: int


@dataclass
class RecursiveAbstractionResult:
    analysis1: FunctionReturnAnalysis
    analysis2: FunctionReturnAnalysis
    matches: List[AbstractedCallMatch]

    @property
    def applied(self) -> bool:
        return bool(self.matches)


def abstract_recursive_calls(
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    debug: bool = False,
) -> RecursiveAbstractionResult:
    """
    未解決の再帰呼び出しプレースホルダを、共有サマリ変数へ抽象化する。

    soundness を大きく崩さないよう、Ghidra が与える object identity に
    依拠して以下を対応対象にする。
    - self-recursive call
    - call_target_expr が object-centric に一致する deferred call
    - direct target の function identity が一致する deferred call
    """

    analysis1.normalize_deferred_calls()
    analysis2.normalize_deferred_calls()
    deferred1 = list((analysis1.deferred_calls or {}).values())
    deferred2 = list((analysis2.deferred_calls or {}).values())
    if not deferred1 or not deferred2:
        return RecursiveAbstractionResult(analysis1=analysis1, analysis2=analysis2, matches=[])

    grouped1 = _group_deferred_calls(analysis1, deferred1)
    grouped2 = _group_deferred_calls(analysis2, deferred2)

    matches: List[AbstractedCallMatch] = []
    next_summary_index = 10_000

    for key in sorted(set(grouped1) & set(grouped2)):
        left_infos = grouped1[key]
        right_infos = grouped2[key]
        pair_count = min(len(left_infos), len(right_infos))
        for pair_index in range(pair_count):
            summary_name = f"summary_rec_{next_summary_index}"
            matches.append(
                AbstractedCallMatch(
                    deferred_key1=left_infos[pair_index].deferred_call_ref.stable_key(),
                    deferred_key2=right_infos[pair_index].deferred_call_ref.stable_key(),
                    summary_name=summary_name,
                    summary_index=next_summary_index,
                )
            )
            next_summary_index += 1

    if not matches:
        return RecursiveAbstractionResult(analysis1=analysis1, analysis2=analysis2, matches=[])

    mapping1 = {match.deferred_key1: match for match in matches}
    mapping2 = {match.deferred_key2: match for match in matches}

    transformed1 = _rewrite_analysis_with_abstract_calls(analysis1, mapping1, debug=debug)
    transformed2 = _rewrite_analysis_with_abstract_calls(analysis2, mapping2, debug=debug)
    return RecursiveAbstractionResult(
        analysis1=transformed1,
        analysis2=transformed2,
        matches=matches,
    )


def _group_deferred_calls(
    analysis: FunctionReturnAnalysis,
    deferred_calls: Sequence[DeferredCallInfo],
) -> Dict[Tuple[Tuple[object, ...], Tuple[Tuple[object, ...], ...]], List[DeferredCallInfo]]:
    grouped: Dict[Tuple[Tuple[object, ...], Tuple[Tuple[object, ...], ...]], List[DeferredCallInfo]] = {}
    for info in deferred_calls:
        key = _deferred_call_key(analysis, info)
        if key is None:
            continue
        grouped.setdefault(key, []).append(info)
    return grouped


def _deferred_call_key(
    analysis: FunctionReturnAnalysis,
    info: DeferredCallInfo,
) -> Optional[Tuple[Tuple[object, ...], Tuple[Tuple[object, ...], ...]]]:
    if info is None:
        return None

    target_key = _recursive_target_key(analysis, info)
    if target_key is None:
        return None
    arg_key = tuple(_recursive_argument_key(arg) for arg in (info.arguments or []))
    return target_key, arg_key


def _recursive_argument_key(expr: Optional[Expression]) -> Tuple[object, ...]:
    if expr is None:
        return ("none",)
    return _object_centric_expression_key(expr, for_call_target=False)


def _recursive_target_key(
    analysis: FunctionReturnAnalysis,
    info: DeferredCallInfo,
) -> Optional[Tuple[object, ...]]:
    target_ref = getattr(info, "target_ref", None)
    function_ref = getattr(analysis, "function_ref", None)
    if (
        function_ref is not None
        and target_ref is not None
        and target_ref.analysis_key() == function_ref.analysis_key()
    ):
        return ("self_recursive",)
    if (
        target_ref is not None
        and getattr(target_ref, "function_name", None)
        and getattr(target_ref, "function_name", None) == getattr(analysis, "function_name", None)
    ):
        return ("self_recursive",)

    target_expr_key = _call_target_expression_key(getattr(info, "call_target_expr", None))
    if target_expr_key is not None:
        return ("target_expr", target_expr_key)

    function_name = getattr(target_ref, "function_name", None)
    if function_name:
        return ("target_name", function_name)

    if target_ref is None:
        return None

    stable_key = target_ref.stable_key()
    if stable_key and stable_key[0] != "unknown":
        return ("target_ref", stable_key)
    return None


def _call_target_expression_key(expr: Optional[Expression]) -> Optional[Tuple[object, ...]]:
    if expr is None:
        return None
    return _object_centric_expression_key(expr, for_call_target=True)


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
    *,
    debug: bool = False,
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
    )

    existing_indices = {
        int(param.get("index", -1))
        for param in cloned.parameters
        if isinstance(param.get("index", -1), int)
    }

    for match in placeholder_mapping.values():
        if match.summary_index not in existing_indices:
            cloned.parameters.append(
                {
                    "name": match.summary_name,
                    "index": match.summary_index,
                    "size": 4,
                    "data_type": "int",
                    "is_signed": True,
                    "synthetic_recursive_summary": True,
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
        )
        for ret in (analysis.returns or [])
    ]

    if placeholder_mapping and "recursive_relational_abstraction" not in cloned.analysis_notes:
        cloned.analysis_notes.append("recursive_relational_abstraction")

    # 共有抽象へ置き換えられた placeholder は unresolved 扱いから外す
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
            size = expr.size or 4
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

    rebuilt = Expression(
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
    )
    return rebuilt

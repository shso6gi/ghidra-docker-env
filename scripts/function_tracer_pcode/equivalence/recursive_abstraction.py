# -*- coding: utf-8 -*-
"""Relational abstraction layer for unresolved recursive call summaries."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from ..model import Condition, DeferredCallInfo, Expression, ExpressionType, FunctionReturnAnalysis, ReturnInfo


@dataclass(frozen=True)
class AbstractedCallMatch:
    placeholder1: str
    placeholder2: str
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

    soundness を大きく崩さないよう、現時点では
    - self-recursive call
    - もしくは target 名が一致する deferred call
    のみを対応対象にする。
    """

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
                    placeholder1=left_infos[pair_index].placeholder_name,
                    placeholder2=right_infos[pair_index].placeholder_name,
                    summary_name=summary_name,
                    summary_index=next_summary_index,
                )
            )
            next_summary_index += 1

    if not matches:
        return RecursiveAbstractionResult(analysis1=analysis1, analysis2=analysis2, matches=[])

    mapping1 = {match.placeholder1: match for match in matches}
    mapping2 = {match.placeholder2: match for match in matches}

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
) -> Dict[Tuple[str, Tuple[str, ...]], List[DeferredCallInfo]]:
    grouped: Dict[Tuple[str, Tuple[str, ...]], List[DeferredCallInfo]] = {}
    for info in deferred_calls:
        key = _deferred_call_key(analysis, info)
        if key is None:
            continue
        grouped.setdefault(key, []).append(info)
    return grouped


def _deferred_call_key(
    analysis: FunctionReturnAnalysis,
    info: DeferredCallInfo,
) -> Optional[Tuple[str, Tuple[str, ...]]]:
    if info is None or not info.target_name:
        return None

    if info.target_name == analysis.function_name:
        target_key = "__self__"
    else:
        # 名前が一致する call にだけ共有抽象を許す
        target_key = info.target_name

    arg_key = tuple(_canonicalize_expression(arg) for arg in (info.arguments or []))
    return target_key, arg_key


def _canonicalize_expression(expr: Optional[Expression]) -> str:
    if expr is None:
        return "<none>"
    if expr.expr_type == ExpressionType.PARAMETER:
        index = expr.value if isinstance(expr.value, int) else -1
        return f"param@{index}:{expr.size or 0}"
    if expr.expr_type == ExpressionType.VARIABLE:
        return f"var:{expr.name}:{expr.size or 0}"
    if expr.expr_type == ExpressionType.CONSTANT:
        return f"const:{expr.value}:{expr.size or 0}"
    if expr.expr_type == ExpressionType.UNKNOWN:
        return f"unknown:{expr.name}"
    if expr.expr_type == ExpressionType.PHI and expr.value:
        parts = []
        for cond, value in expr.value:
            cond_key = _canonicalize_expression(cond.expression) if cond is not None else "<none>"
            parts.append(f"{cond_key}->{_canonicalize_expression(value)}")
        return "phi(" + ",".join(parts) + ")"
    operands = ",".join(_canonicalize_expression(op) for op in expr.operands or [])
    return f"{expr.expr_type.name}:{expr.operator}:{operands}:{expr.size or 0}"


def _rewrite_analysis_with_abstract_calls(
    analysis: FunctionReturnAnalysis,
    placeholder_mapping: Dict[str, AbstractedCallMatch],
    *,
    debug: bool = False,
) -> FunctionReturnAnalysis:
    cloned = FunctionReturnAnalysis(
        function_name=analysis.function_name,
        entry_point=analysis.entry_point,
        parameters=[dict(param) for param in (analysis.parameters or [])],
        returns=[],
        return_type=analysis.return_type,
        signedness_result=analysis.signedness_result,
        unknown_event_count=analysis.unknown_event_count,
        unknown_event_reasons=list(analysis.unknown_event_reasons),
        analysis_notes=list(analysis.analysis_notes),
        recovered_from_decompiler=analysis.recovered_from_decompiler,
        incomplete_control_flow=analysis.incomplete_control_flow,
        deferred_calls=dict(analysis.deferred_calls),
        effect_summary=analysis.effect_summary,
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
        name: info
        for name, info in cloned.deferred_calls.items()
        if name not in placeholder_mapping
    }
    return cloned


def _rewrite_expression(
    expr: Optional[Expression],
    placeholder_mapping: Dict[str, AbstractedCallMatch],
) -> Optional[Expression]:
    if expr is None:
        return None

    if expr.expr_type == ExpressionType.UNKNOWN and expr.name in placeholder_mapping:
        match = placeholder_mapping[expr.name]
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
        storage_info=expr.storage_info,
        read_order_key=getattr(expr, "read_order_key", None),
    )
    return rebuilt

# -*- coding: utf-8 -*-
"""record / replay で同一性を比べる比較面（Issue #109 PR-A）。

記録器と再生 test が**同じ関数**を使う（片方だけの比較面を持たせない）。
「最終 outcome が同じ」では不十分なので、解析側は return 式・条件・parameter・
return ABI・side effect の書き込み先 / 条件 / 値 / 順序まで、判定側は canonical
な決定面まで降ろす。effect の**件数だけ**の比較は行わない。
"""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Optional


ANALYSIS_SNAPSHOT_SCHEMA = "recorded-pcode-analysis-snapshot-v1"
CHECK_SNAPSHOT_SCHEMA = "recorded-pcode-check-snapshot-v1"


def _plain(value: Any) -> Any:
    """JSON 化できる素の値へ落とす。落とせない object は型名を残す。"""

    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, Mapping):
        return {str(key): _plain(item) for key, item in sorted(
            value.items(), key=lambda pair: str(pair[0])
        )}
    if isinstance(value, (list, tuple, set, frozenset)):
        items = list(value)
        if isinstance(value, (set, frozenset)):
            items = sorted(items, key=repr)
        return [_plain(item) for item in items]
    return "<non-json:{}>".format(type(value).__name__)


def _render_expression(expression: Any) -> Optional[str]:
    if expression is None:
        return None
    return expression.to_string()


def _render_conditions(conditions: Any) -> List[str]:
    return [condition.to_string() for condition in (conditions or [])]


def _parameter_snapshot(parameter: Mapping[str, Any]) -> Dict[str, Any]:
    # ``data_type_obj`` は Ghidra object そのものなので比較面に出さない
    # （``data_type`` の描画名と ``storage`` が観測面）。
    return {
        "name": _plain(parameter.get("name")),
        "index": _plain(parameter.get("index")),
        "size": _plain(parameter.get("size")),
        "data_type": _plain(parameter.get("data_type")),
        "is_signed": _plain(parameter.get("is_signed")),
        "storage": _plain(parameter.get("storage")),
        "owner_entry_offset": _plain(parameter.get("owner_entry_offset")),
    }


def _return_snapshot(index: int, info: Any) -> Dict[str, Any]:
    return {
        "order_index": index,
        "address": _plain(info.address),
        "return_kind": _plain(info.return_kind),
        "acceptance_status": _plain(info.acceptance_status),
        "branch_index": _plain(info.branch_index),
        "pcode_identity": _plain(info.pcode_identity),
        "pcode_order": _plain(info.pcode_order),
        "pcode_time": _plain(info.pcode_time),
        "value": _render_expression(info.value),
        "conditions": _render_conditions(info.conditions),
        "validation_blockers": _plain(tuple(info.validation_blockers or ())),
    }


def _effect_snapshot(index: int, effect: Any) -> Dict[str, Any]:
    provenance = getattr(effect, "provenance", None)
    return {
        "order_index": index,
        "order_key": _plain(effect.order_key),
        "location": _plain(effect.location.to_dict()),
        "location_stable_key": _plain(effect.location.stable_key()),
        "value": _render_expression(effect.value),
        "conditions": _render_conditions(effect.conditions),
        "provenance_source_kind": _plain(
            getattr(provenance, "source_kind", None)
        ),
        "provenance_complete": _plain(
            provenance.is_complete() if provenance is not None else None
        ),
    }


def _effect_summary_snapshot(summary: Any) -> Optional[Dict[str, Any]]:
    if summary is None:
        return None
    return {
        "parameter_names": _plain(list(summary.parameter_names or [])),
        "has_unsupported_call": _plain(summary.has_unsupported_call),
        "incomplete_reasons": _plain(list(summary.incomplete_reasons or ())),
        "synthetic_expr": _render_expression(summary.synthetic_expr),
        "unsupported_call_sites": [
            {
                "order_key": _plain(site.order_key),
                "reason": _plain(site.reason),
                "target_expr": _render_expression(site.target_expr),
                "arguments": [
                    _render_expression(argument) for argument in site.arguments
                ],
                "path_conditions": _render_conditions(site.path_conditions),
            }
            for site in summary.unsupported_call_sites
        ],
        # 件数だけの比較にしないため、effect は 1 件ずつ書き込み先 / 条件 /
        # 値 / 順序まで降ろす。
        "effects": [
            _effect_snapshot(index, effect)
            for index, effect in enumerate(summary.effects or [])
        ],
    }


def _signedness_snapshot(signedness: Any) -> Optional[Dict[str, Any]]:
    if signedness is None:
        return None
    to_dict = getattr(signedness, "to_dict", None)
    if not callable(to_dict):
        # 反射で「それらしい属性」を集めると、比較面が黙って狭くなる。
        raise TypeError(
            "signedness result has no to_dict(); the comparison surface would "
            "be narrowed silently"
        )
    return _plain(to_dict())


def analysis_snapshot(analysis: Any) -> Optional[Dict[str, Any]]:
    """1 つの ``FunctionReturnAnalysis`` の比較面。"""

    if analysis is None:
        return None
    return {
        "schema": ANALYSIS_SNAPSHOT_SCHEMA,
        "function_name": _plain(analysis.function_name),
        "entry_point": _plain(analysis.entry_point),
        "return_type": _plain(analysis.return_type),
        "program_is_big_endian": _plain(analysis.program_is_big_endian),
        "recovered_from_decompiler": _plain(analysis.recovered_from_decompiler),
        "incomplete_control_flow": _plain(analysis.incomplete_control_flow),
        "analysis_notes": _plain(list(analysis.analysis_notes or [])),
        "unknown_event_reasons": _plain(list(analysis.unknown_event_reasons or [])),
        "parameters": [
            _parameter_snapshot(parameter)
            for parameter in (analysis.parameters or [])
        ],
        "returns": [
            _return_snapshot(index, info)
            for index, info in enumerate(analysis.returns or [])
        ],
        "return_abi_facts": _plain(analysis.return_abi_facts or {}),
        "return_type_provenance": _plain(analysis.return_type_provenance or {}),
        "signedness_result": _signedness_snapshot(analysis.signedness_result),
        "effect_summary": _effect_summary_snapshot(analysis.effect_summary),
        "expansion_budget_truncations": _plain(
            [
                getattr(truncation, "to_dict", lambda: truncation)()
                for truncation in (analysis.expansion_budget_truncations or ())
            ]
        ),
    }


class AnalysisSnapshotCollector:
    """``analyzer_factory`` に噛ませて、解析の**列**を side ごとに記録する。

    1 pair の実行で同じ側が複数回解析されること（型修正 phase の再解析）が
    あるので、最後の 1 件ではなく列として保持する。record と replay で列が
    一致することを assert する。
    """

    def __init__(self) -> None:
        self.snapshots: Dict[str, List[Optional[Dict[str, Any]]]] = {}
        self.analyzer_programs: List[str] = []

    def wrap(self, inner_factory):
        collector = self

        def factory(program, **kwargs):
            analyzer = inner_factory(program, **kwargs)
            side = _side_key(kwargs.get("binary_id"), program)
            collector.analyzer_programs.append(side)
            original = analyzer.analyze_function_by_name

            def analyze_function_by_name(function_name, timeout):
                analysis = original(function_name, timeout)
                collector.snapshots.setdefault(side, []).append(
                    analysis_snapshot(analysis)
                )
                return analysis

            analyzer.analyze_function_by_name = analyze_function_by_name
            return analyzer

        return factory

    def payload(self) -> Dict[str, Any]:
        return {
            "schema": ANALYSIS_SNAPSHOT_SCHEMA,
            "analyzer_programs": list(self.analyzer_programs),
            "sides": {
                side: list(entries)
                for side, entries in sorted(self.snapshots.items())
            },
        }


def _side_key(binary_id: Any, program: Any) -> str:
    if type(binary_id) is str and binary_id:
        return binary_id
    return "program:{}".format(id(program))


#: 判定面の比較 key（`c_active` の reason id、`q_open` の proof kind、decisive
#: proof kind、conditional 列、stage 経路）。
def check_snapshot(payload: Mapping[str, Any]) -> Dict[str, Any]:
    """`EquivalenceResult.to_dict()` から judgement の比較面を取り出す。"""

    bundle = payload.get("canonical_result_finalization_bundle") or {}
    projection = (
        bundle.get("canonical_semantic_result_projection") or {}
    ).get("payload") or {}
    return {
        "schema": CHECK_SNAPSHOT_SCHEMA,
        "final_outcome": _plain(payload.get("final_outcome")),
        "is_equivalent": _plain(payload.get("is_equivalent")),
        "conditional_outcome": _plain(payload.get("conditional_outcome")),
        "stage_path": _plain(payload.get("stage_path")),
        "c_active_reason_ids": sorted(
            str(row.get("reason_id"))
            for row in (payload.get("c_active_base") or [])
        ),
        "q_open_proof_kinds": sorted(
            str(row.get("proof_kind"))
            for row in (payload.get("q_open_base") or [])
        ),
        "decisive_proof_kinds": _plain(projection.get("decisive_proof_kinds")),
        "canonical_outcome": _plain(projection.get("canonical_outcome")),
        "error_kind": _plain(projection.get("error_kind")),
        "function1_name": _plain(payload.get("function1_name")),
        "function2_name": _plain(payload.get("function2_name")),
        "binary1_name": _plain(payload.get("binary1_name")),
        "binary2_name": _plain(payload.get("binary2_name")),
        "identical_fast_path_disposition": _plain(
            payload.get("identical_fast_path_disposition")
        ),
        "decisive_proof_provenance_kind": _plain(
            (payload.get("decisive_proof_provenance") or {}).get("kind")
        ),
    }


__all__ = [
    "ANALYSIS_SNAPSHOT_SCHEMA",
    "AnalysisSnapshotCollector",
    "CHECK_SNAPSHOT_SCHEMA",
    "analysis_snapshot",
    "check_snapshot",
]

# -*- coding: utf-8 -*-
"""反例が依存し得る、側ごとの program の状態（Issue #282, I6）。

左右の query では、memory・image の object の番地・出口の状態の値を側ごとの記号で描く（`core.render_smt.sides`）。
側ごとの記号は、左右の対応を証明できない部分の **上近似** なので、UNSAT（EQ）の根拠としては健全だが、
SAT の model が選んだ値は、実際の memory の状態として実現できるとは限らない。たとえば

* 左右の配列に別の値を置いた model（同じ object を指す番地なら、呼び出し時点の内容は同じ。D-M1）
* image の read-only data の cell に、image に無い値を置いた model（bessi0 の閾値: #282）
* 幅ごとの配列に、byte として矛盾する値を置いた model
* global の番地の記号に、配置と矛盾する値を置いた model

がある。実現の条件（E 領域の共有・Q1 の公理・番地の制約）を描いて解き直すのは PR-282-P の範囲で、この段階では、
比べた case の組がこれらの記号を **読むなら** 反例を実現できると言わない: ref `memory_state_unrealized:<kind>:<digest16>`
を SAT の安全性の blocker に足す。ref は `sat_safety_ref_resolution` の表で `ANALYSIS_UNSAFETY`（replay で解除しない）。

判定は描画の文字列を見ない: case の式の node の種類と、凍結した projection（`semantic_projection`）から決める。
renderer が側ごとの記号で描く node の集合と同じ規則（`core.render_smt.render` / `unknowns.side_address_smt` /
`intrinsics.memory_function_name`）。
"""

from __future__ import annotations

import hashlib
from typing import Dict, Iterable, List, Optional, Tuple

MEMORY_STATE_UNREALIZED_REF_PREFIX = "memory_state_unrealized"

#: kind の値（ref の 2 番目の field）
KIND_ARRAY = "array"
KIND_GLOBAL_ADDRESS = "global_address"
KIND_IMAGE_ADDRESS = "image_address"
KIND_STATE = "state"
KIND_OBSERVATION = "observation"

_MEMORY_FUNCTION_INTRINSICS = frozenset({"READONLY_SUM"})


def _node_kinds(node) -> Iterable[str]:
    from scripts.function_tracer_pcode.core import ExpressionType
    from scripts.function_tracer_pcode.core.intrinsics import READONLY_SUM_OPCODE
    from scripts.function_tracer_pcode.core.runtime_refs import ReadonlyReductionRef
    from scripts.function_tracer_pcode.core.semantic_snapshot import semantic_projection

    expr_type = getattr(node, "expr_type", None)
    if expr_type == ExpressionType.MEMORY:
        yield KIND_ARRAY
        return
    if expr_type == ExpressionType.INTRINSIC:
        name = str(getattr(node, "name", "") or "")
        opcode = getattr(node, "opcode", None)
        if (
            name in _MEMORY_FUNCTION_INTRINSICS
            or opcode == READONLY_SUM_OPCODE
            or isinstance(getattr(node, "runtime_ref", None), ReadonlyReductionRef)
        ):
            yield KIND_ARRAY
    if expr_type in (ExpressionType.CONSTANT, ExpressionType.VARIABLE):
        projection = semantic_projection(node)
        if projection.address_object_identity is not None:
            yield KIND_GLOBAL_ADDRESS
        elif projection.address_in_image:
            yield KIND_IMAGE_ADDRESS
        if expr_type == ExpressionType.VARIABLE:
            from scripts.function_tracer_pcode.core.observation_index import is_observation_index

            if is_observation_index(node):
                yield KIND_OBSERVATION
            elif projection.declares_variable_symbol:
                yield KIND_STATE


def _iter_nodes(expr) -> Iterable[object]:
    from scripts.function_tracer_pcode.core.render_smt.attributes import iter_expression_nodes

    if expr is None:
        return ()
    return iter_expression_nodes(expr)


def _node_label(node) -> str:
    from scripts.function_tracer_pcode.core.structural import expression_key_safe

    key = expression_key_safe(node, budget=64)
    if key is None:
        return f"{getattr(getattr(node, 'expr_type', None), 'name', '?')}:{getattr(node, 'size', None)}"
    return repr(key)


def side_state_dependence(values: Iterable[object]) -> Dict[str, Tuple[str, ...]]:
    """式（Expression / Condition）の列が読む、側ごとの状態の記号。kind → node の label（整列済み）。"""

    found: Dict[str, set] = {}
    for value in values:
        expr = getattr(value, "expression", value) if value is not None else None
        for node in _iter_nodes(expr):
            for kind in _node_kinds(node):
                found.setdefault(kind, set()).add(_node_label(node))
    return {kind: tuple(sorted(labels)) for kind, labels in sorted(found.items())}


def case_side_state_values(case) -> List[object]:
    """case の組で SMT に入る値（戻り値・正規化後の戻り値・経路の条件・比較面）。"""

    values: List[object] = []
    for name in ("value_expr", "normalized_value_expr", "comparison_surface"):
        value = getattr(case, name, None)
        if value is not None and hasattr(value, "expr_type"):
            values.append(value)
    for name in ("conditions", "summary_conditions"):
        values.extend(list(getattr(case, name, None) or ()))
    return values


def memory_state_unrealized_refs(
    dependence: Dict[str, Tuple[str, ...]],
    *,
    exclude_kinds: Tuple[str, ...] = (),
) -> List[str]:
    """依存の表から blocker の ref（kind ごとに 1 つ）。"""

    refs: List[str] = []
    for kind, labels in sorted(dependence.items()):
        if kind in exclude_kinds or not labels:
            continue
        digest = hashlib.sha256("\x00".join((kind,) + tuple(labels)).encode("utf-8")).hexdigest()[:16]
        refs.append(f"{MEMORY_STATE_UNREALIZED_REF_PREFIX}:{kind}:{digest}")
    return refs


def case_pair_memory_state_refs(case1, case2) -> List[str]:
    """比べた case の組の SAT が依存し得る、実現を確かめていない側ごとの状態の ref。"""

    return memory_state_unrealized_refs(
        side_state_dependence(case_side_state_values(case1) + case_side_state_values(case2))
    )


def analysis_pair_memory_state_refs(analysis1, analysis2) -> List[str]:
    """関数全体（monolithic）の SAT が依存し得る、側ごとの状態の ref。"""

    values: List[object] = []
    for analysis in (analysis1, analysis2):
        if analysis is None:
            continue
        for ret in list(getattr(analysis, "returns", None) or ()):
            values.append(getattr(ret, "value", None))
            values.extend(list(getattr(ret, "conditions", None) or ()))
        effect_summary = getattr(analysis, "effect_summary", None)
        surface = getattr(effect_summary, "synthetic_expr", None) if effect_summary is not None else None
        if surface is not None:
            values.append(surface)
    return memory_state_unrealized_refs(side_state_dependence(values))


def query_reads_side_state(values: Iterable[object]) -> bool:
    """値の列が側ごとの状態の記号を読むか（閉じた式の即時合格を止める判定）。"""

    return bool(side_state_dependence(values))


def is_memory_state_unrealized_ref(ref: Optional[str]) -> bool:
    return isinstance(ref, str) and ref.startswith(MEMORY_STATE_UNREALIZED_REF_PREFIX + ":")

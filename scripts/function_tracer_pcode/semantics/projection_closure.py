# -*- coding: utf-8 -*-
"""raw surface に対する parameter projection closure の走査（Issue #167）。

入力は semantic-width 書き換え **前** の analysis（``StrategySourceAnalysisPair``
の raw）で、semantic hint は一切読まない。書き換え後の式で closure を判定すると、
書き換えの前提を書き換え結果で正当化する循環になる（v3 §0.1）。

判定は保守的な構造 whitelist:

* parameter の occurrence は ``SUBPIECE(p, k)`` の explicit extract の下にある
  ときだけ、読む bit 範囲 ``[8k, 8k + w)`` を記録する。裸の occurrence は
  closure を壊す。
* 構造が分からない node（``UNKNOWN``、不透明な ``CALL``、runtime ref 付き
  ``INTRINSIC``、未知の種別）、閉路、同じ register を別名で読む変数、
  identity の分からない parameter / 変数は **skip せず** witness を返す。
* 観測 surface は下の adapter 表で列挙する。新しい surface は adapter を 1 つ
  足せばよく、判定規則には触らない。

closure at N は「全 surface の要求 bit 幅 <= N かつ witness 無し」。幅ごとに
独立に判定する（32 で閉じても 16 で閉じるとは限らない）。
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Dict, Iterator, List, Optional, Tuple

from scripts.function_tracer_pcode.core import ExpressionType
from scripts.function_tracer_pcode.core.errors import ExpressionCycleError
from scripts.function_tracer_pcode.core.semantic_snapshot import (
    ordered_semantic_edges,
    traverse_semantic_graph,
)
from scripts.function_tracer_pcode.semantics.projection_contract import (
    ClosureWitness,
    ProjectionClosure,
)
from scripts.function_tracer_pcode.semantics.semantic_width import (
    _coerce_storage_info,
    _storage_identity_key,
)


# ---------------------------------------------------------------------------
# parameter identity
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _ParameterEntry:
    """parameter 表の 1 行の identity（index・名前・storage）。"""

    index: Optional[int]
    name: Optional[str]
    storage_key: Optional[Tuple[object, ...]]


@dataclass(frozen=True)
class _ParameterTarget:
    index: int
    bit_width: int
    name: Optional[str]
    storage_key: Optional[Tuple[object, ...]]
    storage: Any
    #: 同じ表の他の parameter。leaf が「別 parameter」だと言えるのは、この
    #: どれかに解決できたときだけ（どこにも解決しない leaf は identity 不明）。
    others: Tuple[_ParameterEntry, ...] = ()


def _parameter_entry(descriptor: Any) -> Tuple[_ParameterEntry, Any]:
    try:
        index = int(descriptor.get("index"))
    except (TypeError, ValueError, AttributeError):
        index = None
    getter = getattr(descriptor, "get", None)
    storage = _coerce_storage_info(getter("storage_info", getter("storage"))) if callable(getter) else None
    name = getter("name") if callable(getter) else None
    return _ParameterEntry(index, name or None, _storage_identity_key(storage)), storage


def _parameter_target(analysis: Any, parameter_index: int, parameter_bits: int) -> Optional[_ParameterTarget]:
    entries = [_parameter_entry(descriptor) for descriptor in getattr(analysis, "parameters", None) or ()]
    for position, (entry, storage) in enumerate(entries):
        if entry.index != parameter_index:
            continue
        return _ParameterTarget(
            index=entry.index,
            bit_width=int(parameter_bits),
            name=entry.name,
            storage_key=entry.storage_key,
            storage=storage,
            others=tuple(other for at, (other, _storage) in enumerate(entries) if at != position),
        )
    return None


# ---------------------------------------------------------------------------
# node rules
# ---------------------------------------------------------------------------


#: parameter の tie だけでは入力の全 bit が対応しない理由: 同じ register を別名で
#: 読む、または表のどの parameter にも解決しない parameter leaf（lowering では
#: 側ごとに別の自由 symbol になる）。
HIDDEN_INPUT_REASONS = frozenset({
    "register_alias",
    "register_alias_unknown",
    "parameter_storage_unknown",
    "parameter_identity_unknown",
})


@dataclass(frozen=True)
class _Demand:
    """node の評価結果。

    ``bits``: parameter を読む最大の上端 bit（occurrence 無しは 0）。
    ``witness``: closure をどの幅でも壊す最初の理由。
    ``hidden``: 全幅の tie でも入力が対応しない理由（``HIDDEN_INPUT_REASONS``）の最初の 1 つ。
    ``witness`` とは別に運ぶ（同じ式に裸の occurrence があっても隠れない）。
    """

    bits: int = 0
    witness: Optional[Tuple[str, str]] = None
    hidden: Optional[Tuple[str, str]] = None


_NO_DEMAND = _Demand()


def _broken(reason: str, detail: str) -> _Demand:
    item = (reason, detail)
    return _Demand(0, item, item if reason in HIDDEN_INPUT_REASONS else None)


def _node_label(node: Any) -> str:
    kind = getattr(getattr(node, "expr_type", None), "name", type(node).__name__)
    detail = getattr(node, "operator", None) or getattr(node, "name", None)
    return f"{kind}:{detail}" if detail else str(kind)


def _integer(value: Any) -> Optional[int]:
    """Python int と、Ghidra 由来の int 派生型（JPype の ``JInt`` / ``JLong``）を同じに扱う。"""

    if isinstance(value, bool) or not isinstance(value, int):
        return None
    return int(value)


def _identity_matches(
    index: Optional[int],
    storage_key: Optional[Tuple[object, ...]],
    name: Optional[str],
    entry: Any,
) -> bool:
    return (
        (index is not None and index == entry.index)
        or (storage_key is not None and storage_key == entry.storage_key)
        or bool(name and name == entry.name)
    )


def _parameter_occurrence(node: Any, target: _ParameterTarget) -> Optional[str]:
    """PARAMETER node が target か。``"match"`` / ``"other"`` / ``"unknown"``.

    SMT への lowering は leaf を index で parameter 表に揃えてから名前で束縛する
    ので、index・storage・名前の **どれか 1 つでも** target と一致すれば target の
    occurrence とみなす（取り逃すと closure が空虚に成立する）。``"other"`` は
    表の別の行に解決できたときだけ。どの行にも解決しない leaf は lowering で
    表に無い自由 symbol になり、target との対応が言えないので ``"unknown"``。
    """

    index = _integer(getattr(node, "value", None))
    if index is not None and index < 0:
        index = None
    storage_key = _storage_identity_key(getattr(node, "storage_info", None))
    name = getattr(node, "name", None) or None
    if _identity_matches(index, storage_key, name, target):
        return "match"
    if any(_identity_matches(index, storage_key, name, other) for other in target.others):
        return "other"
    return "unknown"


def _variable_occurrence(node: Any, target: _ParameterTarget) -> Optional[str]:
    """VARIABLE node が名前で parameter の symbol に束縛されるか。

    lowering は parameter と追加変数を **名前** で symbol に対応付ける
    （``proof/formula/symbol_replace.py``）。parameter と同名の VARIABLE は、storage
    に関係なくその parameter の全幅 symbol として描かれる。target と同名なら
    ``"match"``、別 parameter と同名なら ``"other"``、どちらでもなければ None。
    """

    name = getattr(node, "name", None) or None
    if name is None:
        return None
    if name == target.name:
        return "match"
    if any(name == other.name for other in target.others):
        return "other"
    return None


def _leaf_occurrence(node: Any, target: _ParameterTarget) -> Optional[str]:
    kind = getattr(node, "expr_type", None)
    if kind == ExpressionType.PARAMETER:
        return _parameter_occurrence(node, target)
    if kind == ExpressionType.VARIABLE:
        return _variable_occurrence(node, target)
    return None


def _variable_aliases_target(node: Any, target: _ParameterTarget) -> Optional[str]:
    """VARIABLE が target と同じ register を読むか。分からなければ理由を返す。"""

    storage = _coerce_storage_info(getattr(node, "storage_info", None))
    if storage is None:
        return "variable_storage_unknown"
    if not getattr(storage, "is_register", False):
        return None
    if target.storage is None or not getattr(target.storage, "is_register", False):
        return "parameter_storage_unknown"
    try:
        if storage.shares_base_register_with(target.storage):
            return "register_alias"
    except (AttributeError, TypeError, ValueError):
        return "register_alias_unknown"
    return None


def _subpiece_demand(node: Any, target: _ParameterTarget) -> Optional[_Demand]:
    """``SUBPIECE(p, k)`` を explicit extract として評価する。p でなければ None。"""

    operands = list(getattr(node, "operands", None) or ())
    if len(operands) != 2:
        return None
    source, offset = operands
    if _leaf_occurrence(source, target) != "match":
        return None
    if getattr(offset, "expr_type", None) != ExpressionType.CONSTANT:
        return _broken("extract_offset_not_constant", _node_label(node))
    try:
        byte_offset = int(offset.value)
        result_bits = int(node.get_bit_width())
    except (TypeError, ValueError, AttributeError):
        return _broken("extract_width_unknown", _node_label(node))
    if byte_offset < 0 or result_bits <= 0:
        return _broken("extract_width_unknown", _node_label(node))
    return _Demand(byte_offset * 8 + result_bits)


def _structural_fragment_witness(node: Any, target: _ParameterTarget) -> Optional[Tuple[str, str]]:
    """``PIECE(v, p)`` / ``(v << w) | p`` は v を p の register の上位断片として読む形。

    ``VariableAnalyzer`` は storage が無くてもこの形から断片を推定する。v は SMT 上
    自由な入力なので、p の tie だけでは入力の全 bit が対応しない。
    """

    operator = getattr(node, "operator", None)
    operands = list(getattr(node, "operands", None) or ())
    if len(operands) != 2:
        return None
    candidates = []
    if operator == "PIECE":
        candidates.append((operands[0], operands[1]))
    elif operator == "INT_OR":
        for shifted, low in ((operands[0], operands[1]), (operands[1], operands[0])):
            if (
                getattr(shifted, "expr_type", None) == ExpressionType.BINARY_OP
                and getattr(shifted, "operator", None) == "INT_LEFT"
                and len(getattr(shifted, "operands", None) or ()) == 2
            ):
                candidates.append((shifted.operands[0], low))
    for high, low in candidates:
        if (
            getattr(high, "expr_type", None) != ExpressionType.VARIABLE
            or getattr(low, "expr_type", None) != ExpressionType.PARAMETER
        ):
            continue
        occurrence = _parameter_occurrence(low, target)
        if occurrence == "match":
            return ("register_alias", f"structural_fragment:{getattr(high, 'name', None)}")
        if occurrence == "unknown":
            return ("register_alias_unknown", f"structural_fragment:{getattr(high, 'name', None)}")
    return None


def _evaluate_node(node: Any, target: _ParameterTarget, child: Callable[[Any], _Demand]) -> _Demand:
    kind = getattr(node, "expr_type", None)
    if kind in (ExpressionType.CONSTANT, ExpressionType.LITERAL):
        return _NO_DEMAND
    if kind == ExpressionType.PARAMETER:
        occurrence = _parameter_occurrence(node, target)
        if occurrence == "match":
            return _broken("bare_parameter", _node_label(node))
        if occurrence == "unknown":
            return _broken("parameter_identity_unknown", _node_label(node))
        return _NO_DEMAND
    if kind == ExpressionType.VARIABLE:
        occurrence = _variable_occurrence(node, target)
        if occurrence == "match":
            return _broken("bare_parameter", _node_label(node))
        if occurrence == "other":
            return _NO_DEMAND
        alias = _variable_aliases_target(node, target)
        return _NO_DEMAND if alias is None else _broken(alias, _node_label(node))
    if kind == ExpressionType.UNKNOWN:
        return _broken("unknown_node", _node_label(node))
    if kind == ExpressionType.CALL:
        return _broken("opaque_call", _node_label(node))
    if kind == ExpressionType.INTRINSIC and getattr(node, "runtime_ref", None) is not None:
        return _broken("opaque_runtime_ref", type(node.runtime_ref).__name__)
    if kind == ExpressionType.BINARY_OP and getattr(node, "operator", None) == "SUBPIECE":
        demand = _subpiece_demand(node, target)
        if demand is not None:
            return demand
    if kind == ExpressionType.BINARY_OP:
        fragment = _structural_fragment_witness(node, target)
        if fragment is not None:
            return _broken(*fragment)
    if kind not in (
        ExpressionType.BINARY_OP,
        ExpressionType.UNARY_OP,
        ExpressionType.MEMORY,
        ExpressionType.INTRINSIC,
        ExpressionType.PHI,
    ):
        return _broken("unknown_node", _node_label(node))
    bits = 0
    witness = None
    hidden = None
    for edge in ordered_semantic_edges(node):
        if edge.child is None:
            continue
        result = child(edge.child)
        bits = max(bits, result.bits)
        witness = witness or result.witness
        hidden = hidden or result.hidden
    return _Demand(bits, witness, hidden)


class _DemandScanner:
    """1 parameter 分の node 評価を DAG 共有込みで 1 回ずつ行う。"""

    def __init__(self, target: _ParameterTarget):
        self.target = target
        self._memo: Dict[int, Tuple[Any, _Demand]] = {}

    def demand(self, root: Any) -> _Demand:
        if root is None:
            return _NO_DEMAND
        hit = self._memo.get(id(root))
        if hit is not None and hit[0] is root:
            return hit[1]
        try:
            order = traverse_semantic_graph(root, prune=self._known).post_order
        except ExpressionCycleError:
            return _broken("cycle", _node_label(root))
        for node in order:
            self._memo[id(node)] = (node, _evaluate_node(node, self.target, self._lookup))
        return self._memo[id(root)][1]

    def _known(self, node: Any) -> bool:
        hit = self._memo.get(id(node))
        return hit is not None and hit[0] is node

    def _lookup(self, node: Any) -> _Demand:
        hit = self._memo.get(id(node))
        if hit is None or hit[0] is not node:
            # post_order は子を先に並べるので、ここに来るのは内部不整合だけ。
            return _broken("unscanned_child", _node_label(node))
        return hit[1]


# ---------------------------------------------------------------------------
# surface adapters
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _SurfaceItem:
    """走査対象 1 件。``expression`` か、走査せずに closure を壊す ``witness``。"""

    surface: str
    location: str
    expression: Any = None
    witness: Optional[Tuple[str, str]] = None


def _conditions(surface: str, location: str, conditions: Any) -> Iterator[_SurfaceItem]:
    for index, condition in enumerate(conditions or ()):
        yield _SurfaceItem(surface, f"{location}[{index}]", getattr(condition, "expression", None))


def _return_surfaces(analysis: Any) -> Iterator[_SurfaceItem]:
    for index, ret in enumerate(getattr(analysis, "returns", None) or ()):
        yield _SurfaceItem("return_value", f"returns[{index}].value", getattr(ret, "value", None))
        yield from _conditions("path_condition", f"returns[{index}].conditions", getattr(ret, "conditions", None))
    for index, candidate in enumerate(getattr(analysis, "summary_return_candidates", None) or ()):
        if getattr(candidate, "acceptance_status", None) not in {"accepted", "validated"}:
            continue
        info = getattr(candidate, "return_info", None)
        location = f"summary_return_candidates[{index}]"
        yield _SurfaceItem("return_value", f"{location}.value", getattr(info, "value", None))
        yield from _conditions("path_condition", f"{location}.conditions", getattr(info, "conditions", None))


def _outcome_surfaces(analysis: Any) -> Iterator[_SurfaceItem]:
    for index, outcome in enumerate(getattr(analysis, "return_outcomes", None) or ()):
        location = f"return_outcomes[{index}]"
        yield _SurfaceItem("return_value", f"{location}.value", getattr(outcome, "value", None))
        yield from _conditions("path_condition", f"{location}.guard", getattr(outcome, "guard", None))
        info = getattr(outcome, "return_info", None)
        if info is not None:
            yield _SurfaceItem("return_value", f"{location}.return_info.value", getattr(info, "value", None))
            yield from _conditions(
                "path_condition", f"{location}.return_info.conditions", getattr(info, "conditions", None)
            )
    for index, outcome in enumerate(getattr(analysis, "divergence_outcomes", None) or ()):
        yield from _conditions("path_condition", f"divergence_outcomes[{index}].guard", getattr(outcome, "guard", None))
    for index, _outcome in enumerate(getattr(analysis, "unknown_outcomes", None) or ()):
        # 観測が模型化されていない outcome は、どの bit を読むか言えない。
        yield _SurfaceItem("observation", f"unknown_outcomes[{index}]", witness=("unknown_outcome", ""))
    if getattr(analysis, "incomplete_control_flow", False):
        yield _SurfaceItem("observation", "incomplete_control_flow", witness=("control_flow_incomplete", ""))


def _storage_keys_overlap(left: Tuple[object, ...], right: Tuple[object, ...]) -> bool:
    """storage identity key（``StorageInfo.storage_identity_key``）が同じ入力 bit を含むか。"""

    if left[0] != right[0]:
        return False
    if left[0] == "register_storage":
        # (kind, space, base offset, base bits, bit offset, bits): 同じ親 register。
        return tuple(left[1:4]) == tuple(right[1:4])
    if left[0] == "memory_storage":
        # (kind, space, offset, size): 同じ space の byte 範囲が重なる。
        return left[1] == right[1] and left[2] < right[2] + right[3] and right[2] < left[2] + left[3]
    return tuple(left) == tuple(right)


def _store_destination_witness(location: Any, target: _ParameterTarget) -> Optional[Tuple[str, str]]:
    base = getattr(location, "base_ref", None)
    kind = getattr(base, "kind", None)
    if kind in {"stack_frame", "global"}:
        # 固定 base と定数 step だけの宛先は parameter の bit を読まない。
        return None
    if kind == "storage":
        # 宛先 address は base storage の入口値。それが target の storage と
        # 重なれば parameter の bit を読む。どちらかの identity が無ければ不明。
        key = getattr(base, "storage_identity_key", None)
        if not key or not target.storage_key:
            return ("store_destination_alias_unknown", "storage")
        if _storage_keys_overlap(tuple(key), tuple(target.storage_key)):
            return ("store_destination_parameter_base", f"param_{target.index}")
        return None
    if kind != "parameter":
        return ("store_destination_unknown", str(kind))
    index = _integer(getattr(base, "parameter_index", None))
    name = getattr(base, "parameter_name", None)
    if index == target.index or (name and name == target.name):
        return ("store_destination_parameter_base", f"param_{target.index}")
    if index is not None or (name and target.name):
        return None
    return ("store_destination_alias_unknown", str(name))


def _effect_surfaces(analysis: Any, target: _ParameterTarget) -> Iterator[_SurfaceItem]:
    summary = getattr(analysis, "effect_summary", None)
    if summary is None:
        return
    for index, effect in enumerate(getattr(summary, "effects", None) or ()):
        location = f"effects[{index}]"
        yield _SurfaceItem("store_value", f"{location}.value", getattr(effect, "value", None))
        yield from _conditions("store_condition", f"{location}.conditions", getattr(effect, "conditions", None))
        witness = _store_destination_witness(getattr(effect, "location", None), target)
        if witness is not None:
            yield _SurfaceItem("store_destination", f"{location}.location", witness=witness)
    yield _SurfaceItem("synthetic_expression", "effect_summary.synthetic_expr", getattr(summary, "synthetic_expr", None))
    for index, evidence in enumerate((getattr(summary, "call_argument_evidence", None) or {}).values()):
        if evidence is None:
            continue
        location = f"call_argument_evidence[{index}]"
        for arg_index, argument in enumerate(getattr(evidence, "arguments", None) or ()):
            yield _SurfaceItem("call_argument", f"{location}.arguments[{arg_index}]", argument)
        for group_index, group in enumerate(getattr(evidence, "path_conditions", None) or ()):
            yield from _conditions("call_condition", f"{location}.path_conditions[{group_index}]", group)
        if not getattr(evidence, "coverage_complete", False):
            yield _SurfaceItem("call_argument", location, witness=("call_argument_incomplete", ""))
    for index, evidence in enumerate(getattr(summary, "call_target_resolution_evidence", None) or ()):
        # 間接 call の target は式として持つ（path 条件は return/effect の条件と同じ
        # 構造 key なので、そちらの surface で走査済み）。
        yield _SurfaceItem(
            "call_target",
            f"call_target_resolution_evidence[{index}].target_expr",
            getattr(evidence, "target_expr", None),
        )
    for index, site in enumerate(getattr(summary, "unsupported_call_sites", None) or ()):
        # 要約できなかった call は効果が分からないので、引数だけ見ても足りない。
        yield _SurfaceItem("call_effect", f"unsupported_call_sites[{index}]", witness=(
            "unsupported_call_effect", str(getattr(site, "reason", "")),
        ))
    if getattr(summary, "has_unsupported_call", False) and not getattr(summary, "unsupported_call_sites", None):
        yield _SurfaceItem("call_effect", "effect_summary", witness=("unsupported_call_effect", "unrecorded"))
    for reason in getattr(summary, "incomplete_reasons", None) or ():
        yield _SurfaceItem("observation", "effect_summary", witness=("effect_summary_incomplete", str(reason)))


def _deferred_call_surfaces(analysis: Any) -> Iterator[_SurfaceItem]:
    """展開しなかった call（再帰要約の対象を含む）の引数と間接 target。

    要約は引数の一致で call 結果を対応付けるので、引数が読む bit も観測に入る。
    引数を回収しきれていない call は、どの bit を読むか言えない。
    """

    for index, info in enumerate((getattr(analysis, "deferred_calls", None) or {}).values()):
        location = f"deferred_calls[{index}]"
        for arg_index, argument in enumerate(getattr(info, "arguments", None) or ()):
            yield _SurfaceItem("call_argument", f"{location}.arguments[{arg_index}]", argument)
        yield _SurfaceItem("call_target", f"{location}.call_target_expr", getattr(info, "call_target_expr", None))
        if getattr(info, "call_argument_recovery_status", None) != "complete":
            yield _SurfaceItem("call_argument", location, witness=(
                "call_argument_incomplete", str(getattr(info, "call_argument_recovery_status", "")),
            ))


def _surfaces(analysis: Any, target: _ParameterTarget) -> Iterator[_SurfaceItem]:
    yield from _return_surfaces(analysis)
    yield from _outcome_surfaces(analysis)
    yield from _effect_surfaces(analysis, target)
    yield from _deferred_call_surfaces(analysis)


# ---------------------------------------------------------------------------
# public entry
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ParameterDemand:
    """1 parameter の raw 需要。``closure(N)`` で幅ごとの判定を作る。"""

    parameter_index: int
    parameter_bits: int
    demanded_bits: int
    demand_location: str
    witnesses: Tuple[ClosureWitness, ...]
    #: 全幅の tie でも入力が対応しない箇所（``HIDDEN_INPUT_REASONS``）。
    hidden_inputs: Tuple[ClosureWitness, ...] = ()

    def closure(self, narrow_bits: int) -> ProjectionClosure:
        witnesses = list(self.witnesses)
        if self.demanded_bits > int(narrow_bits):
            surface, _, location = self.demand_location.partition("@")
            witnesses.append(
                ClosureWitness(
                    surface=surface or "unknown",
                    location=location or "unknown",
                    reason="extract_outside_projection",
                    detail=f"reads_bits={self.demanded_bits}>N={int(narrow_bits)}",
                )
            )
        return ProjectionClosure(
            parameter_index=self.parameter_index,
            parameter_bits=self.parameter_bits,
            narrow_bits=int(narrow_bits),
            witnesses=tuple(witnesses),
        )


def scan_parameter_demand(analysis: Any, parameter_index: int, parameter_bits: int) -> ParameterDemand:
    """raw analysis 上で parameter が読む bit 範囲と、closure を壊す witness を集める。"""

    target = _parameter_target(analysis, parameter_index, parameter_bits)
    if target is None:
        return ParameterDemand(
            parameter_index,
            parameter_bits,
            0,
            "",
            (ClosureWitness("parameter", f"param_index={parameter_index}", "parameter_descriptor_missing"),),
        )
    scanner = _DemandScanner(target)
    demanded_bits = 0
    demand_location = ""
    witnesses: List[ClosureWitness] = []
    hidden_inputs: List[ClosureWitness] = []
    for item in _surfaces(analysis, target):
        if item.witness is not None:
            witnesses.append(ClosureWitness(item.surface, item.location, item.witness[0], item.witness[1]))
            continue
        if item.expression is None:
            continue
        result = scanner.demand(item.expression)
        if result.witness is not None:
            witnesses.append(ClosureWitness(item.surface, item.location, *result.witness))
        if result.hidden is not None:
            hidden_inputs.append(ClosureWitness(item.surface, item.location, *result.hidden))
        if result.bits > demanded_bits:
            demanded_bits = result.bits
            demand_location = f"{item.surface}@{item.location}"
    return ParameterDemand(
        parameter_index=parameter_index,
        parameter_bits=parameter_bits,
        demanded_bits=demanded_bits,
        demand_location=demand_location,
        witnesses=tuple(witnesses),
        hidden_inputs=tuple(hidden_inputs),
    )


def scan_projection_closure(
    analysis: Any,
    parameter_index: int,
    parameter_bits: int,
    narrow_bits: int,
) -> ProjectionClosure:
    """``scan_parameter_demand(...).closure(narrow_bits)`` の短縮形。"""

    return scan_parameter_demand(analysis, parameter_index, parameter_bits).closure(narrow_bits)

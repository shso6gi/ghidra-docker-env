# -*- coding: utf-8 -*-
"""最終 relation の構築（R0〜R5、v5 §4.5）。raw analysis だけを受け付ける。

十分性の判定点はここだけ（``_SideContext.hidden_inputs`` と表全体の欠陥）。入力領域の
事実（封印した raw baseline・仮説の台帳・synthetic の名乗り）は core の
``ParameterDomainAudit`` が報告し、ここは「欠陥が 1 つでもあれば、その parameter は
どの規則でも十分性を持たない」と決めるだけ（Issue #185: provenance ≠ proof）。
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core.parameter_domain import (
    SYNTHETIC_PARAMETER_KINDS,
    ParameterDomainAudit,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence.evidence import (
    InputExtensionEvidence,
    analysis_parameter_binding,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence.model import (
    LEFT,
    RIGHT,
    InputCorrespondence,
    InputCorrespondenceSet,
    InputRelationKind,
    SideParameter,
)
from scripts.function_tracer_pcode.proof.formula.input_correspondence.pairing import (
    build_parameter_pairs,
)
from scripts.function_tracer_pcode.proof.formula.params import collect_param_info
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
from scripts.function_tracer_pcode.semantics.projection_closure import (
    ParameterDemand,
    scan_parameter_demand,
)
from scripts.function_tracer_pcode.semantics.rewrite_contract import (
    RewriteAssumption,
    is_rewritten_surface,
)


#: R3 で試す共通射影幅（固定順、大きい方から採る）。
PROJECTION_CANDIDATE_BITS = (64, 32, 16, 8)


@dataclass
class _SideContext:
    side: str
    analysis: Any
    evidence_by_index: Dict[int, InputExtensionEvidence]
    demands: Dict[Tuple[int, int], ParameterDemand] = field(default_factory=dict)
    _domain_audit: Optional[ParameterDomainAudit] = None

    @property
    def domain_audit(self) -> ParameterDomainAudit:
        """この側の入力領域の監査（analysis が無い補助 relation は正本が無い）。"""

        if self._domain_audit is None:
            self._domain_audit = ParameterDomainAudit.of(self.analysis)
        return self._domain_audit

    def table_defects(self) -> Tuple[str, ...]:
        """表全体の入力領域の欠陥（正本が無い・台帳が読めない・正本の index が消えた）。"""

        return tuple(
            f"{defect.kind}:{self.side}" + (f":{defect.detail}" if defect.detail else "")
            for defect in self.domain_audit.table_defects()
        )

    def demand(self, parameter: SideParameter) -> Optional[ParameterDemand]:
        if self.analysis is None:
            return None
        key = (parameter.index, parameter.bit_width)
        if key not in self.demands:
            self.demands[key] = scan_parameter_demand(self.analysis, parameter.index, parameter.bit_width)
        return self.demands[key]

    def closed_at(self, parameter: SideParameter, bits: int) -> Tuple[bool, Tuple[str, ...]]:
        demand = self.demand(parameter)
        if demand is None:
            return False, ("closure_unavailable",)
        closure = demand.closure(bits)
        return closure.closed, closure.evidence_refs()

    def hidden_inputs(self, parameter: SideParameter, info: ParameterInfo) -> Tuple[str, ...]:
        """どの規則の tie にも入らない入力。1 つでもあれば、その pair は十分性を持たない。

        * closure が見つけた別名の読み（register 別名、未解決 leaf、宣言と幅の違う leaf）。
        * 入力領域を封印した raw baseline で証明できない parameter（Issue #185）: 正本が無い、
          baseline にちょうど 1 つの index が無い、(幅, 符号) が baseline と違う、仮説の台帳に
          記録がある、synthetic の出所を名乗る。名乗り・登録・名前の一致は十分性を与えない。
        """

        demand = self.demand(parameter)
        closure_refs = () if demand is None else tuple(item.as_evidence_ref() for item in demand.hidden_inputs)
        type_class = getattr(info, "type_class", None)
        domain_refs = tuple(
            defect.as_evidence_ref()
            for defect in self.domain_audit.parameter_defects(
                index=info.index,
                bits=info.bit_width,
                signed=info.is_signed,
                synthetic_kind=type_class if type_class in SYNTHETIC_PARAMETER_KINDS else None,
            )
        )
        return closure_refs + domain_refs

    def evidence(self, parameter: SideParameter) -> Optional[InputExtensionEvidence]:
        evidence = self.evidence_by_index.get(parameter.index)
        if evidence is None or int(evidence.storage_bits) != int(parameter.bit_width):
            return None
        return evidence


def _evidence_by_index(
    analysis: Any,
    evidence: Sequence[InputExtensionEvidence],
) -> Dict[int, InputExtensionEvidence]:
    result: Dict[int, InputExtensionEvidence] = {}
    if analysis is None:
        return result
    for item in evidence or ():
        if type(item) is not InputExtensionEvidence:
            continue
        binding = analysis_parameter_binding(analysis, item.binding.parameter_index)
        if binding is None or binding != item.binding:
            continue
        result[int(item.binding.parameter_index)] = item
    return result


def _side_parameter(info: Optional[ParameterInfo]) -> Optional[SideParameter]:
    if info is None:
        return None
    return SideParameter(int(info.index), int(info.bit_width), str(info.original_name))


def _extension_bound(
    left: SideParameter,
    right: SideParameter,
    contexts: Mapping[str, _SideContext],
) -> Optional[InputCorrespondence]:
    """R1 / R2 / R2'。IEE が無ければ None。"""

    left_iee = contexts[LEFT].evidence(left)
    right_iee = contexts[RIGHT].evidence(right)
    if left_iee is None and right_iee is None:
        return None

    def assumption(side: str, parameter: SideParameter, iee: InputExtensionEvidence):
        return (
            side,
            RewriteAssumption(parameter.index, parameter.bit_width, int(iee.logical_bits), iee.kind),
        )

    if left_iee is not None and right_iee is not None:
        if int(left_iee.logical_bits) != int(right_iee.logical_bits):
            return None
        bits = int(left_iee.logical_bits)
        return InputCorrespondence(
            left, right, InputRelationKind.EXTENSION_BOUND, "R1", bits,
            (assumption(LEFT, left, left_iee), assumption(RIGHT, right, right_iee)),
            True,
            ("iee:left", "iee:right"),
        )

    iee_side, iee_param, iee, other_side, other_param = (
        (LEFT, left, left_iee, RIGHT, right)
        if left_iee is not None
        else (RIGHT, right, right_iee, LEFT, left)
    )
    bits = int(iee.logical_bits)
    ordered = lambda first, second: (first, second) if iee_side == LEFT else (second, first)
    if other_param.bit_width == bits:
        return InputCorrespondence(
            *ordered(iee_param, other_param), InputRelationKind.EXTENSION_BOUND, "R2", bits,
            (assumption(iee_side, iee_param, iee),), True, (f"iee:{iee_side}",),
        )
    if bits < other_param.bit_width:
        closed, _refs = contexts[other_side].closed_at(other_param, bits)
        if closed:
            return InputCorrespondence(
                *ordered(iee_param, other_param), InputRelationKind.EXTENSION_BOUND, "R2'", bits,
                (assumption(iee_side, iee_param, iee),), True,
                (f"iee:{iee_side}", f"closure:{other_side}@{bits}"),
            )
    return None


def _relation_for_pair(
    left_info: Optional[ParameterInfo],
    right_info: Optional[ParameterInfo],
    contexts: Mapping[str, _SideContext],
) -> InputCorrespondence:
    left = _side_parameter(left_info)
    right = _side_parameter(right_info)
    # R0
    if left is None or right is None:
        present = LEFT if left is not None else RIGHT
        return InputCorrespondence(
            left, right, InputRelationKind.MISSING_SIDE, "R0", 0, (), False,
            (f"missing_side:only_{present}",),
        )

    # 同じ入力を別名で読む箇所（register 別名、未解決 leaf、宣言と幅の違う leaf）は
    # どの規則の tie にも入らない。どの relation になっても十分性を持たない。
    hidden = tuple(
        f"{side}:{ref}"
        for side, parameter, info in ((LEFT, left, left_info), (RIGHT, right, right_info))
        for ref in contexts[side].hidden_inputs(parameter, info)
    )

    # R1 / R2 / R2'
    bound = _extension_bound(left, right, contexts)
    if bound is not None:
        if hidden:
            return replace(bound, decisive_sufficient=False, evidence=("hidden_input", *hidden))
        return bound

    min_bits = min(left.bit_width, right.bit_width)

    # R3: 両側 raw closure が共通幅 N (< min W) で成立するときの最大 N
    for bits in PROJECTION_CANDIDATE_BITS:
        if not (0 < bits < min_bits):
            continue
        left_closed, _ = contexts[LEFT].closed_at(left, bits)
        right_closed, _ = contexts[RIGHT].closed_at(right, bits)
        if left_closed and right_closed:
            if hidden:
                return InputCorrespondence(
                    left, right, InputRelationKind.SEMANTIC_PROJECTION, "R3", bits, (), False,
                    ("hidden_input", *hidden),
                )
            return InputCorrespondence(
                left, right, InputRelationKind.SEMANTIC_PROJECTION, "R3", bits, (), True,
                (f"closure:left@{bits}", f"closure:right@{bits}"),
            )

    # R4
    if left.bit_width == right.bit_width:
        if hidden:
            return InputCorrespondence(
                left, right, InputRelationKind.FULL_REGISTER_EQUALITY, "R4", left.bit_width, (), False,
                ("hidden_input", *hidden),
            )
        return InputCorrespondence(
            left, right, InputRelationKind.FULL_REGISTER_EQUALITY, "R4", left.bit_width, (), True, (),
        )

    # R5
    wide_side, wide = (LEFT, left) if left.bit_width > right.bit_width else (RIGHT, right)
    closed, refs = contexts[wide_side].closed_at(wide, min_bits)
    if hidden:
        return InputCorrespondence(
            left, right, InputRelationKind.WIDTH_OVERLAP, "R5", min_bits, (), False,
            ("hidden_input", *hidden),
        )
    if closed:
        return InputCorrespondence(
            left, right, InputRelationKind.WIDTH_OVERLAP, "R5", min_bits, (), True,
            (f"closure:{wide_side}@{min_bits}",),
        )
    return InputCorrespondence(
        left, right, InputRelationKind.WIDTH_OVERLAP, "R5", min_bits, (), False,
        (f"wide_side_not_closed:{wide_side}@{min_bits}", *refs[:4]),
    )


def _structural_defects(
    params1: Sequence[ParameterInfo],
    params2: Sequence[ParameterInfo],
    pairs: Sequence[Any],
) -> Tuple[str, ...]:
    defects: List[str] = []
    for side, params in ((LEFT, params1), (RIGHT, params2)):
        indices = [param.index for param in params]
        if len(indices) != len(set(indices)):
            defects.append(f"duplicate_parameter_index:{side}")
        if any(int(index) < 0 for index in indices):
            defects.append(f"negative_parameter_index:{side}")
    seen1: set = set()
    seen2: set = set()
    for pair in pairs:
        for seen, param, side in ((seen1, pair.param1, LEFT), (seen2, pair.param2, RIGHT)):
            if param is None:
                continue
            if id(param) in seen:
                defects.append(f"parameter_paired_twice:{side}:{param.index}")
            seen.add(id(param))
    for side, params, seen in ((LEFT, params1, seen1), (RIGHT, params2, seen2)):
        for param in params:
            if id(param) not in seen:
                defects.append(f"parameter_unpaired:{side}:{param.index}")
    return tuple(defects)


class RawAnalysisRequiredError(TypeError):
    """最終 relation を書き換え済み analysis から作ろうとした（closure の循環）。"""


def build_input_correspondence_set(
    analysis1: Any,
    analysis2: Any,
    *,
    input_extension_evidence: Sequence[InputExtensionEvidence] = (),
) -> InputCorrespondenceSet:
    """raw analysis 2 つと validator 済み IEE から最終 relation set を作る唯一の入口。

    ``analysis1`` / ``analysis2`` は semantic-width 書き換え **前** の raw でなければ
    ならない。closure をそこで判定するためで、書き換え済み surface（normalizer や
    出力面の揃えが作った analysis）を渡すと ``RawAnalysisRequiredError``。
    """

    for analysis in (analysis1, analysis2):
        if is_rewritten_surface(analysis):
            raise RawAnalysisRequiredError("input_correspondence_requires_raw_analysis")
    params1 = collect_param_info(list(getattr(analysis1, "parameters", None) or []), "_1")
    params2 = collect_param_info(list(getattr(analysis2, "parameters", None) or []), "_2")
    contexts = {
        LEFT: _SideContext(LEFT, analysis1, _evidence_by_index(analysis1, input_extension_evidence)),
        RIGHT: _SideContext(RIGHT, analysis2, _evidence_by_index(analysis2, input_extension_evidence)),
    }
    return _build_set(params1, params2, contexts)


def rebuild_input_correspondence_set(
    previous: InputCorrespondenceSet,
    analysis1: Any,
    analysis2: Any,
    *,
    input_extension_evidence: Sequence[InputExtensionEvidence] = (),
) -> InputCorrespondenceSet:
    """``previous`` と同じ raw pair の relation を、pairing・R0〜R5・closure 走査から作り直す。

    certificate の独立検査用。parameter 表だけは ``previous`` が同じ raw descriptor から
    抽出したものを使う（抽出は Ghidra の型 object に問い合わせるので、繰り返すと
    記録済み Ghidra 出力の再生と食い違う）。relation の判定そのもの（closure・規則）は
    全部やり直す。
    """

    for analysis in (analysis1, analysis2):
        if is_rewritten_surface(analysis):
            raise RawAnalysisRequiredError("input_correspondence_requires_raw_analysis")
    contexts = {
        LEFT: _SideContext(LEFT, analysis1, _evidence_by_index(analysis1, input_extension_evidence)),
        RIGHT: _SideContext(RIGHT, analysis2, _evidence_by_index(analysis2, input_extension_evidence)),
    }
    return _build_set(list(previous.left_parameters), list(previous.right_parameters), contexts)


def build_tie_only_correspondence_set(
    params1: Sequence[ParameterInfo],
    params2: Sequence[ParameterInfo],
) -> InputCorrespondenceSet:
    """analysis の無い補助証明（call effect の UNSAT 側 obligation）用の relation。

    同じ pairing と R0〜R5 を使うが、closure も IEE も与えないので R3 / R1 / R2 は
    成立せず、extension 仮定は含意されない（最終 relation の tie だけへの弱め）。
    premise が入力領域を狭めないので、UNSAT はどの入力についても成り立つ。analysis が
    無いので入力領域の正本も無く（Issue #185）、この set は常に不十分: SAT を確定に
    使ってはいけない（決定の authority は raw pair の最終 relation だけ）。
    """

    contexts = {
        LEFT: _SideContext(LEFT, None, {}),
        RIGHT: _SideContext(RIGHT, None, {}),
    }
    return _build_set(list(params1), list(params2), contexts)


def _build_set(
    params1: Sequence[ParameterInfo],
    params2: Sequence[ParameterInfo],
    contexts: Mapping[str, _SideContext],
) -> InputCorrespondenceSet:
    pairs = build_parameter_pairs(list(params1), list(params2))
    correspondences = tuple(
        _relation_for_pair(pair.param1, pair.param2, contexts)
        for pair in pairs
    )
    # 表全体の入力領域の欠陥は pair が 1 つも無い（EMPTY）ときも set を不十分にする:
    # 「入力が 0 個」も正本で証明される主張（Issue #185）。
    domain_defects = contexts[LEFT].table_defects() + contexts[RIGHT].table_defects()
    return InputCorrespondenceSet(
        correspondences=correspondences,
        left_parameter_count=len(params1),
        right_parameter_count=len(params2),
        structural_defects=_structural_defects(params1, params2, pairs) + domain_defects,
        left_parameters=tuple(params1),
        right_parameters=tuple(params2),
    )

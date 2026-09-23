# -*- coding: utf-8 -*-
"""最終 ``InputCorrespondence``（parameter 入力の対応関係）の唯一の owner（Issue #167）。

比較する 2 関数の parameter をどう結び付けるか（premise）、どの入力 extension
仮定が成り立つか（entailed assumptions）、それを使う書き換えの許可
（``RewriteAuthorization``）、SAT / UNSAT を最終判定に使ってよいか
（``decisive_sufficient``）は、全部ここで決める 1 つの relation から導出する。
consumer（SMT header、normalizer、decisive gate、診断）は結果だけを受け取り、
自分で case 分岐を持たない。

順序が本質（v5 §4.3）:

1. raw analysis（semantic-width 書き換え前）から ``ProjectionClosure`` を作る
   （``semantics/projection_closure.py``、hint 非依存）。
2. ``InputExtensionEvidence``（IEE）は validator を通ったものだけを受け取る。
3. parameter pair ごとに R0〜R5（v5 §4.5）で最終 relation を 1 つ決める。
4. その relation から premise / entailed / authorization / 十分性を導出する。

side ごとの authorization を先に normalizer へ渡してはいけない。fallback で最終
relation から extension 仮定が消えたら、それに依存する書き換えも同時に消える
必要がある（v5 §0.2）。この module はその順序を型で固定する: authorization は
``InputCorrespondenceSet.authorization`` からしか作れない値として扱う。
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from enum import Enum
import hashlib
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.proof.formula.params import (
    build_parameter_pairs,
    collect_param_info,
)
from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
from scripts.function_tracer_pcode.semantics.projection_closure import (
    ParameterDemand,
    scan_parameter_demand,
)
from scripts.function_tracer_pcode.semantics.projection_contract import (
    ExtensionKind,
    RewriteAssumption,
    RewriteAuthorization,
)


LEFT = "left"
RIGHT = "right"
_SIDES = (LEFT, RIGHT)

#: 1 pair の不足理由として evidence ref に載せる witness の数（先頭から）。
_EVIDENCE_REF_ITEMS = 4

#: R3 で試す共通射影幅（固定順、大きい方から採る）。
PROJECTION_CANDIDATE_BITS = (64, 32, 16, 8)


def _digest(payload: Any) -> str:
    return hashlib.sha256(repr(payload).encode("utf-8")).hexdigest()


# ---------------------------------------------------------------------------
# InputExtensionEvidence（ABI 規約・適用対象・出所の 3 命題）
# ---------------------------------------------------------------------------


_IEE_TOKEN = object()
_TRUSTED_CLASSIFICATION_TOKEN = object()


@dataclass(frozen=True)
class ParameterBinding:
    """証拠が指す binary / function / parameter。3 命題はこれが一致して初めて結合する。"""

    binary_id: str
    function_identity: str
    parameter_index: int

    def __post_init__(self) -> None:
        if not self.binary_id or not self.function_identity or int(self.parameter_index) < 0:
            raise ValueError("parameter binding requires binary, function and index")


@dataclass(frozen=True)
class AbiExtensionRule:
    """ABI 規約: その ABI では、この register class の引数がこの形で拡張される。

    規約だけでは「この parameter の元の宣言幅」は分からない（v5 §0.1）。
    ``logical_bits`` / ``is_signed`` はこの規則が適用される宣言型の条件であり、
    parameter がその型であることは ``TrustedParameterClassification`` が別に示す。
    """

    abi_id: str
    binary_id: str
    register_class: str
    storage_bits: int
    logical_bits: int
    is_signed: Optional[bool]
    kind: ExtensionKind
    source_reference: str

    def applies_to(self, logical_bits: int, is_signed: bool) -> bool:
        if int(logical_bits) != int(self.logical_bits):
            return False
        return self.is_signed is None or bool(is_signed) == self.is_signed


@dataclass(frozen=True, init=False)
class TrustedParameterClassification:
    """build identity に結び付いた信頼済み signature から得た parameter の元の宣言型。

    Ghidra の推論型、usage hint、返却幅の証明、手動で付けた未検証型は **これに
    ならない**。production にはまだこれを発行する経路が無い（v5 §4.4）ので、
    値は封印 token を持つ trusted adapter からしか作れない。
    """

    binding: ParameterBinding
    logical_bits: int
    is_signed: bool
    type_class: str
    provenance_kind: str
    provenance_digest: str

    def __init__(
        self,
        binding: ParameterBinding,
        logical_bits: int,
        is_signed: bool,
        type_class: str,
        provenance_kind: str,
        provenance_digest: str,
        *,
        _factory_token: object = None,
    ) -> None:
        if _factory_token is not _TRUSTED_CLASSIFICATION_TOKEN:
            raise ValueError("trusted parameter classifications are adapter-issued")
        if not provenance_kind or not provenance_digest:
            raise ValueError("trusted parameter classification requires provenance")
        object.__setattr__(self, "binding", binding)
        object.__setattr__(self, "logical_bits", int(logical_bits))
        object.__setattr__(self, "is_signed", bool(is_signed))
        object.__setattr__(self, "type_class", str(type_class))
        object.__setattr__(self, "provenance_kind", str(provenance_kind))
        object.__setattr__(self, "provenance_digest", str(provenance_digest))


@dataclass(frozen=True)
class StorageObservation:
    """当該 parameter の物理 storage（register slice）の観測。"""

    binding: ParameterBinding
    register_name: str
    register_class: str
    bit_offset: int
    storage_bits: int
    base_register_bits: int


@dataclass(frozen=True, init=False)
class InputExtensionEvidence:
    """validator が 3 命題を同じ parameter に結合できたときだけ存在する証拠。

    意味: parameter（幅 ``storage_bits``）の値は常に
    ``ext_kind(low_{logical_bits}(value))``。
    """

    binding: ParameterBinding
    logical_bits: int
    storage_bits: int
    kind: ExtensionKind
    abi_id: str
    classification_provenance_digest: str
    storage_register: str

    def __init__(self, *args: Any, _factory_token: object = None, **kwargs: Any) -> None:
        if _factory_token is not _IEE_TOKEN:
            raise ValueError("input extension evidence is issued only by the validator")
        values = dict(zip(
            (
                "binding", "logical_bits", "storage_bits", "kind", "abi_id",
                "classification_provenance_digest", "storage_register",
            ),
            args,
        ))
        values.update(kwargs)
        for name, value in values.items():
            object.__setattr__(self, name, value)

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "input_extension_evidence_v1",
            self.binding.binary_id,
            self.binding.function_identity,
            int(self.binding.parameter_index),
            int(self.logical_bits),
            int(self.storage_bits),
            self.kind.value,
            self.abi_id,
            self.classification_provenance_digest,
            self.storage_register,
        )


@dataclass(frozen=True)
class InputExtensionRefusal:
    """IEE を発行しなかった理由（どの命題が欠けた / 食い違ったか）。"""

    binding: Optional[ParameterBinding]
    reasons: Tuple[str, ...]


def validate_input_extension_evidence(
    rule: Optional[AbiExtensionRule],
    classification: Optional[TrustedParameterClassification],
    storage: Optional[StorageObservation],
) -> Tuple[Optional[InputExtensionEvidence], Tuple[str, ...]]:
    """3 命題を独立に検査し、全部が同じ parameter に結合できたときだけ IEE を返す。"""

    reasons: List[str] = []
    if rule is None:
        reasons.append("abi_rule_missing")
    if classification is None:
        reasons.append("trusted_classification_missing")
    elif type(classification) is not TrustedParameterClassification:
        reasons.append("classification_not_trusted")
    if storage is None:
        reasons.append("storage_observation_missing")
    if reasons:
        return None, tuple(reasons)

    if classification.binding != storage.binding:
        reasons.append("classification_storage_binding_mismatch")
    if rule.binary_id != storage.binding.binary_id:
        reasons.append("abi_rule_binary_mismatch")
    if rule.register_class != storage.register_class:
        reasons.append("register_class_mismatch")
    if storage.bit_offset != 0:
        reasons.append("storage_not_low_slice")
    if storage.storage_bits != rule.storage_bits or storage.base_register_bits != rule.storage_bits:
        reasons.append("storage_width_mismatch")
    if classification.type_class != "int":
        reasons.append("classification_not_integral")
    if not (0 < classification.logical_bits < storage.storage_bits):
        reasons.append("no_extension_between_logical_and_storage")
    if not rule.applies_to(classification.logical_bits, classification.is_signed):
        reasons.append("abi_rule_not_applicable_to_declared_type")
    if reasons:
        return None, tuple(reasons)

    evidence = InputExtensionEvidence(
        storage.binding,
        classification.logical_bits,
        storage.storage_bits,
        rule.kind,
        rule.abi_id,
        classification.provenance_digest,
        storage.register_name,
        _factory_token=_IEE_TOKEN,
    )
    return evidence, ()


def analysis_parameter_binding(analysis: Any, parameter_index: int) -> Optional[ParameterBinding]:
    """analysis の binary / function identity に parameter を結び付ける。"""

    binary_id = getattr(analysis, "binary_id", None)
    function_ref = getattr(analysis, "function_ref", None)
    function_identity = None
    if function_ref is not None:
        stable_key = getattr(function_ref, "stable_key", None)
        function_identity = repr(stable_key()) if callable(stable_key) else None
    if not binary_id or not function_identity or int(parameter_index) < 0:
        return None
    return ParameterBinding(str(binary_id), function_identity, int(parameter_index))


# ---------------------------------------------------------------------------
# relation
# ---------------------------------------------------------------------------


class InputRelationKind(str, Enum):
    FULL_REGISTER_EQUALITY = "FULL_REGISTER_EQUALITY"
    WIDTH_OVERLAP = "WIDTH_OVERLAP"
    SEMANTIC_PROJECTION = "SEMANTIC_PROJECTION"
    EXTENSION_BOUND = "EXTENSION_BOUND"
    MISSING_SIDE = "MISSING_SIDE"


@dataclass(frozen=True)
class SideParameter:
    index: int
    bit_width: int
    name: str


@dataclass(frozen=True)
class InputCorrespondence:
    """1 parameter pair の最終 relation と、それから導出される全ての値。"""

    left: Optional[SideParameter]
    right: Optional[SideParameter]
    kind: InputRelationKind
    rule: str
    tie_bits: int
    entailed: Tuple[Tuple[str, RewriteAssumption], ...]
    decisive_sufficient: bool
    evidence: Tuple[str, ...] = field(default_factory=tuple)

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "input_correspondence_v1",
            None if self.left is None else (self.left.index, self.left.bit_width),
            None if self.right is None else (self.right.index, self.right.bit_width),
            self.kind.value,
            self.rule,
            int(self.tie_bits),
            tuple((side, item.stable_key()) for side, item in self.entailed),
            bool(self.decisive_sufficient),
            tuple(self.evidence),
        )

    @property
    def label(self) -> str:
        left = "-" if self.left is None else str(self.left.index)
        right = "-" if self.right is None else str(self.right.index)
        return f"param[{left},{right}]"

    def premise_lines(self, left_smt: Optional[str], right_smt: Optional[str]) -> List[str]:
        """この relation の SMT premise。tie と entailed な extension 制約だけ。"""

        if self.kind is InputRelationKind.MISSING_SIDE:
            return [f"; {self.label}: missing in one function (no premise)"]
        left_bits = self.left.bit_width
        right_bits = self.right.bit_width
        lines = [f"; {self.label} {left_smt} ({left_bits}bit) ~ {right_smt} ({right_bits}bit): {self.kind.value} rule {self.rule}"]
        if self.kind is InputRelationKind.FULL_REGISTER_EQUALITY:
            lines.append(f"(assert (= {left_smt} {right_smt}))")
        elif self.kind is InputRelationKind.WIDTH_OVERLAP:
            if left_bits < right_bits:
                lines.append(f"(assert (= {left_smt} {_low(right_smt, right_bits, left_bits)}))")
            else:
                lines.append(f"(assert (= {_low(left_smt, left_bits, right_bits)} {right_smt}))")
        else:
            bits = self.tie_bits
            lines.append(
                f"(assert (= {_low(left_smt, left_bits, bits)} {_low(right_smt, right_bits, bits)}))"
            )
        for side, assumption in self.entailed:
            name = left_smt if side == LEFT else right_smt
            lines.append(extension_assumption_line(name, assumption))
        return lines


def _low(name: Optional[str], width: int, bits: int) -> str:
    if int(width) == int(bits):
        return str(name)
    return f"((_ extract {int(bits) - 1} 0) {name})"


def extension_assumption_line(smt_name: str, assumption: RewriteAssumption) -> str:
    """entailed な ``p == ext(low_N(p))`` を SMT に描く唯一の関数。"""

    extend = assumption.parameter_bits - assumption.narrow_bits
    return (
        f"(assert (= {smt_name} ((_ {assumption.kind.smt_operator} {extend}) "
        f"((_ extract {assumption.narrow_bits - 1} 0) {smt_name}))))"
    )


class InputCorrespondenceStatus(str, Enum):
    COMPLETE = "COMPLETE"
    EMPTY = "EMPTY"
    INSUFFICIENT = "INSUFFICIENT"


@dataclass(frozen=True)
class InputCorrespondenceSet:
    """全 parameter pair の最終 relation。premise・authorization・十分性の唯一の出所。"""

    correspondences: Tuple[InputCorrespondence, ...]
    left_parameter_count: int
    right_parameter_count: int
    structural_defects: Tuple[str, ...] = ()
    #: relation を決めたときの parameter 表（pairing と同じ値）。SMT 式を組む側は
    #: これを ``parameter_infos`` で受け取り、Ghidra の型 object から作り直さない。
    left_parameters: Tuple[ParameterInfo, ...] = field(default=(), compare=False, repr=False)
    right_parameters: Tuple[ParameterInfo, ...] = field(default=(), compare=False, repr=False)

    @property
    def digest(self) -> str:
        return _digest(
            (
                "input_correspondence_set_v1",
                int(self.left_parameter_count),
                int(self.right_parameter_count),
                tuple(item.stable_key() for item in self.correspondences),
                tuple(self.structural_defects),
            )
        )

    @property
    def status(self) -> InputCorrespondenceStatus:
        if self.structural_defects:
            return InputCorrespondenceStatus.INSUFFICIENT
        if self.left_parameter_count == 0 and self.right_parameter_count == 0 and not self.correspondences:
            return InputCorrespondenceStatus.EMPTY
        if not self.correspondences:
            # 片側にだけ parameter がある、または pairing が 1 件も作れなかった。
            return InputCorrespondenceStatus.INSUFFICIENT
        if all(item.decisive_sufficient for item in self.correspondences):
            return InputCorrespondenceStatus.COMPLETE
        return InputCorrespondenceStatus.INSUFFICIENT

    @property
    def decisive_sufficient(self) -> bool:
        return self.status is not InputCorrespondenceStatus.INSUFFICIENT

    def insufficiency_evidence(self) -> Tuple[str, ...]:
        refs = [f"input_correspondence:{defect}" for defect in self.structural_defects]
        if not self.correspondences and not (
            self.left_parameter_count == 0 and self.right_parameter_count == 0
        ):
            refs.append("input_correspondence:no_parameter_pairs")
        for item in self.correspondences:
            if item.decisive_sufficient:
                continue
            detail = "|".join(item.evidence[:_EVIDENCE_REF_ITEMS]) if item.evidence else "insufficient"
            refs.append(f"input_correspondence:{item.label}:{item.kind.value}:{detail}")
        return tuple(refs)

    def authorization(self, side: str) -> RewriteAuthorization:
        if side not in _SIDES:
            raise ValueError(f"unknown side: {side!r}")
        return RewriteAuthorization(
            assumptions=tuple(
                assumption
                for item in self.correspondences
                for entailed_side, assumption in item.entailed
                if entailed_side == side
            ),
            source_digest=self.digest,
        )

    def parameter_infos(self, side: str, suffix: str) -> List[ParameterInfo]:
        """この relation の parameter 表の複製（SMT 名は ``suffix``、entailed 仮定付き）。"""

        if side not in _SIDES:
            raise ValueError(f"unknown side: {side!r}")
        stored = self.left_parameters if side == LEFT else self.right_parameters
        return [
            replace(
                param,
                smt_name=f"{param.original_name}{suffix}",
                entailed_extension=self.entailed_assumption(side, param.index),
            )
            for param in stored
        ]

    def entailed_assumption(self, side: str, parameter_index: int) -> Optional[RewriteAssumption]:
        for item in self.correspondences:
            for entailed_side, assumption in item.entailed:
                if entailed_side == side and assumption.parameter_index == parameter_index:
                    return assumption
        return None

    def premise_lines(
        self,
        params1: Sequence[ParameterInfo],
        params2: Sequence[ParameterInfo],
    ) -> List[str]:
        """SMT header の parameter premise。名前は caller の ``ParameterInfo`` から引く。"""

        by_index1 = {param.index: param for param in params1}
        by_index2 = {param.index: param for param in params2}
        lines = [
            "; " + "-" * 40,
            f"; Parameter input correspondence ({self.status.value}, {self.digest[:16]})",
            "; " + "-" * 40,
        ]
        for item in self.correspondences:
            left_smt = _bound_smt_name(item.left, by_index1)
            right_smt = _bound_smt_name(item.right, by_index2)
            lines.extend(item.premise_lines(left_smt, right_smt))
        lines.append("")
        return lines

    def kind_counts(self) -> Dict[str, int]:
        counts: Dict[str, int] = {}
        for item in self.correspondences:
            counts[item.kind.value] = counts.get(item.kind.value, 0) + 1
        return counts

    def diagnostic_line(self) -> str:
        """診断専用の 1 行（判定には使わない。authority はこの set の値そのもの）。"""

        relations = ", ".join(
            f"{item.label}={item.kind.value}/{item.rule}/tie{item.tie_bits}"
            + (f"/entailed:{'+'.join(side for side, _ in item.entailed)}" if item.entailed else "")
            for item in self.correspondences
        )
        return (
            f"Input correspondence: status={self.status.value} digest={self.digest[:16]} "
            f"relations=[{relations}] insufficiency={list(self.insufficiency_evidence())}"
        )


def _bound_smt_name(side: Optional[SideParameter], by_index: Mapping[int, ParameterInfo]) -> Optional[str]:
    if side is None:
        return None
    param = by_index.get(side.index)
    if param is None or int(param.bit_width) != int(side.bit_width):
        # 同じ descriptor から作った ParameterInfo と食い違うのは内部不整合。
        raise ValueError(f"input_correspondence_parameter_mismatch:{side.index}")
    return param.smt_name


def extension_premise_lines(params: Sequence[ParameterInfo]) -> List[str]:
    """補助 query 用: entailed な extension 仮定だけを描く（hint は使わない）。"""

    lines: List[str] = []
    for param in params:
        assumption = getattr(param, "entailed_extension", None)
        if assumption is None:
            continue
        if int(param.bit_width) != int(assumption.parameter_bits):
            continue
        lines.append(f"; {param.smt_name}: entailed {assumption.kind.value} extension from {assumption.narrow_bits} bits")
        lines.append(extension_assumption_line(param.smt_name, assumption))
    return lines


# ---------------------------------------------------------------------------
# construction（R0〜R5）
# ---------------------------------------------------------------------------


@dataclass
class _SideContext:
    side: str
    analysis: Any
    evidence_by_index: Dict[int, InputExtensionEvidence]
    demands: Dict[Tuple[int, int], ParameterDemand] = field(default_factory=dict)

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

    def hidden_inputs(self, parameter: SideParameter) -> Tuple[str, ...]:
        demand = self.demand(parameter)
        if demand is None:
            return ()
        return tuple(item.as_evidence_ref() for item in demand.hidden_inputs)

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
    left: Optional[SideParameter],
    right: Optional[SideParameter],
    contexts: Mapping[str, _SideContext],
) -> InputCorrespondence:
    # R0
    if left is None or right is None:
        present = LEFT if left is not None else RIGHT
        return InputCorrespondence(
            left, right, InputRelationKind.MISSING_SIDE, "R0", 0, (), False,
            (f"missing_side:only_{present}",),
        )

    # R1 / R2 / R2'
    bound = _extension_bound(left, right, contexts)
    if bound is not None:
        return bound

    min_bits = min(left.bit_width, right.bit_width)

    # R3: 両側 raw closure が共通幅 N (< min W) で成立するときの最大 N
    for bits in PROJECTION_CANDIDATE_BITS:
        if not (0 < bits < min_bits):
            continue
        left_closed, _ = contexts[LEFT].closed_at(left, bits)
        right_closed, _ = contexts[RIGHT].closed_at(right, bits)
        if left_closed and right_closed:
            return InputCorrespondence(
                left, right, InputRelationKind.SEMANTIC_PROJECTION, "R3", bits, (), True,
                (f"closure:left@{bits}", f"closure:right@{bits}"),
            )

    hidden = tuple(
        f"{side}:{ref}"
        for side, parameter in ((LEFT, left), (RIGHT, right))
        for ref in contexts[side].hidden_inputs(parameter)
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


def build_input_correspondence_set(
    analysis1: Any,
    analysis2: Any,
    *,
    input_extension_evidence: Sequence[InputExtensionEvidence] = (),
) -> InputCorrespondenceSet:
    """raw analysis 2 つと validator 済み IEE から最終 relation set を作る。

    ``analysis1`` / ``analysis2`` は semantic-width 書き換え **前** の raw でなければ
    ならない（closure をそこで判定するため）。
    """

    params1 = collect_param_info(list(getattr(analysis1, "parameters", None) or []), "_1")
    params2 = collect_param_info(list(getattr(analysis2, "parameters", None) or []), "_2")
    contexts = {
        LEFT: _SideContext(LEFT, analysis1, _evidence_by_index(analysis1, input_extension_evidence)),
        RIGHT: _SideContext(RIGHT, analysis2, _evidence_by_index(analysis2, input_extension_evidence)),
    }
    return _build_set(params1, params2, contexts)


def build_parameter_only_correspondence_set(
    params1: Sequence[ParameterInfo],
    params2: Sequence[ParameterInfo],
) -> InputCorrespondenceSet:
    """analysis の無い補助証明用（caller parameter だけ）。closure も IEE も無い。

    closure が取れないので R3 / R2' は成立せず、幅の違う pair は十分性を持たない。
    premise は tie だけなので、UNSAT 側の証明に使っても入力領域を狭めない。
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
        _relation_for_pair(_side_parameter(pair.param1), _side_parameter(pair.param2), contexts)
        for pair in pairs
    )
    return InputCorrespondenceSet(
        correspondences=correspondences,
        left_parameter_count=len(params1),
        right_parameter_count=len(params2),
        structural_defects=_structural_defects(params1, params2, pairs),
        left_parameters=tuple(params1),
        right_parameters=tuple(params2),
    )

# -*- coding: utf-8 -*-
"""最終 relation の値と、そこから導出する premise・authorization・十分性。

consumer（SMT header、normalizer、decisive gate、補助 query、診断）はこの値だけを
読み、自分で case 分岐を持たない。値を作るのは ``relation.py`` だけ。
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from enum import Enum
import hashlib
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.proof.formula.types import ParameterInfo
from scripts.function_tracer_pcode.semantics.rewrite_contract import (
    RewriteAssumption,
    RewriteAuthorization,
)


LEFT = "left"
RIGHT = "right"
_SIDES = (LEFT, RIGHT)

#: 1 pair の不足理由として evidence ref に載せる witness の数（先頭から）。
_EVIDENCE_REF_ITEMS = 4


def _digest(payload: Any) -> str:
    return hashlib.sha256(repr(payload).encode("utf-8")).hexdigest()


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
        # 両側の表も入れる: SMT 式の parameter 名と owner を含まない key（index・名前）は表の行で
        # 解決されるので、表（名前を含む）が違えば組の (index, 幅) が同じでも別の比較。組の名前は
        # 表の行の名前なので、表を入れれば組の名前も区別される（plan v4 PR-P）。
        return _digest(
            (
                "input_correspondence_set_v2",
                int(self.left_parameter_count),
                int(self.right_parameter_count),
                tuple(item.stable_key() for item in self.correspondences),
                tuple(self.structural_defects),
                tuple(_parameter_row_key(row) for row in self.left_parameters),
                tuple(_parameter_row_key(row) for row in self.right_parameters),
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

    def covered_input_names(self, side: str) -> frozenset:
        """その側の入力記号のうち、十分な relation が対応を与えるものの名前（parameter 名）。

        decisive gate はこの集合に無い自由入力記号に依存する SAT を確定させない。
        """

        if side not in _SIDES:
            raise ValueError(f"unknown side: {side!r}")
        stored = self.left_parameters if side == LEFT else self.right_parameters
        names_by_index = {param.index: param.original_name for param in stored}
        covered = set()
        for item in self.correspondences:
            if not item.decisive_sufficient or item.kind is InputRelationKind.MISSING_SIDE:
                continue
            parameter = item.left if side == LEFT else item.right
            if parameter is None or parameter.index not in names_by_index:
                continue
            covered.add(names_by_index[parameter.index])
        return frozenset(covered)

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

    def entailed_projection_extension(
        self,
        wide_side: str,
        parameter_index: int,
        wide_bits: int,
        narrow_bits: int,
    ) -> Optional[RewriteAssumption]:
        """同じ index の parameter の wide 側が narrow 側の extension であるという仮定。

        pair の relation が ``EXTENSION_BOUND``（tie = ``narrow_bits``）で、wide 側が
        ``wide_bits``、narrow 側が ``narrow_bits`` の parameter であり、wide 側に
        ``narrow_bits`` からの extension が entail されているときだけ返す。register の
        射影（readonly identity の proof）が使ってよい入力仮定はこれだけ。
        """

        if wide_side not in _SIDES:
            raise ValueError(f"unknown side: {wide_side!r}")
        for item in self.correspondences:
            if item.kind is not InputRelationKind.EXTENSION_BOUND or item.left is None or item.right is None:
                continue
            wide = item.left if wide_side == LEFT else item.right
            narrow = item.right if wide_side == LEFT else item.left
            if (wide.index, narrow.index) != (parameter_index, parameter_index):
                continue
            if (wide.bit_width, narrow.bit_width, item.tie_bits) != (wide_bits, narrow_bits, narrow_bits):
                return None
            assumption = self.entailed_assumption(wide_side, parameter_index)
            if (
                assumption is None
                or assumption.parameter_bits != wide_bits
                or assumption.narrow_bits != narrow_bits
            ):
                return None
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


def _parameter_row_key(row: ParameterInfo) -> Tuple[Any, ...]:
    extension = row.entailed_extension
    return (
        int(row.index),
        str(row.original_name),
        str(row.smt_name),
        int(row.bit_width),
        bool(row.is_signed),
        None if extension is None else extension.stable_key(),
        row.type_class,
        row.abi_register_name,
        row.abi_bank,
        row.abi_bank_ordinal,
    )


def _bound_smt_name(side: Optional[SideParameter], by_index: Mapping[int, ParameterInfo]) -> Optional[str]:
    if side is None:
        return None
    param = by_index.get(side.index)
    if param is None or int(param.bit_width) != int(side.bit_width):
        # 同じ descriptor から作った ParameterInfo と食い違うのは内部不整合。
        raise ValueError(f"input_correspondence_parameter_mismatch:{side.index}")
    return param.smt_name


def shared_entailed_extensions(parameters: Sequence[ParameterInfo]) -> Dict[int, RewriteAssumption]:
    """左右どちらの parameter にもなり得る symbol（補助 query）が引き継ぐ入力仮定。

    ``parameters`` は最終 relation の ``parameter_infos`` の値（左右両側）。symbol は
    (index, 幅) が同じなら左右どちらの parameter にもなり得るので、その (index, 幅) の
    **全ての** parameter が同じ仮定を含意するときだけ引き継ぐ（片側だけの含意を他方へ
    持ち込まない）。semantic hint は入力全体の仮定ではないので読まない。
    """

    by_slot: Dict[Tuple[int, int], List[Optional[RewriteAssumption]]] = {}
    for parameter in parameters or ():
        try:
            slot = (int(getattr(parameter, "index")), int(getattr(parameter, "bit_width")))
        except (TypeError, ValueError):
            continue
        by_slot.setdefault(slot, []).append(getattr(parameter, "entailed_extension", None))
    extensions: Dict[int, RewriteAssumption] = {}
    for (index, bit_width), assumptions in sorted(by_slot.items()):
        first = assumptions[0]
        if first is None or first.parameter_bits != bit_width:
            continue
        if any(assumption != first for assumption in assumptions):
            continue
        current = extensions.get(index)
        if current is None or first.parameter_bits > current.parameter_bits:
            extensions[index] = first
    return extensions


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

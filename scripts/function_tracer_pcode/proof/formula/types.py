# -*- coding: utf-8 -*-
"""FormulaBuilder で共有する軽量データ型。"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple

from scripts.function_tracer_pcode.proof.formula.variable import ExtraVariableAnalysis
from scripts.function_tracer_pcode.semantics.rewrite_contract import RewriteAssumption


@dataclass
class ParameterInfo:
    """パラメータ情報"""

    original_name: str
    smt_name: str
    bit_width: int
    index: int
    is_signed: bool = True
    #: 最終 ``InputCorrespondence`` が含意する ``p == ext(low_N(p))``。
    #: 値を決めるのは ``InputCorrespondenceSet``（``parameter_infos`` と、補助 query の
    #: symbol 用の ``shared_entailed_extensions``）だけ
    #: （Issue #167: semantic hint を入力全体の仮定として使わない）。
    entailed_extension: Optional[RewriteAssumption] = None
    type_class: Optional[str] = None
    abi_register_name: Optional[str] = None
    abi_bank: Optional[str] = None
    abi_bank_ordinal: Optional[int] = None


@dataclass
class ExtraVariableInfo:
    """追加変数情報"""

    original_name: str
    smt_name: str
    bit_width: int
    analysis: Optional[ExtraVariableAnalysis] = None


@dataclass
class ParameterPair:
    """2つの関数間で対応付けたパラメータペア"""

    index: int
    param1: Optional[ParameterInfo]
    param2: Optional[ParameterInfo]

    def has_width_mismatch(self) -> bool:
        if self.param1 is None or self.param2 is None:
            return True
        return self.param1.bit_width != self.param2.bit_width

    def get_overlapping_width(self) -> int:
        if self.param1 is None or self.param2 is None:
            return 0
        return min(self.param1.bit_width, self.param2.bit_width)

@dataclass
class FormulaBuilderResult:
    """SMT式構築の結果"""

    formula: str
    return_var1: str
    return_var2: str
    extra_vars1: List[ExtraVariableInfo]
    extra_vars2: List[ExtraVariableInfo]
    constrained_fragments: List[str]
    param_fragment_constrained: List[str]
    #: 式の parameter premise を決めた最終 ``InputCorrespondenceSet``（Issue #167）。
    #: decisive gate が dispatch frame の relation と同一かを照合する。
    input_correspondence: Any = None


@dataclass
class FormulaBuildContext:
    """FormulaBuilder 内で共有する構築コンテキスト"""

    params1: List[ParameterInfo]
    params2: List[ParameterInfo]
    extra_vars1: List[ExtraVariableInfo]
    extra_vars2: List[ExtraVariableInfo]
    var_analyses1: Dict[str, ExtraVariableAnalysis]
    var_analyses2: Dict[str, ExtraVariableAnalysis]
    input_correspondence: Any
    return_size1: int
    return_size2: int
    smt_logic: str
    header_lines: List[str]
    runtime_unknown_declarations: List[Tuple[str, int]]
    constrained_fragments: List[str]
    param_fragment_constrained: List[str]
    #: Issue #298: 比較の UB 除外（``proof.ub.premise.UbPremise``。無効なら None）
    ub_premise: Any = None

# -*- coding: utf-8 -*-
"""関数解析結果のデータモデル"""

from __future__ import annotations
from dataclasses import dataclass, field, replace
from typing import List, Dict, Optional, Any, TYPE_CHECKING, Tuple

if TYPE_CHECKING:
    from .condition import Condition
    from .expression import Expression
    from ..analysis.signedness import SignednessEvidence
    from ..analysis.effect_summary import EffectSummary
    from .signature import SignatureHypothesis, FunctionSignature
from .signature import (
    get_data_type_display_name,
    is_unsigned_data_type,
    parameters_without_runtime_objects,
)
from .call_target import CallTargetRef, coerce_call_target_ref
from .runtime_refs import DeferredCallRef, UnknownValueRef

@dataclass
class ReturnInfo:
    """単一のreturn文の情報"""
    address: str
    value: Expression
    conditions: List[Condition] = field(default_factory=list)
    branch_index: Optional[int] = None
    pcode_identity: Optional[str] = None
    pcode_order: Optional[int] = None
    pcode_time: Optional[int] = None

    def site_key(self) -> str:
        """return site の安定識別子を返す。"""
        return self.pcode_identity or self.address
    
    def to_dict(self) -> Dict:
        result = {
            "address": self.address,
            "value": self.value.to_dict(),
            "conditions": [c.to_dict() for c in self.conditions],
            "branch_index": self.branch_index,
        }
        if self.pcode_identity is not None:
            result["pcode_identity"] = self.pcode_identity
        if self.pcode_order is not None:
            result["pcode_order"] = self.pcode_order
        if self.pcode_time is not None:
            result["pcode_time"] = self.pcode_time
        return result


@dataclass(init=False)
class DeferredCallInfo:
    """解析時に展開できなかった呼び出しサイトの情報。"""

    deferred_call_ref: DeferredCallRef
    target_ref: CallTargetRef
    arguments: List["Expression"] = field(default_factory=list)
    call_target_expr: Optional["Expression"]
    display_hint: Optional[str]

    def __init__(
        self,
        placeholder_name: Optional[str] = None,
        target_ref=None,
        arguments: Optional[List["Expression"]] = None,
        call_target_expr: Optional["Expression"] = None,
        sequence: Optional[int] = None,
        deferred_call_ref: Optional[DeferredCallRef] = None,
    ) -> None:
        normalized = coerce_call_target_ref(target_ref) or CallTargetRef.unknown()
        self.deferred_call_ref = deferred_call_ref or DeferredCallRef(
            target_ref=normalized,
            sequence=sequence,
        )
        self.target_ref = normalized
        self.arguments = list(arguments or [])
        self.call_target_expr = call_target_expr
        self.display_hint = placeholder_name or self.deferred_call_ref.display_name()

    @property
    def placeholder_name(self) -> str:
        return self.display_hint or self.deferred_call_ref.display_name()

    @property
    def sequence(self) -> Optional[int]:
        return self.deferred_call_ref.sequence

    @property
    def target_name(self) -> str:
        return self.target_ref.display_name()

    @property
    def target_key(self):
        return self.target_ref.analysis_key()

    def identity_key(self):
        target_expr_key = (
            self.call_target_expr.structural_key()
            if self.call_target_expr is not None
            else None
        )
        argument_key = tuple(
            arg.structural_key() if arg is not None else ("none",)
            for arg in (self.arguments or [])
        )
        return (
            "deferred_call",
            self.deferred_call_ref.stable_key(),
            target_expr_key,
            argument_key,
        )

    @property
    def unknown_ref(self) -> UnknownValueRef:
        return UnknownValueRef.deferred_call(
            deferred_call_ref=self.deferred_call_ref,
            target_ref=self.target_ref,
        )

    def to_dict(self) -> Dict[str, Any]:
        result = {
            "placeholder_name": self.placeholder_name,
            "target_name": self.target_name,
            "deferred_call_ref": self.deferred_call_ref.to_dict(),
            "target_ref": self.target_ref.to_dict(),
            "unknown_ref": self.unknown_ref.to_dict(),
            "arguments": [arg.to_dict() for arg in self.arguments],
        }
        if self.call_target_expr is not None:
            result["call_target_expr"] = self.call_target_expr.to_dict()
        return result

@dataclass
class SignednessResult:
    """符号性推定の結果（軽量版）"""
    signedness: str = "unknown"  # "signed", "unsigned", "unknown"
    evidence_summary: Dict[str, int] = field(default_factory=dict)
    opcode_counts: Dict[str, int] = field(default_factory=dict)
    excluded_fastpath_count: int = 0
    excluded_opcode_counts: Dict[str, int] = field(default_factory=dict)
    
    def is_signed(self) -> bool:
        return self.signedness == "signed"
    
    def is_unsigned(self) -> bool:
        return self.signedness == "unsigned"
    
    def is_unknown(self) -> bool:
        return self.signedness == "unknown"
    
    def should_fix_to_signed(self) -> bool:
        """
        unsigned型をsigned型に修正すべきかどうか
        
        Returns:
            True: signed証拠があるため修正すべき
            False: 修正すべきでない
        """
        return self.is_signed()
    
    def to_dict(self) -> Dict[str, Any]:
        result = {
            "signedness": self.signedness,
            "evidence_summary": self.evidence_summary,
            "opcode_counts": self.opcode_counts,
        }
        if self.excluded_fastpath_count > 0:
            result["excluded_fastpath_count"] = self.excluded_fastpath_count
            result["excluded_opcode_counts"] = self.excluded_opcode_counts
        return result
    
    @classmethod
    def from_evidence(cls, evidence: 'SignednessEvidence') -> 'SignednessResult':
        """SignednessEvidenceから生成（Phase 2対応）"""
        return cls(
            signedness=evidence.result.value,
            evidence_summary=evidence.get_summary(),
            opcode_counts=evidence.get_opcode_counts(),
            excluded_fastpath_count=len(evidence.excluded_fastpath),
            excluded_opcode_counts=evidence.get_excluded_opcode_counts(),
        )


@dataclass(frozen=True)
class ComparisonSurface:
    """等価性比較で使う値面の記述。

    宣言上の return type と、実際に等価性比較へ流す値面を分離する。
    ``return_value`` は通常の戻り値、``memory_effect`` は void 関数の副作用要約を表す。
    """

    kind: str
    explicit_bit_width: Optional[int] = None
    type_name: Optional[str] = None
    type_obj: Any = None
    use_sign_extension: Optional[bool] = None
    evidence: Dict[str, Any] = field(default_factory=dict)

    def __post_init__(self) -> None:
        if self.kind not in {"return_value", "memory_effect"}:
            raise ValueError(f"Unsupported comparison surface kind: {self.kind}")

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": self.kind,
            "explicit_bit_width": self.explicit_bit_width,
            "type_name": self.type_name,
            "use_sign_extension": self.use_sign_extension,
            "evidence": dict(self.evidence),
        }

@dataclass
class FunctionReturnAnalysis:
    """関数のreturn値解析結果"""
    function_name: str
    entry_point: str
    parameters: List[Dict]
    returns: List[ReturnInfo]
    function_ref: Optional[CallTargetRef] = None
    return_type: Optional[str] = None
    return_type_obj: Any = None
    signedness_result: Optional[SignednessResult] = None
    unknown_event_count: int = 0
    unknown_event_reasons: List[str] = field(default_factory=list)
    analysis_notes: List[str] = field(default_factory=list)
    recovered_from_decompiler: bool = False
    incomplete_control_flow: bool = False
    deferred_calls: Dict[Tuple[Any, ...], DeferredCallInfo] = field(default_factory=dict)
    effect_summary: Optional["EffectSummary"] = None
    signature_hypotheses: List[Dict[str, Any]] = field(default_factory=list)
    comparison_surface: Optional[ComparisonSurface] = None

    def __post_init__(self) -> None:
        if self.function_ref is None:
            entry_offset = None
            try:
                entry_offset = int(str(self.entry_point), 0)
            except Exception:
                entry_offset = None
            self.function_ref = CallTargetRef.from_name(
                self.function_name,
                entry_offset=entry_offset,
            )
        self.normalize_deferred_calls()

    def normalize_deferred_calls(self) -> None:
        if not self.deferred_calls:
            return
        normalized: Dict[Tuple[Any, ...], DeferredCallInfo] = {}
        for key, info in list(self.deferred_calls.items()):
            if isinstance(info, DeferredCallInfo):
                identity = info.deferred_call_ref.stable_key()
                normalized[identity] = info
            else:
                normalized[key] = info
        self.deferred_calls = normalized

    def to_dict(self) -> Dict:
        result = {
            "function_name": self.function_name,
            "entry_point": self.entry_point,
            "function_ref": self.function_ref.to_dict() if self.function_ref is not None else None,
            "parameters": parameters_without_runtime_objects(self.parameters),
            "returns": [r.to_dict() for r in self.returns],
            "return_type": get_data_type_display_name(self.return_type_obj, self.return_type),
            "unknown_event_count": self.unknown_event_count,
            "unknown_event_reasons": list(self.unknown_event_reasons),
            "analysis_notes": list(self.analysis_notes),
            "recovered_from_decompiler": self.recovered_from_decompiler,
            "incomplete_control_flow": self.incomplete_control_flow,
            "deferred_calls": [info.to_dict() for info in self.deferred_calls.values()],
        }
        
        if self.signedness_result:
            result["signedness"] = self.signedness_result.to_dict()
        if self.signature_hypotheses:
            result["signature_hypotheses"] = list(self.signature_hypotheses)
        if self.comparison_surface is not None:
            result["comparison_surface"] = self.comparison_surface.to_dict()
        
        return result
    
    def get_inferred_signedness(self) -> str:
        """推定された符号性を取得"""
        if self.signedness_result:
            return self.signedness_result.signedness
        return "unknown"
    
    def should_fix_return_to_signed(self) -> bool:
        """
        戻り値の型をsignedに修正すべきかどうか
        
        Returns:
            True: unsigned型だがsigned証拠があるため修正すべき
            False: 修正不要
        """
        if self.signedness_result is None:
            return False
        
        # 戻り値の型がunsigned系の場合のみ修正対象
        if (
            get_data_type_display_name(self.return_type_obj, self.return_type)
            and is_unsigned_data_type(self.return_type_obj, self.return_type)
            and self.signedness_result.should_fix_to_signed()
        ):
                return True
        
        return False

    def has_unknown_return(self) -> bool:
        """UNKNOWN 式を含む戻り値候補があるか。"""
        return any(
            getattr(ret.value, "expr_type", None) is not None
            and ret.value.expr_type.name == "UNKNOWN"
            for ret in self.returns
        )

    def _expression_contains_unresolved_value(self, expr) -> bool:
        """式木に solver へ流せない未解決値が残っているかを判定する。"""
        if expr is None:
            return True

        expr_type = getattr(expr, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_type is None or expr_kind is None:
            return True

        if expr_type in {expr_kind.UNKNOWN, expr_kind.CALL}:
            return True

        if expr_type == expr_kind.PHI and expr.value:
            for cond, value in expr.value:
                cond_expr = getattr(cond, "expression", None) if cond is not None else None
                if cond_expr is not None and self._expression_contains_unresolved_value(cond_expr):
                    return True
                if self._expression_contains_unresolved_value(value):
                    return True
            return False

        for operand in getattr(expr, "operands", []) or []:
            if self._expression_contains_unresolved_value(operand):
                return True

        return False

    def has_unresolved_return_value(self) -> bool:
        """ネストした UNKNOWN/CALL を含む戻り値・ガードがあるか。"""
        for ret in self.returns:
            if self._expression_contains_unresolved_value(ret.value):
                return True
            for cond in ret.conditions:
                cond_expr = getattr(cond, "expression", None)
                if cond_expr is not None and self._expression_contains_unresolved_value(cond_expr):
                    return True
        return False

    def _retains_post_state_reads_after_lowering(self, expr, conditions) -> bool:
        """effect summary を使っても object-centric post-state read が残るか。"""
        from ..analysis.effect_summary import (
            expression_contains_post_state_reads,
            lower_post_state_expression_for_smt_if_needed,
        )

        if not expression_contains_post_state_reads(expr):
            return False

        effect_summary = getattr(self, "effect_summary", None)
        effects = getattr(effect_summary, "effects", None) if effect_summary is not None else None
        if not effects:
            return True

        try:
            lowered = lower_post_state_expression_for_smt_if_needed(
                expr,
                conditions,
                effects,
                self.parameters,
            )
        except Exception:
            return True
        return expression_contains_post_state_reads(lowered)

    def has_symbolic_post_state_reads(self) -> bool:
        """戻り値・ガードに SMT lowering 不能な object-centric post-state read が残っているか。"""
        for ret in self.returns:
            if self._retains_post_state_reads_after_lowering(ret.value, ret.conditions):
                return True
            for cond in ret.conditions:
                cond_expr = getattr(cond, "expression", None)
                if cond_expr is not None and self._retains_post_state_reads_after_lowering(
                    cond_expr,
                    ret.conditions,
                ):
                    return True
        return False

    def count_unconditional_returns(self) -> int:
        """条件なしの return 候補数を返す。"""
        return sum(1 for ret in self.returns if not ret.conditions)

    def has_overlapping_unconditional_returns(self) -> bool:
        """条件なし return が複数あり、monolithic 化が危険か。"""
        return self.count_unconditional_returns() > 1

    def should_skip_monolithic_fallback(self) -> bool:
        """解析が不完全で monolithic fallback を避けるべきか。"""
        if "return_case_coverage_gap" in self.analysis_notes:
            return True
        if self.recovered_from_decompiler:
            return False
        if not self.incomplete_control_flow:
            return False
        return self.has_unresolved_return_value() or self.has_overlapping_unconditional_returns()

    def get_signature(self) -> "FunctionSignature":
        """現在の解析結果から有効シグネチャを取得する。"""
        from .signature import FunctionSignature

        return FunctionSignature.from_analysis(self)

    def with_signature_hypothesis(
        self,
        hypothesis: "SignatureHypothesis",
    ) -> "FunctionReturnAnalysis":
        """型仮説を重ねた新しい解析ビューを返す。"""
        if not hypothesis.has_changes():
            return self

        updated_signature, return_changed, param_changed = self.get_signature().apply_hypothesis(
            hypothesis
        )
        if not (return_changed or param_changed):
            return self

        updated_notes = list(self.analysis_notes)
        description = hypothesis.describe()
        if description not in updated_notes:
            updated_notes.append(description)

        updated_hypotheses = list(self.signature_hypotheses)
        updated_hypotheses.append(hypothesis.to_dict())

        return replace(
            self,
            return_type=updated_signature.return_type,
            return_type_obj=updated_signature.return_type_obj,
            parameters=updated_signature.parameters or [],
            analysis_notes=updated_notes,
            signature_hypotheses=updated_hypotheses,
        )

    def get_decisive_sat_unsafety_reasons(self) -> List[str]:
        """
        SAT を「非等価の決め手」として扱うには危険な要因を列挙する。

        UNKNOWN へ倒すべき保守条件のみを返し、UNSAT 証明の利用は妨げない。
        """
        reasons: List[str] = []

        if self.has_unresolved_return_value():
            reasons.append("unresolved_return_value")
        if self.has_symbolic_post_state_reads():
            reasons.append("symbolic_post_state_reads")
        if self.has_overlapping_unconditional_returns():
            reasons.append("overlapping_unconditional_returns")
        if self.incomplete_control_flow and not self.recovered_from_decompiler:
            reasons.append("incomplete_control_flow")

        for note in self.analysis_notes:
            if note in {
                "indirect_control_flow_unresolved",
                "symbolic_post_state_reads",
                "return_case_coverage_gap",
            } and note not in reasons:
                reasons.append(note)

        return reasons

    def _expr_bit_width(self, expr) -> int:
        if expr is None:
            return 0
        try:
            from .render_smt import expression_smt_bit_width

            return max(0, int(expression_smt_bit_width(expr) or 0))
        except Exception:
            pass
        bit_width = getattr(expr, "get_bit_width", None)
        if callable(bit_width):
            try:
                return max(0, int(bit_width() or 0))
            except Exception:
                return 0
        return 0

    def _default_return_bit_width(self) -> int:
        from .signature import get_declared_type_size_bits

        declared_bits = get_declared_type_size_bits(
            getattr(self, "return_type_obj", None),
            self.return_type,
        )
        if declared_bits is not None and int(declared_bits) > 0:
            return int(declared_bits)

        expr_bits = [
            self._expr_bit_width(ret.value)
            for ret in self.returns
            if ret.value is not None
        ]
        expr_bits = [bits for bits in expr_bits if bits > 0]
        if expr_bits:
            return max(expr_bits)
        return 32

    def _derive_void_effect_surface(self) -> Optional[ComparisonSurface]:
        effect_summary = getattr(self, "effect_summary", None)
        synthetic_expr = getattr(effect_summary, "synthetic_expr", None) if effect_summary is not None else None
        if synthetic_expr is None:
            return None

        bit_width = self._expr_bit_width(synthetic_expr)
        if bit_width <= 0:
            bit_width = max(
                (
                    self._expr_bit_width(ret.value)
                    for ret in self.returns
                    if ret.value is not None
                ),
                default=0,
            )
        if bit_width <= 0:
            return None

        evidence = {
            "source": "effect_summary.synthetic_expr",
            "effect_count": len(getattr(effect_summary, "effects", []) or []),
        }
        return ComparisonSurface(
            kind="memory_effect",
            explicit_bit_width=bit_width,
            use_sign_extension=False,
            evidence=evidence,
        )

    def get_comparison_surface(self) -> ComparisonSurface:
        if self.comparison_surface is not None:
            surface = self.comparison_surface
            if surface.explicit_bit_width is not None and int(surface.explicit_bit_width) > 0:
                return surface
            if surface.kind == "memory_effect":
                derived = self._derive_void_effect_surface()
                if derived is not None:
                    merged_evidence = dict(surface.evidence)
                    merged_evidence.update(derived.evidence)
                    return replace(
                        surface,
                        explicit_bit_width=derived.explicit_bit_width,
                        evidence=merged_evidence,
                    )
            return surface

        from .signature import get_data_type_display_name, is_void_data_type

        display_name = get_data_type_display_name(self.return_type_obj, self.return_type)
        if is_void_data_type(self.return_type_obj, display_name):
            derived = self._derive_void_effect_surface()
            if derived is not None:
                return derived

        return ComparisonSurface(
            kind="return_value",
            explicit_bit_width=self._default_return_bit_width(),
            type_name=self.return_type,
            type_obj=self.return_type_obj,
        )

    def get_comparison_bit_width(self) -> int:
        surface = self.get_comparison_surface()
        if surface.explicit_bit_width is not None and int(surface.explicit_bit_width) > 0:
            return int(surface.explicit_bit_width)
        return self._default_return_bit_width()

    def get_comparison_type_name(self) -> Optional[str]:
        surface = self.get_comparison_surface()
        return surface.type_name

    def get_comparison_type_obj(self):
        surface = self.get_comparison_surface()
        return surface.type_obj

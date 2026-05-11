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
from .runtime_refs import DeferredCallRef, PcodeOpRef, UnknownValueRef

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
    pcode_op_ref: Optional[PcodeOpRef] = None

    def site_key(self) -> str:
        """return site の安定識別子を返す。"""
        if self.pcode_op_ref is not None:
            return repr(self.pcode_op_ref.stable_key())
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
        if self.pcode_op_ref is not None:
            result["pcode_op_ref"] = self.pcode_op_ref.to_dict()
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
    ``explicit_bit_width`` は surface-local な幅であり、用途別 API
    (``get_return_value_solver_bit_width`` / ``get_memory_effect_bit_width``)
    を通して解釈する。
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


_SIGNED_COMPARE_TO_UNSIGNED = {
    "INT_SLESS": "INT_LESS",
    "INT_SLESSEQUAL": "INT_LESSEQUAL",
}
_UNSIGNED_COMPARE_TO_SIGNED = {
    "INT_LESS": "INT_SLESS",
    "INT_LESSEQUAL": "INT_SLESSEQUAL",
}
_SIGNEDNESS_TRANSPARENT_UNARY_OPS = {"INT_SEXT", "INT_ZEXT", "CAST", "COPY"}


def _build_param_override_by_index(
    original_parameters: List[Dict[str, Any]],
    updated_parameters: List[Dict[str, Any]],
) -> Dict[int, Dict[str, Any]]:
    overrides: Dict[int, Dict[str, Any]] = {}
    for fallback_index, updated_param in enumerate(updated_parameters or []):
        updated_index = int(updated_param.get("index", fallback_index))
        if fallback_index >= len(original_parameters or []):
            continue
        original_param = original_parameters[fallback_index]
        original_signed = bool(original_param.get("is_signed", True))
        updated_signed = bool(updated_param.get("is_signed", True))
        if original_signed == updated_signed:
            continue
        overrides[updated_index] = updated_param
    return overrides


def _rewrite_conditions_for_param_signedness(
    conditions: List["Condition"],
    param_overrides: Dict[int, Dict[str, Any]],
) -> Tuple[List["Condition"], bool]:
    if not conditions or not param_overrides:
        return list(conditions or []), False

    from .condition import Condition

    rewritten_conditions: List[Condition] = []
    changed = False
    for condition in conditions or []:
        if condition is None or getattr(condition, "expression", None) is None:
            rewritten_conditions.append(condition)
            continue
        rewritten_expr, expr_changed = _rewrite_expression_for_param_signedness(
            condition.expression,
            param_overrides,
        )
        rewritten_conditions.append(Condition(rewritten_expr, bool(getattr(condition, "negated", False))))
        changed = changed or expr_changed
    return rewritten_conditions, changed


def _find_parameter_override_for_expression(
    expr: Optional["Expression"],
    param_overrides: Dict[int, Dict[str, Any]],
) -> Optional[Dict[str, Any]]:
    if expr is None or not param_overrides:
        return None
    expr_type = getattr(expr, "expr_type", None)
    if expr_type is not None and getattr(expr_type, "name", None) == "PARAMETER":
        try:
            param_index = int(getattr(expr, "value", -1))
        except (TypeError, ValueError):
            param_index = -1
        if param_index in param_overrides:
            return param_overrides[param_index]
        return None
    if expr_type is not None and getattr(expr_type, "name", None) == "UNARY_OP":
        if getattr(expr, "operator", None) in _SIGNEDNESS_TRANSPARENT_UNARY_OPS and getattr(expr, "operands", None):
            return _find_parameter_override_for_expression(expr.operands[0], param_overrides)
    return None


def _rewrite_runtime_ref_for_param_signedness(
    runtime_ref: Any,
    param_overrides: Dict[int, Dict[str, Any]],
) -> Tuple[Any, bool]:
    if runtime_ref is None or not param_overrides:
        return runtime_ref, False

    changed = False
    kwargs: Dict[str, Any] = {}

    count_index = getattr(runtime_ref, "count_parameter_index", None)
    try:
        count_index_value = int(count_index) if count_index is not None else None
    except (TypeError, ValueError):
        count_index_value = None
    if count_index_value is not None and count_index_value in param_overrides:
        desired_signed = bool(param_overrides[count_index_value].get("is_signed", True))
        if getattr(runtime_ref, "signed_counter", None) != desired_signed:
            kwargs["signed_counter"] = desired_signed
            changed = True
        if getattr(runtime_ref, "signed_loop", None) != desired_signed and hasattr(runtime_ref, "signed_loop"):
            kwargs["signed_loop"] = desired_signed
            changed = True

    for attr_name in ("start_expr", "limit_expr", "step_expr"):
        if not hasattr(runtime_ref, attr_name):
            continue
        original_expr = getattr(runtime_ref, attr_name, None)
        rewritten_expr, expr_changed = _rewrite_expression_for_param_signedness(
            original_expr,
            param_overrides,
        )
        if expr_changed:
            kwargs[attr_name] = rewritten_expr
            changed = True

    if hasattr(runtime_ref, "guard_constraints"):
        rewritten_guards, guard_changed = _rewrite_conditions_for_param_signedness(
            list(getattr(runtime_ref, "guard_constraints", ()) or ()),
            param_overrides,
        )
        if guard_changed:
            kwargs["guard_constraints"] = tuple(rewritten_guards)
            changed = True

    for attr_name in ("loop_summary", "accumulator_proof"):
        if not hasattr(runtime_ref, attr_name):
            continue
        nested_ref = getattr(runtime_ref, attr_name, None)
        rewritten_ref, nested_changed = _rewrite_runtime_ref_for_param_signedness(
            nested_ref,
            param_overrides,
        )
        if nested_changed:
            kwargs[attr_name] = rewritten_ref
            changed = True

    if not changed:
        return runtime_ref, False
    return replace(runtime_ref, **kwargs), True


def _rewrite_expression_for_param_signedness(
    expr: Optional["Expression"],
    param_overrides: Dict[int, Dict[str, Any]],
) -> Tuple[Optional["Expression"], bool]:
    if expr is None or not param_overrides:
        return expr, False

    from .condition import Condition

    changed = False
    rebuilt = expr
    expr_type = getattr(expr, "expr_type", None)

    if expr_type is not None and getattr(expr_type, "name", None) == "PHI" and getattr(expr, "value", None):
        rewritten_branches = []
        branch_changed = False
        for cond, value in expr.value:
            rewritten_cond = cond
            if cond is not None and getattr(cond, "expression", None) is not None:
                cond_expr, cond_changed = _rewrite_expression_for_param_signedness(
                    cond.expression,
                    param_overrides,
                )
                rewritten_cond = Condition(cond_expr, bool(getattr(cond, "negated", False)))
                branch_changed = branch_changed or cond_changed
            rewritten_value, value_changed = _rewrite_expression_for_param_signedness(
                value,
                param_overrides,
            )
            branch_changed = branch_changed or value_changed
            rewritten_branches.append((rewritten_cond, rewritten_value))
        if branch_changed:
            rebuilt = expr.clone_with(value=rewritten_branches)
            changed = True
    elif getattr(expr, "operands", None):
        rewritten_operands = []
        operand_changed = False
        for operand in expr.operands:
            rewritten_operand, child_changed = _rewrite_expression_for_param_signedness(
                operand,
                param_overrides,
            )
            rewritten_operands.append(rewritten_operand)
            operand_changed = operand_changed or child_changed
        if operand_changed:
            rebuilt = expr.clone_with(operands=rewritten_operands)
            changed = True

    rewritten_runtime_ref, runtime_ref_changed = _rewrite_runtime_ref_for_param_signedness(
        getattr(rebuilt, "runtime_ref", None),
        param_overrides,
    )
    if runtime_ref_changed:
        rebuilt = rebuilt.clone_with(runtime_ref=rewritten_runtime_ref)
        changed = True

    if expr_type is not None and getattr(expr_type, "name", None) == "PARAMETER":
        override_param = _find_parameter_override_for_expression(rebuilt, param_overrides)
        if override_param is not None:
            updated_data_type = override_param.get("data_type")
            updated_data_type_obj = override_param.get("data_type_obj")
            updated_size = int(override_param.get("size", getattr(rebuilt, "size", 0)) or getattr(rebuilt, "size", 0) or 0)
            if (
                updated_data_type != getattr(rebuilt, "data_type", None)
                or updated_data_type_obj is not getattr(rebuilt, "data_type_obj", None)
                or (updated_size > 0 and updated_size != getattr(rebuilt, "size", 0))
            ):
                rebuilt = rebuilt.clone_with(
                    data_type=updated_data_type,
                    data_type_obj=updated_data_type_obj,
                    size=updated_size if updated_size > 0 else getattr(rebuilt, "size", 0),
                )
                changed = True

    if (
        getattr(rebuilt, "expr_type", None) is not None
        and getattr(getattr(rebuilt, "expr_type", None), "name", None) == "BINARY_OP"
        and getattr(rebuilt, "operator", None) in set(_UNSIGNED_COMPARE_TO_SIGNED) | set(_SIGNED_COMPARE_TO_UNSIGNED)
    ):
        from ..analysis.condition.simplifier import ConditionSimplifier

        fact = ConditionSimplifier.extract_scalar_constraint(Condition(rebuilt, False))
        override_param = None if fact is None else _find_parameter_override_for_expression(getattr(fact, "expr", None), param_overrides)
        if override_param is not None:
            desired_signed = bool(override_param.get("is_signed", True))
            if desired_signed and rebuilt.operator in _UNSIGNED_COMPARE_TO_SIGNED:
                rebuilt = rebuilt.clone_with(operator=_UNSIGNED_COMPARE_TO_SIGNED[rebuilt.operator])
                changed = True
            elif not desired_signed and rebuilt.operator in _SIGNED_COMPARE_TO_UNSIGNED:
                rebuilt = rebuilt.clone_with(operator=_SIGNED_COMPARE_TO_UNSIGNED[rebuilt.operator])
                changed = True

    return rebuilt, changed

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
    analysis_scope_key: Optional[Tuple[Any, ...]] = None
    program_is_big_endian: Optional[bool] = None

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
        if self.analysis_scope_key is not None:
            result["analysis_scope_key"] = self.analysis_scope_key
        if self.program_is_big_endian is not None:
            result["program_is_big_endian"] = bool(self.program_is_big_endian)
        
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

    def _iter_expression_nodes(self, expr):
        if expr is None:
            return
        yield expr
        expr_type = getattr(expr, "expr_type", None)
        expr_kind = getattr(expr_type, "__class__", None)
        if expr_kind is not None and expr_type == expr_kind.PHI:
            for cond, value in getattr(expr, "value", None) or []:
                cond_expr = getattr(cond, "expression", None) if cond is not None else None
                if cond_expr is not None:
                    yield from self._iter_expression_nodes(cond_expr)
                yield from self._iter_expression_nodes(value)
            return
        for operand in getattr(expr, "operands", None) or []:
            yield from self._iter_expression_nodes(operand)

    def _expression_has_effect_sensitive_raw_memory_read(self, expr, conditions) -> bool:
        effect_summary = getattr(self, "effect_summary", None)
        effects = getattr(effect_summary, "effects", None) if effect_summary is not None else None
        if not effects:
            return False

        from ..analysis.effect_summary import (
            canonicalize_expr_read_location,
            expression_contains_post_state_reads,
            lower_post_state_expression_for_smt_if_needed,
            locations_match,
        )
        from ..analysis.condition.simplifier import ConditionSimplifier

        scan_expr = expr
        if expression_contains_post_state_reads(expr):
            try:
                lowered = lower_post_state_expression_for_smt_if_needed(
                    expr,
                    conditions,
                    effects,
                    self.parameters,
                )
            except Exception:
                lowered = None
            if lowered is not None:
                scan_expr = lowered

        for node in self._iter_expression_nodes(scan_expr):
            expr_type = getattr(node, "expr_type", None)
            expr_kind = getattr(expr_type, "__class__", None)
            if expr_kind is None or expr_type != expr_kind.MEMORY:
                continue
            if expression_contains_post_state_reads(node):
                continue
            location = canonicalize_expr_read_location(node, self.parameters)
            if location is None:
                continue
            try:
                read_order_key = getattr(node, "read_order_key", None)
                read_order_key = int(read_order_key) if read_order_key is not None else None
            except Exception:
                read_order_key = None
            for effect in effects:
                effect_location = getattr(effect, "location", None)
                if effect_location is None:
                    continue
                if read_order_key is not None:
                    try:
                        effect_order_key = int(getattr(effect, "order_key", 0))
                    except Exception:
                        effect_order_key = 0
                    if effect_order_key >= read_order_key:
                        continue
                combined_conditions = list(conditions or []) + list(getattr(effect, "conditions", None) or [])
                if ConditionSimplifier.object_centric_is_contradiction(combined_conditions):
                    continue
                if not locations_match(
                    location,
                    effect_location,
                    combined_conditions,
                ):
                    continue
                return True
        return False

    def has_effect_sensitive_raw_memory_reads(self) -> bool:
        """store effect と同じ object location を読む raw MEM が return/guard に残っているか。"""
        for ret in self.returns:
            if self._expression_has_effect_sensitive_raw_memory_read(ret.value, ret.conditions):
                return True
            for cond in ret.conditions:
                cond_expr = getattr(cond, "expression", None)
                if cond_expr is not None and self._expression_has_effect_sensitive_raw_memory_read(
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
        if "return_case_coverage_inconclusive" in self.analysis_notes:
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

        updated_returns = list(self.returns or [])
        param_overrides = _build_param_override_by_index(
            list(self.parameters or []),
            list(updated_signature.parameters or []),
        )
        if param_overrides:
            rewritten_returns: List[ReturnInfo] = []
            returns_changed = False
            for info in self.returns or []:
                rewritten_value, value_changed = _rewrite_expression_for_param_signedness(
                    info.value,
                    param_overrides,
                )
                rewritten_conditions, cond_changed = _rewrite_conditions_for_param_signedness(
                    list(info.conditions or []),
                    param_overrides,
                )
                if value_changed or cond_changed:
                    returns_changed = True
                    rewritten_returns.append(
                        replace(
                            info,
                            value=rewritten_value,
                            conditions=rewritten_conditions,
                        )
                    )
                else:
                    rewritten_returns.append(info)
            if returns_changed:
                updated_returns = rewritten_returns

        return replace(
            self,
            return_type=updated_signature.return_type,
            return_type_obj=updated_signature.return_type_obj,
            parameters=updated_signature.parameters or [],
            returns=updated_returns,
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
        if self.has_effect_sensitive_raw_memory_reads():
            reasons.append("effect_sensitive_raw_memory_reads")
        if self.has_overlapping_unconditional_returns():
            reasons.append("overlapping_unconditional_returns")
        if self.incomplete_control_flow and not self.recovered_from_decompiler:
            reasons.append("incomplete_control_flow")
        effect_summary = getattr(self, "effect_summary", None)
        if (
            effect_summary is not None
            and getattr(effect_summary, "has_unsupported_call", False)
        ):
            reasons.append("unsupported_call_effect_summary")
        if effect_summary is not None:
            effect_incomplete_reasons = getattr(effect_summary, "incomplete_reasons", ())
            if not isinstance(effect_incomplete_reasons, (list, tuple, set, frozenset)):
                effect_incomplete_reasons = ()
            for reason in effect_incomplete_reasons:
                if reason not in reasons:
                    reasons.append(reason)

        for note in self.analysis_notes:
            if note in {
                "indirect_control_flow_unresolved",
                "symbolic_post_state_reads",
                "return_case_coverage_gap",
                "return_case_coverage_inconclusive",
                "effect_summary_path_coverage_incomplete",
                "bounded_call_refinement_argument_alignment_failed",
                "bounded_call_refinement_deferred_target_unresolved",
                "bounded_call_refinement_return_summary_unusable",
                "effect_call_argument_evidence_incomplete",
            } and note not in reasons:
                reasons.append(note)

        return reasons

    def get_equivalence_blocking_unsafety_reasons(self) -> List[str]:
        """
        UNSAT を「等価の決め手」として扱うには危険な解析要因を列挙する。

        return value が全ペア UNSAT でも、side-effect summary が不完全なら
        モデル化されていない STORE/CALL 効果を等価証明から落としているため、
        final EQUIVALENT にはしない。
        """
        reasons: List[str] = []
        effect_summary = getattr(self, "effect_summary", None)
        if effect_summary is not None:
            if getattr(effect_summary, "has_unsupported_call", False):
                reasons.append("unsupported_call_effect_summary")
            effect_incomplete_reasons = getattr(effect_summary, "incomplete_reasons", ())
            if not isinstance(effect_incomplete_reasons, (list, tuple, set, frozenset)):
                effect_incomplete_reasons = ()
            for reason in effect_incomplete_reasons:
                if reason not in reasons:
                    reasons.append(reason)

        for note in self.analysis_notes:
            if note in {
                "effect_summary_path_coverage_incomplete",
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

    def _default_return_value_solver_bit_width(self) -> int:
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
            explicit_bit_width=self._default_return_value_solver_bit_width(),
            type_name=self.return_type,
            type_obj=self.return_type_obj,
        )

    def _surface_explicit_bit_width(self, surface: ComparisonSurface) -> Optional[int]:
        try:
            bits = int(surface.explicit_bit_width or 0)
        except (TypeError, ValueError):
            return None
        return bits if bits > 0 else None

    def get_return_value_solver_bit_width(self) -> int:
        """Bit-vector width for the real return-value solver surface."""

        surface = self.get_comparison_surface()
        if surface.kind != "return_value":
            raise ValueError(
                "return_value solver width requested for non-return comparison surface: "
                f"{surface.kind}"
            )
        explicit_bits = self._surface_explicit_bit_width(surface)
        if explicit_bits is not None:
            return explicit_bits
        return self._default_return_value_solver_bit_width()

    def get_memory_effect_bit_width(self) -> int:
        """Bit-vector width of the synthetic memory-effect comparison value."""

        surface = self.get_comparison_surface()
        if surface.kind != "memory_effect":
            raise ValueError(
                "memory_effect width requested for non-memory comparison surface: "
                f"{surface.kind}"
            )
        explicit_bits = self._surface_explicit_bit_width(surface)
        if explicit_bits is not None:
            return explicit_bits
        derived = self._derive_void_effect_surface()
        if derived is not None:
            derived_bits = self._surface_explicit_bit_width(derived)
            if derived_bits is not None:
                return derived_bits
        raise ValueError("memory_effect comparison surface has no positive effect width")

    def get_comparison_bit_width(self, *, purpose: Optional[str] = None) -> int:
        """Legacy compatibility guard for ambiguous comparison widths."""

        if purpose == "return_value_solver":
            return self.get_return_value_solver_bit_width()
        if purpose == "memory_effect":
            return self.get_memory_effect_bit_width()
        raise ValueError(
            "get_comparison_bit_width() is ambiguous; use "
            "get_return_value_solver_bit_width() or get_memory_effect_bit_width()"
        )

    def get_comparison_type_name(self) -> Optional[str]:
        surface = self.get_comparison_surface()
        return surface.type_name

    def get_comparison_type_obj(self):
        surface = self.get_comparison_surface()
        return surface.type_obj

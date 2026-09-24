"""Standalone data models for effect summaries."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, ClassVar, Dict, List, Optional, Sequence, Tuple

from scripts.function_tracer_pcode.core.json_encoding import as_list, each, inline, materialize, source_converter
from scripts.function_tracer_pcode.core import (
    CallTargetRef,
    CanonicalLocation,
    Condition,
    Expression,
    LocationBaseRef,
    PcodeBlockRef,
    PcodeOpRef,
    expression_provenance_key,
)
from scripts.function_tracer_pcode.analysis.effects._api import (
    _bind_location_to_parameter_refs,
    _call_target_ref_analysis_key,
    _call_target_ref_is_resolved,
    _callee_param_identities_are_object_proven,
    _coerce_callee_parameter_ref,
    _condition_evidence_key,
    _normalize_call_argument_recovery_status,
    _stable_target_expression_key,
    _try_get_order_key,
)

_UNKNOWN_EFFECT_ORDER_KEY = -1


class EffectOrderUnavailable(RuntimeError):
    """Raised when a real P-code op cannot provide a conservative order key."""

@dataclass(frozen=True)
class StoreEffectProvenance:
    """Object-derived producer identity for one summarized STORE effect."""

    source_kind: str
    producer_pcode_op_ref: Optional[PcodeOpRef]
    producer_block_ref: Optional[PcodeBlockRef] = None
    call_target_ref: Optional[CallTargetRef] = None
    callee_effect_index: Optional[int] = None
    nested_effect_provenance: Optional["StoreEffectProvenance"] = None

    def is_complete(self) -> bool:
        if self.source_kind not in {"local_store", "call_derived"}:
            return False
        if self.producer_pcode_op_ref is None:
            return False
        if self.producer_block_ref is None:
            return False
        if any(
            getattr(self.producer_pcode_op_ref, attribute, None) is None
            for attribute in (
                "binary_id",
                "function_entry_space",
                "function_entry_offset",
                "target_space",
                "target_offset",
                "seq_time",
                "seq_order",
                "opcode",
            )
        ):
            return False
        if self.source_kind == "call_derived":
            return (
                self.call_target_ref is not None
                and not self.call_target_ref.is_unknown()
                and self.callee_effect_index is not None
                and int(self.callee_effect_index) >= 0
                and self.nested_effect_provenance is not None
                and self.nested_effect_provenance.is_complete()
            )
        return (
            self.call_target_ref is None
            and self.callee_effect_index is None
            and self.nested_effect_provenance is None
        )

    def stable_key(self) -> Tuple[object, ...]:
        return (
            "store_effect_provenance",
            self.source_kind,
            (
                self.producer_pcode_op_ref.stable_key()
                if self.producer_pcode_op_ref is not None
                else None
            ),
            (
                self.producer_block_ref.stable_key()
                if self.producer_block_ref is not None
                else None
            ),
            (
                self.call_target_ref.stable_key()
                if self.call_target_ref is not None
                else None
            ),
            self.callee_effect_index,
            (
                self.nested_effect_provenance.stable_key()
                if self.nested_effect_provenance is not None
                else None
            ),
        )

    def json_items(self):
        yield "source_kind", self.source_kind
        yield "producer_pcode_op_ref", self.producer_pcode_op_ref
        yield "producer_block_ref", self.producer_block_ref
        yield "call_target_ref", self.call_target_ref
        yield "callee_effect_index", self.callee_effect_index
        yield "nested_effect_provenance", self.nested_effect_provenance
        yield "complete", self.is_complete()

    def to_dict(self) -> Dict[str, object]:
        return materialize(self)

@dataclass
class StoreEffect:
    location: CanonicalLocation
    value: Expression
    conditions: List[Condition]
    order_key: int
    provenance: Optional[StoreEffectProvenance] = None

@dataclass(frozen=True)
class UnsupportedCallEffectRef:
    """Object-derived evidence for a call whose effects were not summarized."""

    pcode_op_ref: Optional[PcodeOpRef]
    target_ref: Optional[CallTargetRef]
    reason: str
    order_key: int
    target_expr: Optional[Expression] = None
    arguments: Tuple[Expression, ...] = ()
    path_conditions: Tuple[Condition, ...] = ()

    @classmethod
    def from_call_op(
        cls,
        op,
        *,
        target_ref: Optional[CallTargetRef],
        target_expr: Optional[Expression] = None,
        arguments: Sequence[Expression] = (),
        path_conditions: Sequence[Condition] = (),
        reason: str,
        pcode_op_ref: Optional[PcodeOpRef] = None,
    ) -> "UnsupportedCallEffectRef":
        return cls(
            pcode_op_ref=pcode_op_ref if pcode_op_ref is not None else PcodeOpRef.from_pcode_op(op),
            target_ref=target_ref,
            target_expr=target_expr,
            arguments=tuple(arguments or ()),
            path_conditions=tuple(path_conditions or ()),
            reason=str(reason),
            order_key=_try_get_order_key(op, default=_UNKNOWN_EFFECT_ORDER_KEY),
        )

    def stable_key(self) -> Tuple[object, ...]:
        target_key = self.target_ref.stable_key() if self.target_ref is not None else None
        target_expr_key = _stable_target_expression_key(self.target_expr)
        return (
            "unsupported_call_effect",
            self.pcode_op_ref.stable_key() if self.pcode_op_ref is not None else None,
            target_key,
            target_expr_key,
            tuple(
                (
                    "argument",
                    index,
                    expression_provenance_key(argument),
                )
                for index, argument in enumerate(self.arguments or ())
            ),
            tuple(_condition_evidence_key(condition) for condition in self.path_conditions or ()),
            int(self.order_key),
        )

    def json_items(self):
        yield "kind", "unsupported_call_effect"
        yield "pcode_op_ref", self.pcode_op_ref
        yield "target_ref", self.target_ref
        yield "target_expr", self.target_expr
        yield "arguments", each(self.arguments or ())
        yield "path_conditions", each(self.path_conditions or ())
        yield "reason", self.reason
        yield "order_key", int(self.order_key)

    def to_dict(self) -> Dict[str, object]:
        return materialize(self)

@dataclass(frozen=True)
class CallTargetResolutionEvidence:
    """Object-derived evidence for recovered call target resolution."""

    pcode_op_ref: Optional[PcodeOpRef]
    target_ref: Optional[CallTargetRef]
    target_expr: Optional[Expression]
    resolution_kind: str
    path_condition_keys: Tuple[Tuple[object, ...], ...]
    target_condition_keys: Tuple[Tuple[object, ...], ...]
    order_key: int

    @classmethod
    def from_call_op(
        cls,
        op,
        *,
        target_ref: Optional[CallTargetRef],
        target_expr: Optional[Expression],
        resolution_kind: str,
        path_conditions: Sequence[Condition],
        target_conditions: Sequence[Condition],
        pcode_op_ref: Optional[PcodeOpRef] = None,
    ) -> "CallTargetResolutionEvidence":
        return cls(
            pcode_op_ref=pcode_op_ref if pcode_op_ref is not None else PcodeOpRef.from_pcode_op(op),
            target_ref=target_ref,
            target_expr=target_expr,
            resolution_kind=str(resolution_kind),
            path_condition_keys=tuple(_condition_evidence_key(cond) for cond in path_conditions or ()),
            target_condition_keys=tuple(_condition_evidence_key(cond) for cond in target_conditions or ()),
            order_key=_try_get_order_key(op, default=_UNKNOWN_EFFECT_ORDER_KEY),
        )

    def stable_key(self) -> Tuple[object, ...]:
        return (
            "call_target_resolution_evidence",
            self.pcode_op_ref.stable_key() if self.pcode_op_ref is not None else None,
            self.target_ref.stable_key() if self.target_ref is not None else None,
            _stable_target_expression_key(self.target_expr),
            self.resolution_kind,
            self.path_condition_keys,
            self.target_condition_keys,
            int(self.order_key),
        )

    def json_items(self):
        yield "kind", "call_target_resolution_evidence"
        yield "pcode_op_ref", self.pcode_op_ref
        yield "target_ref", self.target_ref
        yield "target_expr", self.target_expr
        yield "resolution_kind", self.resolution_kind
        yield "path_condition_keys", self.path_condition_keys
        yield "target_condition_keys", self.target_condition_keys
        yield "order_key", int(self.order_key)

    def to_dict(self) -> Dict[str, object]:
        return materialize(self)

@dataclass(frozen=True)
class CallSiteEffectSummaryEvidence:
    """Per-callsite evidence describing whether callee effects were summarized.

    This is memory/effect evidence only.  It does not claim return, termination,
    ABI, or cross-binary equivalence and therefore cannot discharge a blocker by
    itself.
    """

    pcode_op_ref: Optional[PcodeOpRef]
    target_ref: Optional[CallTargetRef]
    argument_keys: Tuple[Tuple[object, ...], ...]
    path_condition_keys: Tuple[Tuple[object, ...], ...]
    summary_status: str
    memory_effect_count: int = 0
    has_unsupported_nested_call: bool = False
    incomplete_reasons: Tuple[str, ...] = ()
    callee_control_profile_key: Optional[Tuple[object, ...]] = None
    callee_ordered_scalar_store_candidate: bool = False
    callee_cfg_edge_keys: Tuple[
        Tuple[Tuple[object, ...], Tuple[object, ...]], ...
    ] = ()
    callee_recursive_scc_proven: bool = False
    callee_recursive_scc_identity: Optional[str] = None
    callee_recursive_scc_member_keys: Tuple[Tuple[object, ...], ...] = ()
    return_summary_status: str = "unavailable"
    return_semantic_bit_width: Optional[int] = None
    return_signed: Optional[bool] = None
    return_value_keys: Tuple[Tuple[object, ...], ...] = ()
    return_guard_keys: Tuple[Tuple[object, ...], ...] = ()
    return_partitions: Tuple[Tuple[Tuple[Condition, ...], Expression], ...] = field(
        default=(),
        repr=False,
        compare=False,
    )
    memory_effects: Tuple[StoreEffect, ...] = field(
        default=(),
        repr=False,
        compare=False,
    )
    source: str = "direct_call_effect_summary"

    def stable_key(self) -> Tuple[object, ...]:
        return (
            "call_site_effect_summary_evidence",
            self.pcode_op_ref.stable_key() if self.pcode_op_ref is not None else None,
            self.target_ref.stable_key() if self.target_ref is not None else None,
            self.argument_keys,
            self.path_condition_keys,
            self.summary_status,
            int(self.memory_effect_count),
            bool(self.has_unsupported_nested_call),
            self.incomplete_reasons,
            self.callee_control_profile_key,
            self.callee_ordered_scalar_store_candidate,
            self.callee_cfg_edge_keys,
            self.callee_recursive_scc_proven,
            self.callee_recursive_scc_identity,
            self.callee_recursive_scc_member_keys,
            self.return_summary_status,
            self.return_semantic_bit_width,
            self.return_signed,
            self.return_value_keys,
            self.return_guard_keys,
            tuple(
                (
                    effect.location.stable_key(),
                    expression_provenance_key(effect.value),
                    tuple(_condition_evidence_key(item) for item in effect.conditions),
                    int(effect.order_key),
                )
                for effect in self.memory_effects
            ),
            self.source,
        )

    def json_items(self):
        yield "kind", "call_site_effect_summary_evidence"
        yield "pcode_op_ref", self.pcode_op_ref
        yield "target_ref", self.target_ref
        yield "argument_keys", self.argument_keys
        yield "path_condition_keys", self.path_condition_keys
        yield "summary_status", self.summary_status
        yield "memory_effect_count", int(self.memory_effect_count)
        yield "has_unsupported_nested_call", bool(self.has_unsupported_nested_call)
        yield "incomplete_reasons", self.incomplete_reasons
        yield "callee_control_profile_key", self.callee_control_profile_key
        yield "callee_ordered_scalar_store_candidate", bool(self.callee_ordered_scalar_store_candidate)
        yield "callee_cfg_edge_keys", self.callee_cfg_edge_keys
        yield "callee_recursive_scc_proven", bool(self.callee_recursive_scc_proven)
        yield "callee_recursive_scc_identity", self.callee_recursive_scc_identity
        yield "callee_recursive_scc_member_keys", self.callee_recursive_scc_member_keys
        yield "return_summary_status", self.return_summary_status
        yield "return_semantic_bit_width", self.return_semantic_bit_width
        yield "return_signed", self.return_signed
        yield "return_value_keys", self.return_value_keys
        yield "return_guard_keys", self.return_guard_keys
        yield "memory_effects", each(self.memory_effects, _store_effect_source)
        yield "source", self.source

    def to_dict(self) -> Dict[str, object]:
        return materialize(self)

@dataclass(frozen=True)
class FunctionControlEffectProfile:
    """Object-derived function-body census for the narrow direct-call lane."""

    block_count: int
    pcode_op_count: int
    return_block_count: int
    pcode_enumeration_complete: bool
    cfg_edges_complete: bool
    cfg_acyclic: bool
    terminal_return_coverage_complete: bool
    load_count: int = 0
    store_count: int = 0
    call_count: int = 0
    callind_count: int = 0
    callother_count: int = 0
    branchind_count: int = 0
    float_op_count: int = 0
    pcode_after_return_count: int = 0
    abnormal_terminal_block_count: int = 0
    call_like_pcode_op_keys: Tuple[Tuple[object, ...], ...] = ()
    call_like_identity_complete: bool = False
    function_identity_key: Optional[Tuple[object, ...]] = None
    direct_call_target_keys: Tuple[Tuple[object, ...], ...] = ()
    call_graph_edges_complete: bool = False
    recursive_scc_proven: bool = False
    recursive_scc_identity: Optional[str] = None
    recursive_scc_member_keys: Tuple[Tuple[object, ...], ...] = ()
    phase2_unsafe_mnemonics: Tuple[str, ...] = ()
    region_entry_block_key: Optional[Tuple[object, ...]] = None
    region_exit_block_keys: Tuple[Tuple[object, ...], ...] = ()
    region_block_keys: Tuple[Tuple[object, ...], ...] = ()
    region_cfg_edge_keys: Tuple[
        Tuple[Tuple[object, ...], Tuple[object, ...]], ...
    ] = ()
    region_pcode_op_keys: Tuple[Tuple[object, ...], ...] = ()
    region_live_in_keys: Tuple[Tuple[object, ...], ...] = ()
    region_live_out_keys: Tuple[Tuple[object, ...], ...] = ()
    region_identity_complete: bool = False
    region_single_entry: bool = False
    region_all_exits_enumerated: bool = False
    region_cross_edges_enumerated: bool = False
    unsupported_mnemonics: Tuple[str, ...] = ()

    @property
    def phase2_memory_free_scalar_candidate(self) -> bool:
        return (
            self.pcode_enumeration_complete
            and self.cfg_edges_complete
            and self.cfg_acyclic
            and self.terminal_return_coverage_complete
            and self.load_count == 0
            and self.store_count == 0
            and self.call_count == 0
            and self.callind_count == 0
            and self.callother_count == 0
            and self.branchind_count == 0
            and self.float_op_count == 0
            and self.pcode_after_return_count == 0
            and self.abnormal_terminal_block_count == 0
            and self.call_like_identity_complete
            and not self.phase2_unsafe_mnemonics
            and not self.unsupported_mnemonics
        )

    @property
    def phase3_ordered_scalar_store_candidate(self) -> bool:
        return (
            self.pcode_enumeration_complete
            and self.cfg_edges_complete
            and self.cfg_acyclic
            and self.terminal_return_coverage_complete
            and self.load_count == 0
            and self.call_count == 0
            and self.callind_count == 0
            and self.callother_count == 0
            and self.branchind_count == 0
            and self.float_op_count == 0
            and self.pcode_after_return_count == 0
            and self.abnormal_terminal_block_count == 0
            and self.call_like_identity_complete
            and not self.phase2_unsafe_mnemonics
            and not self.unsupported_mnemonics
        )

    def stable_key(self) -> Tuple[object, ...]:
        return (
            "function_control_effect_profile",
            int(self.block_count),
            int(self.pcode_op_count),
            int(self.return_block_count),
            bool(self.pcode_enumeration_complete),
            bool(self.cfg_edges_complete),
            bool(self.cfg_acyclic),
            bool(self.terminal_return_coverage_complete),
            int(self.load_count),
            int(self.store_count),
            int(self.call_count),
            int(self.callind_count),
            int(self.callother_count),
            int(self.branchind_count),
            int(self.float_op_count),
            int(self.pcode_after_return_count),
            int(self.abnormal_terminal_block_count),
            self.call_like_pcode_op_keys,
            bool(self.call_like_identity_complete),
            self.function_identity_key,
            self.direct_call_target_keys,
            bool(self.call_graph_edges_complete),
            bool(self.recursive_scc_proven),
            self.recursive_scc_identity,
            self.recursive_scc_member_keys,
            self.phase2_unsafe_mnemonics,
            self.region_entry_block_key,
            self.region_exit_block_keys,
            self.region_block_keys,
            self.region_cfg_edge_keys,
            self.region_pcode_op_keys,
            self.region_live_in_keys,
            self.region_live_out_keys,
            bool(self.region_identity_complete),
            bool(self.region_single_entry),
            bool(self.region_all_exits_enumerated),
            bool(self.region_cross_edges_enumerated),
            self.unsupported_mnemonics,
            bool(self.phase2_memory_free_scalar_candidate),
        )

    def json_items(self):
        yield "block_count", int(self.block_count)
        yield "pcode_op_count", int(self.pcode_op_count)
        yield "return_block_count", int(self.return_block_count)
        yield "pcode_enumeration_complete", bool(self.pcode_enumeration_complete)
        yield "cfg_edges_complete", bool(self.cfg_edges_complete)
        yield "cfg_acyclic", bool(self.cfg_acyclic)
        yield "terminal_return_coverage_complete", bool(self.terminal_return_coverage_complete)
        yield "load_count", int(self.load_count)
        yield "store_count", int(self.store_count)
        yield "call_count", int(self.call_count)
        yield "callind_count", int(self.callind_count)
        yield "callother_count", int(self.callother_count)
        yield "branchind_count", int(self.branchind_count)
        yield "float_op_count", int(self.float_op_count)
        yield "pcode_after_return_count", int(self.pcode_after_return_count)
        yield "abnormal_terminal_block_count", int(self.abnormal_terminal_block_count)
        yield "call_like_pcode_op_keys", self.call_like_pcode_op_keys
        yield "call_like_identity_complete", bool(self.call_like_identity_complete)
        yield "function_identity_key", self.function_identity_key
        yield "direct_call_target_keys", self.direct_call_target_keys
        yield "call_graph_edges_complete", bool(self.call_graph_edges_complete)
        yield "recursive_scc_proven", bool(self.recursive_scc_proven)
        yield "recursive_scc_identity", self.recursive_scc_identity
        yield "recursive_scc_member_keys", self.recursive_scc_member_keys
        yield "phase2_unsafe_mnemonics", as_list(self.phase2_unsafe_mnemonics)
        yield "region_entry_block_key", self.region_entry_block_key
        yield "region_exit_block_keys", self.region_exit_block_keys
        yield "region_block_keys", self.region_block_keys
        yield "region_cfg_edge_keys", self.region_cfg_edge_keys
        yield "region_pcode_op_keys", self.region_pcode_op_keys
        yield "region_live_in_keys", self.region_live_in_keys
        yield "region_live_out_keys", self.region_live_out_keys
        yield "region_identity_complete", bool(self.region_identity_complete)
        yield "region_single_entry", bool(self.region_single_entry)
        yield "region_all_exits_enumerated", bool(self.region_all_exits_enumerated)
        yield "region_cross_edges_enumerated", bool(self.region_cross_edges_enumerated)
        yield "unsupported_mnemonics", as_list(self.unsupported_mnemonics)
        yield "phase2_memory_free_scalar_candidate", bool(self.phase2_memory_free_scalar_candidate)
        yield "phase3_ordered_scalar_store_candidate", bool(self.phase3_ordered_scalar_store_candidate)

    def to_dict(self) -> Dict[str, object]:
        return materialize(self)

@source_converter
def _store_effect_source(effect: "StoreEffect") -> object:
    """`CallSiteEffectSummaryEvidence.memory_effects` の 1 要素の表示（固定個数の member）。"""

    return inline(
        ("location", effect.location),
        ("value", effect.value),
        ("conditions", each(effect.conditions)),
        ("order_key", int(effect.order_key)),
        ("provenance", effect.provenance),
    )


@dataclass
class EffectSummary:
    parameter_names: List[str]
    effects: List[StoreEffect]
    synthetic_expr: Optional[Expression] = None
    has_unsupported_call: bool = False
    incomplete_reasons: Tuple[str, ...] = ()
    parameter_refs: List[LocationBaseRef] = field(default_factory=list)
    call_argument_evidence: Dict[Tuple[object, ...], "CallArgumentEvidence"] = field(default_factory=dict)
    unsupported_call_sites: Tuple[UnsupportedCallEffectRef, ...] = ()
    call_target_resolution_evidence: Tuple[CallTargetResolutionEvidence, ...] = ()
    call_site_effect_summary_evidence: Tuple[CallSiteEffectSummaryEvidence, ...] = ()
    function_control_effect_profile: Optional[FunctionControlEffectProfile] = None

    def __post_init__(self) -> None:
        self.incomplete_reasons = tuple(dict.fromkeys(self.incomplete_reasons or ()))
        self.unsupported_call_sites = tuple(self.unsupported_call_sites or ())
        self.call_target_resolution_evidence = tuple(self.call_target_resolution_evidence or ())
        self.call_site_effect_summary_evidence = tuple(self.call_site_effect_summary_evidence or ())
        if self.parameter_refs:
            self.parameter_refs = [
                coerced
                for index, ref in enumerate(self.parameter_refs)
                for coerced in [_coerce_callee_parameter_ref(ref, index)]
                if coerced is not None
            ]
        else:
            self.parameter_refs = []
        if self.parameter_refs:
            self.effects = [
                StoreEffect(
                    location=_bind_location_to_parameter_refs(effect.location, self.parameter_refs),
                    value=effect.value,
                    conditions=list(effect.conditions or []),
                    order_key=effect.order_key,
                    provenance=effect.provenance,
                )
                for effect in (self.effects or [])
            ]
        else:
            self.effects = [
                StoreEffect(
                    location=effect.location,
                    value=effect.value,
                    conditions=list(effect.conditions or []),
                    order_key=effect.order_key,
                    provenance=effect.provenance,
                )
                for effect in (self.effects or [])
            ]

@dataclass(frozen=True)
class CallArgumentEvidence:
    """Path-covered call-site argument evidence keyed by a concrete P-code op."""

    RECOVERY_COMPLETE: ClassVar[str] = "complete"
    RECOVERY_RECOVERABLE_PARTIAL: ClassVar[str] = "recoverable_partial"
    RECOVERY_INCONCLUSIVE: ClassVar[str] = "inconclusive"

    pcode_op_ref: object
    target_ref: Optional[CallTargetRef]
    callee_param_identities: Tuple[Tuple[object, ...], ...]
    arguments: Tuple[Expression, ...]
    sources: Tuple[str, ...]
    path_conditions: Tuple[Tuple[Condition, ...], ...] = ()
    coverage_complete: bool = False
    recovery_status: str = RECOVERY_COMPLETE
    reason: Optional[str] = None
    #: Issue #20 PR-D: ABI で決定した引数スロットの identity correspondence。
    #: ``binary_id`` を含まないので左右で比較できるが、値の一致は意味しない。
    abi_argument_slots: Tuple[Any, ...] = ()
    #: 復元できなかったスロットの side-specific fresh 参照。
    fresh_argument_refs: Tuple[Any, ...] = ()

    def __post_init__(self) -> None:
        status = _normalize_call_argument_recovery_status(self.recovery_status)
        if bool(self.coverage_complete):
            status = self.RECOVERY_COMPLETE
        elif status == self.RECOVERY_COMPLETE:
            status = self.RECOVERY_INCONCLUSIVE
        object.__setattr__(self, "recovery_status", status)

    def stable_key(self) -> Optional[Tuple[object, ...]]:
        stable_key = getattr(self.pcode_op_ref, "stable_key", None)
        if not callable(stable_key):
            return None
        return stable_key()

    def is_usable(self) -> bool:
        return (
            bool(self.coverage_complete)
            and _call_target_ref_is_resolved(self.target_ref)
            and _callee_param_identities_are_object_proven(self.callee_param_identities)
            and len(self.arguments) == len(self.callee_param_identities)
        )

    def is_recoverable_partial(self) -> bool:
        return (
            self.recovery_status == self.RECOVERY_RECOVERABLE_PARTIAL
            and _call_target_ref_is_resolved(self.target_ref)
            and _callee_param_identities_are_object_proven(self.callee_param_identities)
            and 0 < len(self.arguments) <= len(self.callee_param_identities)
        )

    def target_matches(self, target_ref: Optional[CallTargetRef]) -> bool:
        if not _call_target_ref_is_resolved(self.target_ref) or not _call_target_ref_is_resolved(target_ref):
            return False
        return _call_target_ref_analysis_key(self.target_ref) == _call_target_ref_analysis_key(target_ref)

@dataclass(frozen=True)
class CallArgumentWidthEvidence:
    """Proof metadata for call-site arguments recovered from narrower storage."""

    source_bits: int
    target_bits: int
    source_storage_key: Optional[Tuple[object, ...]] = None
    target_storage_key: Optional[Tuple[object, ...]] = None
    source: str = "live_in_unmodified"

    def is_partial(self) -> bool:
        return int(self.source_bits or 0) > 0 and int(self.source_bits or 0) < int(self.target_bits or 0)

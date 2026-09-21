# -*- coding: utf-8 -*-
"""関数解析結果のデータモデル"""

from __future__ import annotations
from dataclasses import dataclass, field, fields as dataclass_fields, is_dataclass, replace
from copy import deepcopy
import hashlib
import json
from typing import List, Dict, Optional, Any, TYPE_CHECKING, Tuple, Mapping

if TYPE_CHECKING:
    from scripts.function_tracer_pcode.core.condition import Condition
    from scripts.function_tracer_pcode.core.expression import Expression
    from scripts.function_tracer_pcode.analysis.signedness import SignednessEvidence
    from scripts.function_tracer_pcode.analysis.effects.summary import EffectSummary
    from scripts.function_tracer_pcode.core.signature import SignatureHypothesis, FunctionSignature
from scripts.function_tracer_pcode.core.signature import (
    get_data_type_display_name,
    get_declared_type_size_bits,
    is_void_data_type,
    is_unsigned_data_type,
    parameters_without_runtime_objects,
)
from scripts.function_tracer_pcode.core.call_target import CallTargetRef, coerce_call_target_ref
from scripts.function_tracer_pcode.core.semantic_freeze import freeze_condition, freeze_expression
from scripts.function_tracer_pcode.core.runtime_refs import (
    EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON,
    EXPANSION_CASE_BUDGET_EXCEEDED_REASON,
    CallModelCandidateRef,
    DeferredCallRef,
    ExpansionBudgetTruncation,
    PcodeBlockRef,
    PcodeOpRef,
    UnknownValueRef,
    merge_expansion_budget_truncations,
)


def _jsonable_nested_tuple(value: Any) -> Any:
    if isinstance(value, dict):
        return {
            key: _jsonable_nested_tuple(item)
            for key, item in value.items()
        }
    if isinstance(value, tuple):
        return [_jsonable_nested_tuple(item) for item in value]
    if isinstance(value, list):
        return [_jsonable_nested_tuple(item) for item in value]
    return value


def _stable_json_digest(value: Any) -> str:
    try:
        payload = json.dumps(
            _jsonable_nested_tuple(value),
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
        )
    except (TypeError, ValueError):
        payload = repr(_jsonable_nested_tuple(value))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def _semantic_copy(value: Any) -> Any:
    """Copy analysis-owned structure while retaining opaque runtime leaves.

    PyGhidra values such as ``data_type_obj`` are Java proxies and cannot be
    reconstructed by :func:`copy.deepcopy`.  They are immutable references for
    the purposes of an analysis successor.  Copy ordinary containers and
    dataclasses recursively so those proxies do not force the surrounding
    authority/provenance structure to be shared.
    """

    if isinstance(value, dict):
        return {
            _semantic_copy(key): _semantic_copy(item)
            for key, item in value.items()
        }
    if isinstance(value, list):
        return [_semantic_copy(item) for item in value]
    if isinstance(value, tuple):
        return tuple(_semantic_copy(item) for item in value)
    if isinstance(value, set):
        return {_semantic_copy(item) for item in value}
    if isinstance(value, frozenset):
        return frozenset(_semantic_copy(item) for item in value)
    # ``DeferredCallInfo`` is an ``init=False`` dataclass with a semantic
    # constructor.  ``dataclasses.replace`` cannot reconstruct it and falling
    # back to the source object would share mutable call arguments/evidence
    # between an analysis and its successor.
    if isinstance(value, DeferredCallInfo):
        return value.clone()
    if is_dataclass(value) and not isinstance(value, type):
        try:
            return replace(
                value,
                **{
                    field_info.name: _semantic_copy(getattr(value, field_info.name))
                    for field_info in dataclass_fields(value)
                },
            )
        except (TypeError, AttributeError):
            return value
    try:
        return deepcopy(value)
    except (TypeError, AttributeError):
        # Opaque Java/PyGhidra proxies are intentionally identity-preserved.
        return value


@dataclass
class ReturnPathEvidence:
    terminal_op_ref: Optional[PcodeOpRef]
    coverage_status: str
    path_block_keys: Tuple[Tuple[Any, ...], ...] = ()
    path_guard_keys: Tuple[Tuple[Any, ...], ...] = ()
    pruning_proof_keys: Tuple[Tuple[Any, ...], ...] = ()
    guard_rewrite_proof_keys: Tuple[Tuple[Any, ...], ...] = ()
    schema_version: int = 1

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "return_path_evidence_v1",
            int(self.schema_version),
            self.terminal_op_ref.stable_key() if self.terminal_op_ref is not None else None,
            self.coverage_status,
            self.path_block_keys,
            self.path_guard_keys,
            self.pruning_proof_keys,
            self.guard_rewrite_proof_keys,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "schema_version": int(self.schema_version),
            "terminal_op_ref": self.terminal_op_ref.to_dict() if self.terminal_op_ref is not None else None,
            "coverage_status": self.coverage_status,
            "path_block_keys": _jsonable_nested_tuple(self.path_block_keys),
            "path_guard_keys": _jsonable_nested_tuple(self.path_guard_keys),
            "pruning_proof_keys": _jsonable_nested_tuple(self.pruning_proof_keys),
            "guard_rewrite_proof_keys": _jsonable_nested_tuple(self.guard_rewrite_proof_keys),
        }


@dataclass(frozen=True)
class VarnodeFlowRef:
    """Object-derived identity of one Varnode in a RETURN value flow."""

    space_id: Optional[int]
    space_name: str
    offset: int
    size: int

    @classmethod
    def from_varnode(cls, varnode: Any) -> Optional["VarnodeFlowRef"]:
        if varnode is None:
            return None
        try:
            address = varnode.getAddress()
            space = address.getAddressSpace() if address is not None else None
            return cls(
                space_id=(int(space.getSpaceID()) if space is not None else None),
                space_name=(str(space.getName()) if space is not None else "unknown"),
                offset=int(varnode.getOffset()),
                size=int(varnode.getSize()),
            )
        except Exception:
            return None

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "varnode_flow_ref",
            self.space_id,
            self.space_name,
            self.offset,
            self.size,
        )


@dataclass(frozen=True)
class ReturnValueFlowStep:
    """One validated producer edge on the concrete RETURN input def-chain."""

    op_ref: PcodeOpRef
    output_ref: VarnodeFlowRef
    input_refs: Tuple[VarnodeFlowRef, ...]
    traversed_input_index: int

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "return_value_flow_step",
            self.op_ref.stable_key(),
            self.output_ref.stable_key(),
            tuple(item.stable_key() for item in self.input_refs),
            self.traversed_input_index,
        )


@dataclass(frozen=True)
class ReturnValueFlowCertificate:
    """Certificate from an actual RETURN input through its producer chain.

    ``payload_expression_identity`` is obtained by tracing the concrete input
    Varnode of the certified extension op.  It binds the object flow to the
    semantic expression subsequently used by the SMT consumer.
    """

    return_op_ref: PcodeOpRef
    return_input_index: int
    return_input_ref: VarnodeFlowRef
    steps: Tuple[ReturnValueFlowStep, ...]
    extension_step_index: Optional[int]
    payload_expression_identity: Tuple[Any, ...] = ()
    schema_version: int = 1

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "return_value_flow_certificate",
            self.schema_version,
            self.return_op_ref.stable_key(),
            self.return_input_index,
            self.return_input_ref.stable_key(),
            tuple(item.stable_key() for item in self.steps),
            self.extension_step_index,
            self.payload_expression_identity,
        )


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
    return_value_pcode_op_refs: Tuple[PcodeOpRef, ...] = field(default_factory=tuple)
    return_value_flow_certificate: Optional[ReturnValueFlowCertificate] = None
    return_kind: str = "exact"
    acceptance_status: Optional[str] = None
    summary_candidate_id: Optional[Tuple[Any, ...]] = None
    summary_candidate_source_key: Optional[Tuple[Any, ...]] = None
    summary_transition_evidence_key: Optional[Tuple[Any, ...]] = None
    retained_exact_return_ref: Optional[Tuple[Any, ...]] = None
    validation_blockers: Tuple[str, ...] = field(default_factory=tuple)
    return_path_evidence: Optional[ReturnPathEvidence] = None

    def __post_init__(self) -> None:
        # 解析結果は **確定した意味** なので、組み上がった時点で凍らせる。
        # ここから先（proof / render / authority）は snapshot だけを読み、
        # 値を変えたい処理は新しい `ReturnInfo` を作る。
        freeze_expression(self.value)
        for condition in self.conditions or ():
            freeze_condition(condition)

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
        if self.pcode_op_ref is not None:
            result["pcode_op_ref"] = self.pcode_op_ref.to_dict()
        if self.return_value_pcode_op_refs:
            result["return_value_pcode_op_refs"] = [
                ref.to_dict() for ref in self.return_value_pcode_op_refs
            ]
        if self.return_value_flow_certificate is not None:
            result["return_value_flow_certificate"] = _jsonable_nested_tuple(
                self.return_value_flow_certificate.stable_key()
            )
        if self.return_kind != "exact":
            result["return_kind"] = self.return_kind
        if self.retained_exact_return_ref is not None:
            result["retained_exact_return_ref"] = _jsonable_nested_tuple(
                self.retained_exact_return_ref
            )
        if self.acceptance_status is not None:
            result["acceptance_status"] = self.acceptance_status
        if self.summary_candidate_id is not None:
            result["summary_candidate_id"] = _jsonable_nested_tuple(self.summary_candidate_id)
        if self.summary_candidate_source_key is not None:
            result["summary_candidate_source_key"] = _jsonable_nested_tuple(
                self.summary_candidate_source_key
            )
        if self.summary_transition_evidence_key is not None:
            result["summary_transition_evidence_key"] = _jsonable_nested_tuple(
                self.summary_transition_evidence_key
            )
        if self.validation_blockers:
            result["validation_blockers"] = list(self.validation_blockers)
        if self.return_path_evidence is not None:
            result["return_path_evidence"] = self.return_path_evidence.to_dict()
        return result


@dataclass
class ReturnOutcome:
    """A returning member of a function outcome partition."""

    guard: Tuple[Condition, ...]
    value: Expression
    storage: Optional[Tuple[Any, ...]] = None
    provenance: Dict[str, Any] = field(default_factory=dict)
    return_info: Optional[ReturnInfo] = None

    def to_dict(self) -> Dict[str, Any]:
        result = {
            "kind": "return",
            "guard": [condition.to_dict() for condition in self.guard],
            "value": self.value.to_dict(),
            "provenance": _jsonable_nested_tuple(self.provenance),
        }
        if self.storage is not None:
            result["storage"] = _jsonable_nested_tuple(self.storage)
        if self.return_info is not None:
            result["return_info"] = self.return_info.to_dict()
        return result


@dataclass
class DivergenceOutcome:
    """A must-diverge member of a function outcome partition."""

    guard: Tuple[Condition, ...]
    proof: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "divergence",
            "guard": [condition.to_dict() for condition in self.guard],
            "proof": _jsonable_nested_tuple(self.proof),
        }


@dataclass
class UnknownOutcome:
    """An unproved member of an outcome partition."""

    guard: Tuple[Condition, ...]
    reason: str
    evidence: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "kind": "unknown",
            "guard": [condition.to_dict() for condition in self.guard],
            "reason": self.reason,
            "evidence": _jsonable_nested_tuple(self.evidence),
        }


@dataclass(frozen=True)
class TerminationContractRef:
    termination_class: str
    object_identity_key: Tuple[Any, ...]
    payload_key: Tuple[Any, ...]
    effect_key: Tuple[Any, ...]
    observation_contract_key: Tuple[Any, ...]
    source_contract_key: Tuple[Any, ...]
    schema_version: int = 1

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "termination_contract_v1",
            int(self.schema_version),
            self.termination_class,
            self.object_identity_key,
            self.payload_key,
            self.effect_key,
            self.observation_contract_key,
            self.source_contract_key,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "schema_version": int(self.schema_version),
            "termination_class": self.termination_class,
            "object_identity_key": _jsonable_nested_tuple(self.object_identity_key),
            "payload_key": _jsonable_nested_tuple(self.payload_key),
            "effect_key": _jsonable_nested_tuple(self.effect_key),
            "observation_contract_key": _jsonable_nested_tuple(self.observation_contract_key),
            "source_contract_key": _jsonable_nested_tuple(self.source_contract_key),
        }


@dataclass(frozen=True)
class TerminationPathEffectEvidence:
    """Producer output kept outside the semantic outcome seed until validated."""

    terminal_candidate_id: Tuple[Any, ...]
    terminal_op_ref: PcodeOpRef
    control_effect_profile_key: Tuple[Any, ...]
    path_guard_key: Tuple[Any, ...]
    contract: TerminationContractRef
    path_guard: Tuple[Condition, ...] = field(default=(), repr=False, compare=False)
    producer_id: str = "analyzer_terminal_path_effect_v1"
    schema_version: int = 1

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "termination_path_effect_evidence_v1", int(self.schema_version), self.producer_id,
            self.terminal_candidate_id, self.terminal_op_ref.stable_key(),
            self.control_effect_profile_key, self.path_guard_key, self.contract.stable_key(),
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "schema_version": int(self.schema_version),
            "producer_id": self.producer_id,
            "terminal_candidate_id": _jsonable_nested_tuple(self.terminal_candidate_id),
            "terminal_op_ref": self.terminal_op_ref.to_dict(),
            "control_effect_profile_key": _jsonable_nested_tuple(self.control_effect_profile_key),
            "path_guard_key": _jsonable_nested_tuple(self.path_guard_key),
            "path_guard": [condition.to_dict() for condition in self.path_guard],
            "contract": self.contract.to_dict(),
        }


@dataclass(frozen=True)
class TerminalCandidate:
    """Object-derived terminal candidate; this is evidence, not a proof result."""

    candidate_id: Tuple[Any, ...]
    terminal_kind_candidate: str
    block_ref: Optional[PcodeBlockRef] = None
    op_ref: Optional[PcodeOpRef] = None
    cfg_reachable: Optional[bool] = None
    evidence_key: Tuple[Any, ...] = ()
    termination_contract: Optional[TerminationContractRef] = None

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "terminal_candidate_v1",
            self.candidate_id,
            self.terminal_kind_candidate,
            self.block_ref.stable_key() if self.block_ref is not None else None,
            self.op_ref.stable_key() if self.op_ref is not None else None,
            self.cfg_reachable,
            self.evidence_key,
            self.termination_contract.stable_key() if self.termination_contract is not None else None,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "candidate_id": _jsonable_nested_tuple(self.candidate_id),
            "terminal_kind_candidate": self.terminal_kind_candidate,
            "block_ref": self.block_ref.to_dict() if self.block_ref is not None else None,
            "op_ref": self.op_ref.to_dict() if self.op_ref is not None else None,
            "cfg_reachable": self.cfg_reachable,
            "evidence_key": _jsonable_nested_tuple(self.evidence_key),
            "termination_contract": (
                self.termination_contract.to_dict()
                if self.termination_contract is not None else None
            ),
        }


@dataclass(frozen=True)
class SymbolicRegionCandidate:
    """Candidate input region associated with one concrete terminal candidate."""

    candidate_id: Tuple[Any, ...]
    terminal_candidate_id: Tuple[Any, ...]
    guard: Tuple[Condition, ...]
    guard_extraction_complete: bool
    producer_evidence_key: Tuple[Any, ...] = ()
    observed_value: Optional[Expression] = None

    def to_dict(self) -> Dict[str, Any]:
        result = {
            "candidate_id": _jsonable_nested_tuple(self.candidate_id),
            "terminal_candidate_id": _jsonable_nested_tuple(self.terminal_candidate_id),
            "guard": [condition.to_dict() for condition in self.guard],
            "guard_extraction_complete": bool(self.guard_extraction_complete),
            "producer_evidence_key": _jsonable_nested_tuple(self.producer_evidence_key),
        }
        if self.observed_value is not None:
            result["observed_value"] = self.observed_value.to_dict()
        return result


@dataclass(frozen=True)
class FunctionOutcomeSeed:
    """Proof-free semantic surface used by unary outcome obligations."""

    function_identity: Tuple[Any, ...]
    input_domain_contract: Tuple[Any, ...]
    terminal_candidates: Tuple[TerminalCandidate, ...] = ()
    symbolic_regions: Tuple[SymbolicRegionCandidate, ...] = ()
    unresolved_control_evidence: Tuple[Tuple[Any, ...], ...] = ()
    control_flow_evidence_key: Tuple[Any, ...] = ()
    partition_revision: int = 0
    extraction_schema_version: int = 1

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "function_outcome_seed_v1",
            self.function_identity,
            self.input_domain_contract,
            tuple(candidate.stable_key() for candidate in self.terminal_candidates),
            tuple(_stable_json_digest(region.to_dict()) for region in self.symbolic_regions),
            self.unresolved_control_evidence,
            self.control_flow_evidence_key,
            int(self.partition_revision),
            int(self.extraction_schema_version),
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "function_identity": _jsonable_nested_tuple(self.function_identity),
            "input_domain_contract": _jsonable_nested_tuple(self.input_domain_contract),
            "terminal_candidates": [item.to_dict() for item in self.terminal_candidates],
            "symbolic_regions": [item.to_dict() for item in self.symbolic_regions],
            "unresolved_control_evidence": _jsonable_nested_tuple(self.unresolved_control_evidence),
            "control_flow_evidence_key": _jsonable_nested_tuple(self.control_flow_evidence_key),
            "partition_revision": int(self.partition_revision),
            "extraction_schema_version": int(self.extraction_schema_version),
        }


@dataclass
class SummaryReturnCandidate:
    """Loop-summary-derived return candidate kept outside normal returns until accepted."""

    candidate_id: Tuple[Any, ...]
    return_info: ReturnInfo
    guard_structural_key: Tuple[Any, ...]
    value_structural_key: Tuple[Any, ...]
    loop_summary_structural_key: Optional[Tuple[Any, ...]] = None
    transition_evidence_key: Optional[Tuple[Any, ...]] = None
    active_precondition_key: Optional[Tuple[Any, ...]] = None
    summary_applicability_guard_key: Optional[Tuple[Any, ...]] = None
    effect_region_key: Optional[Tuple[Any, ...]] = None
    memory_read_set_key: Optional[Tuple[Any, ...]] = None
    memory_write_set_key: Optional[Tuple[Any, ...]] = None
    call_effect_key: Optional[Tuple[Any, ...]] = None
    ub_assumption_key: Optional[Tuple[Any, ...]] = None
    effect_model_schema_version: str = "summary-return-effect-v1"
    eq_eligible: bool = False
    acceptance_status: str = "candidate"
    validation_blockers: Tuple[str, ...] = field(default_factory=tuple)
    evidence: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "candidate_id": _jsonable_nested_tuple(self.candidate_id),
            "return_info": self.return_info.to_dict(),
            "guard_structural_key": _jsonable_nested_tuple(self.guard_structural_key),
            "value_structural_key": _jsonable_nested_tuple(self.value_structural_key),
            "loop_summary_structural_key": _jsonable_nested_tuple(self.loop_summary_structural_key),
            "transition_evidence_key": _jsonable_nested_tuple(self.transition_evidence_key),
            "active_precondition_key": _jsonable_nested_tuple(self.active_precondition_key),
            "summary_applicability_guard_key": _jsonable_nested_tuple(
                self.summary_applicability_guard_key
            ),
            "effect_region_key": _jsonable_nested_tuple(self.effect_region_key),
            "memory_read_set_key": _jsonable_nested_tuple(self.memory_read_set_key),
            "memory_write_set_key": _jsonable_nested_tuple(self.memory_write_set_key),
            "call_effect_key": _jsonable_nested_tuple(self.call_effect_key),
            "ub_assumption_key": _jsonable_nested_tuple(self.ub_assumption_key),
            "effect_model_schema_version": self.effect_model_schema_version,
            "eq_eligible": bool(self.eq_eligible),
            "acceptance_status": self.acceptance_status,
            "validation_blockers": list(self.validation_blockers),
            "evidence": _jsonable_nested_tuple(self.evidence),
        }


@dataclass(init=False)
class DeferredCallInfo:
    """解析時に展開できなかった呼び出しサイトの情報。"""

    deferred_call_ref: DeferredCallRef
    target_ref: CallTargetRef
    arguments: List["Expression"] = field(default_factory=list)
    call_target_expr: Optional["Expression"]
    display_hint: Optional[str]
    call_argument_recovery_status: str = "inconclusive"
    call_argument_recovery_reason: Optional[str] = None
    effect_class: str = "unknown_effect"
    match_evidence: Dict[str, Any] = field(default_factory=dict)
    domain_policy: Dict[str, Any] = field(default_factory=dict)
    abi_return_width_bits: Optional[int] = None
    abi_return_type_policy: Optional[str] = None
    call_site_multiplicity: Optional[int] = None
    call_model_candidate: Optional["CallModelCandidateRef"] = None

    _VALID_CALL_ARGUMENT_RECOVERY_STATUSES = {
        "complete",
        "recoverable_partial",
        "inconclusive",
    }

    def __init__(
        self,
        placeholder_name: Optional[str] = None,
        target_ref=None,
        arguments: Optional[List["Expression"]] = None,
        call_target_expr: Optional["Expression"] = None,
        sequence: Optional[int] = None,
        deferred_call_ref: Optional[DeferredCallRef] = None,
        call_argument_recovery_status: Optional[str] = None,
        call_argument_recovery_reason: Optional[str] = None,
        effect_class: Optional[str] = None,
        match_evidence: Optional[Dict[str, Any]] = None,
        domain_policy: Optional[Dict[str, Any]] = None,
        abi_return_width_bits: Optional[int] = None,
        abi_return_type_policy: Optional[str] = None,
        call_site_multiplicity: Optional[int] = None,
        call_model_candidate: Optional["CallModelCandidateRef"] = None,
    ) -> None:
        if call_argument_recovery_status is None:
            call_argument_recovery_status = "inconclusive"
        normalized = coerce_call_target_ref(target_ref) or CallTargetRef.unknown()
        self.deferred_call_ref = deferred_call_ref or DeferredCallRef(
            target_ref=normalized,
            sequence=sequence,
        )
        self.target_ref = normalized
        self.arguments = list(arguments or [])
        self.call_target_expr = call_target_expr
        self.display_hint = placeholder_name or self.deferred_call_ref.display_name()
        self.call_argument_recovery_status = self._normalize_call_argument_recovery_status(
            call_argument_recovery_status
        )
        self.call_argument_recovery_reason = call_argument_recovery_reason
        self.effect_class = effect_class or _classify_deferred_call_effect(normalized)
        self.domain_policy = dict(domain_policy or {})
        self.abi_return_width_bits = (
            int(abi_return_width_bits)
            if abi_return_width_bits is not None
            else None
        )
        self.abi_return_type_policy = abi_return_type_policy
        self.call_site_multiplicity = (
            int(call_site_multiplicity)
            if call_site_multiplicity is not None
            else None
        )
        self.call_model_candidate = self._normalize_call_model_candidate(
            call_model_candidate
        )
        self.match_evidence = self._build_match_evidence(match_evidence)

    def clone(self) -> "DeferredCallInfo":
        """Return an independent semantic copy of this deferred call.

        Ghidra target references are immutable identity objects and are kept
        shared.  Expressions, argument evidence, and policy mappings are
        analysis-owned mutable structures and are copied recursively through
        the model copy policy.
        """

        return DeferredCallInfo(
            placeholder_name=self.placeholder_name,
            target_ref=self.target_ref,
            arguments=[_semantic_copy(argument) for argument in self.arguments],
            call_target_expr=(
                _semantic_copy(self.call_target_expr)
                if self.call_target_expr is not None else None
            ),
            deferred_call_ref=self.deferred_call_ref,
            call_argument_recovery_status=self.call_argument_recovery_status,
            call_argument_recovery_reason=self.call_argument_recovery_reason,
            effect_class=self.effect_class,
            match_evidence=_semantic_copy(self.match_evidence),
            domain_policy=_semantic_copy(self.domain_policy),
            abi_return_width_bits=self.abi_return_width_bits,
            abi_return_type_policy=self.abi_return_type_policy,
            call_site_multiplicity=self.call_site_multiplicity,
            call_model_candidate=self.call_model_candidate,
        )

    @property
    def placeholder_name(self) -> str:
        return self.display_hint or self.deferred_call_ref.display_name()

    @staticmethod
    def _normalize_call_model_candidate(candidate: object):
        """decision-neutral な call-model candidate metadata を受け取る。

        型だけを検査する。``core`` は catalog を lookup せず、candidate の
        有無で ``effect_class`` を変えることもしない（Issue #20 PR-B1)。
        """
        if candidate is None:
            return None
        if not isinstance(candidate, CallModelCandidateRef):
            raise TypeError(
                "call_model_candidate must be a CallModelCandidateRef or None"
            )
        return candidate

    @staticmethod
    def _normalize_call_argument_recovery_status(status: object) -> str:
        raw_status = str(status or "inconclusive")
        return raw_status if raw_status in DeferredCallInfo._VALID_CALL_ARGUMENT_RECOVERY_STATUSES else "inconclusive"

    def set_call_argument_recovery_state(
        self,
        status: str,
        reason: Optional[str] = None,
    ) -> None:
        self.call_argument_recovery_status = self._normalize_call_argument_recovery_status(
            status
        )
        self.call_argument_recovery_reason = reason

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

    def _build_match_evidence(
        self,
        extra_evidence: Optional[Dict[str, Any]] = None,
    ) -> Dict[str, Any]:
        target_expr_key = (
            self.call_target_expr.structural_key()
            if self.call_target_expr is not None
            else None
        )
        argument_key = tuple(
            arg.structural_key() if arg is not None else ("none",)
            for arg in (self.arguments or [])
        )
        evidence: Dict[str, Any] = {
            "callee_identity": self.target_ref.stable_key(),
            "callee_name": self.target_ref.display_name(),
            "argument_expression_key": argument_key,
            "call_target_expression_key": target_expr_key,
            "active_guard_key": None,
            "return_case_guard_key": None,
            "abi_return_width_bits": self.abi_return_width_bits,
            "abi_return_type_policy": self.abi_return_type_policy,
            "call_site_multiplicity": self.call_site_multiplicity,
            "effect_class": self.effect_class,
            "domain_policy": dict(self.domain_policy),
        }
        if extra_evidence:
            evidence.update(extra_evidence)
        return evidence

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
            "call_argument_recovery_status": self.call_argument_recovery_status,
            "call_argument_recovery_reason": self.call_argument_recovery_reason,
            "effect_class": self.effect_class,
            "match_evidence": _jsonable_nested_tuple(self.match_evidence),
            "domain_policy": _jsonable_nested_tuple(self.domain_policy),
            "abi_return_width_bits": self.abi_return_width_bits,
            "abi_return_type_policy": self.abi_return_type_policy,
            "call_site_multiplicity": self.call_site_multiplicity,
        }
        if self.call_target_expr is not None:
            result["call_target_expr"] = self.call_target_expr.to_dict()
        if self.call_model_candidate is not None:
            result["call_model_candidate"] = self.call_model_candidate.to_dict()
        return result


def _classify_deferred_call_effect(target_ref: CallTargetRef) -> str:
    if target_ref is None or target_ref.is_unknown():
        return "unresolved_target"
    name = _normalized_deferred_call_name(target_ref.display_name())
    if name in {"printf", "fprintf", "sprintf", "snprintf", "puts", "putchar", "fputs"}:
        return "side_effecting"
    # Issue #20 PR-20-B3: ``sqrt`` / ``sqrtf`` を名前で ``pure_return`` に
    # 分類していた特例は撤去した。外部 callee の値意味は analysis が黙って
    # 与える事実ではなく、conditional lane が明示的な ``AssumptionPremise``
    # として引き受ける（B1 catalog → B2 conditional view → B3 lane）。
    return "unknown_effect"


def _normalized_deferred_call_name(name: Optional[str]) -> str:
    raw = str(name or "").strip()
    if not raw:
        return ""
    raw = raw.split("@", 1)[0]
    raw = raw.rsplit(".", 1)[-1] if "." in raw else raw
    while raw.startswith("_"):
        raw = raw[1:]
    return raw.lower()

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

    from scripts.function_tracer_pcode.core.condition import Condition

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

    from scripts.function_tracer_pcode.core.condition import Condition

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
        from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier

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


# A successor is a new analysis seed, not an implicitly certified derived
# view. Keep the dependency table next to the API so adding a semantic input
# field requires an explicit decision about which authority it invalidates.
_SEMANTIC_SUCCESSOR_INVALIDATION_BY_CHANGE = {
    "returns": frozenset({
        "return_outcomes", "divergence_outcomes", "unknown_outcomes",
        "outcome_seed", "analysis_view_identity", "partition_revision",
        "comparison_surface", "completed_recovery_proof_ids",
        "completed_recovery_proof_evidence", "summary_return_candidates",
        "termination_path_effect_evidence", "quarantined_recurrence_proposals",
    }),
    "parameters": frozenset({
        "effect_summary", "return_outcomes", "divergence_outcomes",
        "unknown_outcomes", "outcome_seed", "analysis_view_identity",
        "partition_revision", "comparison_surface",
        "completed_recovery_proof_ids", "completed_recovery_proof_evidence",
        "summary_return_candidates", "termination_path_effect_evidence",
        "quarantined_recurrence_proposals",
    }),
    "deferred_calls": frozenset({
        "effect_summary", "return_outcomes", "divergence_outcomes",
        "unknown_outcomes", "outcome_seed", "analysis_view_identity",
        "partition_revision", "comparison_surface",
        "completed_recovery_proof_ids", "completed_recovery_proof_evidence",
        "summary_return_candidates", "termination_path_effect_evidence",
        "quarantined_recurrence_proposals",
    }),
    "return_type": frozenset({
        "return_abi_facts", "return_outcomes", "divergence_outcomes",
        "unknown_outcomes", "outcome_seed", "analysis_view_identity",
        "partition_revision", "comparison_surface",
        "completed_recovery_proof_ids", "completed_recovery_proof_evidence",
    }),
    "return_type_obj": frozenset({
        "return_abi_facts", "return_outcomes", "divergence_outcomes",
        "unknown_outcomes", "outcome_seed", "analysis_view_identity",
        "partition_revision", "comparison_surface",
        "completed_recovery_proof_ids", "completed_recovery_proof_evidence",
    }),
    "return_abi_facts": frozenset({
        "return_outcomes", "divergence_outcomes", "unknown_outcomes",
        "outcome_seed", "analysis_view_identity", "partition_revision",
        "comparison_surface", "completed_recovery_proof_ids",
        "completed_recovery_proof_evidence",
    }),
    "effect_summary": frozenset({
        "return_outcomes", "divergence_outcomes", "unknown_outcomes",
        "outcome_seed", "analysis_view_identity", "partition_revision",
        "comparison_surface", "completed_recovery_proof_ids",
        "completed_recovery_proof_evidence",
    }),
    # Issue #131 PR-B: 切り捨て marker は「展開が完全だった」という前提を壊すので、
    # ``returns`` が変わったときと同じ範囲の派生 authority を保守的に無効化する。
    # 記録が増えた後で、marker を知らずに作った証明・seed・view を再利用しない。
    "expansion_budget_truncations": frozenset({
        "return_outcomes", "divergence_outcomes", "unknown_outcomes",
        "outcome_seed", "analysis_view_identity", "partition_revision",
        "comparison_surface", "completed_recovery_proof_ids",
        "completed_recovery_proof_evidence", "summary_return_candidates",
        "termination_path_effect_evidence", "quarantined_recurrence_proposals",
    }),
}

_SEMANTIC_SUCCESSOR_DERIVED_DEFAULTS = {
    "effect_summary": None,
    "return_abi_facts": {},
    "return_outcomes": (),
    "divergence_outcomes": (),
    "unknown_outcomes": (),
    "outcome_seed": None,
    "analysis_view_identity": None,
    "partition_revision": 0,
    "comparison_surface": None,
    "completed_recovery_proof_ids": (),
    "completed_recovery_proof_evidence": (),
    "summary_return_candidates": (),
    "termination_path_effect_evidence": (),
    "quarantined_recurrence_proposals": (),
}


def semantic_successor_invalidated_fields(*changed_fields: str) -> frozenset:
    """変更された semantic 入力に対応する、無効化すべき派生 authority 名の集合。

    ``semantic_successor`` と in-place 同期の双方がこの 1 か所を参照する
    （集合の定義を二重実装しない）。
    """

    return frozenset().union(*(
        _SEMANTIC_SUCCESSOR_INVALIDATION_BY_CHANGE.get(name, frozenset())
        for name in changed_fields
    ))


def semantic_successor_derived_default(name: str) -> Any:
    """派生 authority の既定値を新しい実体として返す。

    mutable な既定値を複数の解析結果で共有しないよう、必ず複製して返す。
    """

    return _semantic_copy(_SEMANTIC_SUCCESSOR_DERIVED_DEFAULTS[name])


def invalidate_semantic_successor_fields(analysis: Any, *changed_fields: str) -> frozenset:
    """既存の解析結果を書き換える経路で、派生 authority を既定値へ戻す。

    Issue #131 PR-B: 切り捨て marker のように、後から同じ解析結果へ追加される
    semantic 入力のための in-place 版。呼び出し側は marker の反映とこの無効化を
    途中状態が観測されない 1 か所で行う。
    """

    invalidated = semantic_successor_invalidated_fields(*changed_fields)
    for name in sorted(invalidated):
        setattr(analysis, name, semantic_successor_derived_default(name))
    return invalidated


def derive_memory_effect_bit_width(returns, effect_summary, expr_bit_width) -> int:
    """``memory_effect`` 比較面の幅を導出する（``FunctionReturnAnalysis`` と
    semantic-width 正規化で共有）。

    ``returns`` の値式の幅（すべて正で一致していること）を第一の権威とし、
    値式から幅が得られないときだけ ``effect_summary.synthetic_expr`` の幅へ
    戻る。値式の幅が食い違う場合は比較面が定義できないので 0 を返す。
    """

    value_bits = []
    for ret in returns or ():
        value = getattr(ret, "value", None)
        if value is None:
            continue
        bits = int(expr_bit_width(value) or 0)
        if bits > 0:
            value_bits.append(bits)
    if value_bits:
        if len(set(value_bits)) != 1:
            return 0
        return value_bits[0]
    synthetic_expr = getattr(effect_summary, "synthetic_expr", None) if effect_summary is not None else None
    if synthetic_expr is None:
        return 0
    return max(0, int(expr_bit_width(synthetic_expr) or 0))


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
    return_type_provenance: Dict[str, Any] = field(default_factory=dict)
    return_abi_facts: Dict[str, Any] = field(default_factory=dict)
    comparison_surface: Optional[ComparisonSurface] = None
    analysis_scope_key: Optional[Tuple[Any, ...]] = None
    program_is_big_endian: Optional[bool] = None
    completed_recovery_proof_ids: Tuple[Tuple[Any, ...], ...] = ()
    completed_recovery_proof_evidence: Tuple[Dict[str, Any], ...] = ()
    binary_id: Optional[str] = None
    summary_return_candidates: Tuple[SummaryReturnCandidate, ...] = ()
    return_outcomes: Tuple[ReturnOutcome, ...] = ()
    divergence_outcomes: Tuple[DivergenceOutcome, ...] = ()
    unknown_outcomes: Tuple[UnknownOutcome, ...] = ()
    analysis_view_identity: Optional[Tuple[Any, ...]] = None
    partition_revision: int = 0
    outcome_seed: Optional[FunctionOutcomeSeed] = None
    termination_path_effect_evidence: Tuple[TerminationPathEffectEvidence, ...] = ()
    quarantined_recurrence_proposals: Tuple[Any, ...] = ()
    # Issue #131: 展開ケース数・経路数の上限で実際に切り捨てが起きた事実。
    # PR-B から semantic 入力（``to_dict`` / snapshot fingerprint / seed / gate）。
    # 記録がある限り「展開が完全だった」ことは前提にできない。
    expansion_budget_truncations: Tuple[ExpansionBudgetTruncation, ...] = ()

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
        if self.binary_id is None:
            self.binary_id = self._infer_binary_id_from_object_evidence()
        if not self.return_type_provenance:
            self.return_type_provenance = self._build_return_type_provenance()
        self.normalize_deferred_calls()

    def semantic_successor(self, **changes: Any) -> "FunctionReturnAnalysis":
        """Build an invalidation-aware successor of this analysis.

        Analysis rewrites commonly change only ``returns``, ``parameters``, or
        ``deferred_calls``.  A hand-written constructor for those rewrites is
        unsafe because new authority/provenance fields can silently be
        dropped.  Start from every dataclass field so additions remain
        retained by default, deep-copying the mutable analysis-owned fields
        while keeping opaque runtime objects (for example Ghidra type objects)
        on their original identity. Derived outcome/proof authority is
        invalidated according to the dependency table whenever a semantic
        input changes. Certified derived views must use their explicit
        constructors such as ``with_accepted_return_partition``.
        """

        field_names = {field_info.name for field_info in dataclass_fields(self)}
        unknown_changes = set(changes) - field_names
        if unknown_changes:
            unknown = ", ".join(sorted(unknown_changes))
            raise TypeError(f"unknown FunctionReturnAnalysis fields: {unknown}")

        invalidated_fields = semantic_successor_invalidated_fields(*changes)
        conflicting_changes = invalidated_fields.intersection(changes)
        if conflicting_changes:
            conflicting = ", ".join(sorted(conflicting_changes))
            raise ValueError(
                "semantic_successor cannot override invalidated derived fields: "
                + conflicting
            )

        # These values may refer to live Ghidra/decompiler objects or are
        # intentionally shared semantic summaries.  The explicit tuple-valued
        # entries are mutable through their nested records and therefore need
        # structural copying as well as the obvious dict/list fields.
        shared_runtime_fields = {
            "function_ref",
            "return_type_obj",
            "signedness_result",
            "effect_summary",
        }
        structural_copy_fields = {
            "parameters",
            "returns",
            "unknown_event_reasons",
            "analysis_notes",
            "deferred_calls",
            "signature_hypotheses",
            "return_type_provenance",
            "return_abi_facts",
            "completed_recovery_proof_evidence",
            "summary_return_candidates",
            "return_outcomes",
            "divergence_outcomes",
            "unknown_outcomes",
            "termination_path_effect_evidence",
            "quarantined_recurrence_proposals",
        }
        successor_values: Dict[str, Any] = {}
        for field_info in dataclass_fields(self):
            name = field_info.name
            if name in changes:
                value = changes[name]
                successor_values[name] = (
                    value
                    if name in shared_runtime_fields
                    else _semantic_copy(value)
                )
                continue
            if name in invalidated_fields:
                successor_values[name] = semantic_successor_derived_default(name)
                continue
            value = getattr(self, name)
            successor_values[name] = (
                value
                if name in shared_runtime_fields
                or name not in structural_copy_fields
                else _semantic_copy(value)
            )
        return replace(self, **successor_values)

    def outcome_function_identity(self) -> Tuple[Any, ...]:
        return (
            "function_identity_v1",
            self.binary_id,
            self.function_ref.stable_key() if self.function_ref is not None else None,
            self.entry_point,
        )

    def with_accepted_return_partition(
        self,
        returns: List[ReturnInfo],
        *,
        summary_return_candidates: Tuple[SummaryReturnCandidate, ...] = (),
        reason: str = "summary_return_acceptance",
    ) -> "FunctionReturnAnalysis":
        """Build a view for an accepted return partition without mutating the seed analysis."""

        next_revision = int(self.partition_revision or 0) + 1
        partition_digest = _stable_json_digest(
            tuple(ret.to_dict() for ret in (returns or ()))
        )
        candidate_digest = _stable_json_digest(
            tuple(candidate.to_dict() for candidate in (summary_return_candidates or ()))
        )
        view_identity = (
            "accepted_return_partition_view",
            ("reason", str(reason or "summary_return_acceptance")),
            ("analysis_scope_key", self.analysis_scope_key),
            ("function_ref", self.function_ref.stable_key() if self.function_ref is not None else None),
            ("base_revision", int(self.partition_revision or 0)),
            ("partition_revision", next_revision),
            ("accepted_return_partition_sha256", partition_digest),
            ("summary_return_candidates_sha256", candidate_digest),
        )
        return replace(
            self,
            parameters=[dict(param) for param in (self.parameters or [])],
            returns=list(returns or ()),
            unknown_event_reasons=list(self.unknown_event_reasons or []),
            analysis_notes=list(self.analysis_notes or []),
            deferred_calls=dict(self.deferred_calls or {}),
            signature_hypotheses=list(self.signature_hypotheses or []),
            return_type_provenance=dict(self.return_type_provenance or {}),
            return_abi_facts=deepcopy(self.return_abi_facts or {}),
            summary_return_candidates=tuple(summary_return_candidates or ()),
            return_outcomes=(),
            divergence_outcomes=(),
            unknown_outcomes=(),
            comparison_surface=None,
            outcome_seed=None,
            analysis_view_identity=view_identity,
            partition_revision=next_revision,
            completed_recovery_proof_ids=(),
            completed_recovery_proof_evidence=(),
            termination_path_effect_evidence=(),
            quarantined_recurrence_proposals=(),
        )

    def with_summary_return_diagnostics(
        self,
        *,
        summary_return_candidates: Tuple[SummaryReturnCandidate, ...] = (),
        blockers: Tuple[str, ...] = (),
        reason: str = "summary_return_diagnostics",
    ) -> "FunctionReturnAnalysis":
        """Build a diagnostics view retaining rejected summary candidates without changing returns."""

        next_revision = int(self.partition_revision or 0) + 1
        candidate_digest = _stable_json_digest(
            tuple(candidate.to_dict() for candidate in (summary_return_candidates or ()))
        )
        blocker_digest = _stable_json_digest(tuple(str(blocker) for blocker in (blockers or ())))
        view_identity = (
            "summary_return_diagnostics_view",
            ("reason", str(reason or "summary_return_diagnostics")),
            ("analysis_scope_key", self.analysis_scope_key),
            ("function_ref", self.function_ref.stable_key() if self.function_ref is not None else None),
            ("base_revision", int(self.partition_revision or 0)),
            ("partition_revision", next_revision),
            ("summary_return_candidates_sha256", candidate_digest),
            ("summary_return_blockers_sha256", blocker_digest),
        )
        view = replace(
            self,
            parameters=[dict(param) for param in (self.parameters or [])],
            returns=list(self.returns or []),
            unknown_event_reasons=list(self.unknown_event_reasons or []),
            analysis_notes=list(self.analysis_notes or []),
            deferred_calls=dict(self.deferred_calls or {}),
            signature_hypotheses=list(self.signature_hypotheses or []),
            return_type_provenance=dict(self.return_type_provenance or {}),
            return_abi_facts=deepcopy(self.return_abi_facts or {}),
            summary_return_candidates=tuple(summary_return_candidates or ()),
            analysis_view_identity=view_identity,
            partition_revision=next_revision,
        )
        for blocker in blockers or ():
            note = f"summary_return_blocker:{blocker}"
            if note not in view.analysis_notes:
                view.analysis_notes.append(note)
        return view

    def _build_return_type_provenance(self) -> Dict[str, Any]:
        return_type = get_data_type_display_name(self.return_type_obj, self.return_type)
        normalized_return_type = str(return_type or "").strip().lower()
        return_type_source = (
            "undefined_decompiler_type"
            if normalized_return_type.startswith("undefined")
            else "decompiler_return_type"
        )
        return {
            "object_derived": True,
            "return_type": return_type,
            "return_type_source": return_type_source,
            "signature_hypothesis_phase": None,
            "resolved_return_override_source": None,
            "counterpart_return_type": None,
            "declared_return_type_width": get_declared_type_size_bits(
                self.return_type_obj,
                return_type,
            ),
        }

    def _infer_binary_id_from_object_evidence(self) -> Optional[str]:
        for ret in self.returns or ():
            binary_id = getattr(getattr(ret, "pcode_op_ref", None), "binary_id", None)
            if binary_id:
                return str(binary_id)
        effect_summary = self.effect_summary
        for site in self._iter_effect_summary_object_evidence(
            getattr(effect_summary, "unsupported_call_sites", None)
        ):
            binary_id = getattr(getattr(site, "pcode_op_ref", None), "binary_id", None)
            if binary_id:
                return str(binary_id)
        for evidence in self._iter_effect_summary_object_evidence(
            getattr(effect_summary, "call_argument_evidence", None)
        ):
            binary_id = getattr(getattr(evidence, "pcode_op_ref", None), "binary_id", None)
            if binary_id:
                return str(binary_id)
        for evidence in self._iter_effect_summary_object_evidence(
            getattr(effect_summary, "call_target_resolution_evidence", None)
        ):
            binary_id = getattr(getattr(evidence, "pcode_op_ref", None), "binary_id", None)
            if binary_id:
                return str(binary_id)
        return None

    @staticmethod
    def _iter_effect_summary_object_evidence(value: Any) -> Tuple[Any, ...]:
        if value is None:
            return ()
        if isinstance(value, dict):
            return tuple(value.values())
        if isinstance(value, (tuple, list, set, frozenset)):
            return tuple(value)
        return ()

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
            "binary_id": self.binary_id,
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
        if self.completed_recovery_proof_ids:
            result["completed_recovery_proof_ids"] = [
                _jsonable_nested_tuple(proof_id)
                for proof_id in self.completed_recovery_proof_ids
            ]
        if self.completed_recovery_proof_evidence:
            result["completed_recovery_proof_evidence"] = [
                _jsonable_nested_tuple(evidence)
                for evidence in self.completed_recovery_proof_evidence
            ]
        if self.summary_return_candidates:
            result["summary_return_candidates"] = [
                candidate.to_dict()
                for candidate in self.summary_return_candidates
            ]
        if self.return_outcomes or self.divergence_outcomes or self.unknown_outcomes:
            result["outcomes"] = [
                *(outcome.to_dict() for outcome in self.return_outcomes),
                *(outcome.to_dict() for outcome in self.divergence_outcomes),
                *(outcome.to_dict() for outcome in self.unknown_outcomes),
            ]
        if self.outcome_seed is not None:
            result["outcome_seed"] = self.outcome_seed.to_dict()
        if self.termination_path_effect_evidence:
            result["termination_path_effect_evidence"] = [
                evidence.to_dict()
                for evidence in self.termination_path_effect_evidence
            ]
        if self.analysis_scope_key is not None:
            result["analysis_scope_key"] = self.analysis_scope_key
        if self.analysis_view_identity is not None:
            result["analysis_view_identity"] = _jsonable_nested_tuple(self.analysis_view_identity)
            result["partition_revision"] = int(self.partition_revision or 0)
        if self.program_is_big_endian is not None:
            result["program_is_big_endian"] = bool(self.program_is_big_endian)
        
        if self.signedness_result:
            result["signedness"] = self.signedness_result.to_dict()
        if self.signature_hypotheses:
            result["signature_hypotheses"] = list(self.signature_hypotheses)
        if self.return_type_provenance:
            result["return_type_provenance"] = _jsonable_nested_tuple(
                self.return_type_provenance
            )
        if self.return_abi_facts:
            result["return_abi_facts"] = _jsonable_nested_tuple(
                self.return_abi_facts
            )
        if self.comparison_surface is not None:
            result["comparison_surface"] = self.comparison_surface.to_dict()
        if self.expansion_budget_truncations:
            # Issue #131 PR-B: 正規化済みの全記録（参照 event ID 込み）を出す。
            # snapshot fingerprint は ``to_dict`` から作られるので、marker の有無・
            # 参照情報の増加はそのまま解析前提の同一性に反映される。
            result["expansion_budget_truncations"] = [
                record.to_dict()
                for record in merge_expansion_budget_truncations(
                    self.expansion_budget_truncations
                )
            ]
        
        return result
    
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
        from scripts.function_tracer_pcode.analysis.effects.summary import (
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

        from scripts.function_tracer_pcode.analysis.effects.summary import (
            canonicalize_expr_read_location,
            expression_contains_post_state_reads,
            lower_post_state_expression_for_smt_if_needed,
            locations_match,
        )
        from scripts.function_tracer_pcode.analysis.condition.simplifier import ConditionSimplifier

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
        if self.has_unknown_outcome_partition():
            return True
        if "return_case_coverage_gap" in self.analysis_notes:
            return True
        if "return_case_coverage_inconclusive" in self.analysis_notes:
            return True
        if self.recovered_from_decompiler:
            return False
        if not self.incomplete_control_flow:
            return False
        return self.has_unresolved_return_value() or self.has_overlapping_unconditional_returns()

    def has_unknown_outcome_partition(self) -> bool:
        return bool(self.unknown_outcomes and (self.return_outcomes or self.divergence_outcomes))

    def get_signature(self) -> "FunctionSignature":
        """現在の解析結果から有効シグネチャを取得する。"""
        from scripts.function_tracer_pcode.core.signature import FunctionSignature

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
        hypothesis_payload = hypothesis.to_dict()
        updated_hypotheses.append(hypothesis_payload)

        updated_returns = list(self.returns or [])
        updated_return_type_name = str(updated_signature.return_type or "").strip().lower()
        return_overridden_to_void = return_changed and (
            is_void_data_type(
                updated_signature.return_type_obj,
                updated_signature.return_type,
            )
            or updated_return_type_name == "void"
        )
        if return_overridden_to_void:
            from scripts.function_tracer_pcode.core.expression import Expression

            updated_returns = [
                replace(info, value=Expression.unknown("void"))
                for info in (self.returns or [])
            ]
        param_overrides = _build_param_override_by_index(
            list(self.parameters or []),
            list(updated_signature.parameters or []),
        )
        if param_overrides and not return_overridden_to_void:
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

        updated_return_type_provenance = self._return_type_provenance_with_hypothesis(
            hypothesis_payload,
            updated_signature.return_type,
            updated_signature.return_type_obj,
            return_changed=return_changed,
        )

        return replace(
            self,
            return_type=updated_signature.return_type,
            return_type_obj=updated_signature.return_type_obj,
            parameters=updated_signature.parameters or [],
            returns=updated_returns,
            comparison_surface=None if return_changed else self.comparison_surface,
            analysis_notes=updated_notes,
            signature_hypotheses=updated_hypotheses,
            return_type_provenance=updated_return_type_provenance,
        )

    def _return_type_provenance_with_hypothesis(
        self,
        hypothesis_payload: Mapping[str, Any],
        return_type: Any,
        return_type_obj: Any,
        *,
        return_changed: bool,
    ) -> Dict[str, Any]:
        provenance = dict(self.return_type_provenance or self._build_return_type_provenance())
        provenance["object_derived"] = True
        provenance["return_type"] = get_data_type_display_name(return_type_obj, return_type)
        provenance["declared_return_type_width"] = get_declared_type_size_bits(
            return_type_obj,
            provenance.get("return_type"),
        )
        if not return_changed:
            return provenance
        phase = hypothesis_payload.get("phase")
        resolved = hypothesis_payload.get("resolved_return_override")
        resolved_source = resolved.get("source") if isinstance(resolved, Mapping) else None
        evidence = hypothesis_payload.get("evidence")
        if not isinstance(evidence, Mapping):
            evidence = {}
        provenance["signature_hypothesis_phase"] = phase
        provenance["resolved_return_override_source"] = resolved_source
        if resolved_source:
            provenance["return_type_source"] = resolved_source
        elif phase:
            provenance["return_type_source"] = phase
        if "counterpart_return_type" in evidence:
            provenance["counterpart_return_type"] = evidence.get("counterpart_return_type")
        return provenance

    def has_expansion_budget_truncation(self) -> bool:
        """展開ケース数・経路数の上限で実際に切り捨てが起きたか（Issue #131）。

        解析面の marker が非空か、効果要約が
        ``effect_expansion_case_budget_exceeded`` を持つ場合に True。
        どちらか一方だけでも「観測したケース集合が全体である」ことは言えないので、
        網羅性・決定的 SAT・無条件 EQ の各 gate はこれを共通判定として使う。
        """

        if tuple(self.expansion_budget_truncations or ()):
            return True
        effect_summary = getattr(self, "effect_summary", None)
        effect_reasons = getattr(effect_summary, "incomplete_reasons", ())
        if not isinstance(effect_reasons, (list, tuple, set, frozenset)):
            return False
        return EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON in effect_reasons

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
        # Issue #131 PR-B: 生き残ったケースが SAT でも、捨てられたケースを
        # 見ていない以上「非等価の決め手」にはできない。
        if self.has_expansion_budget_truncation():
            reasons.append(EXPANSION_CASE_BUDGET_EXCEEDED_REASON)
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

        if (
            "effect_call_argument_evidence_incomplete" not in reasons
            and getattr(self, "deferred_calls", None)
        ):
            for deferred_call in self.deferred_calls.values():
                if (
                    getattr(deferred_call, "call_argument_recovery_status", None)
                    == "inconclusive"
                ):
                    reasons.append("effect_call_argument_evidence_incomplete")
                    break

        return reasons

    def get_equivalence_blocking_unsafety_reasons(self) -> List[str]:
        """
        UNSAT を「等価の決め手」として扱うには危険な解析要因を列挙する。

        return value が全ペア UNSAT でも、side-effect summary が不完全なら
        モデル化されていない STORE/CALL 効果を等価証明から落としているため、
        final EQUIVALENT にはしない。
        """
        reasons: List[str] = []
        # Issue #131 PR-B: 生存ケースが全ペア UNSAT でも、捨てられたケースは
        # 比較対象に入っていない。coverage 証明を経由しない経路でも塞ぐ。
        if self.has_expansion_budget_truncation():
            reasons.append(EXPANSION_CASE_BUDGET_EXCEEDED_REASON)
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
                "effect_call_argument_evidence_incomplete",
            } and note not in reasons:
                reasons.append(note)

        if (
            "effect_call_argument_evidence_incomplete" not in reasons
            and getattr(self, "deferred_calls", None)
        ):
            for deferred_call in self.deferred_calls.values():
                if (
                    getattr(deferred_call, "call_argument_recovery_status", None)
                    == "inconclusive"
                ):
                    reasons.append("effect_call_argument_evidence_incomplete")
                    break
        return reasons

    def _expr_bit_width(self, expr) -> int:
        if expr is None:
            return 0
        try:
            from scripts.function_tracer_pcode.core.render_smt import expression_smt_bit_width

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
        from scripts.function_tracer_pcode.core.signature import get_declared_type_size_bits

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

    def memory_effect_surface_bit_width(self) -> int:
        """``memory_effect`` 比較面の幅（ビット）。

        比較面の幅の権威は、ソルバーが実際に比較する ``returns`` の値式である。
        void 関数では副作用要約 ``effect_summary.synthetic_expr`` がそのまま
        return 値になるため両者は一致するが、store と戻り値を結合した面
        （``observable_effects_and_return_value``）では return 値の方が広い。
        return 値から幅が取れない場合に限り ``synthetic_expr`` へ戻る。
        幅が得られなければ 0。
        """

        return derive_memory_effect_bit_width(
            self.returns, getattr(self, "effect_summary", None), self._expr_bit_width
        )

    def _derive_void_effect_surface(self) -> Optional[ComparisonSurface]:
        effect_summary = getattr(self, "effect_summary", None)
        synthetic_expr = getattr(effect_summary, "synthetic_expr", None) if effect_summary is not None else None
        if synthetic_expr is None:
            return None

        bit_width = self.memory_effect_surface_bit_width()
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

        from scripts.function_tracer_pcode.core.signature import (
            get_data_type_display_name,
            is_void_data_type,
        )

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

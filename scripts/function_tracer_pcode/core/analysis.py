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
from scripts.function_tracer_pcode.core import live_values
from scripts.function_tracer_pcode.core.json_encoding import (
    RESULT_JSON_POLICY,
    as_dict,
    as_list,
    audited_generator,
    each,
    identity_key_of,
    materialize,
    nested,
    pairs_of,
    receiver_items,
)
from scripts.function_tracer_pcode.core.signature import (
    clone_parameter_descriptor,
    parameter_descriptor_source,
    get_data_type_display_name,
    record_return_type_display,
    return_type_display_of,
    get_declared_type_size_bits,
    is_void_data_type,
    is_unsigned_data_type,
)
from scripts.function_tracer_pcode.core.call_target import CallTargetRef, coerce_call_target_ref
from scripts.function_tracer_pcode.core.semantic_freeze import (
    freeze_condition,
    freeze_expression,
    publish_semantic_values,
)
from scripts.function_tracer_pcode.core.parameter_domain import (
    ParameterDomainHypothesis,
    ParameterDomainSealError,
    RawParameterDomains,
    parameter_domain_hypotheses_between,
    parameter_domain_hypotheses_payload_of,
    parameter_descriptor_index,
    raw_parameter_domains_divergence_of,
    record_parameter_domain_view,
    seal_parameter_table,
)
from scripts.function_tracer_pcode.core.runtime_refs import (
    EFFECT_EXPANSION_CASE_BUDGET_EXCEEDED_REASON,
    EXPANSION_CASE_BUDGET_EXCEEDED_REASON,
    CallModelCandidateRef,
    DeferredCallRef,
    ExpansionBudgetTruncation,
    PcodeBlockRef,
    PcodeOpRef,
    UnknownValueRef,
    normalize_expansion_budget_truncations,
)
from scripts.function_tracer_pcode.core.live_values import package_instance


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

    def json_items(self):
        yield "schema_version", live_values.as_int(self.schema_version)
        yield "terminal_op_ref", self.terminal_op_ref
        yield "coverage_status", self.coverage_status
        yield "path_block_keys", nested(self.path_block_keys)
        yield "path_guard_keys", nested(self.path_guard_keys)
        yield "pruning_proof_keys", nested(self.pruning_proof_keys)
        yield "guard_rewrite_proof_keys", nested(self.guard_rewrite_proof_keys)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


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
    #: Issue #297: recurrence summary の member が、関数の RETURN の値を表すことの証拠
    #: （``core.recurrence_return_binding.CountedLoopReturnBindingEvidence``）。builder が付け、
    #: proposal に載る。出力・fingerprint には入れない（proposal の digest が identity を持つ）。
    summary_return_binding_evidence: Optional[Any] = None

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
    
    def json_items(self):
        yield "address", self.address
        yield "value", self.value
        yield "conditions", each(self.conditions)
        yield "branch_index", self.branch_index
        if self.pcode_identity is not None:
            yield "pcode_identity", self.pcode_identity
        if self.pcode_order is not None:
            yield "pcode_order", self.pcode_order
        if self.pcode_time is not None:
            yield "pcode_time", self.pcode_time
        if self.pcode_op_ref is not None:
            yield "pcode_op_ref", self.pcode_op_ref
        if live_values.as_bool(self.return_value_pcode_op_refs):
            yield "return_value_pcode_op_refs", each(self.return_value_pcode_op_refs)
        certificate = self.return_value_flow_certificate
        if certificate is not None:
            # identity の owner（`stable_key`）が作る key をそのまま写す（method は型から引く）
            has_key, certificate_key = identity_key_of(certificate, names=("stable_key",))
            if not has_key:
                raise TypeError("return_value_flow_certificate has no stable_key")
            yield "return_value_flow_certificate", nested(certificate_key)
        if live_values.str_value(self.return_kind) != "exact":
            yield "return_kind", self.return_kind
        if self.retained_exact_return_ref is not None:
            yield "retained_exact_return_ref", nested(self.retained_exact_return_ref)
        if self.acceptance_status is not None:
            yield "acceptance_status", self.acceptance_status
        if self.summary_candidate_id is not None:
            yield "summary_candidate_id", nested(self.summary_candidate_id)
        if self.summary_candidate_source_key is not None:
            yield "summary_candidate_source_key", nested(self.summary_candidate_source_key)
        if self.summary_transition_evidence_key is not None:
            yield "summary_transition_evidence_key", nested(self.summary_transition_evidence_key)
        if live_values.as_bool(self.validation_blockers):
            yield "validation_blockers", as_list(self.validation_blockers)
        if self.return_path_evidence is not None:
            yield "return_path_evidence", self.return_path_evidence

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass
class ReturnOutcome:
    """A returning member of a function outcome partition."""

    guard: Tuple[Condition, ...]
    value: Expression
    storage: Optional[Tuple[Any, ...]] = None
    provenance: Dict[str, Any] = field(default_factory=dict)
    return_info: Optional[ReturnInfo] = None

    def json_items(self):
        yield "kind", "return"
        yield "guard", each(self.guard)
        yield "value", self.value
        yield "provenance", nested(self.provenance)
        if self.storage is not None:
            yield "storage", nested(self.storage)
        if self.return_info is not None:
            yield "return_info", self.return_info

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass
class DivergenceOutcome:
    """A must-diverge member of a function outcome partition."""

    guard: Tuple[Condition, ...]
    proof: Dict[str, Any] = field(default_factory=dict)

    def json_items(self):
        yield "kind", "divergence"
        yield "guard", each(self.guard)
        yield "proof", nested(self.proof)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass
class UnknownOutcome:
    """An unproved member of an outcome partition."""

    guard: Tuple[Condition, ...]
    reason: str
    evidence: Dict[str, Any] = field(default_factory=dict)

    def json_items(self):
        yield "kind", "unknown"
        yield "guard", each(self.guard)
        yield "reason", self.reason
        yield "evidence", nested(self.evidence)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


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

    def json_items(self):
        yield "schema_version", live_values.as_int(self.schema_version)
        yield "termination_class", self.termination_class
        yield "object_identity_key", nested(self.object_identity_key)
        yield "payload_key", nested(self.payload_key)
        yield "effect_key", nested(self.effect_key)
        yield "observation_contract_key", nested(self.observation_contract_key)
        yield "source_contract_key", nested(self.source_contract_key)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
class TerminationPathEffectEvidence:
    """Producer output kept outside the semantic outcome seed until validated."""

    terminal_candidate_id: Tuple[Any, ...]
    terminal_op_ref: PcodeOpRef
    control_effect_profile_key: Tuple[Any, ...]
    path_guard_key: Tuple[Any, ...]
    contract: TerminationContractRef
    path_guard: Tuple[Condition, ...] = field(default=(), repr=False, compare=False)
    #: payload が構造 key で比べる引数の式（key は ``contract.payload_key`` が持つ）。
    #: 入力の射影 closure がこの式を走査する。None は「記録していない」で、走査できない。
    payload_arguments: Optional[Tuple[Any, ...]] = field(default=None, repr=False, compare=False)
    producer_id: str = "analyzer_terminal_path_effect_v1"
    schema_version: int = 1

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "termination_path_effect_evidence_v1", int(self.schema_version), self.producer_id,
            self.terminal_candidate_id, self.terminal_op_ref.stable_key(),
            self.control_effect_profile_key, self.path_guard_key, self.contract.stable_key(),
        )

    def json_items(self):
        yield "schema_version", live_values.as_int(self.schema_version)
        yield "producer_id", self.producer_id
        yield "terminal_candidate_id", nested(self.terminal_candidate_id)
        yield "terminal_op_ref", self.terminal_op_ref
        yield "control_effect_profile_key", nested(self.control_effect_profile_key)
        yield "path_guard_key", nested(self.path_guard_key)
        yield "path_guard", each(self.path_guard)
        yield "contract", self.contract

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


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

    def json_items(self):
        yield "candidate_id", nested(self.candidate_id)
        yield "terminal_kind_candidate", self.terminal_kind_candidate
        yield "block_ref", self.block_ref
        yield "op_ref", self.op_ref
        yield "cfg_reachable", self.cfg_reachable
        yield "evidence_key", nested(self.evidence_key)
        yield "termination_contract", self.termination_contract

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


@dataclass(frozen=True)
class SymbolicRegionCandidate:
    """Candidate input region associated with one concrete terminal candidate."""

    candidate_id: Tuple[Any, ...]
    terminal_candidate_id: Tuple[Any, ...]
    guard: Tuple[Condition, ...]
    guard_extraction_complete: bool
    producer_evidence_key: Tuple[Any, ...] = ()
    observed_value: Optional[Expression] = None

    def json_items(self):
        yield "candidate_id", nested(self.candidate_id)
        yield "terminal_candidate_id", nested(self.terminal_candidate_id)
        yield "guard", each(self.guard)
        yield "guard_extraction_complete", live_values.as_bool(self.guard_extraction_complete)
        yield "producer_evidence_key", nested(self.producer_evidence_key)
        if self.observed_value is not None:
            yield "observed_value", self.observed_value

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


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

    def json_items(self):
        yield "function_identity", nested(self.function_identity)
        yield "input_domain_contract", nested(self.input_domain_contract)
        yield "terminal_candidates", each(self.terminal_candidates)
        yield "symbolic_regions", each(self.symbolic_regions)
        yield "unresolved_control_evidence", nested(self.unresolved_control_evidence)
        yield "control_flow_evidence_key", nested(self.control_flow_evidence_key)
        yield "partition_revision", live_values.as_int(self.partition_revision)
        yield "extraction_schema_version", live_values.as_int(self.extraction_schema_version)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


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

    def json_items(self):
        yield "candidate_id", nested(self.candidate_id)
        yield "return_info", self.return_info
        yield "guard_structural_key", nested(self.guard_structural_key)
        yield "value_structural_key", nested(self.value_structural_key)
        yield "loop_summary_structural_key", nested(self.loop_summary_structural_key)
        yield "transition_evidence_key", nested(self.transition_evidence_key)
        yield "active_precondition_key", nested(self.active_precondition_key)
        yield "summary_applicability_guard_key", nested(self.summary_applicability_guard_key)
        yield "effect_region_key", nested(self.effect_region_key)
        yield "memory_read_set_key", nested(self.memory_read_set_key)
        yield "memory_write_set_key", nested(self.memory_write_set_key)
        yield "call_effect_key", nested(self.call_effect_key)
        yield "ub_assumption_key", nested(self.ub_assumption_key)
        yield "effect_model_schema_version", self.effect_model_schema_version
        yield "eq_eligible", live_values.as_bool(self.eq_eligible)
        yield "acceptance_status", self.acceptance_status
        yield "validation_blockers", as_list(self.validation_blockers)
        yield "evidence", nested(self.evidence)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


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
    #: 呼び出しの op の program point の key（記録した関数の `core.program_order`。Issue #281 / #285）。
    #: callee の読み出しをこの位置へ移す（`analysis.effects.call_boundary.CallSite.for_deferred_call`）。
    #: 同じ関数の中だけで意味を持つ位置で、比べる面（`identity_key` / `match_evidence`）には入れない
    call_site_order_key: Optional[int] = None

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
        call_site_order_key: Optional[int] = None,
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
        self.call_site_order_key = None if call_site_order_key is None else int(call_site_order_key)

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
            call_site_order_key=self.call_site_order_key,
        )

    @property
    def placeholder_name(self) -> str:
        hint = self.display_hint
        if hint is not None and live_values.as_bool(hint):
            return hint
        deferred_call_ref = self.deferred_call_ref
        if package_instance(deferred_call_ref, DeferredCallRef):
            return deferred_call_ref.display_name()
        # 呼び出し地点の参照は `DeferredCallRef`（`__init__` が作る）。それ以外の値の method は呼ばない
        raise TypeError(f"deferred_call_ref is not a DeferredCallRef ({live_values.type_name(type(deferred_call_ref))})")

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
        target_ref = self.target_ref
        if package_instance(target_ref, CallTargetRef):
            return target_ref.display_name()
        # 呼び出し先の参照は `CallTargetRef`（`__init__` が正規化する）。それ以外の値の method は呼ばない
        raise TypeError(f"target_ref is not a CallTargetRef ({live_values.type_name(type(target_ref))})")

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

    def json_items(self):
        yield "placeholder_name", self.placeholder_name
        yield "target_name", self.target_name
        yield "deferred_call_ref", self.deferred_call_ref
        yield "target_ref", self.target_ref
        yield "unknown_ref", self.unknown_ref
        yield "arguments", each(self.arguments)
        yield "call_argument_recovery_status", self.call_argument_recovery_status
        yield "call_argument_recovery_reason", self.call_argument_recovery_reason
        yield "effect_class", self.effect_class
        yield "match_evidence", nested(self.match_evidence)
        yield "domain_policy", nested(self.domain_policy)
        yield "abi_return_width_bits", self.abi_return_width_bits
        yield "abi_return_type_policy", self.abi_return_type_policy
        yield "call_site_multiplicity", self.call_site_multiplicity
        if self.call_target_expr is not None:
            yield "call_target_expr", self.call_target_expr
        if self.call_model_candidate is not None:
            yield "call_model_candidate", self.call_model_candidate

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


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
    
    def json_items(self):
        yield "signedness", self.signedness
        yield "evidence_summary", self.evidence_summary
        yield "opcode_counts", self.opcode_counts
        if live_values.as_int(self.excluded_fastpath_count) > 0:
            yield "excluded_fastpath_count", self.excluded_fastpath_count
            yield "excluded_opcode_counts", self.excluded_opcode_counts

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)
    
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

    def json_items(self):
        yield "kind", self.kind
        yield "explicit_bit_width", self.explicit_bit_width
        yield "type_name", self.type_name
        yield "use_sign_extension", self.use_sign_extension
        yield "evidence", as_dict(self.evidence)

    def to_dict(self) -> Dict[str, Any]:
        return materialize(self)


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


#: 解析 1 件分の直列化の作業量を数える観測点（`ExpressionSizeBudgetExceeded.site`）。
#: monolithic fallback を止める理由（``FunctionReturnAnalysis.monolithic_fallback_skip_reasons`` の code）。
#: 各理由で止めた比較の UNKNOWN を説明する cause の owner は 1 つの表
#: （``authority.domains.return_coverage.MONOLITHIC_FALLBACK_SKIP_CAUSE_OWNERS``）が持つ（Issue #257）。
FALLBACK_SKIP_UNKNOWN_OUTCOME_PARTITION = "unknown_outcome_partition"
FALLBACK_SKIP_RETURN_COVERAGE_GAP = "return_case_coverage_gap"
FALLBACK_SKIP_RETURN_COVERAGE_INCONCLUSIVE = "return_case_coverage_inconclusive"
FALLBACK_SKIP_INCOMPLETE_CONTROL_FLOW = "incomplete_control_flow"
MONOLITHIC_FALLBACK_SKIP_REASONS = (
    FALLBACK_SKIP_UNKNOWN_OUTCOME_PARTITION,
    FALLBACK_SKIP_RETURN_COVERAGE_GAP,
    FALLBACK_SKIP_RETURN_COVERAGE_INCONCLUSIVE,
    FALLBACK_SKIP_INCOMPLETE_CONTROL_FLOW,
)

ANALYSIS_SERIALIZATION_SITE = "core.analysis.FunctionReturnAnalysis.to_dict"


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
    # Issue #282: 側の program の image の範囲（ram の空間の overlay でない block の `[lo, hi)`）。反例の番地が
    # どちらの image にも入らないことの制約（実現の条件）に使う。読めなければ None（実現を示せない）
    program_image_ranges: Optional[Tuple[Tuple[int, int], ...]] = None
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
    # Issue #185: 入力領域の正本。公開境界（``publish_raw_function_analysis``）で parameter 表から
    # 封印した baseline で、既定値を自動で作らない（None = 正本が無い = どの入力も証明されない）。
    # 書くのは ``seal_raw_parameter_domains`` だけ（複製・派生は値ごと引き継ぐ）。
    raw_parameter_domains: Optional[RawParameterDomains] = None
    # Issue #185: 封印の後に parameter の領域を変えた仮説の台帳（provenance。proof ではない）。
    parameter_domain_hypotheses: Tuple[ParameterDomainHypothesis, ...] = ()
    # Issue #297: この解析の HighFunction から取った P-code の事実の写し（``PcodeDataflowSnapshot``）の
    # digest。写しを作った producer が、同じ解析に 1 度だけ書く（successor は引き継ぐ。再解析は新しい
    # 解析なので None から始まる）。return binding の証拠は、この digest と一致しなければ使えない。
    # 出力・fingerprint には入れない（P-code の写しは解析の前提ではなく、証拠の出所の確認に使う）。
    pcode_dataflow_digest: Optional[str] = None

    def __setattr__(self, name: str, value: Any) -> None:
        if name == "expansion_budget_truncations":
            # Issue #131: 記録の順だけの違いは同じ値（正規化は同一性の規則）。書いたときに 1 度だけ
            # 正規化する（記録と参照の和は owner の固定の上限の中。超えれば解析の時点の登録済みの限界）。
            # 出力・fingerprint の walker は正規化済みの記録を数えながら写すだけ
            value = normalize_expansion_budget_truncations(value)
        record_return_type_display(self, name, value)
        # Issue #185: 出力する入力領域の写しも書いたときに作る（出力は live な値の code を呼ばない）
        record_parameter_domain_view(self, name)

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

    def seal_raw_parameter_domains(self) -> "FunctionReturnAnalysis":
        """いまの parameter 表を入力領域の正本として封印する（Issue #185）。

        公開境界（``publish_raw_function_analysis``）だけが呼ぶ。仮説の載った解析（overlay）、
        既に封印した解析は封印できない: 正本は「仮説より前の raw の表」でなければならず、
        作り直すと仮説で変えた表が正本に化ける。表の形の悪さ（重複・欠落した index）は
        例外にせず、その index を認証しないと記録する（``seal_parameter_table``）。
        """

        if self.raw_parameter_domains is not None:
            raise ParameterDomainSealError("raw_parameter_domains_already_sealed")
        if self.signature_hypotheses or self.parameter_domain_hypotheses:
            raise ParameterDomainSealError("hypothesis_view_cannot_be_sealed_as_raw")
        self.raw_parameter_domains = seal_parameter_table(self.parameters)
        return self

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

        # Issue #185: 入力領域の正本と台帳は派生で書き換えない（正本は公開境界の封印だけが作り、
        # 台帳は仮説の適用だけが追記する）。差し替えると仮説を経た式が raw の式に化ける
        authority_changes = {"raw_parameter_domains", "parameter_domain_hypotheses"}.intersection(changes)
        if authority_changes:
            raise ValueError(
                "semantic_successor cannot replace the input-domain authority: "
                + ", ".join(sorted(authority_changes))
            )

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
        return self._materialize(include_derived_proof=True)

    def semantic_snapshot_dict(self) -> Dict:
        """snapshot が使う表現（`to_dict()` から、解析前提でない derived proof を除いたもの）。

        snapshot は完了した recovery proof の id / evidence を捨てる（実行状態で、
        解析前提の identity ではない）ので、作りも数えもしない。残りは `to_dict()` と
        同じ値。
        """

        return self._materialize(include_derived_proof=False)

    def _materialize(self, *, include_derived_proof: bool) -> Dict:
        # Issue #22 PR-22-D: 解析 1 件分の表現は **まとめて** 1 つの直列化の作業量
        # （`core/budget_policy.SerializationWork`、`JsonBudget` の一種）。walker が
        # `json_items()` から 1 要素ずつ引き出して数え、合計が予算を超えた時点で
        # 残りを作らずに限界になる（木は作る前に DAG のまま大きさを数える）。
        from scripts.function_tracer_pcode.core.budget_policy import serialization_scope

        with serialization_scope(
            site=ANALYSIS_SERIALIZATION_SITE,
            target_parts=(
                "function_return_analysis",
                self.binary_id,
                self.function_name,
                self.entry_point,
            ),
        ) as work:
            return RESULT_JSON_POLICY.materialize(
                receiver_items(self, "_json_items", include_derived_proof=include_derived_proof),
                budget=work,
            )

    def json_items(self):
        # 委ねる（`yield from`）: walker はこの generator を record を receiver として進め、再開の前に確かめ直す
        yield from self._json_items(include_derived_proof=True)

    @audited_generator
    def _json_items(self, *, include_derived_proof: bool):
        """表現の schema（1 つだけ）。値は source で渡し、walker が 1 要素ずつ写す。"""

        yield "function_name", self.function_name
        yield "entry_point", self.entry_point
        yield "binary_id", self.binary_id
        yield "function_ref", self.function_ref
        yield "parameters", (
            None if self.parameters is None
            else each(self.parameters, parameter_descriptor_source)
        )
        yield "returns", each(self.returns)
        # 表示名は field を書いたときに作った文字列（Ghidra の object の code を出力で呼ばない）
        yield "return_type", return_type_display_of(self)
        yield "unknown_event_count", self.unknown_event_count
        yield "unknown_event_reasons", as_list(self.unknown_event_reasons)
        yield "analysis_notes", as_list(self.analysis_notes)
        yield "recovered_from_decompiler", self.recovered_from_decompiler
        yield "incomplete_control_flow", self.incomplete_control_flow
        yield "deferred_calls", each(live_values.values_of(self.deferred_calls))
        if include_derived_proof and live_values.as_bool(self.completed_recovery_proof_ids):
            yield "completed_recovery_proof_ids", each(self.completed_recovery_proof_ids, nested)
        if include_derived_proof and live_values.as_bool(self.completed_recovery_proof_evidence):
            yield "completed_recovery_proof_evidence", each(
                self.completed_recovery_proof_evidence, nested,
            )
        if live_values.as_bool(self.summary_return_candidates):
            yield "summary_return_candidates", each(self.summary_return_candidates)
        return_outcomes = self.return_outcomes
        divergence_outcomes = self.divergence_outcomes
        unknown_outcomes = self.unknown_outcomes
        if (
            live_values.as_bool(return_outcomes)
            or live_values.as_bool(divergence_outcomes)
            or live_values.as_bool(unknown_outcomes)
        ):
            # 3 つの列を順に 1 要素ずつ（列を連結・複製しない）
            yield "outcomes", each(_outcomes_in_order(return_outcomes, divergence_outcomes, unknown_outcomes))
        if self.outcome_seed is not None:
            yield "outcome_seed", self.outcome_seed
        if live_values.as_bool(self.termination_path_effect_evidence):
            yield "termination_path_effect_evidence", each(self.termination_path_effect_evidence)
        if self.analysis_scope_key is not None:
            yield "analysis_scope_key", self.analysis_scope_key
        if self.analysis_view_identity is not None:
            yield "analysis_view_identity", nested(self.analysis_view_identity)
            partition_revision = self.partition_revision
            yield "partition_revision", (
                live_values.as_int(partition_revision) if live_values.as_bool(partition_revision) else 0
            )
        if self.program_is_big_endian is not None:
            yield "program_is_big_endian", live_values.as_bool(self.program_is_big_endian)
        if self.program_image_ranges is not None:
            yield "program_image_ranges", self.program_image_ranges

        if live_values.as_bool(self.signedness_result):
            yield "signedness", self.signedness_result
        if live_values.as_bool(self.signature_hypotheses):
            yield "signature_hypotheses", as_list(self.signature_hypotheses)
        # Issue #185: 正本が現在の表と同じ（production の raw 解析の既定の姿）なら出さない。
        # 違うとき（仮説・abstraction・作り直し）と台帳があるときだけ、解析前提の同一性に入る。
        raw_parameter_domains_divergence = raw_parameter_domains_divergence_of(self)
        if raw_parameter_domains_divergence is not None:
            yield "raw_parameter_domains", raw_parameter_domains_divergence
        parameter_domain_hypotheses = parameter_domain_hypotheses_payload_of(self)
        if parameter_domain_hypotheses is not None:
            yield "parameter_domain_hypotheses", each(parameter_domain_hypotheses)
        if live_values.as_bool(self.return_type_provenance):
            yield "return_type_provenance", nested(self.return_type_provenance)
        if live_values.as_bool(self.return_abi_facts):
            yield "return_abi_facts", nested(self.return_abi_facts)
        if self.comparison_surface is not None:
            yield "comparison_surface", self.comparison_surface
        if live_values.as_bool(self.expansion_budget_truncations):
            # Issue #131 PR-B: 正規化済みの全記録（参照 event ID 込み）を出す。
            # snapshot fingerprint は ``to_dict`` から作られるので、marker の有無・
            # 参照情報の増加はそのまま解析前提の同一性に反映される（記録の順だけの違いは同じ
            # 値: 正規化は同一性の規則）。正規化は field を書いたとき（`__setattr__`）に済んでいる
            yield "expansion_budget_truncations", each(self.expansion_budget_truncations)

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

    def has_unresolved_memory_read_aliases(self) -> bool:
        """SMT に入る入口の memory の読み出しのうち、先行し得る store との関係（重ならない）を証明できないものが
        あるか（Issue #282, I3）。判定は `analysis.effects.read_validation` が持つ。EQ と NOT_EQ の両方を止める。"""

        from scripts.function_tracer_pcode.analysis.effects.summary import unresolved_memory_read_aliases

        return bool(unresolved_memory_read_aliases(self))

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
        return bool(self.monolithic_fallback_skip_reasons())

    def monolithic_fallback_skip_reasons(self) -> Tuple[str, ...]:
        """monolithic fallback を止める理由（``MONOLITHIC_FALLBACK_SKIP_REASONS`` の code、並びはその順）。"""
        reasons: List[str] = []
        if self.has_unknown_outcome_partition():
            reasons.append(FALLBACK_SKIP_UNKNOWN_OUTCOME_PARTITION)
        if FALLBACK_SKIP_RETURN_COVERAGE_GAP in self.analysis_notes:
            reasons.append(FALLBACK_SKIP_RETURN_COVERAGE_GAP)
        if FALLBACK_SKIP_RETURN_COVERAGE_INCONCLUSIVE in self.analysis_notes:
            reasons.append(FALLBACK_SKIP_RETURN_COVERAGE_INCONCLUSIVE)
        if (
            not self.recovered_from_decompiler
            and self.incomplete_control_flow
            and (self.has_unresolved_return_value() or self.has_overlapping_unconditional_returns())
        ):
            reasons.append(FALLBACK_SKIP_INCOMPLETE_CONTROL_FLOW)
        return tuple(reasons)

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
        # Issue #185: 領域の変わった index を台帳へ（override の位置 → index の変換は台帳の
        # 側で閉じる）。台帳は provenance で、最終 relation はこの記録を十分性にしない。
        updated_domain_hypotheses = self.parameter_domain_hypotheses + parameter_domain_hypotheses_between(
            self.parameters,
            updated_signature.parameters,
            phase=hypothesis.phase,
            source_of=_hypothesis_source_by_index(hypothesis, updated_signature.parameters),
        )

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
            parameter_domain_hypotheses=updated_domain_hypotheses,
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
        if self.has_unresolved_memory_read_aliases():
            reasons.append("memory_read_alias_unresolved")
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
        # Issue #282 (I3): 先行し得る store と重なり得る入口の memory の読み出しは、入口の値で描くと store を
        # 無視した値になる（偽 EQ の形）
        if self.has_unresolved_memory_read_aliases():
            reasons.append("memory_read_alias_unresolved")
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


def _hypothesis_source_by_index(hypothesis: Any, updated_parameters: Any):
    """台帳の ``source``: 型仮説の override（位置で書かれる）の解決元を、記述子の index で引く。"""

    by_index: Dict[int, str] = {}
    parameters = list(updated_parameters or [])
    for position, spec in dict(getattr(hypothesis, "resolved_parameter_overrides", None) or {}).items():
        try:
            descriptor = parameters[int(position)]
            index = int(parameter_descriptor_index(descriptor))
        except (IndexError, TypeError, ValueError):
            continue
        source = getattr(spec, "source", None)
        if source:
            by_index[index] = str(source)
    default = str(getattr(hypothesis, "reason", "") or getattr(hypothesis, "phase", "") or "signature_hypothesis")
    return lambda index: by_index.get(index, default)


def publish_raw_function_analysis(container: Any) -> Any:
    """解析の公開境界（Issue #185）: 意味値を公開し、raw の parameter 表を入力領域の正本として封印する。

    ``analysis/returns/lifecycle.py`` の公開点と、それを模す test の producer だけが呼ぶ。
    ``FunctionReturnAnalysis`` でない値（sentinel）は公開だけして素通しにする。既に封印した
    解析（analyzer の cache が同じ object を返したもの）は最初の封印をそのまま正本にする
    （封印し直さない。後から表が変わっていれば、それは baseline との差として見える）。
    """

    published = publish_semantic_values(container)
    if isinstance(published, FunctionReturnAnalysis) and published.raw_parameter_domains is None:
        published.seal_raw_parameter_domains()
    return published


def _outcomes_in_order(*groups: Any):
    """outcome の列を順に 1 要素ずつ返す（列は owner の API で辿る。上書きした `__iter__` を呼ばない）。

    `flatten` は空の列にも 1 を数えるので、出力 byte と作業量を一致させる snapshot の
    勘定（`FunctionReturnAnalysis._materialize`）では使わない。
    """

    for group in groups:
        yield from live_values.elements_of(group)

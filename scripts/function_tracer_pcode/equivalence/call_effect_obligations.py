# -*- coding: utf-8 -*-
"""Typed, decision-neutral call/effect proof obligations.

This module is the shadow-model boundary for replacing the legacy policy that
treats the presence of call evidence as an equivalence blocker.  It deliberately
does not discharge a blocker: facts are extracted per binary, relational
obligations are constructed across binaries, and a coupling manifest records
coverage and ambiguity for later solver-backed proof stages.

Ghidra runtime objects must not cross this boundary.  Only object-derived,
serializable identities and semantic keys are retained.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import json
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple, Union

from ..model import FunctionReturnAnalysis, expression_provenance_key


SCHEMA_VERSION = 1
_INTERNAL_SOLVER_PRODUCER_TOKEN = object()


def _jsonable(value: Any) -> Any:
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, Mapping):
        return {
            str(key): _jsonable(item)
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
        }
    if isinstance(value, (tuple, list)):
        return [_jsonable(item) for item in value]
    if isinstance(value, (set, frozenset)):
        items = [_jsonable(item) for item in value]
        return sorted(items, key=lambda item: json.dumps(item, sort_keys=True, default=str))
    stable_key = getattr(value, "stable_key", None)
    if callable(stable_key):
        try:
            return _jsonable(stable_key())
        except Exception:
            pass
    # Do not serialize repr(value): Java proxy reprs and object addresses are not
    # stable semantic identities.  The marker also makes incompleteness visible.
    value_type = type(value)
    return {
        "unsupported_runtime_object": f"{value_type.__module__}.{value_type.__qualname__}",
    }


def _digest(value: Any) -> str:
    payload = json.dumps(
        _jsonable(value),
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _stable_key(value: Any) -> Optional[Tuple[Any, ...]]:
    stable_key = getattr(value, "stable_key", None)
    if not callable(stable_key):
        return None
    try:
        result = stable_key()
    except Exception:
        return None
    return tuple(result) if isinstance(result, (tuple, list)) else None


def _expression_key(value: Any) -> Optional[Tuple[Any, ...]]:
    if value is None:
        return None
    try:
        result = expression_provenance_key(value)
    except Exception:
        return None
    return tuple(result) if isinstance(result, (tuple, list)) else None


def _condition_key(value: Any) -> Optional[Tuple[Any, ...]]:
    if value is None:
        return None
    structural_key = getattr(value, "structural_key", None)
    if callable(structural_key):
        try:
            result = structural_key()
        except Exception:
            result = None
        if isinstance(result, (tuple, list)):
            return (
                "condition",
                bool(getattr(value, "negated", False)),
                tuple(result),
            )
    expression = getattr(value, "expression", None)
    expression_key = _expression_key(expression)
    if expression_key is None:
        return None
    return ("condition", bool(getattr(value, "negated", False)), expression_key)


@dataclass(frozen=True)
class EquivalenceObservationContract:
    """Explicit observation boundary shared by every relational proof."""

    contract_name: str = "eqbench_single_threaded_c_abi"
    observe_return_value: bool = True
    observe_parameter_reachable_memory: bool = True
    observe_globals: bool = True
    observe_tls: bool = True
    observe_heap: bool = True
    observe_volatile: bool = True
    observe_io: bool = True
    observe_userops: bool = True
    observe_termination: bool = True
    observe_traps: bool = True
    observe_errno: bool = False
    observe_fenv: bool = False
    abi_clobber_policy: str = "calling_convention_visible_state"
    undefined_behavior_policy: str = "unknown_unless_shared_defined_domain_proven"
    nondeterminism_policy: str = "unknown_unless_relationally_coupled"
    concurrency_policy: str = "out_of_scope"
    schema_version: int = SCHEMA_VERSION

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "equivalence_observation_contract",
            int(self.schema_version),
            self.contract_name,
            self.observe_return_value,
            self.observe_parameter_reachable_memory,
            self.observe_globals,
            self.observe_tls,
            self.observe_heap,
            self.observe_volatile,
            self.observe_io,
            self.observe_userops,
            self.observe_termination,
            self.observe_traps,
            self.observe_errno,
            self.observe_fenv,
            self.abi_clobber_policy,
            self.undefined_behavior_policy,
            self.nondeterminism_policy,
            self.concurrency_policy,
        )

    @property
    def contract_id(self) -> str:
        return _digest(self.stable_key())

    def to_dict(self) -> Dict[str, Any]:
        return {
            "schema_version": int(self.schema_version),
            "contract_id": self.contract_id,
            "contract_name": self.contract_name,
            "observe_return_value": self.observe_return_value,
            "observe_parameter_reachable_memory": self.observe_parameter_reachable_memory,
            "observe_globals": self.observe_globals,
            "observe_tls": self.observe_tls,
            "observe_heap": self.observe_heap,
            "observe_volatile": self.observe_volatile,
            "observe_io": self.observe_io,
            "observe_userops": self.observe_userops,
            "observe_termination": self.observe_termination,
            "observe_traps": self.observe_traps,
            "observe_errno": self.observe_errno,
            "observe_fenv": self.observe_fenv,
            "abi_clobber_policy": self.abi_clobber_policy,
            "undefined_behavior_policy": self.undefined_behavior_policy,
            "nondeterminism_policy": self.nondeterminism_policy,
            "concurrency_policy": self.concurrency_policy,
        }


@dataclass(frozen=True)
class ArtifactObjectIdentity:
    """Serializable identity; never owns a Function/HighFunction/PcodeOpAST."""

    binary_id: Optional[str]
    function_key: Optional[Tuple[Any, ...]]
    pcode_op_key: Optional[Tuple[Any, ...]] = None
    artifact_digest: Optional[str] = None
    schema_version: int = SCHEMA_VERSION

    def stable_key(self) -> Tuple[Any, ...]:
        return (
            "artifact_object_identity",
            int(self.schema_version),
            self.artifact_digest,
            self.binary_id,
            self.function_key,
            self.pcode_op_key,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "schema_version": int(self.schema_version),
            "artifact_digest": self.artifact_digest,
            "binary_id": self.binary_id,
            "function_key": _jsonable(self.function_key),
            "pcode_op_key": _jsonable(self.pcode_op_key),
        }


@dataclass(frozen=True)
class CallSiteFact:
    fact_id: str
    identity: ArtifactObjectIdentity
    operation_kind: str
    target_candidates: Tuple[Tuple[Any, ...], ...] = ()
    target_categories: Tuple[str, ...] = ()
    target_resolution_status: str = "inconclusive"
    argument_keys: Tuple[Tuple[Any, ...], ...] = ()
    argument_shape_keys: Tuple[Tuple[Any, ...], ...] = ()
    callee_parameter_keys: Tuple[Tuple[Any, ...], ...] = ()
    guard_keys: Tuple[Tuple[Any, ...], ...] = ()
    call_site_multiplicity: Optional[int] = None
    effect_classes: Tuple[str, ...] = ()
    callee_effect_summary_statuses: Tuple[str, ...] = ()
    callee_memory_effect_counts: Tuple[int, ...] = ()
    callee_has_unsupported_nested_call: bool = False
    callee_control_profile_keys: Tuple[Tuple[Any, ...], ...] = ()
    callee_recursive_scc_proven: bool = False
    callee_recursive_scc_identities: Tuple[str, ...] = ()
    callee_recursive_scc_member_keys: Tuple[Tuple[Any, ...], ...] = ()
    callee_return_summary_statuses: Tuple[str, ...] = ()
    callee_return_shape_keys: Tuple[Tuple[Any, ...], ...] = ()
    unsupported_reasons: Tuple[str, ...] = ()
    extraction_failure_causes: Tuple[str, ...] = ()
    evidence_sources: Tuple[str, ...] = ()
    extraction_status: str = "inconclusive"

    @property
    def fact_kind(self) -> str:
        return "call_site"

    def correspondence_operation_class(self) -> str:
        if (
            self.operation_kind in {"direct_call", "indirect_call"}
            and self.target_resolution_status == "resolved"
            and self.target_categories == ("internal_function",)
            and len(self.target_candidates) == 1
        ):
            return "resolved_internal_call_candidate"
        return self.operation_kind

    def semantic_shape_key(self) -> Tuple[Any, ...]:
        # Candidate correspondence must not depend on an unproven callee return
        # relation.  Return shapes are inputs to a later proof stage only.
        return (
            self.fact_kind,
            self.correspondence_operation_class(),
            len(self.argument_keys),
            len(self.callee_parameter_keys),
            self.target_categories,
            self.argument_shape_keys,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "fact_kind": self.fact_kind,
            "fact_id": self.fact_id,
            "identity": self.identity.to_dict(),
            "operation_kind": self.operation_kind,
            "correspondence_operation_class": self.correspondence_operation_class(),
            "target_candidates": _jsonable(self.target_candidates),
            "target_categories": list(self.target_categories),
            "target_resolution_status": self.target_resolution_status,
            "argument_keys": _jsonable(self.argument_keys),
            "argument_shape_keys": _jsonable(self.argument_shape_keys),
            "callee_parameter_keys": _jsonable(self.callee_parameter_keys),
            "guard_keys": _jsonable(self.guard_keys),
            "call_site_multiplicity": self.call_site_multiplicity,
            "effect_classes": list(self.effect_classes),
            "callee_effect_summary_statuses": list(self.callee_effect_summary_statuses),
            "callee_memory_effect_counts": list(self.callee_memory_effect_counts),
            "callee_has_unsupported_nested_call": self.callee_has_unsupported_nested_call,
            "callee_control_profile_keys": _jsonable(self.callee_control_profile_keys),
            "callee_recursive_scc_proven": self.callee_recursive_scc_proven,
            "callee_recursive_scc_identities": list(self.callee_recursive_scc_identities),
            "callee_recursive_scc_member_keys": _jsonable(self.callee_recursive_scc_member_keys),
            "callee_return_summary_statuses": list(self.callee_return_summary_statuses),
            "callee_return_shape_keys": _jsonable(self.callee_return_shape_keys),
            "unsupported_reasons": list(self.unsupported_reasons),
            "extraction_failure_causes": list(self.extraction_failure_causes),
            "evidence_sources": list(self.evidence_sources),
            "extraction_status": self.extraction_status,
        }


@dataclass(frozen=True)
class UserOpFact:
    fact_id: str
    identity: ArtifactObjectIdentity
    userop_semantic_key: Optional[Tuple[Any, ...]] = None
    input_keys: Tuple[Tuple[Any, ...], ...] = ()
    guard_keys: Tuple[Tuple[Any, ...], ...] = ()
    unsupported_reason: Optional[str] = None
    extraction_status: str = "inconclusive"

    @property
    def fact_kind(self) -> str:
        return "userop"

    def semantic_shape_key(self) -> Tuple[Any, ...]:
        return (self.fact_kind, self.userop_semantic_key, len(self.input_keys))

    def to_dict(self) -> Dict[str, Any]:
        return {
            "fact_kind": self.fact_kind,
            "fact_id": self.fact_id,
            "identity": self.identity.to_dict(),
            "userop_semantic_key": _jsonable(self.userop_semantic_key),
            "input_keys": _jsonable(self.input_keys),
            "guard_keys": _jsonable(self.guard_keys),
            "unsupported_reason": self.unsupported_reason,
            "extraction_status": self.extraction_status,
        }


@dataclass(frozen=True)
class RegionBoundaryCertificate:
    entry_block_key: Tuple[Any, ...]
    exit_block_keys: Tuple[Tuple[Any, ...], ...]
    block_keys: Tuple[Tuple[Any, ...], ...]
    pcode_op_keys: Tuple[Tuple[Any, ...], ...]
    live_in_keys: Tuple[Tuple[Any, ...], ...] = ()
    live_out_keys: Tuple[Tuple[Any, ...], ...] = ()
    single_entry: bool = False
    all_exits_enumerated: bool = False
    cross_edges_enumerated: bool = False
    guard_partition_complete: bool = False

    @property
    def is_complete(self) -> bool:
        return (
            self.single_entry
            and self.all_exits_enumerated
            and self.cross_edges_enumerated
            and self.guard_partition_complete
            and bool(self.block_keys)
            and bool(self.pcode_op_keys)
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "entry_block_key": _jsonable(self.entry_block_key),
            "exit_block_keys": _jsonable(self.exit_block_keys),
            "block_keys": _jsonable(self.block_keys),
            "pcode_op_keys": _jsonable(self.pcode_op_keys),
            "live_in_keys": _jsonable(self.live_in_keys),
            "live_out_keys": _jsonable(self.live_out_keys),
            "single_entry": self.single_entry,
            "all_exits_enumerated": self.all_exits_enumerated,
            "cross_edges_enumerated": self.cross_edges_enumerated,
            "guard_partition_complete": self.guard_partition_complete,
            "is_complete": self.is_complete,
        }


@dataclass(frozen=True)
class RegionFact:
    fact_id: str
    function_identity: ArtifactObjectIdentity
    boundary: RegionBoundaryCertificate
    region_kind: str = "whole_function_inline_candidate"
    guard_key: Optional[Tuple[Any, ...]] = None
    input_relation_key: Optional[Tuple[Any, ...]] = None
    output_relation_key: Optional[Tuple[Any, ...]] = None
    state_transformer_key: Optional[Tuple[Any, ...]] = None
    termination_outcome_key: Optional[Tuple[Any, ...]] = None
    trap_outcome_key: Optional[Tuple[Any, ...]] = None

    @property
    def fact_kind(self) -> str:
        return "region"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "fact_kind": self.fact_kind,
            "fact_id": self.fact_id,
            "region_kind": self.region_kind,
            "function_identity": self.function_identity.to_dict(),
            "boundary": self.boundary.to_dict(),
            "guard_key": _jsonable(self.guard_key),
            "input_relation_key": _jsonable(self.input_relation_key),
            "output_relation_key": _jsonable(self.output_relation_key),
            "state_transformer_key": _jsonable(self.state_transformer_key),
            "termination_outcome_key": _jsonable(self.termination_outcome_key),
            "trap_outcome_key": _jsonable(self.trap_outcome_key),
        }


RiskBearingFact = Union[CallSiteFact, UserOpFact, RegionFact]
RelationalEndpoint = Union[CallSiteFact, UserOpFact, RegionFact]


@dataclass(frozen=True)
class SolverProofRecord:
    proof_id: str
    obligation_id: str
    proof_stage: str
    observation_contract_id: str
    left_object_id: Optional[str]
    right_object_id: Optional[str]
    status: str
    failure_cause: Optional[str] = None
    normalized_assertion_digest: Optional[str] = None
    query_digest: Optional[str] = None
    stage_input_digest: Optional[str] = None
    precondition_digest: Optional[str] = None
    solver_name: Optional[str] = None
    solver_version: Optional[str] = None
    solver_result: Optional[str] = None
    dependency_proof_ids: Tuple[str, ...] = ()
    timeout_ms: Optional[int] = None
    unsupported_details: Tuple[str, ...] = ()
    producer_kind: Optional[str] = None
    schema_version: int = SCHEMA_VERSION

    def __post_init__(self) -> None:
        completed = self.status in {"proven", "inactive_proven", "refuted"}
        if self.status == "proven" and self.solver_result != "unsat":
            raise ValueError("A proven solver-backed artifact requires solver_result='unsat'")
        if self.status == "inactive_proven" and self.solver_result != "unsat":
            raise ValueError("inactive_proven requires an UNSAT reachability query")
        if self.status == "refuted" and self.solver_result != "sat":
            raise ValueError("A refuted artifact requires solver_result='sat'")
        if completed:
            required = {
                "proof_id": self.proof_id,
                "obligation_id": self.obligation_id,
                "proof_stage": self.proof_stage,
                "observation_contract_id": self.observation_contract_id,
                "left_object_id": self.left_object_id,
                "right_object_id": self.right_object_id,
                "normalized_assertion_digest": self.normalized_assertion_digest,
                "query_digest": self.query_digest,
                "stage_input_digest": self.stage_input_digest,
                "precondition_digest": self.precondition_digest,
                "solver_name": self.solver_name,
                "solver_version": self.solver_version,
                "producer_kind": self.producer_kind,
            }
            missing = tuple(name for name, value in required.items() if not value)
            if missing:
                raise ValueError(
                    "A completed proof artifact is missing required fields: "
                    + ", ".join(missing)
                )
            if self.timeout_ms is None or int(self.timeout_ms) <= 0:
                raise ValueError("A completed proof artifact requires a positive timeout_ms")

    def to_dict(self) -> Dict[str, Any]:
        return _jsonable(self.__dict__)


@dataclass(frozen=True)
class InternalSolverProofArtifact:
    """Non-serialized trust boundary tying a record to the exact solver query."""

    record: SolverProofRecord
    query_text: str
    normalized_assertion_text: str
    stage_input_payload: Any
    precondition_payload: Any
    producer_kind: str = "internal_parallel_solver_runner"
    producer_token: Any = field(default=None, repr=False, compare=False)

    def verification_failure(self) -> Optional[str]:
        record = self.record
        if self.producer_token is not _INTERNAL_SOLVER_PRODUCER_TOKEN:
            return "untrusted_producer_token"
        if record.producer_kind != self.producer_kind:
            return "producer_kind_mismatch"
        query_digest = hashlib.sha256(self.query_text.encode("utf-8")).hexdigest()
        assertion_digest = hashlib.sha256(
            self.normalized_assertion_text.encode("utf-8")
        ).hexdigest()
        stage_input_digest = _digest(self.stage_input_payload)
        precondition_digest = _digest(self.precondition_payload)
        if record.query_digest != query_digest:
            return "query_digest_mismatch"
        if record.normalized_assertion_digest != assertion_digest:
            return "normalized_assertion_digest_mismatch"
        if record.stage_input_digest != stage_input_digest:
            return "stage_input_digest_mismatch"
        if record.precondition_digest != precondition_digest:
            return "precondition_digest_mismatch"
        expected_proof_id = _digest(
            (
                "solver_proof_record",
                record.proof_stage,
                record.obligation_id,
                record.left_object_id,
                record.right_object_id,
                record.observation_contract_id,
                query_digest,
                assertion_digest,
                stage_input_digest,
                precondition_digest,
                record.dependency_proof_ids,
                record.solver_name,
                record.solver_version,
                record.solver_result,
                record.timeout_ms,
                self.producer_kind,
            )
        )
        if record.proof_id != expected_proof_id:
            return "proof_id_mismatch"
        return None


@dataclass(frozen=True)
class RelationalCallEffectObligation:
    obligation_id: str
    relation_kind: str
    observation_contract_id: str
    left_fact_id: Optional[str]
    right_fact_id: Optional[str]
    proof_stage: str = "correspondence"
    status: str = "pending"
    failure_cause: Optional[str] = None
    correspondence_basis: str = "none"
    dependency_proof_ids: Tuple[str, ...] = ()

    def to_dict(self) -> Dict[str, Any]:
        return _jsonable(self.__dict__)


@dataclass(frozen=True)
class RelationalEffectCoupling:
    coupling_id: str
    observation_contract_id: str
    left_fact_ids: Tuple[str, ...]
    right_fact_ids: Tuple[str, ...]
    obligation_ids: Tuple[str, ...]
    duplicate_left_fact_ids: Tuple[str, ...] = ()
    duplicate_right_fact_ids: Tuple[str, ...] = ()
    uncovered_left_fact_ids: Tuple[str, ...] = ()
    uncovered_right_fact_ids: Tuple[str, ...] = ()
    structural_coverage_complete: bool = False
    semantic_proof_status: str = "pending"

    def to_dict(self) -> Dict[str, Any]:
        return _jsonable(self.__dict__)


@dataclass(frozen=True)
class Phase2DirectCallEligibility:
    obligation_id: str
    status: str
    blockers: Tuple[str, ...]
    required_solver_stages: Tuple[str, ...]

    def to_dict(self) -> Dict[str, Any]:
        result = _jsonable(self.__dict__)
        result["candidate_only"] = self.status == "candidate"
        result["semantic_proof_status"] = "pending" if self.status == "candidate" else "blocked"
        result["stage_proof_status"] = {
            stage: "pending" for stage in self.required_solver_stages
        }
        return result


@dataclass(frozen=True)
class ObligationProofReadiness:
    obligation_id: str
    decision_eligible: bool
    completed_stages: Tuple[str, ...]
    missing_stages: Tuple[str, ...]
    invalid_stages: Tuple[str, ...]
    blockers: Tuple[str, ...]

    def to_dict(self) -> Dict[str, Any]:
        return _jsonable(self.__dict__)


def _target_category(key: Tuple[Any, ...]) -> str:
    if not key:
        return "unknown"
    kind = str(key[0])
    if kind in {"function", "function_name_only"}:
        return "internal_function"
    if kind.startswith("external_function"):
        return "external_function"
    if kind == "code_address":
        return "code_address"
    return "unknown"


def _target_ref_category(target_ref: Any) -> str:
    if target_ref is None:
        return "unknown"
    if getattr(target_ref, "is_external", None) is True:
        return "external_function"
    if (
        getattr(target_ref, "is_thunk", None) is True
        and getattr(target_ref, "thunked_is_external", None) is True
    ):
        return "external_function"
    is_function = getattr(target_ref, "is_function", None)
    if callable(is_function):
        try:
            if is_function():
                return "internal_function"
        except Exception:
            return "unknown"
    is_code_address = getattr(target_ref, "is_code_address", None)
    if callable(is_code_address):
        try:
            if is_code_address():
                return "code_address"
        except Exception:
            return "unknown"
    return "unknown"


def _cross_binary_expression_shape(value: Any) -> Any:
    """Remove artifact-local identity while preserving expression semantics.

    The result is only a correspondence-candidate key.  It is never accepted as
    a proof that argument values or call effects are equivalent.
    """

    if not isinstance(value, (tuple, list)):
        return value
    normalized = tuple(value)
    if not normalized:
        return ()
    kind = str(normalized[0])
    if kind == "runtime_ref" and len(normalized) >= 2:
        return ("runtime_ref", _cross_binary_expression_shape(normalized[1]))
    if kind == "parameter":
        # Runtime parameter refs are (parameter, program, function, index).
        if len(normalized) >= 4 and isinstance(normalized[-1], int):
            return ("parameter", int(normalized[-1]))
        # Structural parameter keys carry ("int", index) plus the bit width.
        for item in normalized[1:]:
            if (
                isinstance(item, (tuple, list))
                and len(item) == 2
                and str(item[0]) == "int"
                and isinstance(item[1], int)
            ):
                width = normalized[-1] if isinstance(normalized[-1], int) else None
                return ("parameter", int(item[1]), width)
        return ("parameter", "index_unavailable")
    if kind == "address":
        return ("address", "artifact_local_address")
    if kind == "deferred_call":
        target_shape = next(
            (
                _cross_binary_expression_shape(item)
                for item in normalized[1:]
                if isinstance(item, (tuple, list))
                and item
                and str(item[0]) in {
                    "function",
                    "function_name_only",
                    "external_function",
                    "code_address",
                }
            ),
            ("target", "unknown"),
        )
        return ("deferred_call_result", target_shape)
    if kind == "deferred_call_site":
        target_shape = next(
            (
                _cross_binary_expression_shape(item)
                for item in normalized[1:]
                if isinstance(item, (tuple, list))
                and item
                and str(item[0]) in {
                    "function",
                    "function_name_only",
                    "external_function",
                    "code_address",
                }
            ),
            ("target", "unknown"),
        )
        return ("deferred_call_site", target_shape)
    if kind in {"function", "function_name_only", "external_function", "code_address"}:
        return ("target", _target_category(normalized))
    if kind == "pcode_op":
        return ("pcode_op", "artifact_local_operation")
    return tuple(_cross_binary_expression_shape(item) for item in normalized)


def _analysis_function_key(analysis: FunctionReturnAnalysis) -> Optional[Tuple[Any, ...]]:
    return _stable_key(getattr(analysis, "function_ref", None))


def _operation_kind(pcode_ref: Any) -> str:
    mnemonic = str(getattr(pcode_ref, "mnemonic", "") or "").upper()
    if mnemonic == "CALL":
        return "direct_call"
    if mnemonic == "CALLIND":
        return "indirect_call"
    if mnemonic == "CALLOTHER":
        return "userop"
    return "unknown_call"


def _dedupe(values: Iterable[Any]) -> Tuple[Any, ...]:
    result: List[Any] = []
    seen: set[str] = set()
    for value in values:
        key = _digest(value)
        if key in seen:
            continue
        seen.add(key)
        result.append(value)
    return tuple(result)


def _extract_side_facts(
    analysis: FunctionReturnAnalysis,
    *,
    binary_name: str,
) -> Tuple[RiskBearingFact, ...]:
    function_key = _analysis_function_key(analysis)
    binary_id = str(getattr(analysis, "binary_id", None) or binary_name or "") or None
    summary = getattr(analysis, "effect_summary", None)
    buckets: Dict[str, Dict[str, Any]] = {}
    function_ref = getattr(analysis, "function_ref", None)
    expected_function_entry = getattr(function_ref, "entry_offset", None)
    if expected_function_entry is None:
        try:
            expected_function_entry = int(str(getattr(analysis, "entry_point", "")), 0)
        except (TypeError, ValueError):
            expected_function_entry = None

    def belongs_to_caller(pcode_ref: Any) -> bool:
        if pcode_ref is None or expected_function_entry is None:
            return True
        actual_entry = getattr(pcode_ref, "function_entry_offset", None)
        if actual_entry is None:
            return True
        try:
            return int(actual_entry) == int(expected_function_entry)
        except (TypeError, ValueError):
            return False

    def bucket_for(pcode_ref: Any, fallback: Any) -> Dict[str, Any]:
        pcode_key = _stable_key(pcode_ref)
        bucket_key = _digest((pcode_key, fallback if pcode_key is None else None))
        bucket = buckets.setdefault(
            bucket_key,
            {
                "pcode_ref": pcode_ref,
                "pcode_key": pcode_key,
                "arguments": [],
                "parameter_keys": [],
                "guards": [],
                "targets": [],
                "target_categories": [],
                "sources": [],
                "unsupported_reasons": [],
                "effect_classes": [],
                "callee_effect_summary_statuses": [],
                "callee_memory_effect_counts": [],
                "callee_has_unsupported_nested_call": False,
                "callee_control_profile_keys": [],
                "callee_recursive_scc_proven": [],
                "callee_recursive_scc_identities": [],
                "callee_recursive_scc_member_keys": [],
                "callee_return_summary_statuses": [],
                "callee_return_shape_keys": [],
                "multiplicities": [],
                "argument_evidence_complete": [],
                "userop_key": None,
            },
        )
        return bucket

    if summary is not None:
        seen_argument_evidence: set[int] = set()
        for evidence in getattr(summary, "call_argument_evidence", {}).values():
            if evidence is None or id(evidence) in seen_argument_evidence:
                continue
            seen_argument_evidence.add(id(evidence))
            pcode_ref = getattr(evidence, "pcode_op_ref", None)
            if not belongs_to_caller(pcode_ref):
                continue
            bucket = bucket_for(pcode_ref, ("call_argument_evidence", len(seen_argument_evidence)))
            bucket["sources"].append("call_argument_evidence")
            target_key = _stable_key(getattr(evidence, "target_ref", None))
            if target_key is not None:
                bucket["targets"].append(target_key)
            bucket["target_categories"].append(
                _target_ref_category(getattr(evidence, "target_ref", None))
            )
            argument_keys = tuple(
                key
                for argument in getattr(evidence, "arguments", ()) or ()
                for key in [_expression_key(argument)]
                if key is not None
            )
            bucket["arguments"].append(argument_keys)
            parameter_keys = tuple(
                tuple(key)
                for key in getattr(evidence, "callee_param_identities", ()) or ()
                if isinstance(key, (tuple, list))
            )
            if parameter_keys:
                bucket["parameter_keys"].append(parameter_keys)
            for guard_group in getattr(evidence, "path_conditions", ()) or ():
                keys = tuple(
                    key
                    for condition in guard_group or ()
                    for key in [_condition_key(condition)]
                    if key is not None
                )
                bucket["guards"].append(keys)
            bucket["argument_evidence_complete"].append(
                bool(getattr(evidence, "coverage_complete", False))
                and str(getattr(evidence, "recovery_status", "")) == "complete"
            )

        for evidence in getattr(summary, "call_target_resolution_evidence", ()) or ():
            if evidence is None:
                continue
            pcode_ref = getattr(evidence, "pcode_op_ref", None)
            if not belongs_to_caller(pcode_ref):
                continue
            bucket = bucket_for(pcode_ref, ("call_target_resolution_evidence", _stable_key(evidence)))
            bucket["sources"].append("call_target_resolution_evidence")
            target_key = _stable_key(getattr(evidence, "target_ref", None))
            if target_key is not None:
                bucket["targets"].append(target_key)
            bucket["target_categories"].append(
                _target_ref_category(getattr(evidence, "target_ref", None))
            )
            for key in getattr(evidence, "path_condition_keys", ()) or ():
                if isinstance(key, (tuple, list)):
                    bucket["guards"].append((tuple(key),))

        for evidence in getattr(summary, "call_site_effect_summary_evidence", ()) or ():
            if evidence is None:
                continue
            pcode_ref = getattr(evidence, "pcode_op_ref", None)
            if not belongs_to_caller(pcode_ref):
                continue
            bucket = bucket_for(pcode_ref, ("call_site_effect_summary_evidence", _stable_key(evidence)))
            bucket["sources"].append("call_site_effect_summary_evidence")
            target_key = _stable_key(getattr(evidence, "target_ref", None))
            if target_key is not None:
                bucket["targets"].append(target_key)
            bucket["target_categories"].append(
                _target_ref_category(getattr(evidence, "target_ref", None))
            )
            arguments = tuple(
                tuple(key)
                for key in getattr(evidence, "argument_keys", ()) or ()
                if isinstance(key, (tuple, list))
            )
            bucket["arguments"].append(arguments)
            guards = tuple(
                tuple(key)
                for key in getattr(evidence, "path_condition_keys", ()) or ()
                if isinstance(key, (tuple, list))
            )
            bucket["guards"].append(guards)
            bucket["callee_effect_summary_statuses"].append(
                str(getattr(evidence, "summary_status", "inconclusive") or "inconclusive")
            )
            bucket["callee_memory_effect_counts"].append(
                int(getattr(evidence, "memory_effect_count", 0) or 0)
            )
            bucket["callee_has_unsupported_nested_call"] = bool(
                bucket["callee_has_unsupported_nested_call"]
                or getattr(evidence, "has_unsupported_nested_call", False)
            )
            profile_key = getattr(evidence, "callee_control_profile_key", None)
            if isinstance(profile_key, (tuple, list)):
                bucket["callee_control_profile_keys"].append(tuple(profile_key))
            bucket["callee_recursive_scc_proven"].append(
                bool(getattr(evidence, "callee_recursive_scc_proven", False))
            )
            scc_identity = getattr(evidence, "callee_recursive_scc_identity", None)
            if scc_identity:
                bucket["callee_recursive_scc_identities"].append(str(scc_identity))
            bucket["callee_recursive_scc_member_keys"].extend(
                tuple(key)
                for key in getattr(evidence, "callee_recursive_scc_member_keys", ()) or ()
                if isinstance(key, (tuple, list))
            )
            bucket["callee_return_summary_statuses"].append(
                str(getattr(evidence, "return_summary_status", "unavailable") or "unavailable")
            )
            bucket["callee_return_shape_keys"].extend(
                _cross_binary_expression_shape(tuple(key))
                for key in getattr(evidence, "return_value_keys", ()) or ()
                if isinstance(key, (tuple, list))
            )

        for index, site in enumerate(getattr(summary, "unsupported_call_sites", ()) or ()):
            if site is None:
                continue
            pcode_ref = getattr(site, "pcode_op_ref", None)
            if not belongs_to_caller(pcode_ref):
                continue
            bucket = bucket_for(pcode_ref, ("unsupported_call_site", index))
            bucket["sources"].append("unsupported_call_site")
            reason = str(getattr(site, "reason", "unsupported_call") or "unsupported_call")
            bucket["unsupported_reasons"].append(reason)
            target_key = _stable_key(getattr(site, "target_ref", None))
            if target_key is not None:
                bucket["targets"].append(target_key)
            bucket["target_categories"].append(
                _target_ref_category(getattr(site, "target_ref", None))
            )
            arguments = tuple(
                key
                for argument in getattr(site, "arguments", ()) or ()
                for key in [_expression_key(argument)]
                if key is not None
            )
            if arguments:
                bucket["arguments"].append(arguments)
            guards = tuple(
                key
                for condition in getattr(site, "path_conditions", ()) or ()
                for key in [_condition_key(condition)]
                if key is not None
            )
            bucket["guards"].append(guards)
            target_expr_key = _expression_key(getattr(site, "target_expr", None))
            if _operation_kind(pcode_ref) == "userop":
                bucket["userop_key"] = target_expr_key

    for index, info in enumerate(getattr(analysis, "deferred_calls", {}).values()):
        deferred_ref = getattr(info, "deferred_call_ref", None)
        pcode_ref = getattr(deferred_ref, "pcode_op_ref", None)
        if not belongs_to_caller(pcode_ref):
            continue
        bucket = bucket_for(pcode_ref, ("deferred_call", index, _stable_key(deferred_ref)))
        bucket["sources"].append("deferred_call")
        target_key = _stable_key(getattr(info, "target_ref", None))
        if target_key is not None:
            bucket["targets"].append(target_key)
        bucket["target_categories"].append(
            _target_ref_category(getattr(info, "target_ref", None))
        )
        arguments = tuple(
            key
            for argument in getattr(info, "arguments", ()) or ()
            for key in [_expression_key(argument)]
            if key is not None
        )
        if arguments:
            bucket["arguments"].append(arguments)
        bucket["effect_classes"].append(
            str(getattr(info, "effect_class", "unknown_effect") or "unknown_effect")
        )
        multiplicity = getattr(info, "call_site_multiplicity", None)
        if multiplicity is not None:
            bucket["multiplicities"].append(int(multiplicity))

    facts: List[RiskBearingFact] = []
    for bucket_key, bucket in sorted(buckets.items()):
        pcode_ref = bucket["pcode_ref"]
        operation_kind = _operation_kind(pcode_ref)
        identity = ArtifactObjectIdentity(
            binary_id=binary_id,
            function_key=function_key,
            pcode_op_key=bucket["pcode_key"],
        )
        if operation_kind == "userop":
            input_groups = _dedupe(bucket["arguments"])
            input_keys = input_groups[0] if len(input_groups) == 1 else ()
            fact_id = _digest(("userop_fact", identity.stable_key(), bucket["userop_key"]))
            facts.append(
                UserOpFact(
                    fact_id=fact_id,
                    identity=identity,
                    userop_semantic_key=bucket["userop_key"],
                    input_keys=input_keys,
                    guard_keys=tuple(key for group in _dedupe(bucket["guards"]) for key in group),
                    unsupported_reason=(
                        str(bucket["unsupported_reasons"][0])
                        if bucket["unsupported_reasons"]
                        else "userop_semantics_unavailable"
                    ),
                    extraction_status="inconclusive",
                )
            )
            continue

        targets = _dedupe(bucket["targets"])
        argument_groups = _dedupe(bucket["arguments"])
        parameter_groups = _dedupe(bucket["parameter_keys"])
        multiplicities = tuple(sorted(set(bucket["multiplicities"])))
        target_status = "resolved" if len(targets) == 1 and _target_category(targets[0]) != "unknown" else (
            "ambiguous" if len(targets) > 1 else "inconclusive"
        )
        evidence_complete = bool(bucket["argument_evidence_complete"]) and all(
            bucket["argument_evidence_complete"]
        )
        extraction_complete = (
            bucket["pcode_key"] is not None
            and operation_kind in {"direct_call", "indirect_call"}
            and target_status == "resolved"
            and len(argument_groups) == 1
            and evidence_complete
            and not bucket["unsupported_reasons"]
        )
        extraction_failure_causes: List[str] = []
        if bucket["pcode_key"] is None:
            extraction_failure_causes.append("pcode_op_identity_missing")
        if operation_kind not in {"direct_call", "indirect_call"}:
            extraction_failure_causes.append("call_operation_kind_unsupported")
        if target_status == "ambiguous":
            extraction_failure_causes.append("call_target_ambiguous")
        elif target_status != "resolved":
            extraction_failure_causes.append("call_target_evidence_missing")
        if not bucket["argument_evidence_complete"]:
            extraction_failure_causes.append("argument_evidence_missing")
        elif not all(bucket["argument_evidence_complete"]):
            extraction_failure_causes.append("argument_coverage_incomplete")
        if len(argument_groups) == 0:
            extraction_failure_causes.append("argument_group_missing")
        elif len(argument_groups) > 1:
            extraction_failure_causes.append("argument_groups_ambiguous")
        if bucket["unsupported_reasons"]:
            extraction_failure_causes.append("unsupported_call_effect")
        fact_id = _digest(("call_site_fact", identity.stable_key(), operation_kind))
        facts.append(
            CallSiteFact(
                fact_id=fact_id,
                identity=identity,
                operation_kind=operation_kind,
                target_candidates=targets,
                target_categories=tuple(sorted(set(bucket["target_categories"]))),
                target_resolution_status=target_status,
                argument_keys=argument_groups[0] if len(argument_groups) == 1 else (),
                argument_shape_keys=(
                    tuple(
                        _cross_binary_expression_shape(key)
                        for key in argument_groups[0]
                    )
                    if len(argument_groups) == 1
                    else ()
                ),
                callee_parameter_keys=parameter_groups[0] if len(parameter_groups) == 1 else (),
                guard_keys=tuple(key for group in _dedupe(bucket["guards"]) for key in group),
                call_site_multiplicity=multiplicities[0] if len(multiplicities) == 1 else None,
                effect_classes=tuple(sorted(set(bucket["effect_classes"]))),
                callee_effect_summary_statuses=tuple(
                    sorted(set(bucket["callee_effect_summary_statuses"]))
                ),
                callee_memory_effect_counts=tuple(
                    sorted(set(bucket["callee_memory_effect_counts"]))
                ),
                callee_has_unsupported_nested_call=bool(
                    bucket["callee_has_unsupported_nested_call"]
                ),
                callee_control_profile_keys=_dedupe(
                    bucket["callee_control_profile_keys"]
                ),
                callee_recursive_scc_proven=(
                    bool(bucket["callee_recursive_scc_proven"])
                    and all(bucket["callee_recursive_scc_proven"])
                    and len(set(bucket["callee_recursive_scc_identities"])) == 1
                ),
                callee_recursive_scc_identities=tuple(
                    sorted(set(bucket["callee_recursive_scc_identities"]))
                ),
                callee_recursive_scc_member_keys=_dedupe(
                    bucket["callee_recursive_scc_member_keys"]
                ),
                callee_return_summary_statuses=tuple(
                    sorted(set(bucket["callee_return_summary_statuses"]))
                ),
                callee_return_shape_keys=tuple(
                    sorted(
                        _dedupe(bucket["callee_return_shape_keys"]),
                        key=_digest,
                    )
                ),
                unsupported_reasons=tuple(sorted(set(bucket["unsupported_reasons"]))),
                extraction_failure_causes=tuple(dict.fromkeys(extraction_failure_causes)),
                evidence_sources=tuple(sorted(set(bucket["sources"]))),
                extraction_status="complete" if extraction_complete else "inconclusive",
            )
        )
    return tuple(facts)


def _extract_whole_function_region_fact(
    analysis: FunctionReturnAnalysis,
    *,
    binary_name: str,
) -> Optional[RegionFact]:
    profile = getattr(
        getattr(analysis, "effect_summary", None),
        "function_control_effect_profile",
        None,
    )
    if profile is None or not getattr(profile, "region_block_keys", None):
        return None
    binary_id = str(getattr(analysis, "binary_id", None) or binary_name or "") or None
    function_identity = ArtifactObjectIdentity(
        binary_id=binary_id,
        function_key=_analysis_function_key(analysis),
    )
    return_cases = []
    for return_info in getattr(analysis, "returns", ()) or ():
        return_cases.append(
            (
                tuple(
                    key
                    for condition in getattr(return_info, "conditions", ()) or ()
                    for key in [_condition_key(condition)]
                    if key is not None
                ),
                _expression_key(getattr(return_info, "value", None)),
            )
        )
    boundary = RegionBoundaryCertificate(
        entry_block_key=tuple(getattr(profile, "region_entry_block_key", ()) or ()),
        exit_block_keys=tuple(getattr(profile, "region_exit_block_keys", ()) or ()),
        block_keys=tuple(getattr(profile, "region_block_keys", ()) or ()),
        pcode_op_keys=tuple(getattr(profile, "region_pcode_op_keys", ()) or ()),
        live_in_keys=tuple(getattr(profile, "region_live_in_keys", ()) or ()),
        live_out_keys=tuple(getattr(profile, "region_live_out_keys", ()) or ()),
        single_entry=bool(getattr(profile, "region_single_entry", False)),
        all_exits_enumerated=bool(
            getattr(profile, "region_all_exits_enumerated", False)
        ),
        cross_edges_enumerated=bool(
            getattr(profile, "region_cross_edges_enumerated", False)
        ),
        # Return extraction does not yet provide a solver-backed total guard
        # partition certificate, so this remains pending by construction.
        guard_partition_complete=False,
    )
    fact_id = _digest(
        (
            "whole_function_inline_region",
            function_identity.stable_key(),
            boundary.entry_block_key,
            boundary.exit_block_keys,
            boundary.pcode_op_keys,
        )
    )
    return RegionFact(
        fact_id=fact_id,
        function_identity=function_identity,
        boundary=boundary,
        input_relation_key=("live_in_storage", boundary.live_in_keys),
        output_relation_key=("return_partition_candidate", tuple(return_cases)),
        state_transformer_key=(
            "memory_free_candidate"
            if int(getattr(profile, "load_count", 0) or 0) == 0
            and int(getattr(profile, "store_count", 0) or 0) == 0
            else "state_transformer_unavailable"
        ,),
        termination_outcome_key=(
            "termination_coverage_candidate",
            bool(getattr(profile, "terminal_return_coverage_complete", False)),
        ),
        trap_outcome_key=("trap_relation_unproven",),
    )


def _mutually_unique_pairs(
    left_facts: Sequence[RiskBearingFact],
    right_facts: Sequence[RiskBearingFact],
) -> Tuple[Tuple[str, str], ...]:
    left_candidates: Dict[str, List[str]] = {fact.fact_id: [] for fact in left_facts}
    right_candidates: Dict[str, List[str]] = {fact.fact_id: [] for fact in right_facts}
    for left in left_facts:
        for right in right_facts:
            if left.semantic_shape_key() != right.semantic_shape_key():
                continue
            left_candidates[left.fact_id].append(right.fact_id)
            right_candidates[right.fact_id].append(left.fact_id)
    pairs = []
    for left_id, right_ids in left_candidates.items():
        if len(right_ids) != 1:
            continue
        right_id = right_ids[0]
        if right_candidates.get(right_id) == [left_id]:
            pairs.append((left_id, right_id))
    return tuple(sorted(pairs))


_PHASE2_REQUIRED_SOLVER_STAGES = (
    "global_coverage",
    "reachability",
    "guard_relation",
    "target_relation",
    "argument_relation",
    "abi_relation",
    "callee_precondition",
    "return_relation",
    "termination_relation",
    "trap_relation",
    "empty_state_transformer_and_frame",
)


def evaluate_obligation_proof_readiness(
    obligation: RelationalCallEffectObligation,
    eligibility: Phase2DirectCallEligibility,
    proof_artifacts: Sequence[InternalSolverProofArtifact],
) -> ObligationProofReadiness:
    """Validate one typed, dependency-linked UNSAT proof per required stage."""

    blockers: List[str] = []
    if eligibility.obligation_id != obligation.obligation_id:
        blockers.append("eligibility_obligation_id_mismatch")
    if eligibility.status != "candidate":
        blockers.append("obligation_not_solver_candidate")
    records_by_stage: Dict[str, List[SolverProofRecord]] = {}
    verified_records: List[SolverProofRecord] = []
    artifact_failures: List[str] = []
    for artifact in proof_artifacts:
        if type(artifact) is not InternalSolverProofArtifact:
            artifact_failures.append("untrusted_proof_artifact_type")
            continue
        failure = artifact.verification_failure()
        if failure is not None:
            artifact_failures.append(failure)
            continue
        verified_records.append(artifact.record)
    proof_ids = [record.proof_id for record in verified_records]
    duplicate_proof_ids = {
        proof_id for proof_id in proof_ids if proof_ids.count(proof_id) > 1
    }
    if artifact_failures:
        blockers.append("proof_artifact_verification_failed")
    if duplicate_proof_ids:
        blockers.append("duplicate_proof_id")
    records_by_id = {
        record.proof_id: record
        for record in verified_records
        if record.proof_id not in duplicate_proof_ids
    }
    for record in records_by_id.values():
        if (
            record.obligation_id != obligation.obligation_id
            or
            record.left_object_id != obligation.left_fact_id
            or record.right_object_id != obligation.right_fact_id
            or record.observation_contract_id != obligation.observation_contract_id
        ):
            continue
        records_by_stage.setdefault(record.proof_stage, []).append(record)

    completed: List[str] = []
    missing: List[str] = []
    invalid: List[str] = []
    previous_proof_id: Optional[str] = None
    for stage in eligibility.required_solver_stages:
        stage_records = records_by_stage.get(stage, [])
        if not stage_records:
            missing.append(stage)
            previous_proof_id = None
            continue
        if len(stage_records) != 1:
            invalid.append(stage)
            previous_proof_id = None
            continue
        record = stage_records[0]
        dependencies_complete = all(
            dependency_id in records_by_id
            and records_by_id[dependency_id].status in {"proven", "inactive_proven"}
            and records_by_id[dependency_id].left_object_id == obligation.left_fact_id
            and records_by_id[dependency_id].right_object_id == obligation.right_fact_id
            and records_by_id[dependency_id].observation_contract_id
            == obligation.observation_contract_id
            for dependency_id in record.dependency_proof_ids
        )
        chain_complete = (
            previous_proof_id is None
            if stage == eligibility.required_solver_stages[0]
            else previous_proof_id is not None
            and previous_proof_id in record.dependency_proof_ids
        )
        if (
            record.status != "proven"
            or record.solver_result != "unsat"
            or not dependencies_complete
            or not chain_complete
        ):
            invalid.append(stage)
            previous_proof_id = None
            continue
        completed.append(stage)
        previous_proof_id = record.proof_id

    selected_records = {
        records_by_stage[stage][0].proof_id: records_by_stage[stage][0]
        for stage in eligibility.required_solver_stages
        if len(records_by_stage.get(stage, ())) == 1
    }
    visiting: set[str] = set()
    visited: set[str] = set()

    def has_dependency_cycle(proof_id: str) -> bool:
        if proof_id in visiting:
            return True
        if proof_id in visited:
            return False
        visiting.add(proof_id)
        for dependency_id in selected_records[proof_id].dependency_proof_ids:
            if dependency_id in selected_records and has_dependency_cycle(dependency_id):
                return True
        visiting.remove(proof_id)
        visited.add(proof_id)
        return False

    dependency_cycle = any(
        has_dependency_cycle(proof_id) for proof_id in tuple(selected_records)
    )

    if missing:
        blockers.append("required_solver_stages_missing")
    if invalid:
        blockers.append("required_solver_stages_invalid")
    if dependency_cycle:
        blockers.append("proof_dependency_cycle")
    decision_eligible = bool(
        eligibility.status == "candidate"
        and eligibility.obligation_id == obligation.obligation_id
        and eligibility.required_solver_stages
        and not missing
        and not invalid
        and not dependency_cycle
        and not artifact_failures
        and not duplicate_proof_ids
        and len(completed) == len(eligibility.required_solver_stages)
    )
    return ObligationProofReadiness(
        obligation_id=obligation.obligation_id,
        decision_eligible=decision_eligible,
        completed_stages=tuple(completed),
        missing_stages=tuple(missing),
        invalid_stages=tuple(invalid),
        blockers=tuple(blockers),
    )


def _phase2_direct_call_eligibility(
    obligation: RelationalCallEffectObligation,
    left_by_id: Mapping[str, RiskBearingFact],
    right_by_id: Mapping[str, RiskBearingFact],
) -> Phase2DirectCallEligibility:
    blockers: List[str] = []
    left = left_by_id.get(str(obligation.left_fact_id or ""))
    right = right_by_id.get(str(obligation.right_fact_id or ""))
    call_region_pair = (
        isinstance(left, CallSiteFact) and isinstance(right, RegionFact)
    ) or (
        isinstance(left, RegionFact) and isinstance(right, CallSiteFact)
    )
    if call_region_pair:
        region = right if isinstance(right, RegionFact) else left
        call = left if isinstance(left, CallSiteFact) else right
        if call.correspondence_operation_class() != "resolved_internal_call_candidate":
            blockers.append("call_to_region_call_target_incomplete")
        if call.extraction_status != "complete":
            blockers.extend(
                f"call_extraction_{cause}"
                for cause in call.extraction_failure_causes
            )
        if len(call.argument_keys) != len(call.callee_parameter_keys):
            blockers.append("call_parameter_alignment_incomplete")
        if call.unsupported_reasons:
            blockers.append("call_unsupported_effect")
        if call.callee_effect_summary_statuses != ("complete",):
            blockers.append(
                "call_recursive_scc_unproven"
                if call.callee_recursive_scc_proven
                else "call_dependency_closure_missing"
            )
        if call.callee_has_unsupported_nested_call:
            blockers.append("call_dependency_closure_missing")
        if not region.boundary.single_entry:
            blockers.append("inline_region_single_entry_unproven")
        if not region.boundary.all_exits_enumerated:
            blockers.append("inline_region_exit_coverage_missing")
        if not region.boundary.cross_edges_enumerated:
            blockers.append("inline_region_cross_edge_coverage_missing")
        if not region.boundary.guard_partition_complete:
            blockers.append("inline_region_guard_partition_missing")
        if region.state_transformer_key in {None, ("state_transformer_unavailable",)}:
            blockers.append("inline_region_state_transformer_missing")
        blockers.extend(
            (
                "call_to_region_input_relation_proof_missing",
                "call_to_region_output_relation_proof_missing",
                "call_to_region_termination_relation_proof_missing",
                "call_to_region_trap_relation_proof_missing",
            )
        )
        return Phase2DirectCallEligibility(
            obligation_id=obligation.obligation_id,
            status="ineligible",
            blockers=tuple(blockers),
            required_solver_stages=(),
        )
    if not isinstance(left, CallSiteFact) or not isinstance(right, CallSiteFact):
        blockers.append("phase2_requires_paired_call_sites")
        for side, fact in (("left", left), ("right", right)):
            if not isinstance(fact, CallSiteFact):
                continue
            if fact.extraction_status != "complete":
                blockers.extend(
                    f"{side}_extraction_{cause}"
                    for cause in fact.extraction_failure_causes
                )
            if fact.callee_effect_summary_statuses != ("complete",):
                blockers.append(
                    f"{side}_recursive_callee_summary_unproven"
                    if fact.callee_recursive_scc_proven
                    else f"{side}_callee_dependency_closure_missing"
                )
    else:
        for side, fact in (("left", left), ("right", right)):
            if fact.correspondence_operation_class() != "resolved_internal_call_candidate":
                blockers.append(f"{side}_not_resolved_internal_call_candidate")
            if fact.extraction_status != "complete":
                blockers.extend(
                    f"{side}_extraction_{cause}"
                    for cause in fact.extraction_failure_causes
                )
            if fact.target_resolution_status != "resolved":
                blockers.append(f"{side}_target_relation_input_incomplete")
            if fact.target_categories != ("internal_function",):
                blockers.append(f"{side}_noninternal_call_target")
            if fact.unsupported_reasons:
                blockers.append(f"{side}_unsupported_call_effect")
            if len(fact.argument_keys) != len(fact.callee_parameter_keys):
                blockers.append(f"{side}_callee_parameter_alignment_incomplete")
            if fact.callee_effect_summary_statuses != ("complete",):
                blockers.append(f"{side}_callee_effect_summary_incomplete")
                blockers.append(
                    f"{side}_recursive_callee_summary_unproven"
                    if fact.callee_recursive_scc_proven
                    else f"{side}_callee_dependency_closure_missing"
                )
            if fact.callee_memory_effect_counts != (0,):
                blockers.append(f"{side}_callee_not_memory_free")
            if fact.callee_has_unsupported_nested_call:
                blockers.append(f"{side}_callee_nested_call_incomplete")
            if len(fact.callee_control_profile_keys) != 1:
                blockers.append(f"{side}_callee_control_profile_missing")
            else:
                profile_key = fact.callee_control_profile_keys[0]
                if (
                    not profile_key
                    or str(profile_key[0]) != "function_control_effect_profile"
                    or profile_key[-1] is not True
                ):
                    blockers.append(f"{side}_callee_not_acyclic_memory_free_scalar")
            if fact.callee_return_summary_statuses != ("candidate",):
                blockers.append(f"{side}_callee_return_summary_missing")
            if not fact.callee_return_shape_keys:
                blockers.append(f"{side}_callee_return_shape_missing")
        if len(left.argument_keys) != len(right.argument_keys):
            blockers.append("argument_arity_relation_missing")
        if not left.argument_keys and (left.callee_parameter_keys or right.callee_parameter_keys):
            blockers.append("argument_relation_missing")

    return Phase2DirectCallEligibility(
        obligation_id=obligation.obligation_id,
        status="candidate" if not blockers else "ineligible",
        blockers=tuple(blockers),
        required_solver_stages=_PHASE2_REQUIRED_SOLVER_STAGES if not blockers else (),
    )


def _primary_proof_stage(eligibility: Phase2DirectCallEligibility) -> str:
    blockers = set(eligibility.blockers)
    if any("recursive_callee" in item for item in blockers):
        return "recursive_call_scc_unproven"
    if "call_recursive_scc_unproven" in blockers:
        return "recursive_call_scc_unproven"
    if any("call_extraction_pcode_op_identity_missing" in item for item in blockers):
        return "callsite_identity_extraction_missing"
    if any("call_extraction_call_target" in item for item in blockers):
        return "call_target_relation_missing"
    if any("call_extraction_argument" in item for item in blockers):
        return "callsite_argument_evidence_incomplete"
    if "call_parameter_alignment_incomplete" in blockers:
        return "abi_argument_relation_missing"
    if "call_unsupported_effect" in blockers:
        return "callee_effect_summary_incomplete"
    if "call_dependency_closure_missing" in blockers:
        return "callee_dependency_closure_missing"
    if any("inline_region_single_entry" in item for item in blockers):
        return "inline_region_single_entry_missing"
    if any("inline_region_exit" in item or "inline_region_cross_edge" in item for item in blockers):
        return "inline_region_boundary_coverage_missing"
    if any("inline_region_guard_partition" in item for item in blockers):
        return "inline_region_guard_partition_missing"
    if any("inline_region_state_transformer" in item for item in blockers):
        return "inline_region_state_transformer_missing"
    if any("call_to_region_input_relation" in item for item in blockers):
        return "call_to_region_input_relation_missing"
    if any("extraction_pcode_op_identity_missing" in item for item in blockers):
        return "callsite_identity_extraction_missing"
    if any("extraction_call_target" in item for item in blockers):
        return "call_target_relation_missing"
    if any("extraction_argument" in item for item in blockers):
        return "callsite_argument_evidence_incomplete"
    if any("extraction_unsupported_call_effect" in item for item in blockers):
        return "callee_effect_summary_incomplete"
    if any("extraction_call_operation_kind_unsupported" in item for item in blockers):
        return "unsupported_call_operation"
    if "phase2_requires_paired_call_sites" in blockers:
        return "callsite_correspondence_missing"
    if any("callee_dependency_closure_missing" in item for item in blockers):
        return "callee_dependency_closure_missing"
    if any("target" in item for item in blockers):
        return "call_target_relation_missing"
    if any("parameter_alignment" in item or "argument_arity" in item for item in blockers):
        return "abi_argument_relation_missing"
    if any("memory" in item for item in blockers):
        return "memory_effect_relation_missing"
    if any("effect_summary" in item or "nested_call" in item for item in blockers):
        return "callee_effect_summary_incomplete"
    if any("return" in item for item in blockers):
        return "callee_return_relation_missing"
    if blockers:
        return "relational_call_effect_input_incomplete"
    return "relational_call_effect_stage_proofs_missing"


def _fact_ids_for_pcode_key(
    facts: Sequence[RiskBearingFact],
    pcode_key: Optional[Tuple[Any, ...]],
) -> Tuple[str, ...]:
    if pcode_key is None:
        return ()
    return tuple(
        fact.fact_id
        for fact in facts
        if getattr(getattr(fact, "identity", None), "pcode_op_key", None) == pcode_key
    )


def _legacy_blockers(
    analysis: FunctionReturnAnalysis,
    side: str,
    facts: Sequence[RiskBearingFact],
) -> Tuple[Tuple[str, Tuple[str, ...], str], ...]:
    reasons: List[Tuple[str, Tuple[str, ...], str]] = []
    all_fact_ids = tuple(fact.fact_id for fact in facts)
    getter = getattr(analysis, "get_equivalence_blocking_unsafety_reasons", None)
    if callable(getter):
        reasons.extend(
            (f"{side}:{reason}", all_fact_ids, "side_risk_set")
            for reason in getter()
        )
    summary = getattr(analysis, "effect_summary", None)
    if summary is not None:
        argument_evidence = tuple(
            evidence
            for evidence in getattr(summary, "call_argument_evidence", {}).values()
            if evidence is not None
        )
        for index, evidence in enumerate(argument_evidence):
            suffix = f":{index}" if len(argument_evidence) > 1 else ""
            reasons.append(
                (
                    f"{side}:effect_call_argument_evidence{suffix}",
                    _fact_ids_for_pcode_key(
                        facts,
                        _stable_key(getattr(evidence, "pcode_op_ref", None)),
                    ),
                    "callsite_pcode_ref",
                )
            )
        target_evidence = tuple(
            evidence
            for evidence in getattr(summary, "call_target_resolution_evidence", ()) or ()
            if evidence is not None
        )
        for index, evidence in enumerate(target_evidence):
            suffix = f":{index}" if len(target_evidence) > 1 else ""
            reasons.append(
                (
                    f"{side}:effect_call_target_resolution_evidence{suffix}",
                    _fact_ids_for_pcode_key(
                        facts,
                        _stable_key(getattr(evidence, "pcode_op_ref", None)),
                    ),
                    "callsite_pcode_ref",
                )
            )
    return tuple(reasons)


def build_call_effect_shadow_manifest(
    analysis1: FunctionReturnAnalysis,
    analysis2: FunctionReturnAnalysis,
    *,
    binary1_name: str,
    binary2_name: str,
    observation_contract: Optional[EquivalenceObservationContract] = None,
) -> Dict[str, Any]:
    """Build a conservative relational manifest without changing a decision."""

    contract = observation_contract or EquivalenceObservationContract()
    left_facts = _extract_side_facts(analysis1, binary_name=binary1_name)
    right_facts = _extract_side_facts(analysis2, binary_name=binary2_name)
    left_profile = getattr(
        getattr(analysis1, "effect_summary", None),
        "function_control_effect_profile",
        None,
    )
    right_profile = getattr(
        getattr(analysis2, "effect_summary", None),
        "function_control_effect_profile",
        None,
    )
    left_by_id = {fact.fact_id: fact for fact in left_facts}
    right_by_id = {fact.fact_id: fact for fact in right_facts}
    left_fact_pcode_keys = tuple(
        fact.identity.pcode_op_key
        for fact in left_facts
        if fact.identity.pcode_op_key is not None
    )
    right_fact_pcode_keys = tuple(
        fact.identity.pcode_op_key
        for fact in right_facts
        if fact.identity.pcode_op_key is not None
    )
    left_census_keys = tuple(
        getattr(left_profile, "call_like_pcode_op_keys", ()) or ()
    )
    right_census_keys = tuple(
        getattr(right_profile, "call_like_pcode_op_keys", ()) or ()
    )
    left_census_complete = bool(
        left_profile is not None
        and getattr(left_profile, "call_like_identity_complete", False) is True
        and sorted(left_census_keys, key=_digest)
        == sorted(left_fact_pcode_keys, key=_digest)
    )
    right_census_complete = bool(
        right_profile is not None
        and getattr(right_profile, "call_like_identity_complete", False) is True
        and sorted(right_census_keys, key=_digest)
        == sorted(right_fact_pcode_keys, key=_digest)
    )
    pairs = _mutually_unique_pairs(left_facts, right_facts)
    paired_left = {left for left, _ in pairs}
    paired_right = {right for _, right in pairs}
    left_unmatched_calls = tuple(
        fact for fact in left_facts
        if fact.fact_id not in paired_left and isinstance(fact, CallSiteFact)
    )
    right_unmatched_calls = tuple(
        fact for fact in right_facts
        if fact.fact_id not in paired_right and isinstance(fact, CallSiteFact)
    )
    left_region = (
        _extract_whole_function_region_fact(analysis1, binary_name=binary1_name)
        if not left_facts and right_unmatched_calls
        else None
    )
    right_region = (
        _extract_whole_function_region_fact(analysis2, binary_name=binary2_name)
        if not right_facts and left_unmatched_calls
        else None
    )
    left_regions = (left_region,) if left_region is not None else ()
    right_regions = (right_region,) if right_region is not None else ()
    left_endpoints = tuple(left_facts) + left_regions
    right_endpoints = tuple(right_facts) + right_regions
    left_by_id = {fact.fact_id: fact for fact in left_endpoints}
    right_by_id = {fact.fact_id: fact for fact in right_endpoints}

    obligations: List[RelationalCallEffectObligation] = []
    for left_id, right_id in pairs:
        left = left_by_id[left_id]
        right = right_by_id[right_id]
        relation_kind = (
            "call_to_call"
            if isinstance(left, CallSiteFact) and isinstance(right, CallSiteFact)
            else "userop_to_userop"
        )
        obligation_id = _digest(
            ("relational_call_effect_obligation", contract.contract_id, left_id, right_id)
        )
        obligations.append(
            RelationalCallEffectObligation(
                obligation_id=obligation_id,
                relation_kind=relation_kind,
                observation_contract_id=contract.contract_id,
                left_fact_id=left_id,
                right_fact_id=right_id,
                status="pending",
                correspondence_basis="mutually_unique_object_shape_candidate",
            )
        )

    call_to_region_count = 0
    if len(left_unmatched_calls) == 1 and right_region is not None:
        call = left_unmatched_calls[0]
        obligation_id = _digest(
            ("relational_call_to_region_obligation", contract.contract_id, call.fact_id, right_region.fact_id)
        )
        obligations.append(
            RelationalCallEffectObligation(
                obligation_id=obligation_id,
                relation_kind="call_to_region",
                observation_contract_id=contract.contract_id,
                left_fact_id=call.fact_id,
                right_fact_id=right_region.fact_id,
                status="pending",
                correspondence_basis="unique_unmatched_call_to_whole_function_region_candidate",
            )
        )
        paired_left.add(call.fact_id)
        paired_right.add(right_region.fact_id)
        call_to_region_count += 1
    if len(right_unmatched_calls) == 1 and left_region is not None:
        call = right_unmatched_calls[0]
        obligation_id = _digest(
            ("relational_region_to_call_obligation", contract.contract_id, left_region.fact_id, call.fact_id)
        )
        obligations.append(
            RelationalCallEffectObligation(
                obligation_id=obligation_id,
                relation_kind="region_to_call",
                observation_contract_id=contract.contract_id,
                left_fact_id=left_region.fact_id,
                right_fact_id=call.fact_id,
                status="pending",
                correspondence_basis="unique_whole_function_region_to_unmatched_call_candidate",
            )
        )
        paired_left.add(left_region.fact_id)
        paired_right.add(call.fact_id)
        call_to_region_count += 1

    for fact in left_facts:
        if fact.fact_id in paired_left:
            continue
        obligation_id = _digest(
            ("relational_call_effect_obligation", contract.contract_id, fact.fact_id, None)
        )
        obligations.append(
            RelationalCallEffectObligation(
                obligation_id=obligation_id,
                relation_kind="unmatched_left",
                observation_contract_id=contract.contract_id,
                left_fact_id=fact.fact_id,
                right_fact_id=None,
                status="pending",
                failure_cause="callsite_unmatched",
            )
        )
    for fact in right_facts:
        if fact.fact_id in paired_right:
            continue
        obligation_id = _digest(
            ("relational_call_effect_obligation", contract.contract_id, None, fact.fact_id)
        )
        obligations.append(
            RelationalCallEffectObligation(
                obligation_id=obligation_id,
                relation_kind="unmatched_right",
                observation_contract_id=contract.contract_id,
                left_fact_id=None,
                right_fact_id=fact.fact_id,
                status="pending",
                failure_cause="callsite_unmatched",
            )
        )

    for region, side in ((left_region, "left"), (right_region, "right")):
        if region is None:
            continue
        used = region.fact_id in (paired_left if side == "left" else paired_right)
        if used:
            continue
        obligation_id = _digest(
            ("unmatched_inline_region", contract.contract_id, side, region.fact_id)
        )
        obligations.append(
            RelationalCallEffectObligation(
                obligation_id=obligation_id,
                relation_kind=f"unmatched_{side}_region",
                observation_contract_id=contract.contract_id,
                left_fact_id=region.fact_id if side == "left" else None,
                right_fact_id=region.fact_id if side == "right" else None,
                status="pending",
                failure_cause="inline_region_correspondence_ambiguous",
            )
        )

    left_uses = [item.left_fact_id for item in obligations if item.left_fact_id is not None]
    right_uses = [item.right_fact_id for item in obligations if item.right_fact_id is not None]
    duplicate_left = tuple(sorted({item for item in left_uses if left_uses.count(item) > 1}))
    duplicate_right = tuple(sorted({item for item in right_uses if right_uses.count(item) > 1}))
    uncovered_left = tuple(sorted(set(left_by_id) - set(left_uses)))
    uncovered_right = tuple(sorted(set(right_by_id) - set(right_uses)))
    coupling_id = _digest(
        (
            "relational_effect_coupling",
            contract.contract_id,
            tuple(sorted(left_by_id)),
            tuple(sorted(right_by_id)),
            tuple(sorted(item.obligation_id for item in obligations)),
        )
    )
    coupling = RelationalEffectCoupling(
        coupling_id=coupling_id,
        observation_contract_id=contract.contract_id,
        left_fact_ids=tuple(sorted(left_by_id)),
        right_fact_ids=tuple(sorted(right_by_id)),
        obligation_ids=tuple(sorted(item.obligation_id for item in obligations)),
        duplicate_left_fact_ids=duplicate_left,
        duplicate_right_fact_ids=duplicate_right,
        uncovered_left_fact_ids=uncovered_left,
        uncovered_right_fact_ids=uncovered_right,
        structural_coverage_complete=(
            not (duplicate_left or duplicate_right or uncovered_left or uncovered_right)
            and left_census_complete
            and right_census_complete
        ),
        semantic_proof_status="pending",
    )
    phase2_eligibility = tuple(
        _phase2_direct_call_eligibility(item, left_by_id, right_by_id)
        for item in obligations
    )
    solver_proof_artifacts: Tuple[InternalSolverProofArtifact, ...] = ()
    proof_readiness = tuple(
        evaluate_obligation_proof_readiness(
            obligation,
            eligibility,
            solver_proof_artifacts,
        )
        for obligation, eligibility in zip(obligations, phase2_eligibility)
    )

    blocker_mapping: List[Dict[str, Any]] = []
    orphan_blockers: List[str] = []
    for side, analysis, facts in (
        ("function1", analysis1, left_facts),
        ("function2", analysis2, right_facts),
    ):
        for blocker, blocker_fact_ids, mapping_basis in _legacy_blockers(
            analysis,
            side,
            facts,
        ):
            mapped = tuple(
                item.obligation_id
                for item in obligations
                if (
                    item.left_fact_id in blocker_fact_ids
                    if side == "function1"
                    else item.right_fact_id in blocker_fact_ids
                )
            )
            blocker_mapping.append(
                {
                    "legacy_blocker": blocker,
                    "obligation_ids": list(mapped),
                    "mapping_status": "mapped" if mapped else "orphan",
                    "mapping_basis": mapping_basis,
                }
            )
            if not mapped:
                orphan_blockers.append(blocker)

    return {
        "schema_version": SCHEMA_VERSION,
        "mode": "shadow_no_decision_effect",
        "observation_contract": contract.to_dict(),
        "left_facts": [fact.to_dict() for fact in left_facts],
        "right_facts": [fact.to_dict() for fact in right_facts],
        "left_regions": [region.to_dict() for region in left_regions],
        "right_regions": [region.to_dict() for region in right_regions],
        "left_function_control_effect_profile": (
            left_profile.to_dict() if callable(getattr(left_profile, "to_dict", None)) else None
        ),
        "right_function_control_effect_profile": (
            right_profile.to_dict() if callable(getattr(right_profile, "to_dict", None)) else None
        ),
        "pcode_call_census_coverage": {
            "left": {
                "status": "complete" if left_census_complete else "incomplete",
                "profile_identity_complete": bool(
                    left_profile is not None
                    and getattr(left_profile, "call_like_identity_complete", False) is True
                ),
                "census_pcode_op_keys": _jsonable(left_census_keys),
                "fact_pcode_op_keys": _jsonable(left_fact_pcode_keys),
                "missing_fact_pcode_op_keys": _jsonable(
                    tuple(key for key in left_census_keys if key not in left_fact_pcode_keys)
                ),
                "orphan_fact_pcode_op_keys": _jsonable(
                    tuple(key for key in left_fact_pcode_keys if key not in left_census_keys)
                ),
            },
            "right": {
                "status": "complete" if right_census_complete else "incomplete",
                "profile_identity_complete": bool(
                    right_profile is not None
                    and getattr(right_profile, "call_like_identity_complete", False) is True
                ),
                "census_pcode_op_keys": _jsonable(right_census_keys),
                "fact_pcode_op_keys": _jsonable(right_fact_pcode_keys),
                "missing_fact_pcode_op_keys": _jsonable(
                    tuple(key for key in right_census_keys if key not in right_fact_pcode_keys)
                ),
                "orphan_fact_pcode_op_keys": _jsonable(
                    tuple(key for key in right_fact_pcode_keys if key not in right_census_keys)
                ),
            },
        },
        "relational_obligations": [item.to_dict() for item in obligations],
        "coupling": coupling.to_dict(),
        "phase2_direct_call_eligibility": [item.to_dict() for item in phase2_eligibility],
        "solver_proof_records": [
            artifact.record.to_dict() for artifact in solver_proof_artifacts
        ],
        "proof_readiness": [item.to_dict() for item in proof_readiness],
        "proof_stage_backlog": [
            {
                "obligation_id": item.obligation_id,
                "semantic_proof_status": (
                    "pending" if item.status == "candidate" else "blocked"
                ),
                "primary_proof_stage": _primary_proof_stage(item),
                "pending_stages": list(item.required_solver_stages),
                "blocking_stages": list(item.blockers),
            }
            for item in phase2_eligibility
        ],
        "legacy_blocker_mapping": blocker_mapping,
        "orphan_legacy_blockers": orphan_blockers,
        "summary": {
            "left_fact_count": len(left_facts),
            "right_fact_count": len(right_facts),
            "paired_obligation_count": len(pairs),
            "call_to_region_obligation_count": call_to_region_count,
            "unmatched_left_count": sum(
                1 for fact in left_facts if fact.fact_id not in paired_left
            ),
            "unmatched_right_count": sum(
                1 for fact in right_facts if fact.fact_id not in paired_right
            ),
            "legacy_blocker_count": len(blocker_mapping),
            "orphan_legacy_blocker_count": len(orphan_blockers),
            "structural_coverage_complete": coupling.structural_coverage_complete,
            "semantic_proof_status": coupling.semantic_proof_status,
            "phase2_candidate_count": sum(
                1 for item in phase2_eligibility if item.status == "candidate"
            ),
            "decision_eligible_obligation_count": sum(
                1 for item in proof_readiness if item.decision_eligible
            ),
        },
    }


def apply_solver_proof_artifacts_to_manifest(
    manifest: Dict[str, Any],
    proof_artifacts: Sequence[InternalSolverProofArtifact],
) -> Dict[str, Any]:
    """Recompute public readiness exclusively from verified internal artifacts."""

    obligations = tuple(
        RelationalCallEffectObligation(
            obligation_id=str(item.get("obligation_id")),
            relation_kind=str(item.get("relation_kind")),
            observation_contract_id=str(item.get("observation_contract_id")),
            left_fact_id=item.get("left_fact_id"),
            right_fact_id=item.get("right_fact_id"),
            proof_stage=str(item.get("proof_stage") or "correspondence"),
            status=str(item.get("status") or "pending"),
            failure_cause=item.get("failure_cause"),
            correspondence_basis=str(item.get("correspondence_basis") or "none"),
            dependency_proof_ids=tuple(item.get("dependency_proof_ids", ()) or ()),
        )
        for item in manifest.get("relational_obligations", ()) or ()
        if isinstance(item, Mapping)
    )
    eligibilities = tuple(
        Phase2DirectCallEligibility(
            obligation_id=str(item.get("obligation_id")),
            status=str(item.get("status")),
            blockers=tuple(item.get("blockers", ()) or ()),
            required_solver_stages=tuple(item.get("required_solver_stages", ()) or ()),
        )
        for item in manifest.get("phase2_direct_call_eligibility", ()) or ()
        if isinstance(item, Mapping)
    )
    artifacts_by_obligation: Dict[str, List[InternalSolverProofArtifact]] = {}
    for artifact in proof_artifacts:
        artifacts_by_obligation.setdefault(
            str(artifact.record.obligation_id),
            [],
        ).append(artifact)
    readiness: List[ObligationProofReadiness] = []
    for obligation, eligibility in zip(obligations, eligibilities):
        readiness.append(
            evaluate_obligation_proof_readiness(
                obligation,
                eligibility,
                artifacts_by_obligation.get(obligation.obligation_id, ()),
            )
        )
    manifest["solver_proof_records"] = [
        artifact.record.to_dict() for artifact in proof_artifacts
    ]
    manifest["proof_readiness"] = [item.to_dict() for item in readiness]
    summary = manifest.get("summary")
    if isinstance(summary, dict):
        summary["decision_eligible_obligation_count"] = sum(
            1 for item in readiness if item.decision_eligible
        )
        summary["solver_proof_record_count"] = len(proof_artifacts)
        summary["solver_proven_stage_count"] = sum(
            1
            for artifact in proof_artifacts
            if artifact.record.status == "proven"
        )
    return manifest


def _structural_coverage_failure_causes(
    payload: Mapping[str, Any],
) -> Tuple[str, ...]:
    failures: List[str] = []
    if payload.get("structural_coverage_complete") is not True:
        failures.append("structural_endpoint_coverage_incomplete")
    for field_name in (
        "duplicate_left_fact_ids",
        "duplicate_right_fact_ids",
        "uncovered_left_fact_ids",
        "uncovered_right_fact_ids",
    ):
        if payload.get(field_name):
            failures.append(f"{field_name}_present")
    for side in ("left", "right"):
        if payload.get(f"{side}_census_status") != "complete":
            failures.append(f"{side}_pcode_census_incomplete")
        census_keys = tuple(
            _digest(item)
            for item in payload.get(f"{side}_census_pcode_op_keys", ()) or ()
        )
        fact_keys = tuple(
            _digest(item)
            for item in payload.get(f"{side}_fact_pcode_op_keys", ()) or ()
        )
        if sorted(census_keys) != sorted(fact_keys):
            failures.append(f"{side}_pcode_census_fact_key_mismatch")
        if payload.get(f"{side}_missing_fact_pcode_op_keys"):
            failures.append(f"{side}_missing_call_facts_present")
        if payload.get(f"{side}_orphan_fact_pcode_op_keys"):
            failures.append(f"{side}_orphan_call_facts_present")
    mappings = payload.get("legacy_blocker_mapping", ()) or ()
    if any(
        not isinstance(item, Mapping) or item.get("mapping_status") != "mapped"
        for item in mappings
    ):
        failures.append("legacy_blocker_mapping_incomplete")
    if payload.get("orphan_legacy_blockers"):
        failures.append("orphan_legacy_blockers_present")
    return tuple(failures)


@dataclass(frozen=True)
class StructuralCoverageCertificate:
    certificate_id: str
    status: str
    exact_coverage_payload: Mapping[str, Any]
    failure_causes: Tuple[str, ...] = ()
    certificate_kind: str = "deterministic_exact_call_effect_coverage"
    schema_version: int = SCHEMA_VERSION

    def verification_failure(self) -> Optional[str]:
        semantic_failures = _structural_coverage_failure_causes(
            self.exact_coverage_payload
        )
        expected_status = "complete" if not semantic_failures else "incomplete"
        if self.status != expected_status or self.failure_causes != semantic_failures:
            return "certificate_payload_status_mismatch"
        expected = _digest(
            (
                self.certificate_kind,
                int(self.schema_version),
                self.status,
                self.exact_coverage_payload,
                self.failure_causes,
            )
        )
        return None if expected == self.certificate_id else "certificate_digest_mismatch"

    def to_dict(self) -> Dict[str, Any]:
        return {
            "schema_version": int(self.schema_version),
            "certificate_kind": self.certificate_kind,
            "certificate_id": self.certificate_id,
            "status": self.status,
            "exact_coverage_payload": _jsonable(self.exact_coverage_payload),
            "failure_causes": list(self.failure_causes),
            "verification_status": (
                "verified" if self.verification_failure() is None else "invalid"
            ),
            "decision_effect": "diagnostic_precondition_only",
        }


def build_structural_coverage_certificate(
    manifest: Mapping[str, Any],
) -> StructuralCoverageCertificate:
    coupling = manifest.get("coupling") if isinstance(manifest, Mapping) else None
    census = (
        manifest.get("pcode_call_census_coverage")
        if isinstance(manifest, Mapping)
        else None
    )
    coupling = coupling if isinstance(coupling, Mapping) else {}
    census = census if isinstance(census, Mapping) else {}
    left_census = census.get("left") if isinstance(census.get("left"), Mapping) else {}
    right_census = census.get("right") if isinstance(census.get("right"), Mapping) else {}
    payload = {
        "coupling_id": coupling.get("coupling_id"),
        "left_fact_ids": coupling.get("left_fact_ids", ()),
        "right_fact_ids": coupling.get("right_fact_ids", ()),
        "obligation_ids": coupling.get("obligation_ids", ()),
        "duplicate_left_fact_ids": coupling.get("duplicate_left_fact_ids", ()),
        "duplicate_right_fact_ids": coupling.get("duplicate_right_fact_ids", ()),
        "uncovered_left_fact_ids": coupling.get("uncovered_left_fact_ids", ()),
        "uncovered_right_fact_ids": coupling.get("uncovered_right_fact_ids", ()),
        "structural_coverage_complete": coupling.get("structural_coverage_complete"),
        "left_census_status": left_census.get("status"),
        "left_census_pcode_op_keys": left_census.get("census_pcode_op_keys", ()),
        "left_fact_pcode_op_keys": left_census.get("fact_pcode_op_keys", ()),
        "left_missing_fact_pcode_op_keys": left_census.get(
            "missing_fact_pcode_op_keys", ()
        ),
        "left_orphan_fact_pcode_op_keys": left_census.get(
            "orphan_fact_pcode_op_keys", ()
        ),
        "right_census_status": right_census.get("status"),
        "right_census_pcode_op_keys": right_census.get("census_pcode_op_keys", ()),
        "right_fact_pcode_op_keys": right_census.get("fact_pcode_op_keys", ()),
        "right_missing_fact_pcode_op_keys": right_census.get(
            "missing_fact_pcode_op_keys", ()
        ),
        "right_orphan_fact_pcode_op_keys": right_census.get(
            "orphan_fact_pcode_op_keys", ()
        ),
        "legacy_blocker_mapping": manifest.get("legacy_blocker_mapping", ()),
        "orphan_legacy_blockers": manifest.get("orphan_legacy_blockers", ()),
    }
    failure_tuple = _structural_coverage_failure_causes(payload)
    status = "complete" if not failure_tuple else "incomplete"
    certificate_id = _digest(
        (
            "deterministic_exact_call_effect_coverage",
            SCHEMA_VERSION,
            status,
            payload,
            failure_tuple,
        )
    )
    return StructuralCoverageCertificate(
        certificate_id=certificate_id,
        status=status,
        exact_coverage_payload=payload,
        failure_causes=failure_tuple,
    )


__all__ = [
    "ArtifactObjectIdentity",
    "CallSiteFact",
    "EquivalenceObservationContract",
    "ObligationProofReadiness",
    "Phase2DirectCallEligibility",
    "RegionBoundaryCertificate",
    "RegionFact",
    "RelationalCallEffectObligation",
    "RelationalEffectCoupling",
    "SolverProofRecord",
    "UserOpFact",
    "build_call_effect_shadow_manifest",
    "StructuralCoverageCertificate",
    "build_structural_coverage_certificate",
    "evaluate_obligation_proof_readiness",
]
